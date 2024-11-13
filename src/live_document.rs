use std::sync::OnceLock;

use im::Vector;
use regex::Regex;
use tower_lsp::lsp_types::Range;

static LINE_SPLIT_REGEX: OnceLock<Regex> = OnceLock::new();

// Respects either Windows or non-Windows line endings.
fn split_lines(text: &str) -> impl Iterator<Item = &str> {
    let re = LINE_SPLIT_REGEX.get_or_init(|| Regex::new(r"\r\n|\n").unwrap());
    re.split(text)
}

// A live document is in the process of being edited.
// It has a version number that is incremented each time the document is edited.
// We also track the version number it had the last time it was saved.
pub struct LiveDocument {
    lines: Vector<LiveLine>,

    // The most recent version we have.
    live_version: i32,

    // The version number the document had the last time it was saved.
    saved_version: i32,
}

// Each line in a LiveDocument has a LiveLine.
#[derive(Clone)]
struct LiveLine {
    // The current text of the line.
    // These do not include \n's.
    text: String,

    // The index of this line the last time the document was saved.
    // If this line has been modified since the last save, this will be None.
    saved_index: Option<u32>,
}

// The empty string gives one empty line, numbered 0.
fn numbered_lines(text: &str) -> Vector<LiveLine> {
    split_lines(text)
        .enumerate()
        .map(|(index, line)| LiveLine {
            text: line.to_string(),
            saved_index: Some(index as u32),
        })
        .collect()
}

// The empty string gives one empty line.
fn nonnumbered_lines(text: &str) -> Vector<LiveLine> {
    split_lines(text)
        .map(|line| LiveLine {
            text: line.to_string(),
            saved_index: None,
        })
        .collect()
}

impl LiveDocument {
    // Called when a file is opened, so we don't have any history before this version.
    pub fn new(text: &str, version: i32) -> LiveDocument {
        LiveDocument {
            lines: numbered_lines(text),
            live_version: version,
            saved_version: version,
        }
    }

    // Changes the document to have a new live version.
    // range is the range in the initial document that was removed.
    // If there is no range, that means the entire document was replaced.
    // text is the text that was inserted at that range.
    pub fn change(
        &mut self,
        range: Option<Range>,
        text: &str,
        new_live_version: i32,
    ) -> Result<(), String> {
        self.live_version = new_live_version;
        let range = match range {
            Some(range) => range,
            None => {
                // Replace the whole document. No line is the same as it was.
                self.lines = nonnumbered_lines(text);
                return Ok(());
            }
        };
        let start_line = range.start.line as usize;
        let end_line = range.end.line as usize;

        if end_line < start_line {
            return Err(format!(
                "end line {} is before start line {}",
                end_line, start_line
            ));
        }
        if end_line >= self.lines.len() {
            // Something is going wrong, but we have no way to handle errors.
            return Err(format!(
                "end line is {} but we only have {} lines",
                end_line,
                self.lines.len()
            ));
        }

        // We are going to replace part of the start line and end line, but maybe not the whole thing.
        // Find the prefix and suffix that we are keeping.
        let prefix: String = if let Some(line) = self.lines.get(start_line) {
            let start_character = range.start.character as usize;
            line.text.chars().take(start_character).collect()
        } else {
            "".to_string()
        };
        let suffix: String = if let Some(line) = self.lines.get(end_line) {
            let end_character = range.end.character as usize;
            line.text.chars().skip(end_character).collect()
        } else {
            "".to_string()
        };
        let combined = format!("{}{}{}", prefix, text, suffix);
        let new_lines = nonnumbered_lines(&combined);
        let keep_right = if end_line < self.lines.len() {
            self.lines.split_off(end_line + 1)
        } else {
            Vector::new()
        };
        let _discard = self.lines.split_off(start_line);
        self.lines.append(new_lines);
        self.lines.append(keep_right);
        Ok(())
    }

    // Changes the document to have the provided text, to save the current live version.
    // Returns the version (which is both saved and live).
    pub fn save(&mut self, text: &str) -> i32 {
        self.lines = numbered_lines(text);
        self.saved_version = self.live_version;
        self.saved_version
    }

    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }

    // Returns a display string.
    // It has each line with a "." in front if it's unchanged, a "*" if it's changed.
    pub fn display(&self) -> String {
        let mut result = vec![];
        for line in self.lines.iter() {
            let prefix = match line.saved_index {
                Some(_) => ".",
                None => "*",
            };
            result.push(format!("{} {}", prefix, line.text));
        }
        result.join("\n")
    }

    // The prefix of the line up to the provided point.
    pub fn get_prefix(&self, line: u32, character: u32) -> String {
        if let Some(line) = self.lines.get(line as usize) {
            line.text.chars().take(character as usize).collect()
        } else {
            "".to_string()
        }
    }

    // When we want to do lookups based on a position in a modified file, we have the problem that
    // we don't have an evaluated environment for the modified file. So we find a nearby point
    // in the last environment we evaluated, and use that environment.
    pub fn get_env_line(&self, current_line: u32) -> u32 {
        for line in self.lines.take(current_line as usize + 1).iter().rev() {
            if let Some(saved_index) = line.saved_index {
                // This line is unchanged from the saved version.
                return saved_index;
            }
        }
        0
    }
}
