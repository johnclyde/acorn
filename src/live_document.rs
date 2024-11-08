use im::Vector;

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
    // The current text of the line
    text: String,

    // The index of this line the last time the document was saved.
    // If this line has been modified since the last save, this will be None.
    saved_index: Option<i32>,
}

fn make_lines(text: &str) -> Vector<LiveLine> {
    text.lines()
        .into_iter()
        .enumerate()
        .map(|(index, line)| LiveLine {
            text: line.to_string(),
            saved_index: Some(index as i32),
        })
        .collect()
}

impl LiveDocument {
    // Called when a file is opened, so we don't have any history before this version.
    pub fn new(text: &str, version: i32) -> LiveDocument {
        LiveDocument {
            lines: make_lines(text),
            live_version: version,
            saved_version: version,
        }
    }

    // Changes the document to have a new live version.
    pub fn change(&mut self, new_live_version: i32) {
        self.live_version = new_live_version;
    }

    // Changes the document to have the provided text, to save the current live version.
    // Returns the version (which is both saved and live).
    pub fn save(&mut self, text: &str) -> i32 {
        self.lines = make_lines(text);
        self.saved_version = self.live_version;
        self.saved_version
    }

    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }
}
