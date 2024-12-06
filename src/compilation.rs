use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::token::Token;

// Errors that happen during compilation.
// We will want to report these along with a location in the source code.
#[derive(Debug)]
pub struct Error {
    message: String,
    token: Token,

    // When you try to import a module that itself had a compilation error, that is a "secondary error".
    // We may or may not want to report these, depending on the context.
    pub secondary: bool,
}

fn fmt_line_part(f: &mut fmt::Formatter, text: &str, line: &str, index: usize) -> fmt::Result {
    write!(f, "{}\n", line)?;
    for (i, _) in line.char_indices() {
        if i < index {
            write!(f, " ")?;
        } else if i < index + text.len() {
            write!(f, "^")?;
        }
    }
    if index >= line.len() {
        // The token is the final newline.
        write!(f, "^")?;
    }
    write!(f, "\n")
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:\n", self.message)?;
        fmt_line_part(
            f,
            &self.token.text(),
            &self.token.line,
            self.token.start as usize,
        )
    }
}

impl Error {
    pub fn new(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
            secondary: false,
        }
    }

    pub fn secondary(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
            secondary: true,
        }
    }

    pub fn range(&self) -> Range {
        self.token.range()
    }
}

pub type Result<T> = std::result::Result<T, Error>;
