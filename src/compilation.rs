use std::fmt;

use tower_lsp::lsp_types::Range;

use crate::token::Token;

// Errors that happen during compilation.
// We will want to report these along with a location in the source code.
#[derive(Debug)]
pub struct Error {
    // The range of tokens the error occurred at.
    first_token: Token,
    last_token: Token,

    message: String,

    // When you try to import a module that itself had a compilation error, that is a "secondary error".
    // We may or may not want to report these.
    // If the primary location is visible, there's no point in also reporting the secondary.
    // But if the primary location is inaccessible, we should report it at the secondary location.
    pub secondary: bool,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}:\n", self.message)?;
        write!(f, "{}\n", self.first_token.line)?;
        for (i, _) in self.first_token.line.char_indices() {
            let i = i as u32;
            if i < self.first_token.start {
                // This is before the area to highlight.
                write!(f, " ")?;
            } else if self.first_token.line_number == self.last_token.line_number
                && i >= self.last_token.start + self.last_token.len
            {
                // This is after the area to highlight.
                break;
            } else {
                // This is the area to highlight.
                write!(f, "^")?;
            }
        }
        if self.first_token.start as usize >= self.first_token.line.len() {
            // The error is at the end of the line.
            write!(f, "^")?;
        }
        write!(f, "\n")
    }
}

impl Error {
    pub fn new(first_token: &Token, last_token: &Token, message: &str) -> Self {
        Error {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            secondary: false,
        }
    }

    pub fn secondary(first_token: &Token, last_token: &Token, message: &str) -> Self {
        Error {
            first_token: first_token.clone(),
            last_token: last_token.clone(),
            message: message.to_string(),
            secondary: true,
        }
    }

    pub fn range(&self) -> Range {
        Range::new(self.first_token.range().start, self.last_token.range().end)
    }
}

pub type Result<T> = std::result::Result<T, Error>;

pub trait ErrorSource {
    fn error(&self, message: &str) -> Error;
}
