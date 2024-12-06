use std::fmt;

use crate::token::Token;

// Errors that happen during compilation.
// We will want to report these along with a location in the source code.
#[derive(Debug)]
pub struct Error {
    pub message: String,
    pub token: Token,

    // external is true when the root error is in a different module.
    pub external: bool,
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
            external: false,
        }
    }

    pub fn external(token: &Token, message: &str) -> Self {
        Error {
            message: message.to_string(),
            token: token.clone(),
            external: true,
        }
    }
}

pub type Result<T> = std::result::Result<T, Error>;
