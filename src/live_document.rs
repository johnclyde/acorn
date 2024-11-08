// A live document is in the process of being edited.
// It has a version number that is incremented each time the document is edited.
// We also track the version number it had the last time it was saved.
pub struct LiveDocument {
    text: String,

    // The most recent version we have.
    // TODO: add this
    // live_version: i32,

    // The version number the document had the last time it was saved.
    saved_version: i32,
}

impl LiveDocument {
    pub fn new(text: String, version: i32) -> LiveDocument {
        LiveDocument {
            text,
            saved_version: version,
        }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn saved_version(&self) -> i32 {
        self.saved_version
    }
}
