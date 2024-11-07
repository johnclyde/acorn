pub struct LiveDocument {
    text: String,
    version: i32,
}

impl LiveDocument {
    pub fn new(text: String, version: i32) -> LiveDocument {
        LiveDocument { text, version }
    }

    pub fn text(&self) -> &str {
        &self.text
    }

    pub fn version(&self) -> i32 {
        self.version
    }
}
