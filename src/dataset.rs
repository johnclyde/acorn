use std::fs::File;

use chrono::Local;
use ndarray::Array1;
use ndarray_npy::NpzWriter;

use crate::common;
use crate::features::Features;

// The dataset is created from a verification run.
// The dataset tracks which activated proof steps are used in the proof.
// features is the features for a particular proof step.
// label is true if the proof step is used in the proof, and false if it is not.
pub struct Dataset {
    pub features: Vec<Features>,
    pub labels: Vec<bool>,
}

impl Dataset {
    pub fn new() -> Self {
        Dataset {
            features: vec![],
            labels: vec![],
        }
    }

    pub fn add(&mut self, features: Features, label: bool) {
        self.features.push(features);
        self.labels.push(label);
    }

    // Saves the dataset to the files/datasets directory.
    pub fn save_with_name(
        &self,
        relative_filename: &str,
    ) -> Result<(), Box<dyn std::error::Error>> {
        let mut d = common::files_dir();
        d.push("datasets");
        d.push(relative_filename);
        let file = File::create(d)?;
        let mut npz = NpzWriter::new(file);
        let features = Features::to_array2(&self.features);
        let labels = Array1::from(self.labels.clone());
        npz.add_array("features", &features)?;
        npz.add_array("labels", &labels)?;
        npz.finish()?;
        Ok(())
    }

    pub fn save_with_tag(&self, tag: &str) {
        let now = Local::now();
        let suffix = now.format("%Y-%m-%d-%H:%M:%S.npz").to_string();
        let filename = format!("{}-{}", tag, suffix);
        println!(
            "Saving dataset with {} items to {}",
            self.features.len(),
            filename
        );
        self.save_with_name(&filename).unwrap();
    }

    pub fn save(&self) {
        self.save_with_tag("dataset");
    }
}
