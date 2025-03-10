use std::collections::BTreeSet;

use crate::module::ModuleId;

// The TheoremCacheEntry contains information about how we proved the goals required for a theorem.
enum TheoremCacheEntry {
    // We skipped this theorem, perhaps because we cached the fact that it was provable.
    Skipped,

    // We used these premises to prove the theorem.
    Premises(BTreeSet<(ModuleId, String)>),
}

impl TheoremCacheEntry {
    fn add_premise(&mut self, qualified_name: (ModuleId, String)) {
        match self {
            TheoremCacheEntry::Skipped => {
                panic!("cannot partially skip premise cache");
            }
            TheoremCacheEntry::Premises(premises) => {
                premises.insert(qualified_name);
            }
        }
    }
}

// The TheoremCache applies to a single module.
pub struct TheoremCache {
    theorems: Vec<(String, TheoremCacheEntry)>,
}

impl TheoremCache {
    pub fn new() -> TheoremCache {
        TheoremCache { theorems: vec![] }
    }

    pub fn skip(&mut self, theorem: &str) {
        if let Some((last_theorem, _)) = self.theorems.last() {
            if last_theorem == theorem {
                return;
            }
        }
        self.theorems
            .push((theorem.to_string(), TheoremCacheEntry::Skipped));
    }

    pub fn report_premises(&mut self, theorem: &str, new_premises: BTreeSet<(ModuleId, String)>) {
        if let Some((last_theorem, existing_premises)) = self.theorems.last_mut() {
            if last_theorem == theorem {
                for premise in new_premises {
                    existing_premises.add_premise(premise);
                }
                return;
            }
        }
        self.theorems.push((
            theorem.to_string(),
            TheoremCacheEntry::Premises(new_premises),
        ));
    }
}
