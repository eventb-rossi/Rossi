//! Stored proof skeletons: the shape of a proof as a `.bpr` records it.
//!
//! A skeleton node pairs the recorded rule with the reasoner input
//! pieces its producer serialized; an open leaf has no rule. Reuse
//! applies the recorded rules structurally; replay re-runs the
//! reasoners on the recorded inputs and ignores the recorded rules.

use std::collections::BTreeMap;

use rossi::formula::{Expression, Predicate};

use crate::rule::Rule;

/// One stored proof-tree node.
#[derive(Debug, Clone, PartialEq)]
pub struct Skeleton {
    /// The recorded rule; `None` for an open leaf.
    pub rule: Option<StoredRule>,
    /// One child per antecedent of the rule.
    pub children: Vec<Skeleton>,
}

impl Skeleton {
    /// An open leaf.
    pub fn open() -> Skeleton {
        Skeleton {
            rule: None,
            children: Vec::new(),
        }
    }
}

/// A recorded rule together with its serialized reasoner input.
#[derive(Debug, Clone, PartialEq)]
pub struct StoredRule {
    /// The rule as recorded (confidence already capped at uncertain
    /// when the reasoner is untrusted).
    pub rule: Rule,
    /// The reasoner input pieces, for replay.
    pub input: StoredInput,
}

/// The serialized reasoner input of one rule, keyed as the reasoner
/// wrote them (the storage's leading `.` stripped). Anything a
/// reasoner can recover from the recorded rule itself is not
/// serialized — deserializers also read the rule.
#[derive(Debug, Clone, Default, PartialEq)]
pub struct StoredInput {
    /// String inputs, e.g. a rewrite position.
    pub strings: BTreeMap<String, String>,
    /// Predicate inputs; a hole in the stored list stays `None`.
    pub preds: BTreeMap<String, Vec<Option<Predicate>>>,
    /// Expression inputs; a hole in the stored list stays `None`.
    pub exprs: BTreeMap<String, Vec<Option<Expression>>>,
}
