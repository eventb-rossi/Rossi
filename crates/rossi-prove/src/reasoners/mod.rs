//! Reasoner implementations, keyed by the registry.
//!
//! Each implemented reasoner re-derives its rule from a sequent and
//! the stored rule (the input-recovery bridge: anything the storage
//! does not serialize explicitly is recovered from the recorded
//! rule). The table below is the replay counterpart of the registry:
//! only trusted descriptors resolve, so a version-conflicting or
//! unknown reasoner never replays.

pub mod structural;

use rossi::formula::tag::AssocPredOp;
use rossi::formula::{Predicate, PredicateKind};

use crate::builder::Reasoner;
use crate::registry::ReasonerDesc;

/// The implementation for `desc`, when the descriptor is trusted and a
/// Rust implementation exists at its version.
pub fn implementation(desc: &ReasonerDesc) -> Option<&'static dyn Reasoner> {
    if !desc.is_trusted() {
        return None;
    }
    let short = desc.id().strip_prefix("org.eventb.core.seqprover.")?;
    let imp: &'static dyn Reasoner = match short {
        "trueGoal" => &structural::TrueGoal,
        "falseHyp" => &structural::FalseHyp,
        "hyp" => &structural::Hyp,
        "impI" => &structural::ImpI,
        "allI" => &structural::AllI,
        "conj" => &structural::Conj,
        "contrHyps" => &structural::ContrHyps,
        "review" => &structural::Review,
        "mngHyp" => &structural::MngHyp,
        _ => return None,
    };
    Some(imp)
}

/// The conjuncts of a conjunction (or the
/// predicate itself), duplicates removed keeping first positions.
pub(crate) fn break_possible_conjunct(pred: &Predicate) -> Vec<Predicate> {
    let conjuncts: Vec<Predicate> = match pred.kind() {
        PredicateKind::Associative {
            op: AssocPredOp::LAnd,
            children,
        } => children.clone(),
        _ => vec![pred.clone()],
    };
    dedup_preserving_order(conjuncts)
}

/// Insertion-ordered set semantics: first occurrence wins, order kept.
pub(crate) fn dedup_preserving_order(preds: Vec<Predicate>) -> Vec<Predicate> {
    let mut out: Vec<Predicate> = Vec::with_capacity(preds.len());
    for pred in preds {
        if !out.contains(&pred) {
            out.push(pred);
        }
    }
    out
}
