//! Sequent-prover kernel for Event-B: the mechanics behind checking
//! stored proofs.
//!
//! The kernel is trusting: applying a proof rule performs structural
//! checks only (needed hypotheses present, goal equal, antecedents
//! well-formed) and never re-derives logical entailment — soundness
//! lives in the reasoners that produce rules. Stored proofs are
//! checked by *reuse* (re-applying their recorded rules) and *replay*
//! (re-running their reasoners), the two modes the proof builder
//! combines.

pub mod confidence;
pub mod hyp_action;
pub mod rule;
pub mod sequent;
pub mod tree;

pub use confidence::Confidence;
pub use hyp_action::HypAction;
pub use rule::{Antecedent, Rule};
pub use sequent::{ProverSequent, TypedIdent};
pub use tree::ProofTreeNode;

#[cfg(test)]
pub(crate) mod test_util {
    use rossi::formula::{Predicate, SealedTypeEnvironment, Type, TypeEnvironmentBuilder};
    use rossi::parse_predicate_str;

    /// A sealed environment from `(name, canonical type)` pairs.
    pub fn env(bindings: &[(&str, &str)]) -> SealedTypeEnvironment {
        let mut builder = TypeEnvironmentBuilder::new();
        for (name, ty) in bindings {
            builder.insert(*name, Type::parse_rodin(ty).expect("test type"));
        }
        builder.make_snapshot()
    }

    /// A predicate parsed and type-checked against `env`.
    pub fn pred(env: &SealedTypeEnvironment, source: &str) -> Predicate {
        parse_predicate_str(source)
            .expect("test predicate")
            .type_check(env)
            .typed
            .expect("test predicate types")
    }
}
