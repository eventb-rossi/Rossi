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

use std::sync::OnceLock;

pub mod bpr;
pub mod bps;
pub mod builder;
pub mod confidence;
pub mod deps;
pub mod hyp_action;
pub mod po_loader;
pub mod reasoners;
pub mod registry;
pub mod rule;
pub mod sequent;
pub mod skeleton;
pub mod status;
pub mod tree;
mod variations;
mod xml;

pub use bpr::{BprError, Keep, ProofBody, ProofEntry, StoredProof, read_bpr, visit_bpr};
pub use bps::{PsStatus, read_bps};
pub use builder::{
    Reasoner, ReasonerProvider, RegistryProvider, ReplayHints, rebuild, replay, reuse,
};
pub use confidence::Confidence;
pub use deps::{ProofDependencies, is_proof_reusable};
pub use hyp_action::HypAction;
pub use po_loader::{PoError, PoFile, PoProject};
pub use registry::{ReasonerDesc, Registration};
pub use rule::{Antecedent, Rule};
pub use sequent::{ProverSequent, TypedIdent};
pub use skeleton::{Skeleton, StoredInput, StoredRule};
pub use status::{StatusVerdict, compute_status};
pub use tree::ProofTreeNode;

/// The worker pool for checking components in parallel, one per
/// process. Its threads carry stacks sized for any accepted formula,
/// so the parser never falls back to mapping a stack segment per call
/// — on default worker stacks that fallback fires on every parse and
/// dominates the run.
pub fn thread_pool() -> &'static rayon::ThreadPool {
    static POOL: OnceLock<rayon::ThreadPool> = OnceLock::new();
    POOL.get_or_init(|| {
        rayon::ThreadPoolBuilder::new()
            .stack_size(rossi::nesting::PARSER_STACK_SIZE)
            .build()
            .expect("worker threads spawn")
    })
}

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

    /// A core seqprover reasoner descriptor by short id.
    pub fn desc(short: &str) -> crate::registry::ReasonerDesc {
        crate::registry::resolve(&format!("org.eventb.core.seqprover.{short}"))
    }
}
