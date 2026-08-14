//! Proof-obligation generation over the typed checked model.
//!
//! Consumes the [`crate::sc_model::ScModel`] a build produces and
//! emits one `.bpo` file per component, describing what must be proved
//! for the model to be correct: well-definedness of its formulas,
//! preservation of its invariants, feasibility of its actions,
//! refinement of its abstraction, and convergence of its events.

pub mod hyp;
pub mod model;
pub mod natures;

pub use model::{Hint, PoFile, PogPredicate, PogSource, ProofObligation, Role};
pub use natures::Nature;
