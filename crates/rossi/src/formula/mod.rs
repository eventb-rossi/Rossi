//! Typed formula objects for the Event-B mathematical language:
//! immutable nodes classified by stable numeric tags ([`tag`]), bound
//! identifiers referenced by de Bruijn index, and types attached
//! directly to expression nodes. The parser builds these directly; the
//! structural component types live in [`crate::ast`].

pub mod assignment;
mod ba;
mod caches;
pub mod decl;
pub mod expression;
pub mod extension;
pub mod factory;
pub mod fresh;
mod hashing;
pub mod occurrences;
pub mod position;
pub mod predicate;
pub mod rewrite;
mod subst;
pub mod tag;
pub mod typecheck;
pub mod typenv;
pub mod types;
pub mod wd;

pub use crate::ast::{Located, SourceId, Span};
pub use assignment::{Assignment, AssignmentKind};
pub use decl::BoundIdentDecl;
pub use expression::{Expression, ExpressionKind, Form};
pub use extension::{ExpressionExtension, Extension, FormulaExtension, PredicateExtension};
pub use factory::{ExtensionError, FactoryError, FormulaFactory};
pub use fresh::FreshNameSolver;
pub use position::{FormulaRef, Position, PositionError};
pub use predicate::{Predicate, PredicateKind};
pub use rewrite::{FormulaRewriter, normalize_quantified_predicate};
pub use typecheck::{ProblemKind, TypeCheckProblem, TypeCheckResult};
pub use typenv::{InferredTypeEnvironment, SealedTypeEnvironment, TypeEnvironmentBuilder};
pub use types::Type;
