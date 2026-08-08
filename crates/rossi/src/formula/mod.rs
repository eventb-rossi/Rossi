//! Typed formula objects for the Event-B mathematical language.
//!
//! This module is the successor to the name-based formula types in
//! [`crate::ast`]: immutable nodes classified by stable numeric tags
//! ([`tag`]), bound identifiers referenced by de Bruijn index, and types
//! attached directly to expression nodes. It is built up alongside the
//! existing AST and is not yet wired into the parser.

pub mod assignment;
mod caches;
pub mod decl;
pub mod expression;
pub mod extension;
pub mod factory;
pub mod fresh;
mod hashing;
pub mod lower;
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

pub use crate::ast::Span;
pub use assignment::{Assignment, AssignmentKind};
pub use decl::BoundIdentDecl;
pub use expression::{Expression, ExpressionKind, Form};
pub use extension::{ExpressionExtension, Extension, FormulaExtension, PredicateExtension};
pub use factory::{ExtensionError, FactoryError, FormulaFactory};
pub use fresh::FreshNameSolver;
pub use position::{FormulaRef, Position, PositionError};
pub use predicate::{Predicate, PredicateKind};
pub use rewrite::FormulaRewriter;
pub use typecheck::{ProblemKind, TypeCheckProblem, TypeCheckResult};
pub use typenv::{InferredTypeEnvironment, SealedTypeEnvironment, TypeEnvironmentBuilder};
pub use types::Type;
