//! The name-bound formula types being replaced by [`crate::formula`].
//!
//! Everything here re-exports under its historical `ast::…` paths, so
//! call sites are unaffected while the two models coexist. The module
//! is deleted once the parser, printer and their consumers have moved
//! to the typed formula model.

pub mod action;
pub mod expression;
pub mod predicate;
pub mod visit_mut;
pub mod walk;

// The moved modules reach their siblings and the structural types
// through `super::…`; these re-exports keep those paths meaningful.
pub use super::{
    ClauseRegion, Component, Context, Event, FileMetadata, Ident, InitialisationEvent,
    LabeledAction, LabeledPredicate, Machine, NamedElement, SetDeclaration, Span, TypedIdentifier,
};
pub use action::{Action, ActionKind};
pub use expression::{
    AtomicBuiltinKind, BuiltinFunction, Expression, ExpressionKind, IdentPattern,
};
pub use predicate::{BuiltinPredicate, Predicate, PredicateKind};
