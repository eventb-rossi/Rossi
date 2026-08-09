//! Predicate AST nodes
//!
//! Predicates represent logical formulas in Event-B, including
//! comparisons, logical connectives, and quantifiers.

use super::{Expression, Ident, Span, TypedIdentifier};

pub use crate::operators::{BuiltinPredicate, ComparisonOp, LogicalOp, Quantifier};

/// An Event-B predicate (logical formula) together with its source location.
///
/// The predicate variant lives in [`PredicateKind`]; `span` records where the
/// predicate came from in the source text, or `None` for synthesized / Rodin-XML
/// nodes. Equality ignores `span` (see [`Expression`] for the rationale).
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Predicate {
    /// The predicate variant.
    pub kind: PredicateKind,
    /// Source span of this predicate, if known.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<Span>,
}

impl Predicate {
    /// Wrap a kind with an explicit (optional) span.
    pub fn new(kind: PredicateKind, span: Option<Span>) -> Self {
        Self { kind, span }
    }
}

/// Equality compares the kind only; the span is positional metadata.
impl PartialEq for Predicate {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Predicate {}

impl From<PredicateKind> for Predicate {
    /// Build a span-less predicate from its kind.
    fn from(kind: PredicateKind) -> Self {
        Self { kind, span: None }
    }
}

/// The variants of an Event-B [`Predicate`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum PredicateKind {
    /// Boolean true
    True,

    /// Boolean false
    False,

    /// Comparison between two expressions
    Comparison {
        op: ComparisonOp,
        left: Expression,
        right: Expression,
    },

    /// Logical negation
    Not(Box<Predicate>),

    /// Binary logical operation
    Logical {
        op: LogicalOp,
        left: Box<Predicate>,
        right: Box<Predicate>,
    },

    /// Quantified predicate: ∀x·P or ∃x·P
    Quantified {
        quantifier: Quantifier,
        identifiers: Vec<TypedIdentifier>,
        predicate: Box<Predicate>,
    },

    /// User-defined predicate function application
    Application {
        function: Ident,
        arguments: Vec<Expression>,
    },

    /// Built-in predicate application: finite(S), partition(S, A, B)
    BuiltinApplication {
        predicate: BuiltinPredicate,
        arguments: Vec<Expression>,
    },
}

impl Predicate {
    /// Create a comparison predicate
    pub fn comparison(op: ComparisonOp, left: Expression, right: Expression) -> Self {
        PredicateKind::Comparison { op, left, right }.into()
    }

    /// Create a logical operation
    pub fn logical(op: LogicalOp, left: Predicate, right: Predicate) -> Self {
        PredicateKind::Logical {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
        .into()
    }

    /// Create a negation
    pub fn negation(predicate: Predicate) -> Self {
        PredicateKind::Not(Box::new(predicate)).into()
    }

    /// Create a quantified predicate
    pub fn quantified(
        quantifier: Quantifier,
        identifiers: Vec<TypedIdentifier>,
        predicate: Predicate,
    ) -> Self {
        PredicateKind::Quantified {
            quantifier,
            identifiers,
            predicate: Box::new(predicate),
        }
        .into()
    }
}
