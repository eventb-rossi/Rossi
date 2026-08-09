//! Expression AST nodes
//!
//! Expressions represent values in Event-B, including sets, numbers,
//! functions, relations, and arithmetic expressions.

use super::{Predicate, Span, TypedIdentifier};

/// Pattern for lambda abstraction parameters (per Event-B kernel language spec §3.3.6).
///
/// Unlike quantified predicates which use comma-separated identifier lists,
/// lambda expressions use maplet-based patterns. Each leaf identifier may
/// optionally carry a type annotation (`x⦂T`), which is what Rodin's bcc
/// emits after type-checking:
/// ```text
/// ⟨ident-pattern⟩ ::= ⟨ident-pattern⟩ { '↦' ⟨ident-pattern⟩ }
///                     | '(' ⟨ident-pattern⟩ ')'
///                     | ⟨ident⟩ [ '⦂' ⟨type⟩ ]
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum IdentPattern {
    /// A single (possibly typed) identifier
    Identifier(TypedIdentifier),
    /// A maplet pattern: left ↦ right (left-associative)
    Maplet(Box<IdentPattern>, Box<IdentPattern>),
}

impl IdentPattern {
    /// Extract all identifier names from this pattern (in left-to-right order)
    pub fn identifiers(&self) -> Vec<&str> {
        match self {
            IdentPattern::Identifier(t) => vec![t.name.as_str()],
            IdentPattern::Maplet(left, right) => {
                let mut ids = left.identifiers();
                ids.extend(right.identifiers());
                ids
            }
        }
    }
}

pub use crate::operators::{AtomicBuiltinKind, BinaryOp, BuiltinFunction, UnaryOp};

/// An Event-B expression together with its source location.
///
/// The expression variant lives in [`ExpressionKind`]; `span` records where the
/// expression came from in the source text. `span` is `None` for nodes that were
/// synthesized (e.g. normalisation rewrites) or built from Rodin XML, where no
/// document offset is meaningful.
///
/// Equality and hashing intentionally ignore `span`: two expressions are equal
/// iff their kinds are structurally equal, regardless of where they appear. This
/// keeps round-trip and hand-built-AST comparisons span-insensitive.
#[derive(Debug, Clone)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Expression {
    /// The expression variant.
    pub kind: ExpressionKind,
    /// Source span of this expression, if known.
    #[cfg_attr(
        feature = "serde",
        serde(default, skip_serializing_if = "Option::is_none")
    )]
    pub span: Option<Span>,
}

impl Expression {
    /// Wrap a kind with an explicit (optional) span.
    pub fn new(kind: ExpressionKind, span: Option<Span>) -> Self {
        Self { kind, span }
    }
}

/// Equality compares the kind only; the span is positional metadata.
impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        self.kind == other.kind
    }
}

impl Eq for Expression {}

impl From<ExpressionKind> for Expression {
    /// Build a span-less expression from its kind.
    fn from(kind: ExpressionKind) -> Self {
        Self { kind, span: None }
    }
}

/// The variants of an Event-B [`Expression`].
#[derive(Debug, Clone, PartialEq, Eq)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum ExpressionKind {
    /// Integer literal
    Integer(i64),

    /// Identifier (variable, constant, or parameter)
    Identifier(String),

    /// Boolean true
    True,

    /// Boolean false
    False,

    /// Empty set
    EmptySet,

    /// Natural numbers set (ℕ)
    Naturals,

    /// Positive natural numbers set (ℕ1)
    Naturals1,

    /// Integer numbers set (ℤ)
    Integers,

    /// Boolean type (BOOL)
    BoolType,

    /// Set enumeration: {e1, e2, ...}
    SetEnumeration(Vec<Expression>),

    /// Set comprehension: {x, y | P} or extended {x · P | E}
    SetComprehension {
        identifiers: Vec<TypedIdentifier>,
        predicate: Box<Predicate>,
        /// Expression body for extended form {x · P | E}; None for basic {x | P}
        expression: Option<Box<Expression>>,
    },

    /// Set builder notation: {E ∣ P} where E is a general expression
    ///
    /// This is the expression-form set comprehension where the member expression
    /// appears before the pipe and the predicate after. Common with maplet patterns:
    /// `{x ↦ y ∣ x ∈ S ∧ y ∈ T}`
    SetBuilder {
        member_expression: Box<Expression>,
        predicate: Box<Predicate>,
    },

    /// Relational image: r\[S\]
    RelationalImage {
        relation: Box<Expression>,
        set: Box<Expression>,
    },

    /// Quantified union: ⋃x·P ∣ E
    QuantifiedUnion {
        identifiers: Vec<TypedIdentifier>,
        predicate: Box<Predicate>,
        expression: Box<Expression>,
    },

    /// Quantified intersection: ⋂x·P ∣ E
    QuantifiedInter {
        identifiers: Vec<TypedIdentifier>,
        predicate: Box<Predicate>,
        expression: Box<Expression>,
    },

    /// Lambda expression: λ pattern · P ∣ E
    Lambda {
        pattern: IdentPattern,
        predicate: Box<Predicate>,
        expression: Box<Expression>,
    },

    /// Binary operation
    Binary {
        op: BinaryOp,
        left: Box<Expression>,
        right: Box<Expression>,
    },

    /// Unary operation
    Unary {
        op: UnaryOp,
        operand: Box<Expression>,
    },

    /// Function/relation application: f(x)
    FunctionApplication {
        function: Box<Expression>,
        argument: Box<Expression>,
    },

    /// Built-in function application: card(S), min(S), etc.
    BuiltinApplication {
        function: BuiltinFunction,
        argument: Box<Expression>,
    },

    /// A generic relational atom written bare: `id`, `prj1`, `prj2`, `pred`,
    /// `succ`. An atomic value (Rodin's generic atomic expressions); applying
    /// one (`prj1(x)`) is an ordinary [`ExpressionKind::FunctionApplication`].
    AtomicBuiltin(AtomicBuiltinKind),

    /// Boolean conversion: bool(P) — converts a predicate to a boolean expression
    Bool(Box<Predicate>),
}

impl Expression {
    /// Create an identifier expression
    pub fn identifier(name: impl Into<String>) -> Self {
        ExpressionKind::Identifier(name.into()).into()
    }

    /// Create an integer expression
    pub fn integer(value: i64) -> Self {
        ExpressionKind::Integer(value).into()
    }

    /// Create a binary operation
    pub fn binary(op: BinaryOp, left: Expression, right: Expression) -> Self {
        ExpressionKind::Binary {
            op,
            left: Box::new(left),
            right: Box::new(right),
        }
        .into()
    }

    /// Create a unary operation
    pub fn unary(op: UnaryOp, operand: Expression) -> Self {
        ExpressionKind::Unary {
            op,
            operand: Box::new(operand),
        }
        .into()
    }
}
