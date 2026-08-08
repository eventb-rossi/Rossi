//! Predicate nodes.

use std::sync::Arc;

use crate::ast::Span;

use super::decl::BoundIdentDecl;
use super::expression::Expression;
use super::factory::FormulaFactory;
use super::hashing::{combine, fold, hash_one};
use super::tag::{self, AssocPredOp, BinaryPredOp, LiteralPredOp, QuantPredOp, RelationalOp, Tag};

/// An immutable predicate.
///
/// Cloning is O(1): the node is a shared handle. Equality is structural
/// (spans never participate; solved types on embedded expressions do)
/// with alpha-equivalence for quantified subterms.
#[derive(Debug, Clone)]
pub struct Predicate(pub(super) Arc<PredData>);

#[derive(Debug)]
pub(super) struct PredData {
    pub(super) kind: PredicateKind,
    pub(super) span: Option<Span>,
    pub(super) hash: u64,
    /// Whether every embedded expression and declaration carries a
    /// solved type.
    pub(super) typed: bool,
    pub(super) free_idents: Box<[String]>,
    pub(super) dangling: Box<[u32]>,
    pub(super) factory: FormulaFactory,
}

/// The structural kind of a [`Predicate`].
///
/// Kinds are public for pattern matching, but predicates can only be
/// constructed through a [`FormulaFactory`].
#[derive(Debug)]
pub enum PredicateKind {
    /// `⊤` or `⊥`.
    Literal(LiteralPredOp),
    /// A predicate meta-variable, e.g. `$P`.
    PredicateVariable(String),
    /// A relational predicate, e.g. `x = y`, `a ∈ S`.
    Relational {
        /// The operator.
        op: RelationalOp,
        /// The left operand.
        left: Expression,
        /// The right operand.
        right: Expression,
    },
    /// `P ⇒ Q` or `P ⇔ Q`.
    Binary {
        /// The operator.
        op: BinaryPredOp,
        /// The left operand.
        left: Predicate,
        /// The right operand.
        right: Predicate,
    },
    /// A conjunction or disjunction with two or more children.
    Associative {
        /// The operator.
        op: AssocPredOp,
        /// The children, in source order; always at least two.
        children: Vec<Predicate>,
    },
    /// `¬ P`.
    Not(Predicate),
    /// `∀ x · P` or `∃ x · P`.
    Quantified {
        /// The operator.
        op: QuantPredOp,
        /// The bound declarations; always at least one. Index 0 in the
        /// body refers to the last declaration.
        decls: Vec<BoundIdentDecl>,
        /// The body, scoped under the declarations.
        pred: Predicate,
    },
    /// `finite(S)`.
    Simple(Expression),
    /// `partition(S, S₁, …, Sₙ)`.
    Multiple(Vec<Expression>),
    /// User predicate application `p(x, y)`.
    ///
    /// A surface-language tolerance node: there is no way to declare a
    /// predicate operator, so this parses, prints and round-trips but
    /// never type-checks.
    Application {
        /// The applied predicate's name.
        function: String,
        /// The span of the name itself (the node span covers the whole
        /// application).
        function_span: Option<Span>,
        /// The arguments, in source order.
        args: Vec<Expression>,
    },
    /// An occurrence of a registered operator extension.
    Extended {
        /// The extension's dynamic tag (`>= FIRST_EXTENSION_TAG`).
        tag: Tag,
        /// Expression children, before all predicate children.
        exprs: Vec<Expression>,
        /// Predicate children.
        preds: Vec<Predicate>,
    },
}

impl Predicate {
    /// The structural kind, for pattern matching.
    pub fn kind(&self) -> &PredicateKind {
        &self.0.kind
    }

    /// The node's numeric tag.
    pub fn tag(&self) -> Tag {
        kind_tag(&self.0.kind)
    }

    /// The source span, if the predicate came from source text.
    pub fn span(&self) -> Option<Span> {
        self.0.span
    }

    /// Whether every embedded expression and declaration carries a
    /// solved type.
    pub fn is_type_checked(&self) -> bool {
        self.0.typed
    }

    /// The factory this predicate was built with.
    pub fn factory(&self) -> &FormulaFactory {
        &self.0.factory
    }

    /// Free-identifier names occurring in the predicate, sorted and
    /// deduplicated. Cached at construction.
    pub fn free_identifiers(&self) -> &[String] {
        &self.0.free_idents
    }

    /// De Bruijn indices occurring in the predicate that are not bound
    /// within it, sorted ascending. Cached at construction.
    pub fn dangling_bound_indices(&self) -> &[u32] {
        &self.0.dangling
    }
}

impl PartialEq for Predicate {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        if self.0.hash != other.0.hash {
            return false;
        }
        kind_eq(&self.0.kind, &other.0.kind)
    }
}

impl Eq for Predicate {}

impl std::hash::Hash for Predicate {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

/// The numeric tag of a kind.
pub(super) fn kind_tag(kind: &PredicateKind) -> Tag {
    match kind {
        PredicateKind::Literal(op) => op.tag(),
        PredicateKind::PredicateVariable(_) => tag::PREDICATE_VARIABLE,
        PredicateKind::Relational { op, .. } => op.tag(),
        PredicateKind::Binary { op, .. } => op.tag(),
        PredicateKind::Associative { op, .. } => op.tag(),
        PredicateKind::Not(_) => tag::FIRST_UNARY_PREDICATE,
        PredicateKind::Quantified { op, .. } => op.tag(),
        PredicateKind::Simple(_) => tag::FIRST_SIMPLE_PREDICATE,
        PredicateKind::Multiple(_) => tag::FIRST_MULTIPLE_PREDICATE,
        PredicateKind::Application { .. } => tag::PRED_APPL,
        PredicateKind::Extended { tag, .. } => *tag,
    }
}

/// The cached structural hash of a kind: children first, then the tag.
///
/// Quantified predicates hash their declaration *count*, not the
/// declarations, so alpha-equivalent formulas hash alike.
pub(super) fn kind_hash(kind: &PredicateKind) -> u64 {
    let children = match kind {
        PredicateKind::Literal(_) => 0,
        PredicateKind::PredicateVariable(name) => hash_one(name),
        PredicateKind::Relational { left, right, .. } => combine(left.0.hash, right.0.hash),
        PredicateKind::Binary { left, right, .. } => combine(left.0.hash, right.0.hash),
        PredicateKind::Associative { children, .. } => fold(children.iter().map(|c| c.0.hash)),
        PredicateKind::Not(child) => child.0.hash,
        PredicateKind::Quantified { decls, pred, .. } => combine(decls.len() as u64, pred.0.hash),
        PredicateKind::Simple(child) => child.0.hash,
        PredicateKind::Multiple(children) => fold(children.iter().map(|c| c.0.hash)),
        PredicateKind::Application { function, args, .. } => {
            combine(hash_one(function), fold(args.iter().map(|a| a.0.hash)))
        }
        PredicateKind::Extended { exprs, preds, .. } => combine(
            fold(exprs.iter().map(|e| e.0.hash)),
            fold(preds.iter().map(|p| p.0.hash)),
        ),
    };
    combine(children, u64::from(kind_tag(kind)))
}

/// Structural kind equality.
pub(super) fn kind_eq(a: &PredicateKind, b: &PredicateKind) -> bool {
    use PredicateKind as K;
    match (a, b) {
        (K::Literal(x), K::Literal(y)) => x == y,
        (K::PredicateVariable(x), K::PredicateVariable(y)) => x == y,
        (
            K::Relational { op, left, right },
            K::Relational {
                op: op2,
                left: left2,
                right: right2,
            },
        ) => op == op2 && left == left2 && right == right2,
        (
            K::Binary { op, left, right },
            K::Binary {
                op: op2,
                left: left2,
                right: right2,
            },
        ) => op == op2 && left == left2 && right == right2,
        (
            K::Associative { op, children },
            K::Associative {
                op: op2,
                children: children2,
            },
        ) => op == op2 && children == children2,
        (K::Not(x), K::Not(y)) => x == y,
        (
            K::Quantified { op, decls, pred },
            K::Quantified {
                op: op2,
                decls: decls2,
                pred: pred2,
            },
        ) => {
            // Declarations compare by solved type only
            // (alpha-equivalence).
            op == op2
                && decls.len() == decls2.len()
                && decls.iter().zip(decls2).all(|(d, d2)| d.alpha_eq(d2))
                && pred == pred2
        }
        (K::Simple(x), K::Simple(y)) => x == y,
        (K::Multiple(x), K::Multiple(y)) => x == y,
        (
            K::Application { function, args, .. },
            K::Application {
                function: function2,
                args: args2,
                ..
            },
        ) => function == function2 && args == args2,
        (
            K::Extended { tag, exprs, preds },
            K::Extended {
                tag: tag2,
                exprs: exprs2,
                preds: preds2,
            },
        ) => tag == tag2 && exprs == exprs2 && preds == preds2,
        _ => false,
    }
}

/// Whether every embedded expression and declaration of a kind carries
/// a solved type. Application is never type-checkable, so it is never
/// "typed" regardless of its arguments.
pub(super) fn kind_typed(kind: &PredicateKind) -> bool {
    match kind {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => true,
        PredicateKind::Relational { left, right, .. } => {
            left.is_type_checked() && right.is_type_checked()
        }
        PredicateKind::Binary { left, right, .. } => left.0.typed && right.0.typed,
        PredicateKind::Associative { children, .. } => children.iter().all(|c| c.0.typed),
        PredicateKind::Not(child) => child.0.typed,
        PredicateKind::Quantified { decls, pred, .. } => {
            decls.iter().all(BoundIdentDecl::is_type_checked) && pred.0.typed
        }
        PredicateKind::Simple(child) => child.is_type_checked(),
        PredicateKind::Multiple(children) => children.iter().all(Expression::is_type_checked),
        PredicateKind::Application { .. } => false,
        PredicateKind::Extended { exprs, preds, .. } => {
            exprs.iter().all(Expression::is_type_checked) && preds.iter().all(|p| p.0.typed)
        }
    }
}
