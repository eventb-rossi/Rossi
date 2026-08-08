//! Expression nodes.

use std::sync::Arc;

use num_bigint::BigInt;

use crate::ast::Span;

use super::decl::BoundIdentDecl;
use super::factory::FormulaFactory;
use super::hashing::{combine, fold, hash_one};
use super::predicate::Predicate;
use super::tag::{self, AssocExprOp, AtomicOp, BinaryExprOp, QuantExprOp, Tag, UnaryExprOp};
use super::types::Type;

/// An immutable, possibly typed expression.
///
/// Cloning is O(1): the node is a shared handle. Equality is structural
/// (spans never participate; solved types do) with alpha-equivalence
/// for quantified subterms, and starts with a pointer, then a
/// cached-hash fast path.
#[derive(Debug, Clone)]
pub struct Expression(pub(super) Arc<ExprData>);

#[derive(Debug)]
pub(super) struct ExprData {
    pub(super) kind: ExpressionKind,
    pub(super) ty: Option<Type>,
    pub(super) span: Option<Span>,
    pub(super) hash: u64,
    pub(super) free_idents: Box<[String]>,
    pub(super) dangling: Box<[u32]>,
    pub(super) factory: FormulaFactory,
}

/// The structural kind of an [`Expression`].
///
/// Kinds are public for pattern matching, but expressions can only be
/// constructed through a [`FormulaFactory`], which owns the structural
/// invariants (child counts, binder arity, form validation).
#[derive(Debug)]
pub enum ExpressionKind {
    /// A free identifier occurrence, e.g. `x` or the primed `x'`.
    FreeIdentifier(String),
    /// A bound identifier occurrence, as a de Bruijn index: 0 refers to
    /// the innermost enclosing declaration. Within one quantifier's
    /// declaration list, index 0 maps to the *last* declaration.
    BoundIdentifier(u32),
    /// An integer literal of arbitrary precision.
    IntegerLiteral(BigInt),
    /// A set defined in extension: `{a, b, c}`. Never empty — a typed
    /// empty set is the `∅` atom.
    SetExtension(Vec<Expression>),
    /// A nullary operator, e.g. `ℤ`, `∅`, `TRUE`, `succ`.
    Atomic(AtomicOp),
    /// `bool(P)` — the predicate reified as a boolean expression.
    Bool(Predicate),
    /// A binary operator, e.g. `x ↦ y`, `a − b`, `f(x)`.
    Binary {
        /// The operator.
        op: BinaryExprOp,
        /// The left operand.
        left: Expression,
        /// The right operand.
        right: Expression,
    },
    /// An associative operator with two or more children, e.g.
    /// `a + b + c`.
    Associative {
        /// The operator.
        op: AssocExprOp,
        /// The children, in source order; always at least two.
        children: Vec<Expression>,
    },
    /// A unary operator, e.g. `card(S)`, `ℙ(S)`, `−x`, `r∼`.
    Unary {
        /// The operator.
        op: UnaryExprOp,
        /// The operand.
        child: Expression,
    },
    /// A quantified expression: comprehension set, quantified union or
    /// quantified intersection.
    Quantified {
        /// The operator.
        op: QuantExprOp,
        /// The bound declarations; always at least one. Index 0 in the
        /// body refers to the last declaration.
        decls: Vec<BoundIdentDecl>,
        /// The constraining predicate, scoped under the declarations.
        pred: Predicate,
        /// The value expression, scoped under the declarations.
        expr: Expression,
        /// How the expression prints; no mathematical meaning.
        form: Form,
    },
    /// A type ascription `E ⦂ T`.
    ///
    /// The right operand is the source spelling of the ascribed type; it
    /// is interpreted as a type by the type-checker. Ascriptions on
    /// arbitrary expressions are accepted (a deliberate leniency of this
    /// dialect) and preserved for printing.
    Ascription {
        /// The ascribed expression.
        expr: Expression,
        /// The type, spelled as an expression.
        type_expr: Expression,
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

/// The print form of a quantified expression. Presentation only: it
/// never affects the meaning, equality, or hash of the expression.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Form {
    /// `{x, y · P ∣ E}` — declarations, predicate and expression all
    /// spelled out. Every quantified expression can print this way.
    Explicit,
    /// `{E ∣ P}` — the declarations are implied by the expression,
    /// which must reference exactly the locally bound identifiers and
    /// nothing else.
    Implicit,
    /// `{x, y ∣ P}` — only the declarations and the predicate are
    /// spelled; the expression is the canonical maplet chain of the
    /// declarations (`x ↦ y`).
    IdentList,
    /// `λ pattern · P ∣ E` — the expression is `pattern ↦ E` where the
    /// pattern is a maplet tree over exactly the bound identifiers.
    Lambda,
}

impl Expression {
    /// The structural kind, for pattern matching.
    pub fn kind(&self) -> &ExpressionKind {
        &self.0.kind
    }

    /// The node's numeric tag.
    pub fn tag(&self) -> Tag {
        kind_tag(&self.0.kind)
    }

    /// The solved type, if the expression has been type-checked (or was
    /// built from type-checked parts).
    pub fn ty(&self) -> Option<&Type> {
        self.0.ty.as_ref()
    }

    /// The source span, if the expression came from source text.
    pub fn span(&self) -> Option<Span> {
        self.0.span
    }

    /// Whether the expression carries a solved type.
    pub fn is_type_checked(&self) -> bool {
        self.0.ty.is_some()
    }

    /// The factory this expression was built with.
    pub fn factory(&self) -> &FormulaFactory {
        &self.0.factory
    }

    /// Free-identifier names occurring in the expression, sorted and
    /// deduplicated. Cached at construction.
    pub fn free_identifiers(&self) -> &[String] {
        &self.0.free_idents
    }

    /// De Bruijn indices occurring in the expression that are not bound
    /// within it, sorted ascending. Cached at construction.
    pub fn dangling_bound_indices(&self) -> &[u32] {
        &self.0.dangling
    }
}

impl PartialEq for Expression {
    fn eq(&self, other: &Self) -> bool {
        if Arc::ptr_eq(&self.0, &other.0) {
            return true;
        }
        if self.0.hash != other.0.hash {
            return false;
        }
        if self.0.ty != other.0.ty {
            return false;
        }
        kind_eq(&self.0.kind, &other.0.kind)
    }
}

impl Eq for Expression {}

impl std::hash::Hash for Expression {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_u64(self.0.hash);
    }
}

/// The numeric tag of a kind.
pub(super) fn kind_tag(kind: &ExpressionKind) -> Tag {
    match kind {
        ExpressionKind::FreeIdentifier(_) => tag::FREE_IDENT,
        ExpressionKind::BoundIdentifier(_) => tag::BOUND_IDENT,
        ExpressionKind::IntegerLiteral(_) => tag::INTLIT,
        ExpressionKind::SetExtension(_) => tag::SETEXT,
        ExpressionKind::Atomic(op) => op.tag(),
        ExpressionKind::Bool(_) => tag::KBOOL,
        ExpressionKind::Binary { op, .. } => op.tag(),
        ExpressionKind::Associative { op, .. } => op.tag(),
        ExpressionKind::Unary { op, .. } => op.tag(),
        ExpressionKind::Quantified { op, .. } => op.tag(),
        ExpressionKind::Ascription { .. } => tag::OFTYPE,
        ExpressionKind::Extended { tag, .. } => *tag,
    }
}

/// The cached structural hash of a kind: children first, then the tag.
///
/// Quantified expressions hash their declaration *count*, not the
/// declarations, so alpha-equivalent formulas hash alike.
pub(super) fn kind_hash(kind: &ExpressionKind) -> u64 {
    let children = match kind {
        ExpressionKind::FreeIdentifier(name) => hash_one(name),
        ExpressionKind::BoundIdentifier(index) => u64::from(*index),
        ExpressionKind::IntegerLiteral(value) => hash_one(value),
        ExpressionKind::SetExtension(members) => fold(members.iter().map(|m| m.0.hash)),
        ExpressionKind::Atomic(_) => 0,
        ExpressionKind::Bool(pred) => pred.0.hash,
        ExpressionKind::Binary { left, right, .. } => combine(left.0.hash, right.0.hash),
        ExpressionKind::Associative { children, .. } => fold(children.iter().map(|c| c.0.hash)),
        ExpressionKind::Unary { child, .. } => child.0.hash,
        ExpressionKind::Quantified {
            decls, pred, expr, ..
        } => combine(combine(decls.len() as u64, pred.0.hash), expr.0.hash),
        ExpressionKind::Ascription { expr, type_expr } => combine(expr.0.hash, type_expr.0.hash),
        ExpressionKind::Extended { exprs, preds, .. } => combine(
            fold(exprs.iter().map(|e| e.0.hash)),
            fold(preds.iter().map(|p| p.0.hash)),
        ),
    };
    combine(children, u64::from(kind_tag(kind)))
}

/// Structural kind equality. Assumes tags/hashes were already compared
/// by the caller; still matches on the operator for correctness.
pub(super) fn kind_eq(a: &ExpressionKind, b: &ExpressionKind) -> bool {
    use ExpressionKind as K;
    match (a, b) {
        (K::FreeIdentifier(x), K::FreeIdentifier(y)) => x == y,
        (K::BoundIdentifier(x), K::BoundIdentifier(y)) => x == y,
        (K::IntegerLiteral(x), K::IntegerLiteral(y)) => x == y,
        (K::SetExtension(x), K::SetExtension(y)) => x == y,
        (K::Atomic(x), K::Atomic(y)) => x == y,
        (K::Bool(x), K::Bool(y)) => x == y,
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
        (
            K::Unary { op, child },
            K::Unary {
                op: op2,
                child: child2,
            },
        ) => op == op2 && child == child2,
        (
            K::Quantified {
                op,
                decls,
                pred,
                expr,
                ..
            },
            K::Quantified {
                op: op2,
                decls: decls2,
                pred: pred2,
                expr: expr2,
                ..
            },
        ) => {
            // The print form does not participate; declarations compare
            // by solved type only (alpha-equivalence).
            op == op2
                && decls.len() == decls2.len()
                && decls.iter().zip(decls2).all(|(d, d2)| d.alpha_eq(d2))
                && pred == pred2
                && expr == expr2
        }
        (
            K::Ascription { expr, type_expr },
            K::Ascription {
                expr: expr2,
                type_expr: type_expr2,
            },
        ) => expr == expr2 && type_expr == type_expr2,
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

/// Validates a requested print form against the actual expression,
/// downgrading as needed. Called once at construction; the stored form
/// is therefore always printable.
pub(super) fn filter_form(form: Form, op: QuantExprOp, n_decls: usize, expr: &Expression) -> Form {
    match form {
        Form::Lambda if op == QuantExprOp::CSet && verify_lambda(n_decls, expr) => Form::Lambda,
        Form::IdentList if op == QuantExprOp::CSet && verify_ident_list(n_decls, expr) => {
            Form::IdentList
        }
        Form::Explicit => Form::Explicit,
        _ if verify_implicit(n_decls, expr) => Form::Implicit,
        _ => Form::Explicit,
    }
}

/// A lambda's expression is `pattern ↦ body` where the pattern is a
/// maplet tree over bound identifiers whose indices strictly decrease
/// left-to-right, ending at 0 — i.e. pairwise-distinct identifiers as
/// the user sees them.
fn verify_lambda(n_decls: usize, expr: &Expression) -> bool {
    let ExpressionKind::Binary {
        op: BinaryExprOp::Mapsto,
        left: pattern,
        ..
    } = &expr.0.kind
    else {
        return false;
    };
    let mut expected = n_decls as i64 - 1;
    fn traverse(pattern: &Expression, expected: &mut i64) -> bool {
        match &pattern.0.kind {
            ExpressionKind::Binary {
                op: BinaryExprOp::Mapsto,
                left,
                right,
            } => traverse(left, expected) && traverse(right, expected),
            ExpressionKind::BoundIdentifier(index) => {
                let matches = i64::from(*index) == *expected;
                *expected -= 1;
                matches
            }
            _ => false,
        }
    }
    traverse(pattern, &mut expected) && expected == -1
}

/// An ident-list comprehension's expression is exactly the left-nested
/// maplet chain of the declarations: `bₙ₋₁ ↦ … ↦ b₁ ↦ b₀`. Anything
/// else would print as an ident list but re-parse differently.
fn verify_ident_list(n_decls: usize, expr: &Expression) -> bool {
    let mut node = expr;
    let mut expected_right: u32 = 0;
    loop {
        match &node.0.kind {
            ExpressionKind::Binary {
                op: BinaryExprOp::Mapsto,
                left,
                right,
            } => {
                if !matches!(
                    right.0.kind,
                    ExpressionKind::BoundIdentifier(i) if i == expected_right
                ) {
                    return false;
                }
                expected_right += 1;
                node = left;
            }
            ExpressionKind::BoundIdentifier(index) => {
                return n_decls == expected_right as usize + 1
                    && u64::from(*index) == expected_right as u64;
            }
            _ => return false,
        }
    }
}

/// An implicit-form expression references exactly the locally bound
/// identifiers: no free identifiers, no identifiers bound outside, and
/// all of the local ones.
fn verify_implicit(n_decls: usize, expr: &Expression) -> bool {
    if !expr.0.free_idents.is_empty() {
        return false;
    }
    let dangling = &expr.0.dangling;
    dangling.len() == n_decls
        && dangling
            .last()
            .is_some_and(|last| *last as usize == n_decls - 1)
}
