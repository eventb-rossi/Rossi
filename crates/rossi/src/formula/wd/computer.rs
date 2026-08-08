//! The well-definedness lemma of a formula (the L operator).
//!
//! Every formula gets a predicate expressing when it denotes: partial
//! operations contribute their guards (a divisor is non-zero, a
//! function argument lies in the domain, a minimized set is non-empty
//! and bounded), conjunction and implication load their left-hand
//! sides as hypotheses for the right, and quantifiers universally
//! close the lemma of their body.

use super::super::assignment::{Assignment, AssignmentKind};
use super::super::expression::{Expression, ExpressionKind};
use super::super::predicate::{Predicate, PredicateKind};
use super::super::tag::{
    AssocPredOp, AtomicOp, BinaryExprOp, BinaryPredOp, QuantExprOp, UnaryExprOp,
};
use super::fb::FormulaBuilder;

pub(super) fn wd_expr(fb: &FormulaBuilder, e: &Expression) -> Predicate {
    match e.kind() {
        ExpressionKind::FreeIdentifier(_)
        | ExpressionKind::BoundIdentifier(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::Atomic(_) => fb.btrue(),
        ExpressionKind::SetExtension(members) => {
            fb.land_all(members.iter().map(|m| wd_expr(fb, m)))
        }
        ExpressionKind::Bool(pred) => wd_pred(fb, pred),
        ExpressionKind::Binary { op, left, right } => {
            let local = binary_wd(fb, *op, left, right);
            fb.land_all([wd_expr(fb, left), wd_expr(fb, right), local])
        }
        ExpressionKind::Associative { children, .. } => {
            fb.land_all(children.iter().map(|c| wd_expr(fb, c)))
        }
        ExpressionKind::Unary { op, child } => {
            let local = unary_wd(fb, *op, child);
            fb.land_all([wd_expr(fb, child), local])
        }
        ExpressionKind::Quantified {
            op,
            decls,
            pred,
            expr,
            ..
        } => {
            let body_wd = fb.land(wd_pred(fb, pred), fb.limp(pred.clone(), wd_expr(fb, expr)));
            let children_wd = fb.forall(decls.clone(), body_wd);
            let local_wd = match op {
                QuantExprOp::QUnion | QuantExprOp::CSet => fb.btrue(),
                QuantExprOp::QInter => fb.exists(decls.clone(), pred.clone()),
            };
            fb.land(children_wd, local_wd)
        }
        ExpressionKind::Ascription { expr, .. } => wd_expr(fb, expr),
        ExpressionKind::Extended { .. } => {
            unreachable!("extension nodes are not constructible yet")
        }
    }
}

fn binary_wd(
    fb: &FormulaBuilder,
    op: BinaryExprOp,
    left: &Expression,
    right: &Expression,
) -> Predicate {
    match op {
        BinaryExprOp::Div => fb.not_zero(right.clone()),
        BinaryExprOp::Mod => fb.land(fb.non_negative(left.clone()), fb.positive(right.clone())),
        BinaryExprOp::Expn => fb.land(
            fb.non_negative(left.clone()),
            fb.non_negative(right.clone()),
        ),
        BinaryExprOp::FunImage => {
            if is_builtin_total_function(left) {
                return fb.btrue();
            }
            fb.land(
                fb.in_domain(left.clone(), right.clone()),
                fb.partial(left.clone()),
            )
        }
        _ => fb.btrue(),
    }
}

fn is_builtin_total_function(expr: &Expression) -> bool {
    matches!(
        expr.kind(),
        ExpressionKind::Atomic(
            AtomicOp::KPred
                | AtomicOp::KSucc
                | AtomicOp::KPrj1Gen
                | AtomicOp::KPrj2Gen
                | AtomicOp::KIdGen
        )
    )
}

fn unary_wd(fb: &FormulaBuilder, op: UnaryExprOp, child: &Expression) -> Predicate {
    match op {
        UnaryExprOp::KCard => fb.finite(child.clone()),
        UnaryExprOp::KMin => fb.land(fb.not_empty(child.clone()), fb.bounded(child.clone(), true)),
        UnaryExprOp::KMax => fb.land(
            fb.not_empty(child.clone()),
            fb.bounded(child.clone(), false),
        ),
        UnaryExprOp::KInter => fb.not_empty(child.clone()),
        _ => fb.btrue(),
    }
}

pub(super) fn wd_pred(fb: &FormulaBuilder, p: &Predicate) -> Predicate {
    match p.kind() {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => fb.btrue(),
        PredicateKind::Relational { left, right, .. } => {
            fb.land(wd_expr(fb, left), wd_expr(fb, right))
        }
        PredicateKind::Binary { op, left, right } => match op {
            BinaryPredOp::LImp => {
                fb.land(wd_pred(fb, left), fb.limp(left.clone(), wd_pred(fb, right)))
            }
            BinaryPredOp::LEqv => fb.land(wd_pred(fb, left), wd_pred(fb, right)),
        },
        PredicateKind::Associative { op, children } => match op {
            // Left conjuncts become hypotheses for the right ones.
            AssocPredOp::LAnd => children.iter().rev().fold(fb.btrue(), |acc, child| {
                fb.land(wd_pred(fb, child), fb.limp(child.clone(), acc))
            }),
            // Left disjuncts excuse the right ones.
            AssocPredOp::LOr => children.iter().rev().fold(fb.btrue(), |acc, child| {
                fb.land(wd_pred(fb, child), fb.lor(child.clone(), acc))
            }),
        },
        PredicateKind::Not(child) => wd_pred(fb, child),
        PredicateKind::Quantified { decls, pred, .. } => {
            // Both quantifiers close the body's lemma universally.
            fb.forall(decls.clone(), wd_pred(fb, pred))
        }
        PredicateKind::Simple(child) => wd_expr(fb, child),
        PredicateKind::Multiple(children) => fb.land_all(children.iter().map(|c| wd_expr(fb, c))),
        PredicateKind::Application { .. } => {
            unreachable!("applications never type-check")
        }
        PredicateKind::Extended { .. } => {
            unreachable!("extension nodes are not constructible yet")
        }
    }
}

pub(super) fn wd_assign(fb: &FormulaBuilder, a: &Assignment) -> Predicate {
    match a.kind() {
        AssignmentKind::BecomesEqualTo { values, .. } => {
            fb.land_all(values.iter().map(|v| wd_expr(fb, v)))
        }
        AssignmentKind::BecomesMemberOf { set, .. } => wd_expr(fb, set),
        AssignmentKind::BecomesSuchThat { primed, pred, .. } => {
            fb.forall(primed.clone(), wd_pred(fb, pred))
        }
    }
}
