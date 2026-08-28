//! The rewriting driver: bottom-up, identity-preserving rewriting
//! where each hook sees a node whose children are already rewritten.
//! Every visited associative node with a same-operator child is
//! flattened one level and counts as changed, rewritten or not, and
//! every visited quantified predicate gets the flattening
//! normalization (unused declarations dropped, nested same-kind
//! quantifiers merged). A formula without changes answers `None` —
//! the reference returns the identical reference there, and reasoners
//! test progress with `==` on references.
//!
//! Two deliberate departures from `rossi`'s generic flattening driver,
//! both anchored in how stored rules are compared: unchanged
//! sub-formulas stay bit-identical (the generic driver folds
//! pre-existing `−(lit)` shapes and registers phantom rewrites the
//! stored proofs never contain), and the unary minus of a literal is
//! never folded at all — the reference parser folds negative literals
//! so its flattening has nothing to do, while this crate's parse
//! keeps `−(lit)`, on the stored side and the produced side alike.
//! Rules must therefore treat `−(lit)` as a negative literal wherever
//! a negative literal is matched.

use rossi::formula::tag::{AssocExprOp, AssocPredOp};
use rossi::formula::{Expression, ExpressionKind, Predicate, PredicateKind};

/// One rewriting hook, invoked per node kind. `None` keeps the node.
pub(crate) trait NodeRewriter {
    fn predicate(&mut self, pred: &Predicate) -> Option<Predicate> {
        let _ = pred;
        None
    }
    fn expression(&mut self, expr: &Expression) -> Option<Expression> {
        let _ = expr;
        None
    }
}

/// One-level merge of same-operator associative predicate children.
fn flatten_pred_once(op: AssocPredOp, children: Vec<Predicate>) -> Vec<Predicate> {
    let mut flat: Vec<Predicate> = Vec::with_capacity(children.len());
    for child in children {
        match child.kind() {
            PredicateKind::Associative {
                op: inner,
                children: nested,
            } if *inner == op => flat.extend(nested.iter().cloned()),
            _ => flat.push(child),
        }
    }
    flat
}

/// One-level merge of same-operator associative children.
pub(crate) fn flatten_once(op: AssocExprOp, children: Vec<Expression>) -> Vec<Expression> {
    let mut flat: Vec<Expression> = Vec::with_capacity(children.len());
    for child in children {
        match child.kind() {
            ExpressionKind::Associative {
                op: inner,
                children: nested,
            } if *inner == op => flat.extend(nested.iter().cloned()),
            _ => flat.push(child),
        }
    }
    flat
}

fn rewrite_expr_vec(
    exprs: &[Expression],
    rw: &mut (impl NodeRewriter + ?Sized),
) -> Option<Vec<Expression>> {
    let mut changed = false;
    let out: Vec<Expression> = exprs
        .iter()
        .map(|e| match rewrite_expr(e, rw) {
            Some(e2) => {
                changed = true;
                e2
            }
            None => e.clone(),
        })
        .collect();
    changed.then_some(out)
}

/// Rewrites an expression bottom-up; `None` means unchanged.
pub(crate) fn rewrite_expr(
    expr: &Expression,
    rw: &mut (impl NodeRewriter + ?Sized),
) -> Option<Expression> {
    let ff = expr.factory().clone();
    let rebuilt: Option<Expression> = match expr.kind() {
        ExpressionKind::FreeIdentifier(_)
        | ExpressionKind::BoundIdentifier(_)
        | ExpressionKind::IntegerLiteral(_)
        | ExpressionKind::Atomic(_) => None,
        ExpressionKind::SetExtension(members) => {
            rewrite_expr_vec(members, rw).map(|m| ff.set_extension(m, None))
        }
        ExpressionKind::Bool(pred) => rewrite_pred(pred, rw).map(|p| ff.bool_expression(p, None)),
        ExpressionKind::Binary { op, left, right } => {
            let l = rewrite_expr(left, rw);
            let r = rewrite_expr(right, rw);
            (l.is_some() || r.is_some()).then(|| {
                ff.binary_expression(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        ExpressionKind::Associative { op, children } => {
            // Same visit-flattening as the predicate side
            // (`AssociativeExpression.rewrite`).
            let rewritten = rewrite_expr_vec(children, rw);
            let current: &[Expression] = rewritten.as_deref().unwrap_or(children);
            let nested = current.iter().any(|c| {
                matches!(c.kind(),
                    ExpressionKind::Associative { op: inner, .. } if inner == op)
            });
            match (rewritten, nested) {
                (None, false) => None,
                (rewritten, nested) => {
                    let mut out = rewritten.unwrap_or_else(|| children.clone());
                    if nested {
                        out = flatten_once(*op, out);
                    }
                    Some(ff.associative_expression(*op, out, None))
                }
            }
        }
        ExpressionKind::Unary { op, child } => {
            rewrite_expr(child, rw).map(|c2| ff.unary_expression(*op, c2, None))
        }
        ExpressionKind::Quantified {
            op,
            decls,
            pred,
            expr: inner,
            form,
        } => {
            let p = rewrite_pred(pred, rw);
            let x = rewrite_expr(inner, rw);
            (p.is_some() || x.is_some()).then(|| {
                ff.quantified_expression(
                    *op,
                    decls.clone(),
                    p.unwrap_or_else(|| pred.clone()),
                    x.unwrap_or_else(|| inner.clone()),
                    None,
                    *form,
                )
            })
        }
        // Ascriptions are stripped from loaded proofs; extensions are
        // out of scope in this crate.
        ExpressionKind::Ascription { .. } | ExpressionKind::Extended { .. } => None,
    };

    let current = rebuilt.as_ref().unwrap_or(expr);
    match rw.expression(current) {
        Some(result) => Some(result),
        None => rebuilt,
    }
}

fn rewrite_pred_vec(
    preds: &[Predicate],
    rw: &mut (impl NodeRewriter + ?Sized),
) -> Option<Vec<Predicate>> {
    let mut changed = false;
    let out: Vec<Predicate> = preds
        .iter()
        .map(|p| match rewrite_pred(p, rw) {
            Some(p2) => {
                changed = true;
                p2
            }
            None => p.clone(),
        })
        .collect();
    changed.then_some(out)
}

/// Rewrites a predicate bottom-up; `None` means unchanged.
pub(crate) fn rewrite_pred(
    pred: &Predicate,
    rw: &mut (impl NodeRewriter + ?Sized),
) -> Option<Predicate> {
    let ff = pred.factory().clone();
    let rebuilt: Option<Predicate> = match pred.kind() {
        PredicateKind::Literal(_) | PredicateKind::PredicateVariable(_) => None,
        PredicateKind::Relational { op, left, right } => {
            let l = rewrite_expr(left, rw);
            let r = rewrite_expr(right, rw);
            (l.is_some() || r.is_some()).then(|| {
                ff.relational_predicate(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        PredicateKind::Binary { op, left, right } => {
            let l = rewrite_pred(left, rw);
            let r = rewrite_pred(right, rw);
            (l.is_some() || r.is_some()).then(|| {
                ff.binary_predicate(
                    *op,
                    l.unwrap_or_else(|| left.clone()),
                    r.unwrap_or_else(|| right.clone()),
                    None,
                )
            })
        }
        PredicateKind::Associative { op, children } => {
            // A same-operator child flattens on every visit,
            // rewritten or not — the node counts as changed either
            // way.
            let rewritten = rewrite_pred_vec(children, rw);
            let current: &[Predicate] = rewritten.as_deref().unwrap_or(children);
            let nested = current.iter().any(|c| {
                matches!(c.kind(),
                    PredicateKind::Associative { op: inner, .. } if inner == op)
            });
            match (rewritten, nested) {
                (None, false) => None,
                (rewritten, nested) => {
                    let mut out = rewritten.unwrap_or_else(|| children.clone());
                    if nested {
                        out = flatten_pred_once(*op, out);
                    }
                    Some(ff.associative_predicate(*op, out, None))
                }
            }
        }
        PredicateKind::Not(inner) => rewrite_pred(inner, rw).map(|p| ff.not_predicate(p, None)),
        PredicateKind::Quantified {
            op,
            decls,
            pred: body,
        } => {
            // Flattening applies its quantifier normalization
            // (unused declarations dropped, directly nested same-kind
            // quantifiers merged) to every visited node, changed or
            // not — this is how SIMP_FORALL/SIMP_EXISTS happen.
            let rewritten = rewrite_pred(body, rw);
            let changed = rewritten.is_some();
            let node = match rewritten {
                Some(new_body) => ff.quantified_predicate(*op, decls.clone(), new_body, None),
                None => pred.clone(),
            };
            match rossi::formula::normalize_quantified_predicate(&node) {
                Some(normal) => Some(normal),
                None => changed.then_some(node),
            }
        }
        PredicateKind::Simple(child) => {
            rewrite_expr(child, rw).map(|e| ff.simple_predicate(e, None))
        }
        PredicateKind::Multiple(children) => {
            rewrite_expr_vec(children, rw).map(|out| ff.multiple_predicate(out, None))
        }
        PredicateKind::Application { .. } | PredicateKind::Extended { .. } => None,
    };

    let current = rebuilt.as_ref().unwrap_or(pred);
    match rw.predicate(current) {
        Some(result) => Some(result),
        None => rebuilt,
    }
}

/// The fixpoint of one
/// rewriting pass. `None` means the very first pass changed nothing.
pub(crate) fn recursive_rewrite(
    pred: &Predicate,
    rw: &mut (impl NodeRewriter + ?Sized),
) -> Option<Predicate> {
    let mut current = rewrite_pred(pred, rw)?;
    loop {
        match rewrite_pred(&current, rw) {
            Some(next) => current = next,
            None => return Some(current),
        }
    }
}
