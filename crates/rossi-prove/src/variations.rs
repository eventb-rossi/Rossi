//! Predicate variations at level L1, the level the latest reasoners
//! use (`Hyp`, `ContrHyps` v1).
//!
//! Given a predicate `P`, these functions enumerate predicates related
//! to it by implication: `stronger_positive` lists `Q` with `Q ⇒ P`,
//! `weaker_positive` lists `Q` with `P ⇒ Q`, and the negative variants
//! speak about `¬P`. Reasoners scan the returned list in order and
//! pick the first entry present among the hypotheses, so both the
//! entries and their order matter exactly — including the duplicate
//! entries the lists contain.

use num_bigint::BigInt;
use rossi::formula::tag::{AtomicOp, RelationalOp, UnaryExprOp};
use rossi::formula::{Expression, ExpressionKind, Predicate, PredicateKind, Type};

/// Predicates `Q` such that `Q ⇒ P` — `getStrongerPositive`.
pub(crate) fn stronger_positive(pred: &Predicate) -> Vec<Predicate> {
    if let PredicateKind::Not(inner) = pred.kind() {
        return stronger_negative(inner);
    }
    if let PredicateKind::Relational { op, left, right } = pred.kind() {
        return stronger_positive_relational(*op, left, right);
    }
    vec![pred.clone()]
}

/// Predicates `Q` such that `Q ⇒ ¬P` — `getStrongerNegative`.
pub(crate) fn stronger_negative(pred: &Predicate) -> Vec<Predicate> {
    if let PredicateKind::Not(inner) = pred.kind() {
        return stronger_positive(inner);
    }
    weaker_positive(pred)
        .iter()
        .map(make_neg_relational)
        .collect()
}

/// Predicates `Q` such that `P ⇒ Q` — `getWeakerPositive`.
pub(crate) fn weaker_positive(pred: &Predicate) -> Vec<Predicate> {
    if let PredicateKind::Not(inner) = pred.kind() {
        return weaker_negative(inner);
    }
    if let PredicateKind::Relational { op, left, right } = pred.kind() {
        return weaker_positive_relational(*op, left, right);
    }
    vec![pred.clone()]
}

/// Predicates `Q` such that `¬P ⇒ Q` — `getWeakerNegative`.
pub(crate) fn weaker_negative(pred: &Predicate) -> Vec<Predicate> {
    if let PredicateKind::Not(inner) = pred.kind() {
        return weaker_positive(inner);
    }
    stronger_positive(pred)
        .iter()
        .map(make_neg_relational)
        .collect()
}

fn stronger_positive_relational(
    op: RelationalOp,
    lhs: &Expression,
    rhs: &Expression,
) -> Vec<Predicate> {
    // Reduce to less-than relations.
    match op {
        RelationalOp::Ge => return stronger_positive_relational(RelationalOp::Le, rhs, lhs),
        RelationalOp::Gt => return stronger_positive_relational(RelationalOp::Lt, rhs, lhs),
        _ => {}
    }
    let mut variations = Vec::new();
    add_equivalent_positive(&mut variations, op, lhs, rhs);
    match op {
        RelationalOp::Le => {
            variations.push(rel(RelationalOp::Lt, lhs, rhs));
            variations.push(rel(RelationalOp::Gt, rhs, lhs));
            variations.push(rel(RelationalOp::Equal, lhs, rhs));
            variations.push(rel(RelationalOp::Equal, rhs, lhs));
        }
        RelationalOp::SubsetEq => {
            variations.push(rel(RelationalOp::Subset, lhs, rhs));
            variations.push(rel(RelationalOp::Equal, lhs, rhs));
            variations.push(rel(RelationalOp::Equal, rhs, lhs));
        }
        _ => {}
    }
    // Level 1 additions.
    match op {
        RelationalOp::Le | RelationalOp::Lt => {
            if is_negative_int_lit(lhs) {
                add_equivalent_positive(&mut variations, RelationalOp::In, rhs, &nat(rhs));
                add_equivalent_positive(&mut variations, RelationalOp::In, rhs, &nat1(rhs));
            }
        }
        RelationalOp::In if is_atomic(rhs, AtomicOp::Natural) => {
            add_equivalent_positive(&mut variations, RelationalOp::In, lhs, &nat1(lhs));
        }
        _ => {}
    }
    variations
}

fn weaker_positive_relational(
    op: RelationalOp,
    lhs: &Expression,
    rhs: &Expression,
) -> Vec<Predicate> {
    // Reduce to less-than relations.
    match op {
        RelationalOp::Ge => return weaker_positive_relational(RelationalOp::Le, rhs, lhs),
        RelationalOp::Gt => return weaker_positive_relational(RelationalOp::Lt, rhs, lhs),
        _ => {}
    }
    let mut variations = Vec::new();
    add_equivalent_positive(&mut variations, op, lhs, rhs);
    match op {
        RelationalOp::Equal => {
            if is_set(rhs) {
                variations.push(rel(RelationalOp::SubsetEq, lhs, rhs));
                variations.push(rel(RelationalOp::SubsetEq, rhs, lhs));
                variations.push(neg(&rel(RelationalOp::Subset, lhs, rhs)));
                variations.push(neg(&rel(RelationalOp::Subset, rhs, lhs)));
            } else if is_integer(rhs) {
                variations.push(rel(RelationalOp::Le, lhs, rhs));
                variations.push(rel(RelationalOp::Ge, rhs, lhs));
                variations.push(rel(RelationalOp::Le, rhs, lhs));
                variations.push(rel(RelationalOp::Ge, lhs, rhs));
            }
        }
        RelationalOp::Lt => {
            variations.push(rel(RelationalOp::Le, lhs, rhs));
            variations.push(rel(RelationalOp::Ge, rhs, lhs));
            variations.push(neg(&rel(RelationalOp::Equal, lhs, rhs)));
            variations.push(neg(&rel(RelationalOp::Equal, rhs, lhs)));
        }
        RelationalOp::Subset => {
            variations.push(rel(RelationalOp::SubsetEq, lhs, rhs));
            variations.push(neg(&rel(RelationalOp::Equal, lhs, rhs)));
            variations.push(neg(&rel(RelationalOp::Equal, rhs, lhs)));
            variations.push(neg(&rel(RelationalOp::Subset, rhs, lhs)));
            variations.push(neg(&rel(RelationalOp::SubsetEq, rhs, lhs)));
        }
        RelationalOp::SubsetEq => {
            variations.push(neg(&rel(RelationalOp::Subset, rhs, lhs)));
        }
        _ => {}
    }
    // Level 1 additions.
    match op {
        RelationalOp::Equal => {
            if is_zero(rhs) {
                add_equivalent_negative(&mut variations, RelationalOp::In, lhs, &nat1(lhs));
            }
            if is_zero(lhs) {
                add_equivalent_negative(&mut variations, RelationalOp::In, rhs, &nat1(rhs));
            }
        }
        RelationalOp::Le | RelationalOp::Lt => {
            if is_positive_int_lit(lhs) {
                add_equivalent_positive(&mut variations, RelationalOp::In, rhs, &nat(rhs));
                add_equivalent_positive(&mut variations, RelationalOp::In, rhs, &nat1(rhs));
            }
        }
        RelationalOp::In if is_atomic(rhs, AtomicOp::Natural1) => {
            add_equivalent_positive(&mut variations, RelationalOp::In, lhs, &nat(lhs));
            add_equivalent_negative(&mut variations, RelationalOp::Equal, lhs, &zero(lhs));
        }
        _ => {}
    }
    variations
}

/// `addEquivalentPositiveRelational`: `lhs op rhs` and its mirrored and
/// L1-equivalent forms.
fn add_equivalent_positive(
    variations: &mut Vec<Predicate>,
    op: RelationalOp,
    lhs: &Expression,
    rhs: &Expression,
) {
    variations.push(rel(op, lhs, rhs));
    match op {
        RelationalOp::Equal => variations.push(rel(RelationalOp::Equal, rhs, lhs)),
        RelationalOp::Lt => variations.push(rel(RelationalOp::Gt, rhs, lhs)),
        RelationalOp::Le => variations.push(rel(RelationalOp::Ge, rhs, lhs)),
        RelationalOp::Gt => variations.push(rel(RelationalOp::Lt, rhs, lhs)),
        RelationalOp::Ge => variations.push(rel(RelationalOp::Le, rhs, lhs)),
        _ => {}
    }
    // Level 1 additions.
    match op {
        RelationalOp::Equal => {
            let ff = lhs.factory();
            let false_expr = ff.atomic_expression(AtomicOp::False, None, None);
            if is_atomic(lhs, AtomicOp::True) {
                variations.push(neg(&rel(RelationalOp::Equal, &false_expr, rhs)));
                variations.push(neg(&rel(RelationalOp::Equal, rhs, &false_expr)));
            }
            if is_atomic(rhs, AtomicOp::True) {
                variations.push(neg(&rel(RelationalOp::Equal, lhs, &false_expr)));
                variations.push(neg(&rel(RelationalOp::Equal, &false_expr, lhs)));
            }
            let true_expr = ff.atomic_expression(AtomicOp::True, None, None);
            if is_atomic(lhs, AtomicOp::False) {
                variations.push(neg(&rel(RelationalOp::Equal, &true_expr, rhs)));
                variations.push(neg(&rel(RelationalOp::Equal, rhs, &true_expr)));
            }
            if is_atomic(rhs, AtomicOp::False) {
                variations.push(neg(&rel(RelationalOp::Equal, lhs, &true_expr)));
                variations.push(neg(&rel(RelationalOp::Equal, &true_expr, lhs)));
            }
        }
        RelationalOp::Lt => {
            if let Some(value) = int_lit(lhs) {
                if value == BigInt::ZERO {
                    variations.push(rel(RelationalOp::In, rhs, &nat1(rhs)));
                } else if value == BigInt::from(-1) {
                    variations.push(rel(RelationalOp::In, rhs, &nat(rhs)));
                }
                let plus = literal(lhs, value + 1);
                variations.push(rel(RelationalOp::Le, &plus, rhs));
                variations.push(rel(RelationalOp::Ge, rhs, &plus));
            }
            if let Some(value) = int_lit(rhs) {
                if value == BigInt::ZERO {
                    variations.push(neg(&rel(RelationalOp::In, lhs, &nat(lhs))));
                } else if value == BigInt::from(1) {
                    variations.push(neg(&rel(RelationalOp::In, lhs, &nat1(lhs))));
                }
                let minus = literal(rhs, value - 1);
                variations.push(rel(RelationalOp::Le, lhs, &minus));
                variations.push(rel(RelationalOp::Ge, &minus, lhs));
            }
        }
        RelationalOp::Le => {
            if let Some(value) = int_lit(lhs) {
                if value == BigInt::ZERO {
                    variations.push(rel(RelationalOp::In, rhs, &nat(rhs)));
                } else if value == BigInt::from(1) {
                    variations.push(rel(RelationalOp::In, rhs, &nat1(rhs)));
                }
                let minus = literal(lhs, value - 1);
                variations.push(rel(RelationalOp::Lt, &minus, rhs));
                variations.push(rel(RelationalOp::Gt, rhs, &minus));
            }
            if let Some(value) = int_lit(rhs) {
                if value == BigInt::ZERO {
                    variations.push(neg(&rel(RelationalOp::In, lhs, &nat1(lhs))));
                } else if value == BigInt::from(-1) {
                    variations.push(neg(&rel(RelationalOp::In, lhs, &nat(lhs))));
                }
                let plus = literal(rhs, value + 1);
                variations.push(rel(RelationalOp::Lt, lhs, &plus));
                variations.push(rel(RelationalOp::Gt, &plus, lhs));
            }
        }
        RelationalOp::Gt => {
            if let Some(value) = int_lit(lhs) {
                if value == BigInt::ZERO {
                    variations.push(neg(&rel(RelationalOp::In, rhs, &nat(rhs))));
                } else if value == BigInt::from(1) {
                    variations.push(neg(&rel(RelationalOp::In, rhs, &nat1(rhs))));
                }
                let minus = literal(lhs, value - 1);
                variations.push(rel(RelationalOp::Ge, &minus, rhs));
                variations.push(rel(RelationalOp::Le, rhs, &minus));
            }
            if let Some(value) = int_lit(rhs) {
                if value == BigInt::ZERO {
                    variations.push(rel(RelationalOp::In, lhs, &nat1(lhs)));
                } else if value == BigInt::from(-1) {
                    variations.push(rel(RelationalOp::In, lhs, &nat(lhs)));
                }
                let plus = literal(rhs, value + 1);
                variations.push(rel(RelationalOp::Ge, lhs, &plus));
                variations.push(rel(RelationalOp::Le, &plus, lhs));
            }
        }
        RelationalOp::Ge => {
            if let Some(value) = int_lit(lhs) {
                if value == BigInt::ZERO {
                    variations.push(neg(&rel(RelationalOp::In, rhs, &nat1(rhs))));
                } else if value == BigInt::from(-1) {
                    variations.push(neg(&rel(RelationalOp::In, rhs, &nat(rhs))));
                }
                let plus = literal(lhs, value + 1);
                variations.push(rel(RelationalOp::Gt, &plus, rhs));
                variations.push(rel(RelationalOp::Lt, rhs, &plus));
            }
            if let Some(value) = int_lit(rhs) {
                if value == BigInt::ZERO {
                    variations.push(rel(RelationalOp::In, lhs, &nat(lhs)));
                } else if value == BigInt::from(1) {
                    variations.push(rel(RelationalOp::In, lhs, &nat1(lhs)));
                }
                let minus = literal(rhs, value - 1);
                variations.push(rel(RelationalOp::Gt, lhs, &minus));
                variations.push(rel(RelationalOp::Lt, &minus, lhs));
            }
        }
        RelationalOp::In => match rhs.kind() {
            ExpressionKind::Atomic(AtomicOp::Natural) => {
                add_equivalent_positive(variations, RelationalOp::Le, &zero(lhs), lhs);
            }
            ExpressionKind::Atomic(AtomicOp::Natural1) => {
                add_equivalent_positive(variations, RelationalOp::Lt, &zero(lhs), lhs);
            }
            _ => {}
        },
        _ => {}
    }
}

/// `addEquivalentNegativeRelational`: forms equivalent to
/// `¬(lhs op rhs)`. The trailing duplicate on the fall-through path
/// is kept for order fidelity.
fn add_equivalent_negative(
    variations: &mut Vec<Predicate>,
    op: RelationalOp,
    lhs: &Expression,
    rhs: &Expression,
) {
    variations.push(neg(&rel(op, lhs, rhs)));
    match op {
        RelationalOp::Equal => {
            variations.push(neg(&rel(RelationalOp::Equal, lhs, rhs)));
            variations.push(neg(&rel(RelationalOp::Equal, rhs, lhs)));
            return;
        }
        RelationalOp::Lt => {
            variations.push(rel(RelationalOp::Ge, lhs, rhs));
            variations.push(rel(RelationalOp::Le, rhs, lhs));
            return;
        }
        RelationalOp::Le => {
            variations.push(rel(RelationalOp::Gt, lhs, rhs));
            variations.push(rel(RelationalOp::Lt, rhs, lhs));
            return;
        }
        RelationalOp::Gt => {
            variations.push(rel(RelationalOp::Le, lhs, rhs));
            variations.push(rel(RelationalOp::Ge, rhs, lhs));
            return;
        }
        RelationalOp::Ge => {
            variations.push(rel(RelationalOp::Lt, lhs, rhs));
            variations.push(rel(RelationalOp::Gt, rhs, lhs));
            return;
        }
        RelationalOp::In => match rhs.kind() {
            ExpressionKind::Atomic(AtomicOp::Natural) => {
                add_equivalent_positive(variations, RelationalOp::Gt, &zero(lhs), lhs);
                return;
            }
            ExpressionKind::Atomic(AtomicOp::Natural1) => {
                add_equivalent_positive(variations, RelationalOp::Ge, &zero(lhs), lhs);
                return;
            }
            _ => {}
        },
        _ => {}
    }
    variations.push(neg(&rel(op, lhs, rhs)));
}

/// `makeNegRelational`: negate, contracting inequalities.
fn make_neg_relational(pred: &Predicate) -> Predicate {
    if let PredicateKind::Relational { op, left, right } = pred.kind() {
        let flipped = match op {
            RelationalOp::Le => Some(RelationalOp::Gt),
            RelationalOp::Ge => Some(RelationalOp::Lt),
            RelationalOp::Lt => Some(RelationalOp::Ge),
            RelationalOp::Gt => Some(RelationalOp::Le),
            _ => None,
        };
        if let Some(flipped) = flipped {
            return rel(flipped, left, right);
        }
    }
    neg(pred)
}

/// Negate, removing an existing negation.
fn neg(pred: &Predicate) -> Predicate {
    if let PredicateKind::Not(inner) = pred.kind() {
        return inner.clone();
    }
    pred.factory().not_predicate(pred.clone(), None)
}

fn rel(op: RelationalOp, left: &Expression, right: &Expression) -> Predicate {
    left.factory()
        .clone()
        .relational_predicate(op, left.clone(), right.clone(), None)
}

fn is_set(expr: &Expression) -> bool {
    matches!(expr.ty(), Some(Type::Pow(_)))
}

fn is_integer(expr: &Expression) -> bool {
    matches!(expr.ty(), Some(Type::Int))
}

fn is_atomic(expr: &Expression, op: AtomicOp) -> bool {
    matches!(expr.kind(), ExpressionKind::Atomic(found) if *found == op)
}

/// A literal value, seeing through the unary minus this crate's
/// parse-normal form keeps (the reference parser folds them).
fn int_lit(expr: &Expression) -> Option<BigInt> {
    match expr.kind() {
        ExpressionKind::IntegerLiteral(value) => Some(value.clone()),
        ExpressionKind::Unary {
            op: UnaryExprOp::UnMinus,
            child,
        } => match child.kind() {
            ExpressionKind::IntegerLiteral(value) => Some(-value.clone()),
            _ => None,
        },
        _ => None,
    }
}

fn is_zero(expr: &Expression) -> bool {
    int_lit(expr).is_some_and(|value| value == BigInt::ZERO)
}

fn is_positive_int_lit(expr: &Expression) -> bool {
    int_lit(expr).is_some_and(|value| value > BigInt::ZERO)
}

fn is_negative_int_lit(expr: &Expression) -> bool {
    int_lit(expr).is_some_and(|value| value < BigInt::ZERO)
}

/// A literal in the crate's parse-normal shape: negative values are a
/// unary minus over the positive literal, as the parser produces them.
fn literal(like: &Expression, value: BigInt) -> Expression {
    let ff = like.factory();
    if value < BigInt::ZERO {
        let unsigned = ff.integer_literal(-value, None);
        ff.unary_expression(UnaryExprOp::UnMinus, unsigned, None)
    } else {
        ff.integer_literal(value, None)
    }
}

fn nat(like: &Expression) -> Expression {
    like.factory()
        .clone()
        .atomic_expression(AtomicOp::Natural, None, None)
}

fn nat1(like: &Expression) -> Expression {
    like.factory()
        .clone()
        .atomic_expression(AtomicOp::Natural1, None, None)
}

fn zero(like: &Expression) -> Expression {
    literal(like, BigInt::ZERO)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{env, pred};

    fn contains(list: &[Predicate], env: &rossi::formula::SealedTypeEnvironment, s: &str) -> bool {
        let expected = pred(env, s);
        list.contains(&expected)
    }

    #[test]
    fn stronger_positive_le_includes_lt_and_equal() {
        let env = env(&[("a", "ℤ"), ("b", "ℤ")]);
        let list = stronger_positive(&pred(&env, "a≤b"));
        for s in ["a≤b", "b≥a", "a<b", "b>a", "a=b", "b=a"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn stronger_positive_ge_reduces_to_swapped_le() {
        let env = env(&[("a", "ℤ"), ("b", "ℤ")]);
        assert_eq!(
            stronger_positive(&pred(&env, "a≥b")),
            stronger_positive(&pred(&env, "b≤a"))
        );
    }

    #[test]
    fn stronger_positive_natural_membership_from_nat1() {
        let env = env(&[("x", "ℤ")]);
        let list = stronger_positive(&pred(&env, "x∈ℕ"));
        // x∈ℕ1 implies x∈ℕ (level 1), and the ℕ membership itself is
        // equivalent to 0≤x.
        for s in ["x∈ℕ", "0≤x", "x≥0", "x∈ℕ1"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn stronger_negative_of_equality_flips_inequalities() {
        let env = env(&[("a", "ℤ"), ("b", "ℤ")]);
        // Q ⇒ ¬(a=b): from the weaker-positive list of a=b, negated
        // with inequality contraction: a≤b becomes a>b, etc.
        let list = stronger_negative(&pred(&env, "a=b"));
        for s in ["¬a=b", "¬b=a", "a>b", "b<a"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn weaker_positive_lt_includes_le_and_disequality() {
        let env = env(&[("a", "ℤ"), ("b", "ℤ")]);
        let list = weaker_positive(&pred(&env, "a<b"));
        for s in ["a<b", "b>a", "a≤b", "b≥a", "¬a=b", "¬b=a"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn literal_bounds_shift_by_one() {
        let env = env(&[("x", "ℤ")]);
        // x<1 is equivalent to x≤0 (and to x∉ℕ1).
        let list = stronger_positive(&pred(&env, "x<1"));
        for s in ["x<1", "x≤0", "¬x∈ℕ1"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn negative_literal_variations_use_parse_normal_shape() {
        let env = env(&[("x", "ℤ")]);
        // L1 lists −1<x among the predicates implying x∈ℕ; the
        // constructed −1 must match the parse-normal unary-minus shape.
        let list = stronger_positive(&pred(&env, "x∈ℕ"));
        for s in ["−1<x", "x>−1"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn parsed_negative_literal_bound_implies_natural_membership() {
        let env = env(&[("x", "ℤ")]);
        // −1<x is equivalent to x∈ℕ at level 1; the parsed −1 arrives
        // as a unary minus over the literal 1.
        let list = stronger_positive(&pred(&env, "−1<x"));
        for s in ["−1<x", "x∈ℕ", "0≤x", "x∈ℕ1"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn literal_constructor_matches_parsed_negative_literal() {
        let env = env(&[("x", "ℤ")]);
        let parsed = pred(&env, "x≤−1");
        let PredicateKind::Relational { right, .. } = parsed.kind() else {
            panic!("expected a relational predicate");
        };
        assert_eq!(int_lit(right), Some(BigInt::from(-1)));
        assert_eq!(&literal(right, BigInt::from(-1)), right);
    }

    #[test]
    fn boolean_true_false_equivalences() {
        let env = env(&[("b", "BOOL")]);
        let list = stronger_positive(&pred(&env, "b=TRUE"));
        assert!(contains(&list, &env, "¬b=FALSE"), "missing ¬b=FALSE");
        assert!(contains(&list, &env, "¬FALSE=b"), "missing ¬FALSE=b");
    }

    #[test]
    fn negated_membership_in_naturals() {
        let env = env(&[("x", "ℤ")]);
        // ¬(x∈ℕ) is equivalent to 0>x.
        let list = stronger_positive(&pred(&env, "¬x∈ℕ"));
        for s in ["¬x∈ℕ", "0>x", "x<0"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
    }

    #[test]
    fn subset_variations() {
        let env = env(&[("S", "ℙ(ℤ)"), ("T", "ℙ(ℤ)")]);
        let list = stronger_positive(&pred(&env, "S⊆T"));
        for s in ["S⊆T", "S⊂T", "S=T", "T=S"] {
            assert!(contains(&list, &env, s), "missing {s}");
        }
        let weaker = weaker_positive(&pred(&env, "S⊂T"));
        for s in ["S⊂T", "S⊆T", "¬S=T", "¬T⊂S", "¬T⊆S"] {
            assert!(contains(&weaker, &env, s), "missing {s}");
        }
    }

    #[test]
    fn non_relational_predicates_stay_singletons() {
        let env = env(&[("S", "ℙ(ℤ)")]);
        let p = pred(&env, "finite(S)");
        assert_eq!(stronger_positive(&p), vec![p.clone()]);
        assert_eq!(weaker_positive(&p), vec![p.clone()]);
        let negated = pred(&env, "¬finite(S)");
        assert_eq!(stronger_positive(&negated), vec![negated.clone()]);
    }
}
