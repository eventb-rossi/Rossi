//! The automatic rewriting reasoners: the fixpoint pass over every
//! visible hypothesis and the goal, and the rewriter implementations
//! driving it, each at its latest level.

use rossi::formula::tag::{AssocPredOp, AtomicOp, LiteralPredOp, RelationalOp};
use rossi::formula::{ExpressionKind, Predicate, PredicateKind};

use crate::builder::{Reasoner, ReplayHints};
use crate::confidence::Confidence;
use crate::hyp_action::HypAction;
use crate::rule::{Antecedent, Rule};
use crate::sequent::ProverSequent;
use crate::skeleton::StoredRule;

use super::break_possible_conjunct;
use super::driver::{NodeRewriter, recursive_rewrite};

fn is_true(pred: &Predicate) -> bool {
    matches!(pred.kind(), PredicateKind::Literal(LiteralPredOp::BTrue))
}

/// Rewrite every visible hypothesis and
/// the goal to fixpoint, emitting one hypothesis action per changed
/// hypothesis. `remove_true_in_post` models the auto-rewrite
/// post-processing, which drops `⊤` before the unchanged-hypothesis
/// check (so an unchanged `⊤` hypothesis is hidden rather than
/// skipped); the base behaviour drops it after.
pub(crate) fn auto_rewrite_rule(
    seq: &ProverSequent,
    stored: &StoredRule,
    rewriter: &mut (impl NodeRewriter + ?Sized),
    remove_true_in_post: bool,
    display: &str,
) -> Result<Rule, String> {
    let mut hyp_actions: Vec<HypAction> = Vec::new();
    for hyp in seq.visible_hyp_iter() {
        let rewritten = recursive_rewrite(hyp, rewriter);
        let changed = rewritten.is_some();
        let inferred_hyp = rewritten.unwrap_or_else(|| hyp.clone());
        let mut inferred_hyps = break_possible_conjunct(&inferred_hyp);
        if remove_true_in_post {
            inferred_hyps.retain(|pred| !is_true(pred));
        }
        if !changed && inferred_hyps.len() == 1 {
            continue;
        }
        inferred_hyps.retain(|pred| !is_true(pred));

        if inferred_hyps.is_empty() {
            hyp_actions.push(HypAction::Hide(vec![hyp.clone()]));
        } else {
            hyp_actions.push(HypAction::Rewrite {
                hyps: vec![hyp.clone()],
                added_idents: Vec::new(),
                inferred: inferred_hyps,
                disappearing: vec![hyp.clone()],
            });
        }
    }

    let new_goal = recursive_rewrite(seq.goal(), rewriter);
    if new_goal.is_none() && hyp_actions.is_empty() {
        return Err("No rewrites applicable".into());
    }
    // A changed goal makes the rule goal-dependent; hypothesis-only
    // rewrites apply at any goal.
    let rule_goal = new_goal.as_ref().map(|_| seq.goal().clone());
    Ok(Rule {
        reasoner: stored.rule.reasoner.clone(),
        goal: rule_goal,
        needed_hyps: Vec::new(),
        confidence: Confidence::DISCHARGED_MAX,
        display: display.into(),
        antecedents: vec![Antecedent {
            goal: new_goal,
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents: Vec::new(),
            hyp_actions,
        }],
    })
}

/// `TypeRewriterImpl` — the four type-simplification rules, applied
/// to relational predicates in the reference pattern order.
struct TypeRewriterImpl;

impl NodeRewriter for TypeRewriterImpl {
    fn predicate(&mut self, pred: &Predicate) -> Option<Predicate> {
        let PredicateKind::Relational { op, left, right } = pred.kind() else {
            return None;
        };
        let ff = pred.factory();
        let truth = |op: LiteralPredOp| Some(ff.literal_predicate(op, None));
        let is_empty_set = |e: &rossi::formula::Expression| {
            matches!(e.kind(), ExpressionKind::Atomic(AtomicOp::EmptySet))
        };
        match op {
            // SIMP_TYPE_IN: E ∈ Typ == ⊤
            RelationalOp::In if right.is_type_expression() => truth(LiteralPredOp::BTrue),
            // SIMP_TYPE_EQUAL_EMPTY: Typ = ∅ == ⊥ and ∅ = Typ == ⊥,
            // in the reference pattern order (a matched shape whose guard
            // fails does not fall through to the mirrored pattern).
            RelationalOp::Equal if is_empty_set(right) => {
                if left.is_type_expression() {
                    truth(LiteralPredOp::BFalse)
                } else {
                    None
                }
            }
            RelationalOp::Equal if is_empty_set(left) => {
                if right.is_type_expression() {
                    truth(LiteralPredOp::BFalse)
                } else {
                    None
                }
            }
            // SIMP_TYPE_SUBSETEQ: S ⊆ Typ == ⊤
            RelationalOp::SubsetEq if right.is_type_expression() => truth(LiteralPredOp::BTrue),
            // SIMP_TYPE_SUBSET_L: S ⊂ Typ == S ≠ Typ
            RelationalOp::Subset if right.is_type_expression() => Some(ff.relational_predicate(
                RelationalOp::NotEqual,
                left.clone(),
                right.clone(),
                None,
            )),
            _ => None,
        }
    }
}

/// `TypeRewrites` (`typeRewrites`) — automatic type simplification.
pub struct TypeRewrites;

impl Reasoner for TypeRewrites {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        auto_rewrite_rule(seq, stored, &mut TypeRewriterImpl, false, "type rewrites")
    }
}

fn literal(pred: &Predicate, op: LiteralPredOp) -> Predicate {
    pred.factory().literal_predicate(op, None)
}

fn is_literal(pred: &Predicate, op: LiteralPredOp) -> bool {
    matches!(pred.kind(), PredicateKind::Literal(found) if *found == op)
}

/// Associative simplification for ∧ and ∨: neutral
/// children drop, a determinant child decides everything, and with
/// `do_multi` duplicates collapse and a contradiction decides.
fn simplify_assoc_pred(
    pred: &Predicate,
    children: &[Predicate],
    neutral: LiteralPredOp,
    determinant: LiteralPredOp,
    do_multi: bool,
) -> Option<Predicate> {
    let mut out: Vec<Predicate> = Vec::new();
    let mut changed = false;
    for child in children {
        if is_literal(child, neutral) {
            changed = true;
        } else if is_literal(child, determinant)
            || (do_multi && out.contains(&super::make_neg(child)))
        {
            return Some(literal(pred, determinant));
        } else if do_multi && out.contains(child) {
            // A duplicate: the insertion-ordered set drops it silently; the
            // shorter child list marks the change.
        } else {
            out.push(child.clone());
        }
    }
    match out.len() {
        0 => Some(literal(pred, neutral)),
        1 => Some(out.into_iter().next().unwrap()),
        len if changed || len != children.len() => {
            let op = match pred.kind() {
                PredicateKind::Associative { op, .. } => *op,
                _ => unreachable!("associative input"),
            };
            Some(pred.factory().associative_predicate(op, out, None))
        }
        _ => None,
    }
}

/// One propositional simplification step on a node whose children
/// are already rewritten, patterns in the reference order,
/// with every option flag fixed at its L5 value (`optionsForLevel`
/// enables them all, and only latest-level reasoners replay here).
/// `None` when no rule fires.
pub(crate) fn simplify_predicate_node(pred: &Predicate) -> Option<Predicate> {
    use LiteralPredOp::{BFalse, BTrue};
    match pred.kind() {
        PredicateKind::Associative { op, children } => match op {
            AssocPredOp::LAnd => simplify_assoc_pred(pred, children, BTrue, BFalse, true),
            AssocPredOp::LOr => simplify_assoc_pred(pred, children, BFalse, BTrue, true),
        },
        PredicateKind::Binary { op, left, right } => match op {
            rossi::formula::tag::BinaryPredOp::LImp => {
                // SIMP_SPECIAL_IMP_BTRUE_L: ⊤ ⇒ P == P
                if is_literal(left, BTrue) {
                    return Some(right.clone());
                }
                // SIMP_SPECIAL_IMP_BFALSE_L: ⊥ ⇒ P == ⊤
                if is_literal(left, BFalse) {
                    return Some(literal(pred, BTrue));
                }
                // SIMP_SPECIAL_IMP_BTRUE_R: P ⇒ ⊤ == ⊤
                if is_literal(right, BTrue) {
                    return Some(right.clone());
                }
                // SIMP_SPECIAL_IMP_BFALSE_R: P ⇒ ⊥ == ¬P
                if is_literal(right, BFalse) {
                    return Some(super::make_neg(left));
                }
                // SIMP_MULTI_IMP: P ⇒ P == ⊤
                if left == right {
                    return Some(literal(pred, BTrue));
                }
                // SIMP_MULTI_IMP_AND: P ∧ … ∧ Q ∧ … ⇒ Q == ⊤
                // SIMP_MULTI_IMP_AND_NOT_R/L: … ⇒ ¬Q with Q among the
                // conjuncts (or the mirrored form) == ¬(left)
                if let PredicateKind::Associative {
                    op: AssocPredOp::LAnd,
                    children,
                } = left.kind()
                {
                    if children.contains(right) {
                        return Some(literal(pred, BTrue));
                    }
                    if children.contains(&super::make_neg(right)) {
                        return Some(super::make_neg(left));
                    }
                }
                // SIMP_MULTI_IMP_NOT_L: ¬P ⇒ P == P
                if let PredicateKind::Not(inner) = left.kind()
                    && inner == right
                {
                    return Some(right.clone());
                }
                // SIMP_MULTI_IMP_NOT_R: P ⇒ ¬P == ¬P
                if let PredicateKind::Not(inner) = right.kind()
                    && inner == left
                {
                    return Some(right.clone());
                }
                None
            }
            rossi::formula::tag::BinaryPredOp::LEqv => {
                // SIMP_SPECIAL_EQV_BTRUE: P ⇔ ⊤ == P, ⊤ ⇔ P == P
                if is_literal(right, BTrue) {
                    return Some(left.clone());
                }
                if is_literal(left, BTrue) {
                    return Some(right.clone());
                }
                // SIMP_MULTI_EQV: P ⇔ P == ⊤
                if left == right {
                    return Some(literal(pred, BTrue));
                }
                // SIMP_SPECIAL_EQV_BFALSE: P ⇔ ⊥ == ¬P, ⊥ ⇔ P == ¬P
                if is_literal(right, BFalse) {
                    return Some(super::make_neg(left));
                }
                if is_literal(left, BFalse) {
                    return Some(super::make_neg(right));
                }
                // SIMP_MULTI_EQV_NOT: P ⇔ ¬P == ⊥ (either side)
                if let PredicateKind::Not(inner) = right.kind()
                    && inner == left
                {
                    return Some(literal(pred, BFalse));
                }
                if let PredicateKind::Not(inner) = left.kind()
                    && inner == right
                {
                    return Some(literal(pred, BFalse));
                }
                None
            }
        },
        PredicateKind::Not(inner) => {
            // SIMP_SPECIAL_NOT_BTRUE / BFALSE, SIMP_NOT_NOT
            if is_literal(inner, BTrue) {
                return Some(literal(pred, BFalse));
            }
            if is_literal(inner, BFalse) {
                return Some(literal(pred, BTrue));
            }
            if let PredicateKind::Not(nested) = inner.kind() {
                return Some(nested.clone());
            }
            None
        }
        PredicateKind::Quantified {
            op,
            decls,
            pred: body,
        } => {
            use rossi::formula::tag::QuantPredOp;
            let ff = pred.factory();
            match (op, body.kind()) {
                // SIMP_FORALL_AND: ∀x·P ∧ … == (∀x·P) ∧ …
                (
                    QuantPredOp::Forall,
                    PredicateKind::Associative {
                        op: AssocPredOp::LAnd,
                        children,
                    },
                ) => Some(
                    ff.associative_predicate(
                        AssocPredOp::LAnd,
                        children
                            .iter()
                            .map(|c| {
                                ff.quantified_predicate(
                                    QuantPredOp::Forall,
                                    decls.clone(),
                                    c.clone(),
                                    None,
                                )
                            })
                            .collect(),
                        None,
                    ),
                ),
                // SIMP_EXISTS_OR: ∃x·P ∨ … == (∃x·P) ∨ …
                (
                    QuantPredOp::Exists,
                    PredicateKind::Associative {
                        op: AssocPredOp::LOr,
                        children,
                    },
                ) => Some(
                    ff.associative_predicate(
                        AssocPredOp::LOr,
                        children
                            .iter()
                            .map(|c| {
                                ff.quantified_predicate(
                                    QuantPredOp::Exists,
                                    decls.clone(),
                                    c.clone(),
                                    None,
                                )
                            })
                            .collect(),
                        None,
                    ),
                ),
                // SIMP_EXISTS_IMP: ∃x·P ⇒ Q == (∀x·P) ⇒ (∃x·Q)
                (
                    QuantPredOp::Exists,
                    PredicateKind::Binary {
                        op: rossi::formula::tag::BinaryPredOp::LImp,
                        left,
                        right,
                    },
                ) => Some(ff.binary_predicate(
                    rossi::formula::tag::BinaryPredOp::LImp,
                    ff.quantified_predicate(QuantPredOp::Forall, decls.clone(), left.clone(), None),
                    ff.quantified_predicate(
                        QuantPredOp::Exists,
                        decls.clone(),
                        right.clone(),
                        None,
                    ),
                    None,
                )),
                _ => None,
            }
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skeleton::StoredInput;
    use crate::test_util::{desc, env, pred};

    fn stored(short: &str) -> StoredRule {
        StoredRule {
            rule: Rule {
                reasoner: desc(short),
                goal: None,
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: String::new(),
                antecedents: Vec::new(),
            },
            input: StoredInput::default(),
        }
    }

    fn sequent(
        env: &rossi::formula::SealedTypeEnvironment,
        hyps: &[&str],
        goal: &str,
    ) -> ProverSequent {
        let hyps: Vec<Predicate> = hyps.iter().map(|s| pred(env, s)).collect();
        ProverSequent::new(env.clone(), hyps.clone(), [], hyps, pred(env, goal))
    }

    #[test]
    fn type_rewrites_simplify_goal_and_hypotheses() {
        let env = env(&[("x", "ℤ"), ("S", "ℙ(ℤ)")]);
        // The goal's x∈ℤ conjunct rewrites to ⊤; a hypothesis
        // reduced entirely to ⊤ is hidden.
        let seq = sequent(&env, &["S⊆ℤ", "S⊂ℤ"], "x∈ℤ∧x>0");
        let rule = TypeRewrites
            .replay(&seq, &stored("typeRewrites:1"), &ReplayHints::default())
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        let ante = &rule.antecedents[0];
        assert_eq!(ante.goal.as_ref(), Some(&pred(&env, "⊤∧x>0")));
        assert_eq!(
            ante.hyp_actions,
            vec![
                HypAction::Hide(vec![pred(&env, "S⊆ℤ")]),
                HypAction::Rewrite {
                    hyps: vec![pred(&env, "S⊂ℤ")],
                    added_idents: Vec::new(),
                    inferred: vec![pred(&env, "S≠ℤ")],
                    disappearing: vec![pred(&env, "S⊂ℤ")],
                },
            ]
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn type_rewrites_fail_without_applicable_rewrites() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &["x>0"], "x>1");
        let err = TypeRewrites
            .replay(&seq, &stored("typeRewrites:1"), &ReplayHints::default())
            .unwrap_err();
        assert_eq!(err, "No rewrites applicable");
    }

    #[test]
    fn empty_set_equality_follows_rodin_pattern_order() {
        let env = env(&[("S", "ℙ(ℤ)")]);
        // ℤ = ∅ rewrites to ⊥ (first pattern), ∅ = ℤ too (second);
        // S = ∅ matches the first pattern's shape but fails its
        // type-expression guard, so it stays — even though the
        // mirrored pattern would not have fired either.
        let seq = sequent(&env, &["ℤ=∅", "∅=ℤ"], "S=∅");
        let rule = TypeRewrites
            .replay(&seq, &stored("typeRewrites:1"), &ReplayHints::default())
            .unwrap();
        // Both hypotheses become ⊥... reduced to nothing? No: ⊥ is
        // not ⊤, so each is rewritten to ⊥, and the goal stays.
        let ante = &rule.antecedents[0];
        assert_eq!(ante.goal, None);
        assert_eq!(ante.hyp_actions.len(), 2);
        for action in &ante.hyp_actions {
            let HypAction::Rewrite { inferred, .. } = action else {
                panic!("expected rewrites, got {action:?}");
            };
            assert_eq!(inferred, &vec![pred(&env, "⊥")]);
        }
    }
}
