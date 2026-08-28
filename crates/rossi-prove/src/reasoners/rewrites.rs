//! The automatic rewriting reasoners: the fixpoint pass over every
//! visible hypothesis and the goal, and the rewriter implementations
//! driving it, each at its latest level.

use rossi::formula::tag::{AtomicOp, LiteralPredOp, RelationalOp};
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
    hide_original: bool,
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

        if inferred_hyps.is_empty() && hide_original {
            hyp_actions.push(HypAction::Hide(vec![hyp.clone()]));
            continue;
        }
        if !inferred_hyps.is_empty() {
            if hide_original {
                hyp_actions.push(HypAction::Rewrite {
                    hyps: vec![hyp.clone()],
                    added_idents: Vec::new(),
                    inferred: inferred_hyps,
                    disappearing: vec![hyp.clone()],
                });
            } else {
                hyp_actions.push(HypAction::ForwardInf {
                    hyps: vec![hyp.clone()],
                    added_idents: Vec::new(),
                    inferred: inferred_hyps,
                });
            }
        }
    }

    let new_goal = recursive_rewrite(seq.goal(), rewriter);
    if let Some(new_goal) = new_goal {
        return Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: Some(seq.goal().clone()),
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: display.into(),
            antecedents: vec![Antecedent {
                goal: Some(new_goal),
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions,
            }],
        });
    }
    if !hyp_actions.is_empty() {
        return Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: display.into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions,
            }],
        });
    }
    Err("No rewrites applicable".into())
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
        auto_rewrite_rule(
            seq,
            stored,
            &mut TypeRewriterImpl,
            true,
            false,
            "type rewrites",
        )
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
