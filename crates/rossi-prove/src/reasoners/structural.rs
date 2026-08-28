//! The core structural reasoners: goal/hypothesis matches, the
//! propositional introductions, and the bookkeeping steps.

use rossi::formula::tag::{AssocPredOp, BinaryPredOp, LiteralPredOp, QuantPredOp};
use rossi::formula::{Predicate, PredicateKind};

use crate::builder::{Reasoner, ReplayHints};
use crate::confidence::Confidence;
use crate::hyp_action::HypAction;
use crate::rule::{Antecedent, Rule};
use crate::sequent::ProverSequent;
use crate::skeleton::StoredRule;
use crate::variations;

use super::{break_possible_conjunct, dedup_preserving_order, display_pred, fresh_instantiation};

/// A closed rule (no antecedents) at maximum confidence.
fn closing_rule(
    stored: &StoredRule,
    goal: Option<Predicate>,
    needed_hyps: Vec<Predicate>,
    display: String,
) -> Rule {
    Rule {
        reasoner: stored.rule.reasoner.clone(),
        goal,
        needed_hyps,
        confidence: Confidence::DISCHARGED_MAX,
        display,
        antecedents: Vec::new(),
    }
}

/// `TrueGoal` — discharges a `⊤` goal.
pub struct TrueGoal;

impl Reasoner for TrueGoal {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        if !matches!(
            seq.goal().kind(),
            PredicateKind::Literal(LiteralPredOp::BTrue)
        ) {
            return Err("Goal is not a tautology".into());
        }
        Ok(closing_rule(
            stored,
            Some(seq.goal().clone()),
            Vec::new(),
            "⊤ goal".into(),
        ))
    }
}

/// `FalseHyp` — discharges any goal from a `⊥` hypothesis.
pub struct FalseHyp;

impl Reasoner for FalseHyp {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let bfalse = seq
            .goal()
            .factory()
            .literal_predicate(LiteralPredOp::BFalse, None);
        if !seq.contains_hypothesis(&bfalse) {
            return Err("no false hypothesis".into());
        }
        Ok(closing_rule(stored, None, vec![bfalse], "⊥ hyp".into()))
    }
}

/// `Hyp` — discharges a goal implied by a hypothesis, scanning the
/// goal's stronger variations in order.
pub struct Hyp;

impl Reasoner for Hyp {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let goal = seq.goal();
        let hypothesis = variations::stronger_positive(goal)
            .into_iter()
            .find(|p| seq.contains_hypothesis(p))
            .ok_or("Goal not in hypothesis")?;
        Ok(closing_rule(
            stored,
            Some(goal.clone()),
            vec![hypothesis],
            "hyp".into(),
        ))
    }
}

/// `ImpI` — introduces an implication: `⊢ A ⇒ B` becomes `A ⊢ B`, the
/// left side split into conjuncts.
pub struct ImpI;

impl Reasoner for ImpI {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let PredicateKind::Binary {
            op: BinaryPredOp::LImp,
            left,
            right,
        } = seq.goal().kind()
        else {
            return Err("Goal is not an implication".into());
        };
        let antecedent = Antecedent {
            goal: Some(right.clone()),
            added_hyps: break_possible_conjunct(left),
            unselected_added: Vec::new(),
            added_idents: Vec::new(),
            hyp_actions: Vec::new(),
        };
        Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: Some(seq.goal().clone()),
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "⇒ goal".into(),
            antecedents: vec![antecedent],
        })
    }
}

/// `AllI` — frees the universally quantified variables of the goal.
/// The stored rule's added identifiers act as name suggestions
/// recovered from the stored antecedent, freshened against the
/// sequent's type environment.
pub struct AllI;

impl Reasoner for AllI {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let goal = seq.goal();
        let PredicateKind::Quantified {
            op: QuantPredOp::Forall,
            decls,
            ..
        } = goal.kind()
        else {
            return Err("Goal is not universally quantified".into());
        };
        let suggested: Vec<&str> = match stored.rule.antecedents.as_slice() {
            [antecedent] => antecedent
                .added_idents
                .iter()
                .map(|ident| ident.name.as_str())
                .collect(),
            _ => Vec::new(),
        };

        let (added_idents, instantiated) =
            fresh_instantiation(decls, goal, seq.type_env(), &suggested)?;

        let names: Vec<&str> = added_idents.iter().map(|i| i.name.as_str()).collect();
        let display = format!("∀ goal (frees {})", names.join(","));
        let antecedent = Antecedent {
            goal: Some(instantiated),
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents,
            hyp_actions: Vec::new(),
        };
        Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: Some(goal.clone()),
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display,
            antecedents: vec![antecedent],
        })
    }
}

/// `Conj` — splits a conjunctive goal into one antecedent per distinct
/// conjunct. Its hypothesis-input base would also accept a
/// hypothesis input, which `Conj` rejects.
pub struct Conj;

impl Reasoner for Conj {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        hints: &ReplayHints,
    ) -> Result<Rule, String> {
        match stored.rule.needed_hyps.as_slice() {
            [] => {}
            [hyp] => {
                // Applying with a hypothesis input:
                // existence is checked first, then Conj refuses it.
                let hyp = hints.apply_pred(hyp);
                if !seq.contains_hypothesis(&hyp) {
                    return Err(format!("Nonexistent hypothesis: {}", display_pred(&hyp)));
                }
                return Err(format!(
                    "Reasoner {} inapplicable to a hypothesis",
                    stored.rule.reasoner.id()
                ));
            }
            _ => return Err("Expected at most one needed hypothesis!".into()),
        }
        let PredicateKind::Associative {
            op: AssocPredOp::LAnd,
            children,
        } = seq.goal().kind()
        else {
            return Err(format!(
                "Reasoner {} inapplicable to {}",
                stored.rule.reasoner.id(),
                display_pred(seq.goal())
            ));
        };
        let antecedents = dedup_preserving_order(children.clone())
            .into_iter()
            .map(|conjunct| Antecedent {
                goal: Some(conjunct),
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: Vec::new(),
            })
            .collect();
        Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: Some(seq.goal().clone()),
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "∧ goal".into(),
            antecedents,
        })
    }
}

/// `ContrHyps` — closes any goal from a hypothesis contradicted by
/// other hypotheses (via stronger variations).
pub struct ContrHyps;

impl ContrHyps {
    /// `ContrHyps.contradictingPredicates`: each sub-predicate of `hyp`
    /// paired with the predicates contradicting it.
    fn contradicting(hyp: &Predicate) -> Vec<(Predicate, Vec<Predicate>)> {
        if let PredicateKind::Not(inner) = hyp.kind() {
            break_possible_conjunct(inner)
                .into_iter()
                .map(|p| {
                    let contras = variations::stronger_positive(&p);
                    (p, contras)
                })
                .collect()
        } else {
            vec![(hyp.clone(), variations::stronger_negative(hyp))]
        }
    }

    /// The needed hypothesis contradicted
    /// by the others, when the stored rule does not pin it down.
    fn find_input(needed: &[Predicate]) -> Option<Predicate> {
        needed
            .iter()
            .find(|candidate| {
                Self::contradicting(candidate)
                    .iter()
                    .all(|(_, contras)| contras.iter().any(|contra| needed.contains(contra)))
            })
            .cloned()
    }
}

impl Reasoner for ContrHyps {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let needed = &stored.rule.needed_hyps;
        let hyp = match needed.as_slice() {
            [single] => single.clone(),
            _ => Self::find_input(needed).ok_or("Unexpected set of needed hypothesis")?,
        };
        let hyp = hints.apply_pred(&hyp);

        if !seq.contains_hypothesis(&hyp) {
            return Err(format!("Nonexistent hypothesis: {}", display_pred(&hyp)));
        }
        let mut needed_hyps = Vec::new();
        for (pred, contras) in Self::contradicting(&hyp) {
            let mut contained = false;
            for contra in contras {
                if seq.contains_hypothesis(&contra) {
                    contained = true;
                    if !needed_hyps.contains(&contra) {
                        needed_hyps.push(contra);
                    }
                }
            }
            if !contained {
                return Err(format!(
                    "Predicate {} is not contradicted by hypotheses",
                    display_pred(&pred)
                ));
            }
        }
        if !needed_hyps.contains(&hyp) {
            needed_hyps.push(hyp.clone());
        }
        Ok(closing_rule(
            stored,
            None,
            needed_hyps,
            format!("ct in hyps ({})", display_pred(&hyp)),
        ))
    }
}

/// `Review` — re-asserts a sequent a reviewer accepted: the stored
/// goal and hypotheses must match, and the rule keeps the reviewer's
/// confidence.
pub struct Review;

impl Reasoner for Review {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let goal = stored
            .rule
            .goal
            .as_ref()
            .ok_or("review rule without a goal")?;
        let goal = hints.apply_pred(goal);
        let hyps = dedup_preserving_order(
            stored
                .rule
                .needed_hyps
                .iter()
                .map(|hyp| hints.apply_pred(hyp))
                .collect(),
        );
        if *seq.goal() != goal || !seq.contains_hypotheses(&hyps) {
            return Err("Reviewed sequent does not match".into());
        }
        let confidence = stored.rule.confidence;
        Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: Some(goal.clone()),
            needed_hyps: hyps,
            confidence,
            display: format!("rv ({}) ({})", confidence.0, display_pred(&goal)),
            antecedents: Vec::new(),
        })
    }
}

/// `MngHyp` — replays a hypothesis-management step: one selection
/// action (select/deselect/hide/show) recovered from the stored rule's
/// single antecedent.
pub struct MngHyp;

impl Reasoner for MngHyp {
    fn replay(
        &self,
        _seq: &ProverSequent,
        stored: &StoredRule,
        hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let [antecedent] = stored.rule.antecedents.as_slice() else {
            return Err("Two many antecedents in the rule".into());
        };
        let [action] = antecedent.hyp_actions.as_slice() else {
            return Err("Two many actions in the rule antecedent".into());
        };
        let rehint = |hyps: &[Predicate]| {
            dedup_preserving_order(hyps.iter().map(|hyp| hints.apply_pred(hyp)).collect())
        };
        let action = match action {
            HypAction::Select(hyps) => HypAction::Select(rehint(hyps)),
            HypAction::Deselect(hyps) => HypAction::Deselect(rehint(hyps)),
            HypAction::Hide(hyps) => HypAction::Hide(rehint(hyps)),
            HypAction::Show(hyps) => HypAction::Show(rehint(hyps)),
            HypAction::ForwardInf { .. } | HypAction::Rewrite { .. } => {
                return Err("not a selection action".into());
            }
        };
        Ok(Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "sl/ds".into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![action],
            }],
        })
    }
}

/// `IsFunGoal` — discharges `E ∈ Ta ⇸ Tb` over type expressions with
/// a hypothesis typing `E` as any kind of function.
pub struct IsFunGoal;

impl Reasoner for IsFunGoal {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        use rossi::formula::ExpressionKind;
        use rossi::formula::tag::{BinaryExprOp, RelationalOp};
        let goal = seq.goal();
        let PredicateKind::Relational {
            op: RelationalOp::In,
            left: element,
            right: set,
        } = goal.kind()
        else {
            return Err("Goal is not an inclusion".into());
        };
        let ExpressionKind::Binary {
            op: BinaryExprOp::PFun,
            left,
            right,
        } = set.kind()
        else {
            return Err("Goal is not a functional inclusion".into());
        };
        if !left.is_type_expression() {
            return Err(
                "Left hand side of functional inclusion in goal is not a type expression.".into(),
            );
        }
        if !right.is_type_expression() {
            return Err(
                "Right hand side of functional inclusion in goal is not a type expression.".into(),
            );
        }
        let is_fun = |e: &rossi::formula::Expression| {
            matches!(
                e.kind(),
                ExpressionKind::Binary {
                    op: BinaryExprOp::PFun
                        | BinaryExprOp::TFun
                        | BinaryExprOp::PInj
                        | BinaryExprOp::TInj
                        | BinaryExprOp::PSur
                        | BinaryExprOp::TSur
                        | BinaryExprOp::TBij,
                    ..
                }
            )
        };
        let fun_hyp = seq
            .visible_hyp_iter()
            .find(|hyp| {
                matches!(hyp.kind(),
                    PredicateKind::Relational {
                        op: RelationalOp::In,
                        left,
                        right,
                    } if left == element && is_fun(right))
            })
            .ok_or("No appropriate hypothesis found")?;
        Ok(closing_rule(
            stored,
            Some(goal.clone()),
            vec![fun_hyp.clone()],
            "functional goal".into(),
        ))
    }
}

/// `FiniteHypBoundedGoal` — discharges a goal asserting a lower or
/// upper bound of a set known finite (or given in extension).
pub struct FiniteHypBoundedGoal;

impl Reasoner for FiniteHypBoundedGoal {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        use rossi::formula::tag::RelationalOp;
        use rossi::formula::{Expression, ExpressionKind};
        // ∃x·∀y·y ∈ S ⇒ (a bound comparison between x and y), with S
        // closed.
        let bound_set = |goal: &Predicate| -> Option<Expression> {
            let PredicateKind::Quantified {
                op: QuantPredOp::Exists,
                decls: outer,
                pred: inner,
            } = goal.kind()
            else {
                return None;
            };
            let PredicateKind::Quantified {
                op: QuantPredOp::Forall,
                decls: inner_decls,
                pred: body,
            } = inner.kind()
            else {
                return None;
            };
            if outer.len() != 1 || inner_decls.len() != 1 {
                return None;
            }
            let PredicateKind::Binary {
                op: BinaryPredOp::LImp,
                left: membership,
                right: bound,
            } = body.kind()
            else {
                return None;
            };
            let PredicateKind::Relational {
                op: RelationalOp::In,
                left: member,
                right: set,
            } = membership.kind()
            else {
                return None;
            };
            if !matches!(member.kind(), ExpressionKind::BoundIdentifier(0)) {
                return None;
            }
            let PredicateKind::Relational {
                op: RelationalOp::Le | RelationalOp::Ge,
                left,
                right,
            } = bound.kind()
            else {
                return None;
            };
            let index = |e: &Expression| match e.kind() {
                ExpressionKind::BoundIdentifier(i) => Some(*i),
                _ => None,
            };
            let (a, b) = (index(left)?, index(right)?);
            if !((a == 0 && b == 1) || (a == 1 && b == 0)) {
                return None;
            }
            set.dangling_bound_indices().is_empty().then(|| set.clone())
        };
        let Some(set) = bound_set(seq.goal()) else {
            return Err("Finite hyp is not applicable".into());
        };
        let finite_hyp = seq
            .visible_hyp_iter()
            .find(|hyp| matches!(hyp.kind(), PredicateKind::Simple(child) if child == &set));
        let needed = match finite_hyp {
            Some(hyp) => vec![hyp.clone()],
            None if matches!(set.kind(), ExpressionKind::SetExtension(_)) => Vec::new(),
            None => return Err("Finite hyp is not applicable".into()),
        };
        Ok(closing_rule(
            stored,
            Some(seq.goal().clone()),
            needed,
            "Existence of minimum or maximum in goal with finite hypothesis".into(),
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sequent::TypedIdent;
    use crate::skeleton::StoredInput;
    use crate::test_util::{desc, env, pred};

    /// A stored rule for `short` whose recorded content is irrelevant
    /// to the reasoner under test.
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

    fn no_hints() -> ReplayHints {
        ReplayHints::default()
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
    fn true_goal_needs_a_tautology() {
        let env = env(&[]);
        let seq = sequent(&env, &[], "⊤");
        let rule = TrueGoal
            .replay(&seq, &stored("trueGoal"), &no_hints())
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        assert!(rule.needed_hyps.is_empty() && rule.antecedents.is_empty());
        assert_eq!(rule.confidence, Confidence::DISCHARGED_MAX);
        assert!(rule.apply(&seq).is_some_and(|children| children.is_empty()));

        let open = sequent(&env, &[], "⊥");
        assert!(
            TrueGoal
                .replay(&open, &stored("trueGoal"), &no_hints())
                .is_err()
        );
    }

    #[test]
    fn false_hyp_closes_any_goal_with_wildcard() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &["⊥"], "x=1");
        let rule = FalseHyp
            .replay(&seq, &stored("falseHyp"), &no_hints())
            .unwrap();
        assert_eq!(rule.goal, None);
        assert_eq!(rule.needed_hyps, vec![pred(&env, "⊥")]);
        assert!(rule.apply(&seq).is_some_and(|children| children.is_empty()));

        let without = sequent(&env, &["x=1"], "x=1");
        assert!(
            FalseHyp
                .replay(&without, &stored("falseHyp"), &no_hints())
                .is_err()
        );
    }

    #[test]
    fn hyp_matches_exact_and_stronger_hypotheses() {
        let env = env(&[("a", "ℤ"), ("b", "ℤ")]);
        // Exact match.
        let seq = sequent(&env, &["a≤b"], "a≤b");
        let rule = Hyp.replay(&seq, &stored("hyp"), &no_hints()).unwrap();
        assert_eq!(rule.needed_hyps, vec![pred(&env, "a≤b")]);

        // a<b is stronger than a≤b: found through variations.
        let seq = sequent(&env, &["a<b"], "a≤b");
        let rule = Hyp.replay(&seq, &stored("hyp"), &no_hints()).unwrap();
        assert_eq!(rule.needed_hyps, vec![pred(&env, "a<b")]);
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));

        // The reverse is not: a≤b does not imply a<b.
        let seq = sequent(&env, &["a≤b"], "a<b");
        assert!(Hyp.replay(&seq, &stored("hyp"), &no_hints()).is_err());
    }

    #[test]
    fn imp_i_splits_the_left_side_into_hypotheses() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &[], "x=1∧x<9⇒x<2");
        let rule = ImpI.replay(&seq, &stored("impI"), &no_hints()).unwrap();
        assert_eq!(rule.display, "⇒ goal");
        assert_eq!(rule.antecedents.len(), 1);
        let ante = &rule.antecedents[0];
        assert_eq!(ante.goal.as_ref(), Some(&pred(&env, "x<2")));
        assert_eq!(ante.added_hyps, vec![pred(&env, "x=1"), pred(&env, "x<9")]);
        let children = rule.apply(&seq).unwrap();
        assert_eq!(children.len(), 1);
        assert_eq!(children[0].goal(), &pred(&env, "x<2"));
        assert!(children[0].contains_hypothesis(&pred(&env, "x=1")));

        let nonimp = sequent(&env, &[], "x=1");
        assert!(ImpI.replay(&nonimp, &stored("impI"), &no_hints()).is_err());
    }

    #[test]
    fn all_i_frees_variables_with_fresh_names() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &[], "∀y,x·y=1∧x=2⇒y<x");
        let rule = AllI.replay(&seq, &stored("allI"), &no_hints()).unwrap();
        let ante = &rule.antecedents[0];
        // y is free in the environment already? No — only x is, so y
        // stays y and the bound x freshens to x0.
        assert_eq!(
            ante.added_idents,
            vec![
                TypedIdent::new("y", rossi::formula::Type::Int),
                TypedIdent::new("x0", rossi::formula::Type::Int),
            ]
        );
        let wide = crate::test_util::env(&[("x", "ℤ"), ("y", "ℤ"), ("x0", "ℤ")]);
        assert_eq!(ante.goal.as_ref(), Some(&pred(&wide, "y=1∧x0=2⇒y<x0")));
        assert_eq!(rule.display, "∀ goal (frees y,x0)");
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn all_i_honours_stored_name_suggestions() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &[], "∀y·y>x");
        let mut with_names = stored("allI");
        with_names.rule.antecedents = vec![Antecedent {
            goal: None,
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents: vec![TypedIdent::new("k", rossi::formula::Type::Int)],
            hyp_actions: Vec::new(),
        }];
        let rule = AllI.replay(&seq, &with_names, &no_hints()).unwrap();
        assert_eq!(
            rule.antecedents[0].added_idents,
            vec![TypedIdent::new("k", rossi::formula::Type::Int)]
        );
    }

    #[test]
    fn conj_splits_distinct_conjuncts() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &[], "x=1∧x<9∧x=1");
        let rule = Conj.replay(&seq, &stored("conj"), &no_hints()).unwrap();
        // The duplicate conjunct collapses, order kept.
        let goals: Vec<_> = rule
            .antecedents
            .iter()
            .map(|a| a.goal.clone().unwrap())
            .collect();
        assert_eq!(goals, vec![pred(&env, "x=1"), pred(&env, "x<9")]);
        assert_eq!(rule.apply(&seq).unwrap().len(), 2);

        // A stored needed hypothesis is Conj's inapplicable-input case.
        let mut with_hyp = stored("conj");
        with_hyp.rule.needed_hyps = vec![pred(&env, "x=1")];
        let seq = sequent(&env, &["x=1"], "x=1∧x<9");
        let err = Conj.replay(&seq, &with_hyp, &no_hints()).unwrap_err();
        assert!(err.contains("inapplicable to a hypothesis"), "{err}");
    }

    #[test]
    fn contr_hyps_finds_the_contradiction() {
        let env = env(&[("x", "ℤ")]);
        // ¬(x=1) is contradicted by the hypothesis x=1.
        let seq = sequent(&env, &["¬x=1", "x=1"], "⊥");
        let mut with_input = stored("contrHyps");
        with_input.rule.needed_hyps = vec![pred(&env, "¬x=1")];
        let rule = ContrHyps.replay(&seq, &with_input, &no_hints()).unwrap();
        assert_eq!(rule.goal, None);
        assert_eq!(
            rule.needed_hyps,
            vec![pred(&env, "x=1"), pred(&env, "¬x=1")]
        );
        assert!(rule.apply(&seq).is_some_and(|children| children.is_empty()));

        // Without the contradicting hypothesis the replay fails.
        let alone = sequent(&env, &["¬x=1"], "⊥");
        assert!(ContrHyps.replay(&alone, &with_input, &no_hints()).is_err());
    }

    #[test]
    fn contr_hyps_recovers_its_input_from_needed_hyps() {
        let env = env(&[("x", "ℤ")]);
        // Two needed hyps stored (the modern shape): the finder picks
        // the one contradicted by the other.
        let seq = sequent(&env, &["x<1", "x≥1"], "⊥");
        let mut with_both = stored("contrHyps");
        with_both.rule.needed_hyps = vec![pred(&env, "x<1"), pred(&env, "x≥1")];
        let rule = ContrHyps.replay(&seq, &with_both, &no_hints()).unwrap();
        assert_eq!(rule.needed_hyps.len(), 2);
    }

    #[test]
    fn review_replays_at_the_reviewer_confidence() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &["x=1"], "x<2");
        let mut reviewed = stored("review");
        reviewed.rule.goal = Some(pred(&env, "x<2"));
        reviewed.rule.needed_hyps = vec![pred(&env, "x=1")];
        reviewed.rule.confidence = Confidence(400);
        let rule = Review.replay(&seq, &reviewed, &no_hints()).unwrap();
        assert_eq!(rule.confidence, Confidence(400));
        assert_eq!(rule.needed_hyps, vec![pred(&env, "x=1")]);
        assert!(rule.display.starts_with("rv (400) ("), "{}", rule.display);
        assert!(rule.apply(&seq).is_some_and(|children| children.is_empty()));

        // A goal drift makes the review invalid.
        let drifted = sequent(&env, &["x=1"], "x<3");
        assert!(Review.replay(&drifted, &reviewed, &no_hints()).is_err());
    }

    #[test]
    fn mng_hyp_replays_the_stored_selection_action() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &["x=1", "x<9"], "x<2");
        let mut managed = stored("mngHyp");
        managed.rule.antecedents = vec![Antecedent {
            goal: None,
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents: Vec::new(),
            hyp_actions: vec![HypAction::Hide(vec![pred(&env, "x<9")])],
        }];
        let rule = MngHyp.replay(&seq, &managed, &no_hints()).unwrap();
        assert_eq!(rule.goal, None);
        assert_eq!(rule.display, "sl/ds");
        let children = rule.apply(&seq).unwrap();
        assert_eq!(children.len(), 1);
        assert!(children[0].is_hidden(&pred(&env, "x<9")));

        // A forward-inference action is not a selection action.
        managed.rule.antecedents[0].hyp_actions = vec![HypAction::ForwardInf {
            hyps: vec![pred(&env, "x=1")],
            added_idents: Vec::new(),
            inferred: vec![pred(&env, "x<9")],
        }];
        assert!(MngHyp.replay(&seq, &managed, &no_hints()).is_err());
    }

    #[test]
    fn registry_provider_serves_only_trusted_implementations() {
        use crate::builder::{ReasonerProvider, RegistryProvider};
        // Implemented and trusted.
        assert!(RegistryProvider.implementation(&desc("hyp")).is_some());
        assert!(
            RegistryProvider
                .implementation(&desc("contrHyps:1"))
                .is_some()
        );
        // Version conflict: contrHyps is at version 1.
        assert!(
            RegistryProvider
                .implementation(&desc("contrHyps:0"))
                .is_none()
        );
        // Registered but not implemented.
        assert!(
            RegistryProvider
                .implementation(&desc("onePointRule:2"))
                .is_none()
        );
        // Unknown id.
        assert!(
            RegistryProvider
                .implementation(&crate::registry::resolve("com.example.mystery"))
                .is_none()
        );
    }

    #[test]
    fn is_fun_goal_discharges_with_a_function_hypothesis() {
        let env = env(&[("f", "ℙ(ℤ×ℤ)"), ("A", "ℙ(ℤ)")]);
        let seq = sequent(&env, &["f ∈ A → ℤ"], "f ∈ ℤ ⇸ ℤ");
        let rule = IsFunGoal
            .replay(&seq, &stored("isFunGoal"), &ReplayHints::default())
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        assert_eq!(rule.needed_hyps, vec![pred(&env, "f ∈ A → ℤ")]);
        assert!(rule.antecedents.is_empty());
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn is_fun_goal_requires_type_expressions() {
        let env = env(&[("f", "ℙ(ℤ×ℤ)"), ("A", "ℙ(ℤ)")]);
        let seq = sequent(&env, &["f ∈ A → ℤ"], "f ∈ A ⇸ ℤ");
        let err = IsFunGoal
            .replay(&seq, &stored("isFunGoal"), &ReplayHints::default())
            .unwrap_err();
        assert!(err.contains("not a type expression"), "{err}");
    }

    #[test]
    fn finite_hyp_bounded_goal_uses_the_finiteness_hypothesis() {
        let env = env(&[("S", "ℙ(ℤ)")]);
        let seq = sequent(&env, &["finite(S)"], "∃x·∀y·y ∈ S ⇒ x ≤ y");
        let rule = FiniteHypBoundedGoal
            .replay(
                &seq,
                &stored("finiteHypBoundedGoal"),
                &ReplayHints::default(),
            )
            .unwrap();
        assert_eq!(rule.needed_hyps, vec![pred(&env, "finite(S)")]);
        assert!(rule.antecedents.is_empty());
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn finite_hyp_bounded_goal_accepts_a_set_in_extension() {
        let env = env(&[("z", "ℤ")]);
        let seq = sequent(&env, &[], "∃x·∀y·y ∈ {1, z} ⇒ y ≤ x");
        let rule = FiniteHypBoundedGoal
            .replay(
                &seq,
                &stored("finiteHypBoundedGoal"),
                &ReplayHints::default(),
            )
            .unwrap();
        assert_eq!(rule.needed_hyps, Vec::<Predicate>::new());
    }

    #[test]
    fn finite_hyp_bounded_goal_fails_without_evidence() {
        let env = env(&[("S", "ℙ(ℤ)")]);
        let seq = sequent(&env, &[], "∃x·∀y·y ∈ S ⇒ x ≤ y");
        let err = FiniteHypBoundedGoal
            .replay(
                &seq,
                &stored("finiteHypBoundedGoal"),
                &ReplayHints::default(),
            )
            .unwrap_err();
        assert_eq!(err, "Finite hyp is not applicable");
    }
}
