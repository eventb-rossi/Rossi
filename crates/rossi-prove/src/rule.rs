//! Proof rules: one reasoner-produced step of a proof.
//!
//! Applying a rule is the kernel's
//! *trusting* check — needed hypotheses present, goal syntactically
//! equal (or the rule goal is a wildcard), antecedent sequents
//! constructible — with no re-derivation of logical entailment;
//! soundness lives in the reasoner that produced the rule.

use rossi::formula::Predicate;

use crate::confidence::Confidence;
use crate::hyp_action::HypAction;
use crate::sequent::{ProverSequent, TypedIdent};

/// One antecedent: the recipe for one child sequent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Antecedent {
    /// The child's goal; `None` keeps the applied-to sequent's goal
    /// (only meaningful under a wildcard rule goal).
    pub goal: Option<Predicate>,
    /// Hypotheses the child gains, selected unless listed below.
    pub added_hyps: Vec<Predicate>,
    /// The added hypotheses to leave unselected — a subset of
    /// `added_hyps`.
    pub unselected_added: Vec<Predicate>,
    /// Free identifiers the child's environment gains.
    pub added_idents: Vec<TypedIdent>,
    /// Hypothesis actions, applied in list order after the additions.
    pub hyp_actions: Vec<HypAction>,
}

impl Antecedent {
    /// The child sequent this antecedent generates from `seq`, or
    /// `None` when generation is impossible: a name clash, a type
    /// error, or an ill-formed rule (a stated rule goal with a
    /// wildcard antecedent goal leaves `goal_instantiation` empty).
    fn gen_sequent(
        &self,
        seq: &ProverSequent,
        goal_instantiation: Option<&Predicate>,
    ) -> Option<ProverSequent> {
        let new_goal = match &self.goal {
            Some(goal) => goal,
            None => goal_instantiation?,
        };
        let mut result = seq.modify(
            &self.added_idents,
            &self.added_hyps,
            &self.unselected_added,
            Some(new_goal),
        )?;
        for action in &self.hyp_actions {
            result = action.perform(&result);
        }
        Some(result)
    }
}

/// A proof rule.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Rule {
    /// The goal this rule discharges; `None` is a wildcard matching
    /// any goal.
    pub goal: Option<Predicate>,
    /// Hypotheses that must be present for the rule to apply.
    pub needed_hyps: Vec<Predicate>,
    /// The confidence of this step.
    pub confidence: Confidence,
    /// Display name, e.g. `simplification rewrites`.
    pub display: String,
    /// The child sequents' recipes; none means the rule closes its
    /// node.
    pub antecedents: Vec<Antecedent>,
}

impl Rule {
    /// Applies this rule to `seq`: the
    /// needed hypotheses must be present, a non-wildcard goal must be
    /// syntactically equal to the sequent's, and every antecedent must
    /// generate its child sequent. `None` when any check fails.
    pub fn apply(&self, seq: &ProverSequent) -> Option<Vec<ProverSequent>> {
        if !seq.contains_hypotheses(&self.needed_hyps) {
            return None;
        }
        if let Some(goal) = &self.goal
            && goal != seq.goal()
        {
            return None;
        }
        let goal_instantiation = self.goal.is_none().then(|| seq.goal().clone());
        self.antecedents
            .iter()
            .map(|antecedent| antecedent.gen_sequent(seq, goal_instantiation.as_ref()))
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{env, pred};
    use rossi::formula::{SealedTypeEnvironment, Type};

    /// x=1, y=3 (selected: x=1; hidden: y=3) ⊢ x<2
    fn base() -> ProverSequent {
        let env = env(&[("x", "ℤ"), ("y", "ℤ")]);
        let h1 = pred(&env, "x=1");
        let h2 = pred(&env, "y=3");
        ProverSequent::new(
            env.clone(),
            [h1.clone(), h2.clone()],
            [h2],
            [h1],
            pred(&env, "x<2"),
        )
    }

    fn wide() -> SealedTypeEnvironment {
        env(&[("x", "ℤ"), ("y", "ℤ"), ("z", "ℤ")])
    }

    fn closing(goal: Option<Predicate>, needed: Vec<Predicate>) -> Rule {
        Rule {
            goal,
            needed_hyps: needed,
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: Vec::new(),
        }
    }

    #[test]
    fn apply_checks_needed_hypotheses_and_goal() {
        let seq = base();
        let env = seq.type_env().clone();

        let ok = closing(Some(seq.goal().clone()), vec![pred(&env, "x=1")]);
        assert!(ok.apply(&seq).is_some_and(|children| children.is_empty()));

        let missing_hyp = closing(None, vec![pred(&env, "x=7")]);
        assert!(missing_hyp.apply(&seq).is_none());

        let wrong_goal = closing(Some(pred(&env, "x<3")), Vec::new());
        assert!(wrong_goal.apply(&seq).is_none());

        // A wildcard goal matches anything.
        let wildcard = closing(None, Vec::new());
        assert!(
            wildcard
                .apply(&seq)
                .is_some_and(|children| children.is_empty())
        );
    }

    #[test]
    fn wildcard_antecedent_inherits_the_goal() {
        let seq = base();
        let rule = Rule {
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: Vec::new(),
            }],
        };
        let children = rule.apply(&seq).expect("applies");
        assert_eq!(children.len(), 1);
        assert_eq!(children[0].goal(), seq.goal());
        // Nothing changed at all: the child is the sequent itself.
        assert!(ProverSequent::ptr_eq(&seq, &children[0]));
    }

    #[test]
    fn stated_rule_goal_with_wildcard_antecedent_is_ill_formed() {
        let seq = base();
        let rule = Rule {
            goal: Some(seq.goal().clone()),
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: Vec::new(),
            }],
        };
        assert!(rule.apply(&seq).is_none());
    }

    #[test]
    fn antecedent_additions_reach_the_child() {
        let seq = base();
        let wide = wide();
        let added = pred(&wide, "z>0");
        let unsel = pred(&wide, "z<9");
        let rule = Rule {
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: vec![Antecedent {
                goal: Some(pred(&wide, "z=1")),
                added_hyps: vec![added.clone(), unsel.clone()],
                unselected_added: vec![unsel.clone()],
                added_idents: vec![TypedIdent::new("z", Type::Int)],
                hyp_actions: Vec::new(),
            }],
        };
        let children = rule.apply(&seq).expect("applies");
        let child = &children[0];
        assert_eq!(child.goal(), &pred(&wide, "z=1"));
        assert_eq!(child.type_env().get("z"), Some(&Type::Int));
        assert!(child.is_selected(&added));
        assert!(child.contains_hypothesis(&unsel));
        assert!(!child.is_selected(&unsel));
    }

    #[test]
    fn antecedent_failure_fails_the_rule() {
        let seq = base();
        // Introducing `x` again clashes with the environment.
        let rule = Rule {
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: vec![TypedIdent::new("x", Type::Int)],
                hyp_actions: Vec::new(),
            }],
        };
        assert!(rule.apply(&seq).is_none());
    }

    #[test]
    fn hyp_actions_run_in_list_order() {
        let seq = base();
        let env = seq.type_env().clone();
        let h1 = pred(&env, "x=1");

        let hide_then_select = vec![
            HypAction::Hide(vec![h1.clone()]),
            HypAction::Select(vec![h1.clone()]),
        ];
        let select_then_hide = vec![
            HypAction::Select(vec![h1.clone()]),
            HypAction::Hide(vec![h1.clone()]),
        ];
        let apply = |actions: Vec<HypAction>| {
            let rule = Rule {
                goal: None,
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: "test".into(),
                antecedents: vec![Antecedent {
                    goal: None,
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions: actions,
                }],
            };
            rule.apply(&seq).expect("applies").remove(0)
        };

        let ends_selected = apply(hide_then_select);
        assert!(ends_selected.is_selected(&h1));
        assert!(!ends_selected.is_hidden(&h1));

        let ends_hidden = apply(select_then_hide);
        assert!(ends_hidden.is_hidden(&h1));
        assert!(!ends_hidden.is_selected(&h1));
    }

    #[test]
    fn rewrite_action_through_a_rule() {
        let seq = base();
        let env = seq.type_env().clone();
        let src = pred(&env, "x=1");
        let inf = pred(&env, "1=x");
        let rule = Rule {
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![HypAction::Rewrite {
                    hyps: vec![src.clone()],
                    added_idents: Vec::new(),
                    inferred: vec![inf.clone()],
                    disappearing: vec![src.clone()],
                }],
            }],
        };
        let child = rule.apply(&seq).expect("applies").remove(0);
        assert!(child.is_selected(&inf));
        assert!(child.is_hidden(&src));
    }
}
