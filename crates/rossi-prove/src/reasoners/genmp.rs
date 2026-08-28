//! `genMP` — generalized modus ponens at level L4: every visible
//! hypothesis (and the goal, negatively) contributes truth-value
//! substitutes for its level-1 variations, and occurrences of those
//! predicates inside the other hypotheses and the goal are replaced
//! by `⊤`/`⊥`.

use std::collections::HashMap;

use rossi::formula::tag::{AssocPredOp, LiteralPredOp};
use rossi::formula::{Expression, ExpressionKind, Predicate, PredicateKind};

use crate::builder::{Reasoner, ReplayHints};
use crate::confidence::Confidence;
use crate::hyp_action::HypAction;
use crate::rule::{Antecedent, Rule};
use crate::sequent::ProverSequent;
use crate::skeleton::StoredRule;
use crate::variations;

/// One entry of the substitution table: occurrences of the map key
/// are replaced by `substitute`, on behalf of `origin`.
struct Substitute {
    origin: Predicate,
    from_goal: bool,
    substitute: Predicate,
}

fn is_neg(pred: &Predicate) -> Option<&Predicate> {
    match pred.kind() {
        PredicateKind::Not(child) => Some(child),
        _ => None,
    }
}

fn is_literal(pred: &Predicate) -> bool {
    matches!(pred.kind(), PredicateKind::Literal(_))
}

fn truth(like: &Predicate, positive: bool) -> Predicate {
    like.factory().literal_predicate(
        if positive {
            LiteralPredOp::BTrue
        } else {
            LiteralPredOp::BFalse
        },
        None,
    )
}

/// `Substitute.makeSubstitutes` with the level-1 variations: the
/// source is stripped of negations (tracking polarity), then its
/// weaker/stronger variations map to `⊤`/`⊥`.
fn add_substitutes(
    table: &mut HashMap<Predicate, Substitute>,
    origin: &Predicate,
    from_goal: bool,
    source: &Predicate,
) {
    let mut is_pos = !from_goal;
    let mut source = source.clone();
    while let Some(child) = is_neg(&source) {
        is_pos = !is_pos;
        source = child.clone();
    }
    let groups: [(Vec<Predicate>, bool); 2] = if is_pos {
        [
            (variations::weaker_positive(&source), true),
            (variations::stronger_negative(&source), false),
        ]
    } else {
        [
            (variations::stronger_positive(&source), false),
            (variations::weaker_negative(&source), true),
        ]
    };
    for (list, positive) in groups {
        for mut to_replace in list {
            let mut positive = positive;
            if let Some(child) = is_neg(&to_replace) {
                to_replace = child.clone();
                positive = !positive;
            }
            if is_literal(&to_replace) {
                continue;
            }
            table.entry(to_replace).or_insert_with(|| Substitute {
                origin: origin.clone(),
                from_goal,
                substitute: truth(origin, positive),
            });
        }
    }
}

/// Substitute extraction at L4: visible hypotheses first, then
/// the goal — per disjunct when it is a disjunction (first entry per
/// predicate wins).
fn extract_substitutes(seq: &ProverSequent) -> HashMap<Predicate, Substitute> {
    let mut table = HashMap::new();
    for hyp in seq.visible_hyp_iter() {
        add_substitutes(&mut table, hyp, false, hyp);
    }
    let goal = seq.goal();
    if let PredicateKind::Associative {
        op: AssocPredOp::LOr,
        children,
    } = goal.kind()
    {
        for child in children {
            add_substitutes(&mut table, goal, true, child);
        }
    } else {
        add_substitutes(&mut table, goal, true, goal);
    }
    table
}

/// The top-down substitution pass over one predicate (the
/// inspector plus `rewriteSubFormula`): an outermost match is
/// replaced and its children are not visited; nothing else is
/// normalized. `origin` is the hypothesis being rewritten, or the
/// goal when `is_goal`.
struct Applier<'a> {
    table: &'a HashMap<Predicate, Substitute>,
    origin: &'a Predicate,
    is_goal: bool,
    /// Hypothesis origins used, in encounter order, deduplicated.
    used_hyps: Vec<Predicate>,
    used_goal: bool,
}

impl Applier<'_> {
    fn rewrite_pred(&mut self, pred: &Predicate) -> Option<Predicate> {
        if let Some(subst) = self.table.get(pred) {
            // The self-rewrite check compares object identities:
            // a hypothesis never matches another predicate object, so
            // only its own substitute (structural match) and, for the
            // goal, goal-derived substitutes are excluded.
            let self_rewrite = if self.is_goal {
                subst.from_goal
            } else {
                !subst.from_goal && subst.origin == *self.origin
            };
            if !self_rewrite {
                if subst.from_goal {
                    self.used_goal = true;
                } else if !self.used_hyps.contains(&subst.origin) {
                    self.used_hyps.push(subst.origin.clone());
                }
                return Some(subst.substitute.clone());
            }
        }
        let ff = pred.factory().clone();
        match pred.kind() {
            PredicateKind::Literal(_)
            | PredicateKind::PredicateVariable(_)
            | PredicateKind::Application { .. }
            | PredicateKind::Extended { .. } => None,
            PredicateKind::Not(child) => {
                self.rewrite_pred(child).map(|p| ff.not_predicate(p, None))
            }
            PredicateKind::Binary { op, left, right } => {
                let l = self.rewrite_pred(left);
                let r = self.rewrite_pred(right);
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
                let mut changed = false;
                let out: Vec<Predicate> = children
                    .iter()
                    .map(|c| match self.rewrite_pred(c) {
                        Some(c2) => {
                            changed = true;
                            c2
                        }
                        None => c.clone(),
                    })
                    .collect();
                changed.then(|| ff.associative_predicate(*op, out, None))
            }
            PredicateKind::Quantified {
                op,
                decls,
                pred: body,
            } => self
                .rewrite_pred(body)
                .map(|p| ff.quantified_predicate(*op, decls.clone(), p, None)),
            PredicateKind::Relational { op, left, right } => {
                let l = self.rewrite_expr(left);
                let r = self.rewrite_expr(right);
                (l.is_some() || r.is_some()).then(|| {
                    ff.relational_predicate(
                        *op,
                        l.unwrap_or_else(|| left.clone()),
                        r.unwrap_or_else(|| right.clone()),
                        None,
                    )
                })
            }
            PredicateKind::Simple(child) => self
                .rewrite_expr(child)
                .map(|e| ff.simple_predicate(e, None)),
            PredicateKind::Multiple(children) => {
                let mut changed = false;
                let out: Vec<Expression> = children
                    .iter()
                    .map(|c| match self.rewrite_expr(c) {
                        Some(c2) => {
                            changed = true;
                            c2
                        }
                        None => c.clone(),
                    })
                    .collect();
                changed.then(|| ff.multiple_predicate(out, None))
            }
        }
    }

    /// Predicates nested inside expressions (`bool(…)`, comprehension
    /// guards) are substitution sites too.
    fn rewrite_expr(&mut self, expr: &Expression) -> Option<Expression> {
        let ff = expr.factory().clone();
        match expr.kind() {
            ExpressionKind::Bool(pred) => {
                self.rewrite_pred(pred).map(|p| ff.bool_expression(p, None))
            }
            ExpressionKind::Binary { op, left, right } => {
                let l = self.rewrite_expr(left);
                let r = self.rewrite_expr(right);
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
                let mut changed = false;
                let out: Vec<Expression> = children
                    .iter()
                    .map(|c| match self.rewrite_expr(c) {
                        Some(c2) => {
                            changed = true;
                            c2
                        }
                        None => c.clone(),
                    })
                    .collect();
                changed.then(|| ff.associative_expression(*op, out, None))
            }
            ExpressionKind::Unary { op, child } => self
                .rewrite_expr(child)
                .map(|e| ff.unary_expression(*op, e, None)),
            ExpressionKind::SetExtension(members) => {
                let mut changed = false;
                let out: Vec<Expression> = members
                    .iter()
                    .map(|c| match self.rewrite_expr(c) {
                        Some(c2) => {
                            changed = true;
                            c2
                        }
                        None => c.clone(),
                    })
                    .collect();
                changed.then(|| ff.set_extension(out, None))
            }
            ExpressionKind::Quantified {
                op,
                decls,
                pred,
                expr: value,
                form,
            } => {
                let p = self.rewrite_pred(pred);
                let v = self.rewrite_expr(value);
                (p.is_some() || v.is_some()).then(|| {
                    ff.quantified_expression(
                        *op,
                        decls.clone(),
                        p.unwrap_or_else(|| pred.clone()),
                        v.unwrap_or_else(|| value.clone()),
                        None,
                        *form,
                    )
                })
            }
            _ => None,
        }
    }
}

/// `GenMPL4` (`genMPL4`) — generalized modus ponens, level 4.
pub struct GenMPL4;

impl Reasoner for GenMPL4 {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let table = extract_substitutes(seq);
        let goal = seq.goal();

        let mut goal_applier = Applier {
            table: &table,
            origin: goal,
            is_goal: true,
            used_hyps: Vec::new(),
            used_goal: false,
        };
        let rewritten_goal = goal_applier.rewrite_pred(goal);
        let needed_hyps = goal_applier.used_hyps;

        let mut is_goal_dependent = false;
        let mut hyp_actions: Vec<HypAction> = Vec::new();
        for hyp in seq.visible_hyp_iter() {
            let mut applier = Applier {
                table: &table,
                origin: hyp,
                is_goal: false,
                used_hyps: Vec::new(),
                used_goal: false,
            };
            let Some(rewritten) = applier.rewrite_pred(hyp) else {
                continue;
            };
            is_goal_dependent |= applier.used_goal;
            // `sourceHyps`: the origins in encounter order, then the
            // rewritten hypothesis itself.
            let mut sources = applier.used_hyps;
            if !sources.contains(hyp) {
                sources.push(hyp.clone());
            }
            hyp_actions.push(HypAction::Rewrite {
                hyps: sources,
                added_idents: Vec::new(),
                inferred: vec![rewritten],
                disappearing: vec![hyp.clone()],
            });
        }

        let rule = |goal: Option<Predicate>,
                    needed_hyps: Vec<Predicate>,
                    antecedent_goal: Option<Predicate>,
                    hyp_actions: Vec<HypAction>| Rule {
            reasoner: stored.rule.reasoner.clone(),
            goal,
            needed_hyps,
            confidence: Confidence::DISCHARGED_MAX,
            display: "generalized MP".into(),
            antecedents: vec![Antecedent {
                goal: antecedent_goal,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions,
            }],
        };
        if let Some(rewritten_goal) = rewritten_goal {
            Ok(rule(
                Some(goal.clone()),
                needed_hyps,
                Some(rewritten_goal),
                hyp_actions,
            ))
        } else if is_goal_dependent {
            if hyp_actions.is_empty() {
                return Err("failure computing re-writing".into());
            }
            Ok(rule(
                Some(goal.clone()),
                Vec::new(),
                Some(goal.clone()),
                hyp_actions,
            ))
        } else if !hyp_actions.is_empty() {
            Ok(rule(None, Vec::new(), None, hyp_actions))
        } else {
            Err("generalized MP no more applicable".into())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skeleton::StoredInput;
    use crate::test_util::{desc, env, pred};

    fn stored() -> StoredRule {
        StoredRule {
            rule: Rule {
                reasoner: desc("genMPL4"),
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
    fn hypothesis_occurrence_in_another_hypothesis_becomes_true() {
        let env = env(&[("x", "ℤ"), ("y", "ℤ"), ("z", "ℤ")]);
        let seq = sequent(&env, &["x>0", "x>0 ⇒ y>0"], "z>0");
        let rule = GenMPL4
            .replay(&seq, &stored(), &ReplayHints::default())
            .unwrap();
        // The goal is untouched and unused: a goal-independent rule.
        assert_eq!(rule.goal, None);
        assert_eq!(
            rule.antecedents[0].hyp_actions,
            vec![HypAction::Rewrite {
                hyps: vec![pred(&env, "x>0"), pred(&env, "x>0 ⇒ y>0")],
                added_idents: Vec::new(),
                inferred: vec![pred(&env, "⊤ ⇒ y>0")],
                disappearing: vec![pred(&env, "x>0 ⇒ y>0")],
            }]
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn hypothesis_rewrites_a_goal_disjunct() {
        let env = env(&[("x", "ℤ"), ("y", "ℤ")]);
        let seq = sequent(&env, &["x>0"], "x>0 ∨ y>0");
        let rule = GenMPL4
            .replay(&seq, &stored(), &ReplayHints::default())
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        assert_eq!(rule.needed_hyps, vec![pred(&env, "x>0")]);
        assert_eq!(
            rule.antecedents[0].goal.as_ref(),
            Some(&pred(&env, "⊤ ∨ y>0"))
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn goal_rewrites_a_hypothesis_negatively() {
        let env = env(&[("x", "ℤ"), ("y", "ℤ")]);
        let seq = sequent(&env, &["x>0 ⇒ y>0"], "x>0");
        let rule = GenMPL4
            .replay(&seq, &stored(), &ReplayHints::default())
            .unwrap();
        // Goal-dependent shape: the rule and its antecedent both keep
        // the unrewritten goal.
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        assert_eq!(rule.needed_hyps, Vec::<Predicate>::new());
        assert_eq!(rule.antecedents[0].goal.as_ref(), Some(seq.goal()));
        assert_eq!(
            rule.antecedents[0].hyp_actions,
            vec![HypAction::Rewrite {
                hyps: vec![pred(&env, "x>0 ⇒ y>0")],
                added_idents: Vec::new(),
                inferred: vec![pred(&env, "⊥ ⇒ y>0")],
                disappearing: vec![pred(&env, "x>0 ⇒ y>0")],
            }]
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn negated_hypothesis_substitutes_false() {
        let env = env(&[("x", "ℤ"), ("y", "ℤ")]);
        let seq = sequent(&env, &["¬x=0", "x=0 ∨ y>0"], "y>1");
        let rule = GenMPL4
            .replay(&seq, &stored(), &ReplayHints::default())
            .unwrap();
        assert_eq!(
            rule.antecedents[0].hyp_actions,
            vec![HypAction::Rewrite {
                hyps: vec![pred(&env, "¬x=0"), pred(&env, "x=0 ∨ y>0")],
                added_idents: Vec::new(),
                inferred: vec![pred(&env, "⊥ ∨ y>0")],
                disappearing: vec![pred(&env, "x=0 ∨ y>0")],
            }]
        );
    }

    #[test]
    fn fails_when_nothing_applies() {
        let env = env(&[("x", "ℤ")]);
        let seq = sequent(&env, &["x>0"], "x>1");
        let err = GenMPL4
            .replay(&seq, &stored(), &ReplayHints::default())
            .unwrap_err();
        assert_eq!(err, "generalized MP no more applicable");
    }
}
