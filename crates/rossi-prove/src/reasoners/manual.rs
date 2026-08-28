//! The manual rewriting reasoners: a stored position — and, for a
//! hypothesis rewrite, the hypothesis recovered from the recorded
//! rule — locate one subformula, which a
//! reasoner-specific rewrite replaces.

use std::str::FromStr;

use rossi::formula::position::Position;
use rossi::formula::tag::{AssocExprOp, AssocPredOp, LiteralPredOp, RelationalOp};
use rossi::formula::{Expression, ExpressionKind, Predicate, PredicateKind, Type};

use crate::builder::{Reasoner, ReplayHints};
use crate::confidence::Confidence;
use crate::hyp_action::HypAction;
use crate::rule::{Antecedent, Rule};
use crate::sequent::ProverSequent;
use crate::skeleton::StoredRule;

use super::{break_possible_conjunct, display_pred};

/// Input recovery: the position comes from
/// the `pos` input string; a rule with a goal is a goal rewrite,
/// otherwise the hypothesis is the first predicate of the first
/// hypothesis action.
fn stored_input(stored: &StoredRule) -> Result<(Option<Predicate>, Position), String> {
    let pos = stored
        .input
        .strings
        .get("pos")
        .ok_or("Missing position input")?;
    let position = Position::from_str(pos).map_err(|_| format!("Bad position: {pos}"))?;
    if stored.rule.goal.is_some() {
        return Ok((None, position));
    }
    let antecedent = stored
        .rule
        .antecedents
        .first()
        .ok_or("Expected exactly one antecedent!")?;
    let action = antecedent
        .hyp_actions
        .first()
        .ok_or("Expected at least one hyp action!")?;
    let hyp = match action {
        HypAction::Rewrite { hyps, .. }
        | HypAction::ForwardInf { hyps, .. }
        | HypAction::Hide(hyps) => hyps.first(),
        _ => None,
    }
    .ok_or("Expected first hyp action to be a forward or hide hyp action!")?;
    Ok((Some(hyp.clone()), position))
}

/// `getNeededHyps`: the hypotheses justifying a rewrite of the given
/// predicate at the given position, or `None` for inapplicability.
type NeededHyps<'a> = &'a dyn Fn(&ProverSequent, &Predicate, &Position) -> Option<Vec<Predicate>>;

/// Rewrite the goal — one antecedent
/// per conjunct of the result — or one hypothesis, whose rewritten
/// conjuncts (minus `⊤`) are inferred and selected, the original
/// hidden.
pub(crate) fn manual_rewrite_rule(
    seq: &ProverSequent,
    stored: &StoredRule,
    rewrite: &dyn Fn(&Predicate, &Position) -> Option<Predicate>,
    needed: NeededHyps<'_>,
    display: &dyn Fn(Option<&Predicate>, &Position) -> String,
) -> Result<Rule, String> {
    let (hyp, position) = stored_input(stored)?;
    let reasoner_id = stored.rule.reasoner.id().to_string();
    match hyp {
        None => {
            let goal = seq.goal();
            let failure = || {
                format!(
                    "Rewriter {reasoner_id} is inapplicable for goal {} at position {position}",
                    display_pred(goal)
                )
            };
            let needed_hyps = needed(seq, goal, &position).ok_or_else(failure)?;
            let new_goal = rewrite(goal, &position).ok_or_else(failure)?;
            let antecedents = break_possible_conjunct(&new_goal)
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
                goal: Some(goal.clone()),
                needed_hyps,
                confidence: Confidence::DISCHARGED_MAX,
                display: display(None, &position),
                antecedents,
            })
        }
        Some(hyp) => {
            if !seq.contains_hypothesis(&hyp) {
                return Err(format!("Nonexistent hypothesis: {}", display_pred(&hyp)));
            }
            let failure = || {
                format!(
                    "Rewriter {reasoner_id} is inapplicable for hypothesis {} at position {position}",
                    display_pred(&hyp)
                )
            };
            let needed_hyps = needed(seq, &hyp, &position).ok_or_else(failure)?;
            let inferred_hyp = rewrite(&hyp, &position).ok_or_else(failure)?;
            let mut inferred = break_possible_conjunct(&inferred_hyp);
            inferred.retain(|pred| {
                !matches!(pred.kind(), PredicateKind::Literal(LiteralPredOp::BTrue))
            });
            let hyp_actions = if inferred.is_empty() {
                vec![HypAction::Hide(vec![hyp.clone()])]
            } else {
                vec![
                    HypAction::Rewrite {
                        hyps: vec![hyp.clone()],
                        added_idents: Vec::new(),
                        inferred: inferred.clone(),
                        disappearing: vec![hyp.clone()],
                    },
                    HypAction::Select(inferred),
                ]
            };
            Ok(Rule {
                reasoner: stored.rule.reasoner.clone(),
                goal: None,
                needed_hyps,
                confidence: Confidence::DISCHARGED_MAX,
                display: display(Some(&hyp), &position),
                antecedents: vec![Antecedent {
                    goal: None,
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions,
                }],
            })
        }
    }
}

/// Membership that simplifies against literal
/// sets.
fn smart_in(member: &Expression, set: &Expression) -> Predicate {
    let ff = member.factory();
    match set.kind() {
        ExpressionKind::SetExtension(members) if members.len() == 1 => ff.relational_predicate(
            RelationalOp::Equal,
            member.clone(),
            members[0].clone(),
            None,
        ),
        ExpressionKind::Atomic(rossi::formula::tag::AtomicOp::EmptySet) => {
            ff.literal_predicate(LiteralPredOp::BFalse, None)
        }
        _ if set.is_type_expression() => ff.literal_predicate(LiteralPredOp::BTrue, None),
        _ => ff.relational_predicate(RelationalOp::In, member.clone(), set.clone(), None),
    }
}

/// Negation with double-negation unwrapping.
fn smart_not(pred: &Predicate) -> Predicate {
    match pred.kind() {
        PredicateKind::Not(child) => child.clone(),
        _ => pred.factory().not_predicate(pred.clone(), None),
    }
}

/// An associative node in the shape its print→parse round-trip
/// yields: a same-operator first child prints without parentheses,
/// so its whole left spine merges into the run, while later
/// same-operator children keep their parentheses and stay nested.
/// Stored rules only exist post-round-trip, so produced formulas
/// must take this shape.
fn assoc_as_parsed(op: AssocExprOp, mut children: Vec<Expression>) -> Expression {
    let ff = children[0].factory().clone();
    while let Some(first) = children.first().cloned() {
        let ExpressionKind::Associative {
            op: inner,
            children: nested,
        } = first.kind()
        else {
            break;
        };
        if *inner != op {
            break;
        }
        let mut merged = nested.clone();
        merged.extend(children.drain(1..));
        children = merged;
    }
    ff.associative_expression(op, children, None)
}

/// Disjointness: a singleton side becomes a negated
/// membership, otherwise the intersection is empty.
fn smart_disjoint(left: &Expression, right: &Expression) -> Predicate {
    let ff = left.factory();
    let singleton = |e: &Expression| match e.kind() {
        ExpressionKind::SetExtension(members) if members.len() == 1 => Some(members[0].clone()),
        _ => None,
    };
    if let Some(member) = singleton(left) {
        return smart_not(&smart_in(&member, right));
    }
    if let Some(member) = singleton(right) {
        return smart_not(&smart_in(&member, left));
    }
    let empty = ff.atomic_expression(
        rossi::formula::tag::AtomicOp::EmptySet,
        None,
        left.ty().cloned(),
    );
    let inter = assoc_as_parsed(AssocExprOp::BInter, vec![left.clone(), right.clone()]);
    ff.relational_predicate(RelationalOp::Equal, inter, empty, None)
}

/// Union: set extensions merge into one (first
/// occurrences kept), anything else is a plain union.
fn smart_union(ty: Option<&Type>, components: &[Expression]) -> Expression {
    let ff = components
        .first()
        .map(|c| c.factory().clone())
        .expect("caller handles the empty case");
    match components {
        [single] => single.clone(),
        _ => {
            let mut members: Vec<Expression> = Vec::new();
            for component in components {
                let ExpressionKind::SetExtension(list) = component.kind() else {
                    let _ = ty;
                    return assoc_as_parsed(AssocExprOp::BUnion, components.to_vec());
                };
                for member in list {
                    if !members.contains(member) {
                        members.push(member.clone());
                    }
                }
            }
            ff.set_extension(members, None)
        }
    }
}

/// Partition expansion: `partition(S, s1, …, sn)` becomes
/// `S = s1 ∪ … ∪ sn` plus pairwise disjointness.
fn expand_partition(pred: &Predicate) -> Option<Predicate> {
    let PredicateKind::Multiple(children) = pred.kind() else {
        return None;
    };
    let ff = pred.factory();
    let (set, components) = children.split_first()?;
    let union = if components.is_empty() {
        ff.atomic_expression(
            rossi::formula::tag::AtomicOp::EmptySet,
            None,
            set.ty().cloned(),
        )
    } else {
        smart_union(set.ty(), components)
    };
    let mut conjuncts =
        vec![ff.relational_predicate(RelationalOp::Equal, set.clone(), union, None)];
    for (i, left) in components.iter().enumerate() {
        for right in &components[i + 1..] {
            conjuncts.push(smart_disjoint(left, right));
        }
    }
    Some(match conjuncts.len() {
        1 => conjuncts.into_iter().next().unwrap(),
        _ => ff.associative_predicate(AssocPredOp::LAnd, conjuncts, None),
    })
}

/// `PartitionRewrites` (`partitionRewrites`) — expands one
/// `partition(…)` occurrence at the stored position.
pub struct PartitionRewrites;

impl Reasoner for PartitionRewrites {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let rewrite = |pred: &Predicate, position: &Position| -> Option<Predicate> {
            let sub = pred.sub_formula(position)?;
            let rossi::formula::position::FormulaRef::Pred(sub) = sub else {
                return None;
            };
            let expanded = expand_partition(sub)?;
            pred.rewrite_sub_formula(
                position,
                rossi::formula::position::FormulaRef::Pred(&expanded),
            )
            .ok()
        };
        let display = |hyp: Option<&Predicate>, position: &Position| match hyp {
            None => "Partition rewrites in goal".to_string(),
            Some(hyp) => format!(
                "Partition rewrites in hyp ({})",
                hyp.sub_formula(position)
                    .and_then(|sub| match sub {
                        rossi::formula::position::FormulaRef::Pred(p) => Some(display_pred(p)),
                        _ => None,
                    })
                    .unwrap_or_default()
            ),
        };
        manual_rewrite_rule(seq, stored, &rewrite, &|_, _, _| Some(Vec::new()), &display)
    }
}

/// The function under a simplifiable restricted application:
/// `((A ⩤ f)(…)`, `(A ◁ f)(…)`, `(f ⩥ A)(…)`, `(f ▷ A)(…)`,
/// `(f ∖ A)(…)` — the simplifiable function image.
fn fun_img_function(pred: &Predicate, position: &Position) -> Option<Expression> {
    use rossi::formula::tag::BinaryExprOp;
    let rossi::formula::position::FormulaRef::Expr(sub) = pred.sub_formula(position)? else {
        return None;
    };
    let ExpressionKind::Binary {
        op: BinaryExprOp::FunImage,
        left,
        ..
    } = sub.kind()
    else {
        return None;
    };
    match left.kind() {
        ExpressionKind::Binary {
            op: BinaryExprOp::DomSub | BinaryExprOp::DomRes,
            right: fun,
            ..
        } => Some(fun.clone()),
        ExpressionKind::Binary {
            op: BinaryExprOp::RanSub | BinaryExprOp::RanRes | BinaryExprOp::SetMinus,
            left: fun,
            ..
        } => Some(fun.clone()),
        _ => None,
    }
}

/// Whether `hyp` types `fun` as a function of any kind —
/// the functional-predicate test.
fn is_fun_pred(hyp: &Predicate, fun: &Expression) -> bool {
    use rossi::formula::tag::BinaryExprOp;
    let PredicateKind::Relational {
        op: RelationalOp::In,
        left,
        right,
    } = hyp.kind()
    else {
        return false;
    };
    matches!(
        right.kind(),
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
    ) && left == fun
}

/// `FunImgSimplifies` (`funImgSimplifies`, version 0) — simplifies a
/// domain- or range-restricted function application to the bare
/// function, needing a hypothesis typing it as a function.
pub struct FunImgSimplifies;

impl Reasoner for FunImgSimplifies {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        let rewrite = |pred: &Predicate, position: &Position| -> Option<Predicate> {
            use rossi::formula::tag::BinaryExprOp;
            let fun = fun_img_function(pred, position)?;
            let rossi::formula::position::FormulaRef::Expr(sub) = pred.sub_formula(position)?
            else {
                return None;
            };
            let ExpressionKind::Binary {
                op: BinaryExprOp::FunImage,
                right: arg,
                ..
            } = sub.kind()
            else {
                return None;
            };
            let replacement =
                pred.factory()
                    .binary_expression(BinaryExprOp::FunImage, fun, arg.clone(), None);
            pred.rewrite_sub_formula(
                position,
                rossi::formula::position::FormulaRef::Expr(&replacement),
            )
            .ok()
        };
        let needed = |seq: &ProverSequent,
                      pred: &Predicate,
                      position: &Position|
         -> Option<Vec<Predicate>> {
            let fun = fun_img_function(pred, position)?;
            let hyp = seq.visible_hyp_iter().find(|hyp| is_fun_pred(hyp, &fun))?;
            Some(vec![hyp.clone()])
        };
        let display = |hyp: Option<&Predicate>, _: &Position| match hyp {
            None => "Functional image simplification in goal".to_string(),
            Some(_) => "Functional image simplification in hyp".to_string(),
        };
        manual_rewrite_rule(seq, stored, &rewrite, &needed, &display)
    }
}

/// Total-domain rewriting (`totalDom`, version 2) — replaces `dom(f)` by
/// a substitute justified by a visible totality hypothesis
/// `f ∈ A <total arrow> B`.
pub struct TotalDom;

impl Reasoner for TotalDom {
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        _hints: &ReplayHints,
    ) -> Result<Rule, String> {
        use rossi::formula::tag::BinaryExprOp;
        // The substitute expression from the `subst` input.
        let substitute = stored
            .input
            .exprs
            .get("subst")
            .and_then(|list| match list.as_slice() {
                [Some(expr)] => Some(expr.clone()),
                _ => None,
            })
            .ok_or("Expected exactly one substitute!")?;
        let (hyp, position) = stored_input(stored)?;

        let to_rewrite = match &hyp {
            None => seq.goal(),
            Some(hyp) => {
                if !seq.contains_hypothesis(hyp) {
                    return Err(format!("Nonexistent hypothesis: {}", display_pred(hyp)));
                }
                hyp
            }
        };
        let failure = || {
            format!(
                "Rewriter {} is inapplicable for{} {} at position {position} with parameters {}",
                stored.rule.reasoner.id(),
                if hyp.is_none() {
                    " goal"
                } else {
                    " hypothesis"
                },
                display_pred(to_rewrite),
                super::display_expr(&substitute),
            )
        };

        // `TotalDomSubstitutions`: f ∈ A <total arrow> B gives dom(f) = A.
        let function = match pred_sub_expr(to_rewrite, &position) {
            Some(sub) => match sub.kind() {
                ExpressionKind::Unary {
                    op: rossi::formula::tag::UnaryExprOp::KDom,
                    child,
                } => child.clone(),
                _ => return Err(failure()),
            },
            None => return Err(failure()),
        };
        let mut needed_hyp = None;
        for candidate in seq.visible_hyp_iter() {
            let PredicateKind::Relational {
                op: RelationalOp::In,
                left,
                right,
            } = candidate.kind()
            else {
                continue;
            };
            let ExpressionKind::Binary {
                op:
                    BinaryExprOp::TFun
                    | BinaryExprOp::TInj
                    | BinaryExprOp::TSur
                    | BinaryExprOp::TBij
                    | BinaryExprOp::TRel
                    | BinaryExprOp::STRel,
                left: domain,
                ..
            } = right.kind()
            else {
                continue;
            };
            if left == &function && domain == &substitute {
                // A later hypothesis overwrites (map semantics).
                needed_hyp = Some(candidate.clone());
            }
        }
        let needed_hyp = needed_hyp.ok_or_else(failure)?;
        let rewritten = to_rewrite
            .rewrite_sub_formula(
                &position,
                rossi::formula::position::FormulaRef::Expr(&substitute),
            )
            .map_err(|_| failure())?;

        let display_sub = |hyp: &Predicate| {
            format!(
                "total function dom substitution in hyp ({})",
                pred_sub_expr(hyp, &position)
                    .map(|e| super::display_expr(&e))
                    .unwrap_or_default()
            )
        };
        match hyp {
            None => Ok(Rule {
                reasoner: stored.rule.reasoner.clone(),
                goal: Some(seq.goal().clone()),
                needed_hyps: vec![needed_hyp],
                confidence: Confidence::DISCHARGED_MAX,
                display: "total function dom substitution in goal".into(),
                antecedents: vec![Antecedent {
                    goal: Some(rewritten),
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions: Vec::new(),
                }],
            }),
            Some(hyp) => Ok(Rule {
                reasoner: stored.rule.reasoner.clone(),
                goal: None,
                needed_hyps: vec![needed_hyp],
                confidence: Confidence::DISCHARGED_MAX,
                display: display_sub(&hyp),
                antecedents: vec![Antecedent {
                    goal: None,
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions: vec![
                        HypAction::Rewrite {
                            hyps: vec![hyp.clone()],
                            added_idents: Vec::new(),
                            inferred: vec![rewritten.clone()],
                            disappearing: vec![hyp.clone()],
                        },
                        HypAction::Select(vec![rewritten]),
                    ],
                }],
            }),
        }
    }
}

/// The expression at `position` inside `pred`, if any.
fn pred_sub_expr(pred: &Predicate, position: &Position) -> Option<Expression> {
    match pred.sub_formula(position)? {
        rossi::formula::position::FormulaRef::Expr(e) => Some(e.clone()),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skeleton::StoredInput;
    use crate::test_util::{desc, env, pred};

    fn stored(goal: Option<Predicate>, hyp: Option<Predicate>, pos: &str) -> StoredRule {
        let antecedents = match &hyp {
            Some(hyp) => vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![HypAction::Rewrite {
                    hyps: vec![hyp.clone()],
                    added_idents: Vec::new(),
                    inferred: Vec::new(),
                    disappearing: vec![hyp.clone()],
                }],
            }],
            None => Vec::new(),
        };
        let mut input = StoredInput::default();
        input.strings.insert("pos".into(), pos.into());
        StoredRule {
            rule: Rule {
                reasoner: desc("partitionRewrites"),
                goal,
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: String::new(),
                antecedents,
            },
            input,
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
    fn goal_partition_expands_into_one_antecedent_per_conjunct() {
        let env = env(&[("S", "ℙ(ℤ)"), ("A", "ℙ(ℤ)"), ("B", "ℙ(ℤ)")]);
        let seq = sequent(&env, &[], "partition(S, A, B)");
        let rule = PartitionRewrites
            .replay(
                &seq,
                &stored(Some(pred(&env, "partition(S, A, B)")), None, ""),
                &ReplayHints::default(),
            )
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        let goals: Vec<Option<Predicate>> =
            rule.antecedents.iter().map(|a| a.goal.clone()).collect();
        assert_eq!(
            goals,
            vec![Some(pred(&env, "S = A ∪ B")), Some(pred(&env, "A ∩ B = ∅")),]
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn hypothesis_partition_with_singletons_uses_memberships() {
        let env = env(&[("S", "ℙ(ℤ)"), ("x", "ℤ"), ("y", "ℤ"), ("B", "ℙ(ℤ)")]);
        let hyp = pred(&env, "partition(S, {x}, {y}, B)");
        let seq = sequent(&env, &["partition(S, {x}, {y}, B)"], "⊥");
        let rule = PartitionRewrites
            .replay(
                &seq,
                &stored(None, Some(hyp.clone()), ""),
                &ReplayHints::default(),
            )
            .unwrap();
        assert_eq!(rule.goal, None);
        let expected = vec![
            pred(&env, "S = {x} ∪ {y} ∪ B"),
            pred(&env, "¬ x = y"),
            pred(&env, "¬ x ∈ B"),
            pred(&env, "¬ y ∈ B"),
        ];
        assert_eq!(
            rule.antecedents[0].hyp_actions,
            vec![
                HypAction::Rewrite {
                    hyps: vec![hyp.clone()],
                    added_idents: Vec::new(),
                    inferred: expected.clone(),
                    disappearing: vec![hyp.clone()],
                },
                HypAction::Select(expected),
            ]
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn nested_partition_position_is_honoured() {
        let env = env(&[("S", "ℙ(ℤ)"), ("A", "ℙ(ℤ)")]);
        // partition at child 1 of the implication.
        let seq = sequent(&env, &[], "S = A ⇒ partition(S, A)");
        let rule = PartitionRewrites
            .replay(
                &seq,
                &stored(Some(seq.goal().clone()), None, "1"),
                &ReplayHints::default(),
            )
            .unwrap();
        assert_eq!(
            rule.antecedents[0].goal.as_ref(),
            Some(&pred(&env, "S = A ⇒ S = A"))
        );
    }

    #[test]
    fn fails_at_a_non_partition_position() {
        let env = env(&[("S", "ℙ(ℤ)"), ("A", "ℙ(ℤ)")]);
        let seq = sequent(&env, &[], "S = A");
        let err = PartitionRewrites
            .replay(
                &seq,
                &stored(Some(seq.goal().clone()), None, ""),
                &ReplayHints::default(),
            )
            .unwrap_err();
        assert!(err.contains("inapplicable for goal"), "{err}");
    }
}

#[cfg(test)]
mod batch30_tests {
    use super::*;
    use crate::skeleton::StoredInput;
    use crate::test_util::{desc, env, pred};

    fn sequent(
        env: &rossi::formula::SealedTypeEnvironment,
        hyps: &[&str],
        goal: &str,
    ) -> ProverSequent {
        let hyps: Vec<Predicate> = hyps.iter().map(|s| pred(env, s)).collect();
        ProverSequent::new(env.clone(), hyps.clone(), [], hyps, pred(env, goal))
    }

    fn expr_of(env: &rossi::formula::SealedTypeEnvironment, source: &str) -> Expression {
        match pred(env, &format!("{source} = {source}")).kind() {
            PredicateKind::Relational { left, .. } => left.clone(),
            _ => unreachable!("an equality was parsed"),
        }
    }

    fn stored_goal(short: &str, goal: Predicate, pos: &str) -> StoredRule {
        let mut input = StoredInput::default();
        input.strings.insert("pos".into(), pos.into());
        StoredRule {
            rule: Rule {
                reasoner: desc(short),
                goal: Some(goal),
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: String::new(),
                antecedents: Vec::new(),
            },
            input,
        }
    }

    #[test]
    fn total_dom_substitutes_in_the_goal() {
        let env = env(&[("f", "ℙ(ℤ×ℤ)"), ("A", "ℙ(ℤ)"), ("B", "ℙ(ℤ)"), ("x", "ℤ")]);
        let seq = sequent(&env, &["f ∈ A → B"], "x ∈ dom(f)");
        let mut stored = stored_goal("totalDom:2", seq.goal().clone(), "1");
        stored
            .input
            .exprs
            .insert("subst".into(), vec![Some(expr_of(&env, "A"))]);
        let rule = TotalDom
            .replay(&seq, &stored, &ReplayHints::default())
            .unwrap();
        assert_eq!(rule.goal.as_ref(), Some(seq.goal()));
        assert_eq!(rule.needed_hyps, vec![pred(&env, "f ∈ A → B")]);
        assert_eq!(
            rule.antecedents[0].goal.as_ref(),
            Some(&pred(&env, "x ∈ A"))
        );
        assert!(rule.apply(&seq).is_some());
    }

    #[test]
    fn total_dom_fails_without_a_totality_hypothesis() {
        let env = env(&[("f", "ℙ(ℤ×ℤ)"), ("A", "ℙ(ℤ)"), ("B", "ℙ(ℤ)"), ("x", "ℤ")]);
        let seq = sequent(&env, &["f ∈ A ⇸ B"], "x ∈ dom(f)");
        let mut stored = stored_goal("totalDom:2", seq.goal().clone(), "1");
        stored
            .input
            .exprs
            .insert("subst".into(), vec![Some(expr_of(&env, "A"))]);
        let err = TotalDom
            .replay(&seq, &stored, &ReplayHints::default())
            .unwrap_err();
        assert!(err.contains("is inapplicable for goal"), "{err}");
    }

    #[test]
    fn fun_img_simplifies_strips_the_restriction() {
        let env = env(&[
            ("f", "ℙ(ℤ×ℤ)"),
            ("A", "ℙ(ℤ)"),
            ("B", "ℙ(ℤ)"),
            ("C", "ℙ(ℤ)"),
            ("x", "ℤ"),
            ("y", "ℤ"),
        ]);
        let seq = sequent(&env, &["f ∈ A ⇸ B"], "(C ◁ f)(x) = y");
        let stored = stored_goal("funImgSimplifies:0", seq.goal().clone(), "0");
        let rule = FunImgSimplifies
            .replay(&seq, &stored, &ReplayHints::default())
            .unwrap();
        assert_eq!(rule.needed_hyps, vec![pred(&env, "f ∈ A ⇸ B")]);
        assert_eq!(
            rule.antecedents[0].goal.as_ref(),
            Some(&pred(&env, "f(x) = y"))
        );
        assert!(rule.apply(&seq).is_some());
    }
}
