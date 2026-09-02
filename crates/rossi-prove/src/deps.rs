//! Proof dependencies: what a proof needs from its sequent, and the
//! reuse predicate deciding whether a stored proof still applies.
//!
//! Dependencies are computed bottom-up over a proof tree; hypothesis
//! actions are processed in reverse order within each antecedent, and
//! a forward inference contributes only when it actually fired at
//! apply time *and* something above used what it inferred. The reuse
//! predicate is the whole of the status-update decision: matching
//! goal, present hypotheses, compatible free identifiers, fresh
//! introduced names, and only trusted reasoners.

use std::collections::BTreeSet;

use rossi::formula::{ExpressionKind, FormulaRef, Predicate};

use crate::hyp_action::HypAction;
use crate::registry::ReasonerDesc;
use crate::rule::Antecedent;
use crate::sequent::{ProverSequent, TypedIdent};
use crate::tree::ProofTreeNode;

/// What a proof needs from the sequent it is reused against.
#[derive(Debug, Clone)]
pub struct ProofDependencies {
    /// The goal the proof discharges; `None` when every rule goal in
    /// the proof is a wildcard, matching any goal.
    pub goal: Option<Predicate>,
    /// Hypotheses the proof needs present.
    pub used_hypotheses: Vec<Predicate>,
    /// Free identifiers, with their types, the proof relies on.
    pub used_free_idents: Vec<TypedIdent>,
    /// Names the proof introduces — they must be fresh at reuse time.
    pub introduced_free_idents: BTreeSet<String>,
    /// Every reasoner the proof steps through.
    pub used_reasoners: Vec<ReasonerDesc>,
}

impl ProofDependencies {
    /// Computes the dependencies of a (partially) built proof tree,
    /// bottom-up.
    pub fn from_tree(root: &ProofTreeNode) -> ProofDependencies {
        node_deps(root).finished()
    }

    /// Whether the proof records any dependency at all — a proof
    /// without dependencies is reusable against any sequent.
    pub fn has_deps(&self) -> bool {
        self.goal.is_some()
            || !self.used_hypotheses.is_empty()
            || !self.used_free_idents.is_empty()
            || !self.introduced_free_idents.is_empty()
            || !self.used_reasoners.is_empty()
    }

    /// Whether any used reasoner depends on context beyond its
    /// sequent, so reuse must re-check its stored rules.
    pub fn is_context_dependent(&self) -> bool {
        self.used_reasoners
            .iter()
            .any(ReasonerDesc::is_context_dependent)
    }
}

/// The reuse predicate — the decision behind the
/// `psBroken` flag: a stored proof applies to `seq` iff its recorded
/// goal matches (or is a wildcard), its used hypotheses are present,
/// its used free identifiers are bound with the same types, its
/// introduced names are fresh, and every reasoner it stepped through
/// is trusted. Context-dependent proofs are conservatively not
/// reusable (their datatype rules are re-run against the origin;
/// rossi does not replay those).
pub fn is_proof_reusable(deps: &ProofDependencies, seq: &ProverSequent) -> bool {
    explain_reuse_failure(deps, seq).is_none()
}

/// Explains why [`is_proof_reusable`] answers no — the first failing
/// check with the offending item, for harness triage.
pub fn explain_reuse_failure(deps: &ProofDependencies, seq: &ProverSequent) -> Option<String> {
    if !deps.has_deps() {
        return None;
    }
    if let Some(goal) = &deps.goal
        && goal != seq.goal()
    {
        return Some(format!("goal mismatch: proof needs {goal:?}"));
    }
    for hyp in &deps.used_hypotheses {
        if !seq.contains_hypothesis(hyp) {
            return Some(format!("missing hypothesis {hyp:?}"));
        }
    }
    for ident in &deps.used_free_idents {
        if seq.type_env().get(&ident.name) != Some(&ident.ty) {
            return Some(format!("identifier {} at {:?}", ident.name, ident.ty));
        }
    }
    for name in &deps.introduced_free_idents {
        if seq.type_env().contains(name) {
            return Some(format!("introduced name {name} is taken"));
        }
    }
    if let Some(desc) = deps.used_reasoners.iter().find(|desc| !desc.is_trusted()) {
        return Some(format!("untrusted reasoner {}", desc.id()));
    }
    if deps.is_context_dependent() {
        return Some("context-dependent proof".to_string());
    }
    None
}

/// The mutable accumulator, using order-preserving vectors with set
/// semantics so the finished dependencies are deterministic.
#[derive(Debug, Default)]
struct Builder {
    goal: Option<Predicate>,
    used_hypotheses: Vec<Predicate>,
    used_free_idents: Vec<TypedIdent>,
    introduced: BTreeSet<String>,
    used_reasoners: Vec<ReasonerDesc>,
}

impl Builder {
    fn finished(self) -> ProofDependencies {
        ProofDependencies {
            goal: self.goal,
            used_hypotheses: self.used_hypotheses,
            used_free_idents: self.used_free_idents,
            introduced_free_idents: self.introduced,
            used_reasoners: self.used_reasoners,
        }
    }

    fn add_hyp(&mut self, hyp: &Predicate) {
        if !self.used_hypotheses.contains(hyp) {
            self.used_hypotheses.push(hyp.clone());
        }
    }

    fn remove_hyp(&mut self, hyp: &Predicate) {
        self.used_hypotheses.retain(|used| used != hyp);
    }

    fn add_ident(&mut self, ident: TypedIdent) {
        if !self.used_free_idents.contains(&ident) {
            self.used_free_idents.push(ident);
        }
    }

    /// Adds every free identifier of `pred`, with its solved type.
    fn add_idents_of(&mut self, pred: &Predicate) {
        let mut found = Vec::new();
        pred.positions(&mut |node| {
            if let FormulaRef::Expr(expr) = node
                && let ExpressionKind::FreeIdentifier(name) = expr.kind()
                && let Some(ty) = expr.ty()
            {
                found.push(TypedIdent::new(name.clone(), ty.clone()));
            }
            false
        });
        for ident in found {
            self.add_ident(ident);
        }
    }

    fn add_reasoner(&mut self, desc: &ReasonerDesc) {
        if !self.used_reasoners.contains(desc) {
            self.used_reasoners.push(desc.clone());
        }
    }

    /// Merges another antecedent's contribution; the sub-builder's
    /// goal is handled separately by wildcard propagation.
    fn merge(&mut self, sub: Builder) {
        for hyp in sub.used_hypotheses {
            if !self.used_hypotheses.contains(&hyp) {
                self.used_hypotheses.push(hyp);
            }
        }
        for ident in sub.used_free_idents {
            self.add_ident(ident);
        }
        self.introduced.extend(sub.introduced);
        for desc in sub.used_reasoners {
            self.add_reasoner(&desc);
        }
    }
}

fn node_deps(node: &ProofTreeNode) -> Builder {
    let Some(rule) = node.rule() else {
        return Builder::default();
    };
    let mut deps = Builder::default();
    let mut dep_goal: Option<Predicate> = None;
    let goal_inst = rule.goal.is_none().then(|| node.sequent().goal().clone());

    for (antecedent, child) in rule.antecedents.iter().zip(node.children()) {
        let mut sub = node_deps(child);

        // Hypothesis actions are processed in REVERSE order, so a
        // forward inference feeding a later one is seen as used.
        for (action, fired) in fired_actions(antecedent, node.sequent(), goal_inst.as_ref())
            .iter()
            .rev()
        {
            process_action(action, *fired, &mut sub);
        }

        for hyp in &antecedent.added_hyps {
            sub.remove_hyp(hyp);
        }
        if let Some(goal) = &antecedent.goal {
            sub.add_idents_of(goal);
        }
        for hyp in &antecedent.added_hyps {
            sub.add_idents_of(hyp);
        }
        for ident in &antecedent.added_idents {
            sub.used_free_idents.retain(|used| used != ident);
            sub.introduced.insert(ident.name.clone());
        }

        // A wildcard antecedent under a wildcard rule goal propagates
        // the sub-proof's goal instantiation upward.
        if antecedent.goal.is_none()
            && let Some(goal) = sub.goal.take()
        {
            debug_assert!(dep_goal.as_ref().is_none_or(|existing| *existing == goal));
            dep_goal = Some(goal);
        }

        deps.merge(sub);
    }

    if rule.goal.is_some() {
        dep_goal = rule.goal.clone();
    }
    deps.goal = dep_goal;
    for hyp in &rule.needed_hyps {
        deps.add_hyp(hyp);
    }
    if let Some(goal) = deps.goal.clone() {
        deps.add_idents_of(&goal);
    }
    for hyp in &rule.needed_hyps.clone() {
        deps.add_idents_of(hyp);
    }
    deps.add_reasoner(&rule.reasoner);
    deps
}

/// Replays the antecedent's action chain against the sequent it was
/// applied to, recording per action whether its forward-inference part
/// changed the sequent — the `skipped` state recorded during
/// `perform` and consults during dependency processing.
fn fired_actions<'a>(
    antecedent: &'a Antecedent,
    seq: &ProverSequent,
    goal_inst: Option<&Predicate>,
) -> Vec<(&'a HypAction, bool)> {
    let new_goal = antecedent.goal.as_ref().or(goal_inst);
    let mut cur = match new_goal.and_then(|goal| {
        seq.modify(
            &antecedent.added_idents,
            &antecedent.added_hyps,
            &antecedent.unselected_added,
            Some(goal),
        )
    }) {
        Some(next) => next,
        // The rule cannot have applied here; treat every action as
        // skipped rather than panicking on a malformed tree.
        None => return antecedent.hyp_actions.iter().map(|a| (a, false)).collect(),
    };

    let mut out = Vec::with_capacity(antecedent.hyp_actions.len());
    for action in &antecedent.hyp_actions {
        let fired = match action {
            HypAction::ForwardInf { .. } | HypAction::Rewrite { .. } => {
                // `RewriteHypAction.perform` records `skipped` from the
                // whole action — the hiding step included — so an
                // inference that adds nothing but still hides a source
                // counts as fired.
                let next = action.perform(&cur);
                let fired = !ProverSequent::ptr_eq(&next, &cur);
                cur = next;
                fired
            }
            _ => {
                cur = action.perform(&cur);
                false
            }
        };
        out.push((action, fired));
    }
    out
}

/// One hypothesis action's dependency contribution. Selection actions
/// contribute nothing; a forward inference (or the inference part of a
/// rewrite) contributes only when it fired and its products are used
/// above: the inferred hypotheses are then traded for the sources.
fn process_action(action: &HypAction, fired: bool, deps: &mut Builder) {
    let (HypAction::ForwardInf {
        hyps,
        added_idents,
        inferred,
    }
    | HypAction::Rewrite {
        hyps,
        added_idents,
        inferred,
        ..
    }) = action
    else {
        return;
    };
    if !fired {
        return;
    }
    let used = inferred.iter().any(|p| deps.used_hypotheses.contains(p))
        || added_idents
            .iter()
            .any(|ident| deps.used_free_idents.contains(ident));
    if !used {
        return;
    }
    for inf in inferred {
        deps.remove_hyp(inf);
    }
    for hyp in hyps {
        deps.add_hyp(hyp);
    }
    for hyp in hyps {
        deps.add_idents_of(hyp);
    }
    for inf in inferred {
        deps.add_idents_of(inf);
    }
    for ident in added_idents {
        deps.used_free_idents.retain(|used| used != ident);
        deps.introduced.insert(ident.name.clone());
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::confidence::Confidence;
    use crate::rule::Rule;
    use crate::test_util::{desc, env, pred};
    use rossi::formula::Type;

    fn base() -> ProverSequent {
        let env = env(&[("x", "ℤ"), ("y", "ℤ")]);
        let h1 = pred(&env, "x=1");
        let h2 = pred(&env, "y=3");
        ProverSequent::new(env.clone(), [h1.clone(), h2], [], [h1], pred(&env, "x<2"))
    }

    fn rule(goal: Option<Predicate>, needed: Vec<Predicate>, antecedents: Vec<Antecedent>) -> Rule {
        Rule {
            reasoner: desc("hyp"),
            goal,
            needed_hyps: needed,
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents,
        }
    }

    fn plain_antecedent(goal: Option<Predicate>) -> Antecedent {
        Antecedent {
            goal,
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents: Vec::new(),
            hyp_actions: Vec::new(),
        }
    }

    fn ident(name: &str) -> TypedIdent {
        TypedIdent::new(name, Type::Int)
    }

    #[test]
    fn closing_rule_records_goal_hyps_idents_and_reasoner() {
        let seq = base();
        let env = seq.type_env().clone();
        let needed = pred(&env, "x=1");
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            Some(seq.goal().clone()),
            vec![needed.clone()],
            Vec::new()
        )));

        let deps = ProofDependencies::from_tree(&node);
        assert!(deps.has_deps());
        assert_eq!(deps.goal.as_ref(), Some(seq.goal()));
        assert_eq!(deps.used_hypotheses, vec![needed]);
        assert_eq!(deps.used_free_idents, vec![ident("x")]);
        assert!(deps.introduced_free_idents.is_empty());
        assert_eq!(deps.used_reasoners, vec![desc("hyp")]);
        assert!(!deps.is_context_dependent());
    }

    #[test]
    fn open_tree_has_no_dependencies_and_is_always_reusable() {
        let node = ProofTreeNode::open(base());
        let deps = ProofDependencies::from_tree(&node);
        assert!(!deps.has_deps());
        assert!(is_proof_reusable(&deps, &base()));
    }

    #[test]
    fn wildcard_goal_instantiation_propagates_upward() {
        let seq = base();
        // Root: wildcard rule with a wildcard antecedent; child closes
        // with an explicit goal.
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(None, Vec::new(), vec![plain_antecedent(None)])));
        assert!(node.children_mut()[0].apply_rule(rule(
            Some(seq.goal().clone()),
            Vec::new(),
            Vec::new()
        )));

        let deps = ProofDependencies::from_tree(&node);
        assert_eq!(deps.goal.as_ref(), Some(seq.goal()));
    }

    #[test]
    fn added_hypotheses_and_idents_are_discharged_by_the_antecedent() {
        let seq = base();
        let wide = env(&[("x", "ℤ"), ("y", "ℤ"), ("z", "ℤ")]);
        let added = pred(&wide, "z=4");
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            None,
            Vec::new(),
            vec![Antecedent {
                goal: None,
                added_hyps: vec![added.clone()],
                unselected_added: Vec::new(),
                added_idents: vec![ident("z")],
                hyp_actions: Vec::new(),
            }]
        )));
        // The child needs the added hypothesis.
        assert!(node.children_mut()[0].apply_rule(rule(None, vec![added], Vec::new())));

        let deps = ProofDependencies::from_tree(&node);
        // The added hypothesis is provided by the rule, not the sequent,
        // and the identifier it introduced is recorded as introduced.
        assert!(deps.used_hypotheses.is_empty());
        assert!(!deps.used_free_idents.contains(&ident("z")));
        assert!(deps.introduced_free_idents.contains("z"));

        // Reuse: fine against the base sequent, refused when `z` is
        // already taken.
        assert!(is_proof_reusable(&deps, &seq));
        let clash = ProverSequent::new(wide.clone(), [], [], [], pred(&wide, "x<2"));
        assert!(!is_proof_reusable(&deps, &clash));
    }

    #[test]
    fn used_forward_inference_trades_products_for_sources() {
        let seq = base();
        let env = seq.type_env().clone();
        let src = pred(&env, "x=1");
        let inf = pred(&env, "x+1=2");
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            None,
            Vec::new(),
            vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![HypAction::ForwardInf {
                    hyps: vec![src.clone()],
                    added_idents: Vec::new(),
                    inferred: vec![inf.clone()],
                }],
            }]
        )));
        assert!(node.children_mut()[0].apply_rule(rule(None, vec![inf.clone()], Vec::new())));

        let deps = ProofDependencies::from_tree(&node);
        assert!(deps.used_hypotheses.contains(&src));
        assert!(!deps.used_hypotheses.contains(&inf));
    }

    #[test]
    fn unused_forward_inference_contributes_nothing() {
        let seq = base();
        let env = seq.type_env().clone();
        let src = pred(&env, "x=1");
        let inf = pred(&env, "x+1=2");
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            None,
            Vec::new(),
            vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![HypAction::ForwardInf {
                    hyps: vec![src.clone()],
                    added_idents: Vec::new(),
                    inferred: vec![inf],
                }],
            }]
        )));
        // The child never uses the inferred hypothesis.
        assert!(node.children_mut()[0].apply_rule(rule(None, Vec::new(), Vec::new())));

        let deps = ProofDependencies::from_tree(&node);
        assert!(!deps.used_hypotheses.contains(&src));
    }

    #[test]
    fn reverse_processing_chains_forward_inferences() {
        let seq = base();
        let env = seq.type_env().clone();
        let a = pred(&env, "x=1");
        let b = pred(&env, "x+1=2");
        let c = pred(&env, "x+2=3");
        let fwd = |hyps: &Predicate, inf: &Predicate| HypAction::ForwardInf {
            hyps: vec![hyps.clone()],
            added_idents: Vec::new(),
            inferred: vec![inf.clone()],
        };
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            None,
            Vec::new(),
            vec![Antecedent {
                goal: None,
                added_hyps: Vec::new(),
                unselected_added: Vec::new(),
                added_idents: Vec::new(),
                hyp_actions: vec![fwd(&a, &b), fwd(&b, &c)],
            }]
        )));
        assert!(node.children_mut()[0].apply_rule(rule(None, vec![c.clone()], Vec::new())));

        let deps = ProofDependencies::from_tree(&node);
        // Needing c pulls in b (second inference), which pulls in a
        // (first inference) — only because actions process in reverse.
        assert!(deps.used_hypotheses.contains(&a));
        assert!(!deps.used_hypotheses.contains(&b));
        assert!(!deps.used_hypotheses.contains(&c));
    }

    #[test]
    fn reuse_predicate_rejections() {
        let seq = base();
        let env = seq.type_env().clone();
        let needed = pred(&env, "x=1");
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(rule(
            Some(seq.goal().clone()),
            vec![needed.clone()],
            Vec::new()
        )));
        let deps = ProofDependencies::from_tree(&node);
        assert!(is_proof_reusable(&deps, &seq));

        // Goal mismatch.
        let other_goal =
            ProverSequent::new(env.clone(), [needed.clone()], [], [], pred(&env, "x<3"));
        assert!(!is_proof_reusable(&deps, &other_goal));

        // Missing used hypothesis.
        let no_hyp = ProverSequent::new(env.clone(), [], [], [], seq.goal().clone());
        assert!(!is_proof_reusable(&deps, &no_hyp));

        // Same name at a different type.
        let retyped = env.to_builder();
        let mut retyped = retyped;
        retyped.insert("x", Type::Bool);
        let retyped = retyped.make_snapshot();
        let clashing = ProverSequent::new(
            retyped.clone(),
            [pred(&retyped, "x=TRUE")],
            [],
            [],
            pred(&retyped, "x=TRUE"),
        );
        assert!(!is_proof_reusable(&deps, &clashing));
    }

    #[test]
    fn untrusted_or_context_dependent_reasoners_defeat_reuse() {
        let seq = base();
        let close = |reasoner: &str| Rule {
            reasoner: crate::registry::resolve(reasoner),
            goal: None,
            needed_hyps: Vec::new(),
            confidence: Confidence::DISCHARGED_MAX,
            display: "test".into(),
            antecedents: Vec::new(),
        };

        // A stale version is untrusted.
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(close("org.eventb.core.seqprover.eq")));
        assert!(!is_proof_reusable(
            &ProofDependencies::from_tree(&node),
            &seq
        ));

        // A context-dependent reasoner is conservatively not reusable.
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(close("org.eventb.core.seqprover.dtDistinctCase")));
        let deps = ProofDependencies::from_tree(&node);
        assert!(deps.is_context_dependent());
        assert!(!is_proof_reusable(&deps, &seq));

        // A trusted oracle is fine.
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(node.apply_rule(close("org.eventb.smt.core.externalSMT")));
        assert!(is_proof_reusable(
            &ProofDependencies::from_tree(&node),
            &seq
        ));
    }
}
