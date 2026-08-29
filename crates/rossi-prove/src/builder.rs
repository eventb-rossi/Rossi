//! The proof builder: reconstructing proof trees from stored skeletons.
//!
//! Three modes. *Reuse* applies the recorded rules structurally,
//! never invoking a reasoner. *Replay* re-runs each reasoner on its
//! recorded input and ignores
//! the recorded rules entirely — the re-validation mode. *Rebuild* is
//! the workhorse: reuse first, replay on failure with replay hints
//! renaming introduced identifiers, a bypass for rules that would do
//! nothing, and a downgrade keeping the structure of steps that can
//! neither be reused nor replayed at uncertain confidence.
//! Dependency-guided subtree reattachment on arity mismatch is
//! deliberately absent; those rebuilds report incomplete instead.

use std::collections::HashMap;

use rossi::formula::{Expression, Predicate};

use crate::confidence::Confidence;
use crate::registry::ReasonerDesc;
use crate::rule::{Antecedent, Rule};
use crate::sequent::ProverSequent;
use crate::skeleton::{Skeleton, StoredRule};
use crate::tree::ProofTreeNode;

/// A replayable reasoner implementation: re-runs the reasoner on the
/// stored input against a sequent, producing a fresh rule. The stored
/// rule is available for reasoners that recover their input from it,
/// but its antecedents must not simply be echoed — replay exists to
/// re-derive them.
pub trait Reasoner: Sync {
    /// Produces the rule for `seq`, or a failure message.
    fn replay(
        &self,
        seq: &ProverSequent,
        stored: &StoredRule,
        hints: &ReplayHints,
    ) -> Result<Rule, String>;
}

/// Resolves reasoner descriptors to implementations.
pub trait ReasonerProvider {
    /// The implementation for `desc`, when one exists and is trusted
    /// to re-run at the stored version.
    fn implementation(&self, desc: &ReasonerDesc) -> Option<&dyn Reasoner>;
}

/// The registry-backed provider: serves the implemented reasoners from
/// [`crate::reasoners`], for trusted descriptors only.
pub struct RegistryProvider;

impl ReasonerProvider for RegistryProvider {
    fn implementation(&self, desc: &ReasonerDesc) -> Option<&dyn Reasoner> {
        crate::reasoners::implementation(desc)
    }
}

/// Identifier renamings that let a replayed proof survive the renaming
/// of introduced identifiers: when a replayed
/// rule introduces the same identifiers under new names (same types),
/// the old names are substituted in the sub-proof's inputs.
#[derive(Debug, Clone, Default)]
pub struct ReplayHints {
    renames: HashMap<String, (String, rossi::formula::Type)>,
}

impl ReplayHints {
    /// Whether no renaming is recorded.
    pub fn is_empty(&self) -> bool {
        self.renames.is_empty()
    }

    /// Records the renamings between a stored antecedent and the one a
    /// replayed rule actually produced: pairwise added identifiers
    /// whose names differ at the same type.
    pub fn add_hints(&mut self, old: &Antecedent, current: &Antecedent) {
        for (old_ident, new_ident) in old.added_idents.iter().zip(&current.added_idents) {
            if old_ident.name != new_ident.name && old_ident.ty == new_ident.ty {
                self.renames.insert(
                    old_ident.name.clone(),
                    (new_ident.name.clone(), new_ident.ty.clone()),
                );
            }
        }
    }

    /// The predicate with every hinted name substituted.
    pub fn apply_pred(&self, pred: &Predicate) -> Predicate {
        if self.renames.is_empty() {
            return pred.clone();
        }
        pred.substitute_free_idents(&self.substitution(pred.factory()))
    }

    /// The expression with every hinted name substituted.
    pub fn apply_expr(&self, expr: &Expression) -> Expression {
        if self.renames.is_empty() {
            return expr.clone();
        }
        expr.substitute_free_idents(&self.substitution(expr.factory()))
    }

    fn substitution(&self, ff: &rossi::formula::FormulaFactory) -> HashMap<String, Expression> {
        self.renames
            .iter()
            .map(|(old, (new, ty))| (old.clone(), ff.free_identifier(new, None, Some(ty.clone()))))
            .collect()
    }
}

/// Whether a stored rule may be applied without re-running its
/// reasoner: the reasoner must be
/// trusted, and context-dependent rules (which are re-checked against
/// their origin) are not reusable here.
fn is_rule_reusable(rule: &Rule) -> bool {
    rule.reasoner.is_trusted() && !rule.reasoner.is_context_dependent()
}

/// Reconstructs the proof under `node` by applying the skeleton's
/// recorded rules — no reasoner runs. True iff every skeleton node was
/// applied.
pub fn reuse(node: &mut ProofTreeNode, skel: &Skeleton) -> bool {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        let Some(stored) = &skel.rule else {
            return true;
        };
        if !is_rule_reusable(&stored.rule) {
            return false;
        }
        if !node.apply_rule(stored.rule.clone()) {
            return false;
        }
        if node.children().len() != skel.children.len() {
            return false;
        }
        let mut complete = true;
        for (child, skel_child) in node.children_mut().iter_mut().zip(&skel.children) {
            complete &= reuse(child, skel_child);
        }
        complete
    })
}

/// Reconstructs the proof under `node` by re-running every reasoner on
/// its recorded input, ignoring the recorded rules — the re-validation
/// mode. True iff every skeleton node was replayed and applied.
pub fn replay(node: &mut ProofTreeNode, skel: &Skeleton, provider: &dyn ReasonerProvider) -> bool {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        let Some(stored) = &skel.rule else {
            return true;
        };
        let hints = ReplayHints::default();
        let Some(produced) = run_reasoner(stored, node.sequent(), &hints, provider) else {
            return false;
        };
        if !node.apply_rule(produced) {
            return false;
        }
        if node.children().len() != skel.children.len() {
            return false;
        }
        let mut complete = true;
        for (child, skel_child) in node.children_mut().iter_mut().zip(&skel.children) {
            complete &= replay(child, skel_child, provider);
        }
        complete
    })
}

/// Reconstructs the proof under `node` with reuse where possible and
/// replay where necessary. `try_replay_uncertain`
/// controls whether uncertain stored rules are re-run (keeping them as
/// recorded when the replay fails) or reused as they are. True iff the
/// whole skeleton was rebuilt; a false result still leaves everything
/// that could be rebuilt applied to the tree.
pub fn rebuild(
    node: &mut ProofTreeNode,
    skel: &Skeleton,
    hints: &ReplayHints,
    try_replay_uncertain: bool,
    provider: &dyn ReasonerProvider,
) -> bool {
    stacker::maybe_grow(64 * 1024, 1024 * 1024, || {
        let Some(stored) = &skel.rule else {
            return true;
        };

        let mut reused = false;
        let mut replayed = false;
        let certain = stored.rule.confidence > Confidence::UNCERTAIN_MAX;
        if certain {
            reused = try_reuse(stored, node, hints);
        }
        if (certain && !reused) || (!certain && try_replay_uncertain) {
            replayed = try_replay(stored, node, hints, provider);
        }

        if !(reused || replayed) {
            if rule_is_skip(node.sequent(), &stored.rule) {
                // The rule would do nothing: bypass it and continue
                // with its only sub-proof.
                return match skel.children.first() {
                    Some(child) => rebuild(node, child, hints, try_replay_uncertain, provider),
                    None => false,
                };
            }
            if !try_uncertain_rule(stored, node) {
                // A richer rebuild would search the skeleton for a
                // subtree here; not ported.
                return false;
            }
        }

        if node.children().len() != skel.children.len() {
            // Rebuilding children unsorted is deliberately not attempted.
            return false;
        }

        // A replayed rule may have renamed introduced identifiers:
        // derive fresh hints for each child from the produced rule.
        let produced_rule = replayed.then(|| node.rule().cloned()).flatten();
        let mut complete = true;
        for (index, (child, skel_child)) in node
            .children_mut()
            .iter_mut()
            .zip(&skel.children)
            .enumerate()
        {
            let child_hints = match &produced_rule {
                Some(rule) => {
                    let mut fresh = hints.clone();
                    fresh.add_hints(&stored.rule.antecedents[index], &rule.antecedents[index]);
                    fresh
                }
                None => hints.clone(),
            };
            complete &= rebuild(
                child,
                skel_child,
                &child_hints,
                try_replay_uncertain,
                provider,
            );
        }
        complete
    })
}

fn try_reuse(stored: &StoredRule, node: &mut ProofTreeNode, hints: &ReplayHints) -> bool {
    // With renaming hints pending, the recorded rule no longer speaks
    // about the right identifiers: never reuse it.
    hints.is_empty() && is_rule_reusable(&stored.rule) && node.apply_rule(stored.rule.clone())
}

fn try_replay(
    stored: &StoredRule,
    node: &mut ProofTreeNode,
    hints: &ReplayHints,
    provider: &dyn ReasonerProvider,
) -> bool {
    match run_reasoner(stored, node.sequent(), hints, provider) {
        Some(produced) => node.apply_rule(produced),
        None => false,
    }
}

fn run_reasoner(
    stored: &StoredRule,
    seq: &ProverSequent,
    hints: &ReplayHints,
    provider: &dyn ReasonerProvider,
) -> Option<Rule> {
    let implementation = provider.implementation(&stored.rule.reasoner)?;
    implementation.replay(seq, stored, hints).ok()
}

/// Whether the rule would leave the sequent exactly as it is — one
/// antecedent producing the identical sequent — so it can be bypassed.
fn rule_is_skip(seq: &ProverSequent, rule: &Rule) -> bool {
    match rule.apply(seq) {
        Some(children) => children.len() == 1 && ProverSequent::ptr_eq(&children[0], seq),
        None => false,
    }
}

/// Applies the stored rule downgraded to uncertain confidence, keeping
/// the proof structure of a step that can neither be reused nor
/// replayed.
fn try_uncertain_rule(stored: &StoredRule, node: &mut ProofTreeNode) -> bool {
    let mut rule = stored.rule.clone();
    rule.confidence = rule.confidence.min(Confidence::UNCERTAIN_MAX);
    node.apply_rule(rule)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::skeleton::StoredInput;
    use crate::test_util::{env, pred};

    fn sequent() -> ProverSequent {
        let env = env(&[("x", "ℤ")]);
        let hyp = pred(&env, "x=1");
        ProverSequent::new(env.clone(), [hyp.clone()], [], [hyp], pred(&env, "x<2"))
    }

    fn closing(reasoner: &str, confidence: Confidence, goal: Option<Predicate>) -> StoredRule {
        StoredRule {
            rule: Rule {
                reasoner: crate::registry::resolve(reasoner),
                goal,
                needed_hyps: Vec::new(),
                confidence,
                display: "test".into(),
                antecedents: Vec::new(),
            },
            input: StoredInput::default(),
        }
    }

    fn leaf(stored: StoredRule) -> Skeleton {
        Skeleton {
            rule: Some(stored),
            children: Vec::new(),
        }
    }

    /// A provider with one mock implementation for one reasoner id.
    struct Mock<'a> {
        id: &'a str,
        reasoner: &'a dyn Reasoner,
    }

    impl ReasonerProvider for Mock<'_> {
        fn implementation(&self, desc: &ReasonerDesc) -> Option<&dyn Reasoner> {
            (desc.id() == self.id).then_some(self.reasoner)
        }
    }

    /// Replays by closing the node at the sequent's goal.
    struct CloseAtGoal;

    impl Reasoner for CloseAtGoal {
        fn replay(
            &self,
            seq: &ProverSequent,
            stored: &StoredRule,
            _hints: &ReplayHints,
        ) -> Result<Rule, String> {
            Ok(Rule {
                reasoner: stored.rule.reasoner.clone(),
                goal: Some(seq.goal().clone()),
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: "mock".into(),
                antecedents: Vec::new(),
            })
        }
    }

    #[test]
    fn reuse_applies_trusted_rules_and_refuses_untrusted() {
        let seq = sequent();
        let trusted = leaf(closing(
            "org.eventb.core.seqprover.hyp",
            Confidence::DISCHARGED_MAX,
            Some(seq.goal().clone()),
        ));
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(reuse(&mut node, &trusted));
        assert!(node.is_closed());
        assert_eq!(node.confidence(), Confidence::DISCHARGED_MAX);

        // A stale version is untrusted: reuse refuses outright.
        let untrusted = leaf(closing(
            "org.eventb.core.seqprover.eq",
            Confidence::UNCERTAIN_MAX,
            Some(seq.goal().clone()),
        ));
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(!reuse(&mut node, &untrusted));
        assert!(node.is_open());

        // An open skeleton leaf is trivially reused.
        let mut node = ProofTreeNode::open(seq);
        assert!(reuse(&mut node, &Skeleton::open()));
        assert!(node.is_open());
    }

    #[test]
    fn replay_ignores_stored_rules_and_needs_an_implementation() {
        let seq = sequent();
        // The stored rule has a wrong goal; the mock re-derives a
        // correct one, so replay succeeds where reuse would not.
        let env = seq.type_env().clone();
        let stored = leaf(closing(
            "org.eventb.core.seqprover.hyp",
            Confidence::DISCHARGED_MAX,
            Some(pred(&env, "x<9")),
        ));
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(!reuse(&mut node, &stored));

        let provider = Mock {
            id: "org.eventb.core.seqprover.hyp",
            reasoner: &CloseAtGoal,
        };
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(replay(&mut node, &stored, &provider));
        assert!(node.is_closed());

        // Without an implementation, replay fails.
        let mut node = ProofTreeNode::open(seq);
        assert!(!replay(&mut node, &stored, &RegistryProvider));
        assert!(node.is_open());
    }

    #[test]
    fn rebuild_reuses_then_replays_then_downgrades() {
        let seq = sequent();
        let env = seq.type_env().clone();
        let no_hints = ReplayHints::default();

        // Certain and trusted: reused as recorded.
        let stored = leaf(closing(
            "org.eventb.core.seqprover.hyp",
            Confidence::DISCHARGED_MAX,
            Some(seq.goal().clone()),
        ));
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(rebuild(
            &mut node,
            &stored,
            &no_hints,
            false,
            &RegistryProvider
        ));
        assert_eq!(node.confidence(), Confidence::DISCHARGED_MAX);

        // Certain but inapplicable (wrong goal): replay repairs it
        // when an implementation exists.
        let wrong_goal = leaf(closing(
            "org.eventb.core.seqprover.hyp",
            Confidence::DISCHARGED_MAX,
            Some(pred(&env, "x<9")),
        ));
        let provider = Mock {
            id: "org.eventb.core.seqprover.hyp",
            reasoner: &CloseAtGoal,
        };
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(rebuild(&mut node, &wrong_goal, &no_hints, false, &provider));
        assert!(node.is_closed());

        // Untrusted with no implementation: the structure is kept at
        // uncertain confidence.
        let untrusted = leaf(closing(
            "org.eventb.core.seqprover.eq",
            Confidence::UNCERTAIN_MAX,
            Some(seq.goal().clone()),
        ));
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(rebuild(
            &mut node,
            &untrusted,
            &no_hints,
            false,
            &RegistryProvider
        ));
        assert!(node.is_closed());
        assert_eq!(node.confidence(), Confidence::UNCERTAIN_MAX);

        // Certain, trusted, but inapplicable and unimplemented: the
        // downgrade still keeps nothing since the rule cannot apply.
        let mut node = ProofTreeNode::open(seq);
        assert!(!rebuild(
            &mut node,
            &wrong_goal,
            &no_hints,
            false,
            &RegistryProvider
        ));
        assert!(node.is_open());
    }

    #[test]
    fn rebuild_bypasses_skip_rules() {
        let seq = sequent();
        // An untrusted wildcard rule with one no-op antecedent: it can
        // neither be reused nor replayed, but it would change nothing,
        // so rebuild bypasses it and applies its sub-proof directly.
        let skip = StoredRule {
            rule: Rule {
                reasoner: crate::registry::resolve("org.eventb.core.seqprover.eq"),
                goal: None,
                needed_hyps: Vec::new(),
                confidence: Confidence::DISCHARGED_MAX,
                display: "noop".into(),
                antecedents: vec![Antecedent {
                    goal: None,
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions: Vec::new(),
                }],
            },
            input: StoredInput::default(),
        };
        let inner = leaf(closing(
            "org.eventb.core.seqprover.hyp",
            Confidence::DISCHARGED_MAX,
            Some(seq.goal().clone()),
        ));
        let skel = Skeleton {
            rule: Some(skip),
            children: vec![inner],
        };
        let mut node = ProofTreeNode::open(seq.clone());
        assert!(rebuild(
            &mut node,
            &skel,
            &ReplayHints::default(),
            false,
            &RegistryProvider
        ));
        // The skip rule left no node behind: the inner rule closed the
        // root directly.
        assert!(node.is_closed());
        assert!(node.children().is_empty());
        assert_eq!(
            node.rule().map(|rule| rule.reasoner.id().to_string()),
            Some("org.eventb.core.seqprover.hyp".to_string())
        );
    }

    #[test]
    fn replay_hints_rename_introduced_identifiers() {
        let mut hints = ReplayHints::default();
        let old = Antecedent {
            goal: None,
            added_hyps: Vec::new(),
            unselected_added: Vec::new(),
            added_idents: vec![crate::sequent::TypedIdent::new(
                "z",
                rossi::formula::Type::Int,
            )],
            hyp_actions: Vec::new(),
        };
        let mut current = old.clone();
        current.added_idents[0].name = "w".into();
        hints.add_hints(&old, &current);
        assert!(!hints.is_empty());

        let wide = crate::test_util::env(&[("x", "ℤ"), ("z", "ℤ"), ("w", "ℤ")]);
        let renamed = hints.apply_pred(&pred(&wide, "z=x"));
        assert_eq!(renamed, pred(&wide, "w=x"));

        // A type mismatch produces no hint.
        let mut retyped = old.clone();
        retyped.added_idents[0].name = "b".into();
        retyped.added_idents[0].ty = rossi::formula::Type::Bool;
        let mut none = ReplayHints::default();
        none.add_hints(&old, &retyped);
        assert!(none.is_empty());
    }
}
