//! Proof trees: rules applied to sequents, confidence-aggregated.
//!
//! Trimmed down to what checking and replay need:
//! an owned tree with [`ProofTreeNode::apply_rule`] as the sole
//! mutation point and no deltas, parent pointers, or pruning.

use crate::confidence::Confidence;
use crate::rule::Rule;
use crate::sequent::ProverSequent;

/// One node of a proof tree.
#[derive(Debug, Clone)]
pub struct ProofTreeNode {
    sequent: ProverSequent,
    rule: Option<Rule>,
    children: Vec<ProofTreeNode>,
}

impl ProofTreeNode {
    /// An open node — no rule applied yet.
    pub fn open(sequent: ProverSequent) -> ProofTreeNode {
        ProofTreeNode {
            sequent,
            rule: None,
            children: Vec::new(),
        }
    }

    /// The node's sequent.
    pub fn sequent(&self) -> &ProverSequent {
        &self.sequent
    }

    /// The rule applied at this node, if any.
    pub fn rule(&self) -> Option<&Rule> {
        self.rule.as_ref()
    }

    /// The child nodes, one per antecedent of the applied rule.
    pub fn children(&self) -> &[ProofTreeNode] {
        &self.children
    }

    /// Mutable access to the children, for the proof builder's
    /// recursive descent.
    pub fn children_mut(&mut self) -> &mut [ProofTreeNode] {
        &mut self.children
    }

    /// Whether no rule is applied here yet.
    pub fn is_open(&self) -> bool {
        self.rule.is_none()
    }

    /// Whether this subtree has no open node.
    pub fn is_closed(&self) -> bool {
        self.rule.is_some() && self.children.iter().all(ProofTreeNode::is_closed)
    }

    /// Applies `rule` here — the tree's sole mutation point, the
    /// `ProofTreeNode.applyRule`. False (leaving the node untouched)
    /// when a rule is already applied or the rule does not apply to
    /// this node's sequent; on success the children are fresh open
    /// nodes, one per antecedent.
    pub fn apply_rule(&mut self, rule: Rule) -> bool {
        if self.rule.is_some() {
            return false;
        }
        let Some(antecedents) = rule.apply(&self.sequent) else {
            return false;
        };
        self.children = antecedents.into_iter().map(ProofTreeNode::open).collect();
        self.rule = Some(rule);
        true
    }

    /// The subtree's confidence: [`Confidence::PENDING`] when open,
    /// otherwise the minimum of the rule's confidence and every
    /// child's — one uncertain step caps the whole proof.
    pub fn confidence(&self) -> Confidence {
        match &self.rule {
            None => Confidence::PENDING,
            Some(rule) => self
                .children
                .iter()
                .map(ProofTreeNode::confidence)
                .fold(rule.confidence, Confidence::min),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::rule::Antecedent;
    use crate::test_util::{env, pred};

    fn seq(goal: &str) -> ProverSequent {
        let env = env(&[("x", "ℤ")]);
        let hyp = pred(&env, "x=1");
        ProverSequent::new(env.clone(), [hyp.clone()], [], [hyp], pred(&env, goal))
    }

    fn branching(confidence: Confidence, branches: usize) -> Rule {
        Rule {
            goal: None,
            needed_hyps: Vec::new(),
            confidence,
            display: "test".into(),
            antecedents: (0..branches)
                .map(|_| Antecedent {
                    goal: None,
                    added_hyps: Vec::new(),
                    unselected_added: Vec::new(),
                    added_idents: Vec::new(),
                    hyp_actions: Vec::new(),
                })
                .collect(),
        }
    }

    #[test]
    fn closing_rule_closes_the_node() {
        let mut node = ProofTreeNode::open(seq("x<2"));
        assert!(node.is_open());
        assert_eq!(node.confidence(), Confidence::PENDING);

        assert!(node.apply_rule(branching(Confidence::DISCHARGED_MAX, 0)));
        assert!(node.is_closed());
        assert!(node.children().is_empty());
        assert_eq!(node.confidence(), Confidence::DISCHARGED_MAX);

        // A second application is refused.
        assert!(!node.apply_rule(branching(Confidence::DISCHARGED_MAX, 0)));
    }

    #[test]
    fn inapplicable_rule_leaves_the_node_open() {
        let mut node = ProofTreeNode::open(seq("x<2"));
        let env = node.sequent().type_env().clone();
        let mut rule = branching(Confidence::DISCHARGED_MAX, 0);
        rule.needed_hyps = vec![pred(&env, "x=9")];
        assert!(!node.apply_rule(rule));
        assert!(node.is_open());
    }

    #[test]
    fn confidence_is_the_minimum_over_the_tree() {
        let mut node = ProofTreeNode::open(seq("x<2"));
        assert!(node.apply_rule(branching(Confidence::DISCHARGED_MAX, 2)));
        assert!(!node.is_closed());
        // An open child keeps the tree pending.
        assert_eq!(node.confidence(), Confidence::PENDING);

        let [first, second] = node.children_mut() else {
            panic!("two children")
        };
        assert!(first.apply_rule(branching(Confidence::DISCHARGED_MAX, 0)));
        assert!(second.apply_rule(branching(Confidence(400), 0)));
        assert!(node.is_closed());
        // The reviewed branch caps the whole proof.
        assert_eq!(node.confidence(), Confidence(400));
    }
}
