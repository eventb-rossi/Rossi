//! Subsumption simplification of well-definedness lemmas.
//!
//! The lemma is reinterpreted as a tree of universal closures,
//! implications, conjunctions and opaque predicate leaves. Bound
//! indices are first equalized — every leaf is shifted as if all the
//! universal quantifiers were hoisted to the root — so that syntactic
//! comparison works across depths. Each leaf then yields a lemma
//! "antecedents ⊢ consequent" (the antecedents being the left-hand
//! sides of the implications above it); a leaf is subsumed when its
//! consequent already appears among its antecedents, or when another
//! lemma with the same consequent and a subset of its antecedents is
//! known. Subsumed leaves render as ⊤ and the final flatten removes
//! them.

use std::collections::HashSet;

use super::super::decl::BoundIdentDecl;
use super::super::predicate::{Predicate, PredicateKind};
use super::super::tag::{AssocPredOp, BinaryPredOp, QuantPredOp};
use super::fb::FormulaBuilder;

/// One node of the simplification tree, held in an arena.
struct Node {
    kind: NodeKind,
    subsumed: bool,
    /// The leaf's index-equalized form (leaves only).
    normalized: Option<Predicate>,
}

enum NodeKind {
    Forall {
        decls: Vec<BoundIdentDecl>,
        child: usize,
    },
    Limp {
        left: usize,
        right: usize,
    },
    Land {
        children: Vec<usize>,
    },
    Leaf {
        original: Predicate,
    },
}

/// A leaf with the hypotheses it sits under.
#[derive(Clone)]
struct Lemma {
    antecedents: HashSet<Predicate>,
    consequent: Predicate,
    origin: usize,
}

impl Lemma {
    /// Whether this lemma makes `other` redundant: same consequent from
    /// no more hypotheses.
    fn subsumes(&self, other: &Lemma) -> bool {
        self.consequent == other.consequent && self.antecedents.is_subset(&other.antecedents)
    }
}

pub(super) fn improve(fb: &FormulaBuilder, lemma: &Predicate) -> Predicate {
    let mut tree = Tree { nodes: Vec::new() };
    let root = tree.build(lemma);
    let depth = tree.max_binding_depth(root);
    tree.equalize(root, depth);
    let mut known: Vec<Lemma> = Vec::new();
    tree.simplify(root, &mut known, &HashSet::new(), fb);
    tree.as_predicate(root, fb, true).flatten()
}

struct Tree {
    nodes: Vec<Node>,
}

impl Tree {
    fn add(&mut self, kind: NodeKind) -> usize {
        self.nodes.push(Node {
            kind,
            subsumed: false,
            normalized: None,
        });
        self.nodes.len() - 1
    }

    fn build(&mut self, pred: &Predicate) -> usize {
        match pred.kind() {
            PredicateKind::Quantified {
                op: QuantPredOp::Forall,
                decls,
                pred: child,
            } => {
                let decls = decls.clone();
                let child = self.build(child);
                self.add(NodeKind::Forall { decls, child })
            }
            PredicateKind::Binary {
                op: BinaryPredOp::LImp,
                left,
                right,
            } => {
                let left = self.build(left);
                let right = self.build(right);
                self.add(NodeKind::Limp { left, right })
            }
            PredicateKind::Associative {
                op: AssocPredOp::LAnd,
                children,
            } => {
                let children = children.iter().map(|c| self.build(c)).collect();
                self.add(NodeKind::Land { children })
            }
            _ => self.add(NodeKind::Leaf {
                original: pred.clone(),
            }),
        }
    }

    /// The deepest chain of universal quantifiers above any leaf.
    fn max_binding_depth(&self, id: usize) -> usize {
        match &self.nodes[id].kind {
            NodeKind::Forall { decls, child } => decls.len() + self.max_binding_depth(*child),
            NodeKind::Limp { left, right } => self
                .max_binding_depth(*left)
                .max(self.max_binding_depth(*right)),
            NodeKind::Land { children } => children
                .iter()
                .map(|c| self.max_binding_depth(*c))
                .max()
                .unwrap_or(0),
            NodeKind::Leaf { .. } => 0,
        }
    }

    /// Shifts every leaf as if all quantifiers were hoisted to the
    /// root: a leaf under `d` of the `offset` binders shifts by
    /// `offset - d`.
    fn equalize(&mut self, id: usize, offset: usize) {
        match &self.nodes[id].kind {
            NodeKind::Forall { decls, child } => {
                let child = *child;
                let inner = offset - decls.len();
                self.equalize(child, inner);
            }
            NodeKind::Limp { left, right } => {
                let (left, right) = (*left, *right);
                self.equalize(left, offset);
                self.equalize(right, offset);
            }
            NodeKind::Land { children } => {
                for child in children.clone() {
                    self.equalize(child, offset);
                }
            }
            NodeKind::Leaf { original } => {
                let normalized = original.shift_bound_identifiers(offset as i32);
                self.nodes[id].normalized = Some(normalized);
            }
        }
    }

    /// The node's predicate: the original spelling when `original`,
    /// the normalized one for comparisons. A subsumed node is ⊤.
    fn as_predicate(&self, id: usize, fb: &FormulaBuilder, original: bool) -> Predicate {
        let node = &self.nodes[id];
        if node.subsumed {
            return fb.btrue();
        }
        match &node.kind {
            NodeKind::Forall { decls, child } => {
                let body = self.as_predicate(*child, fb, original);
                if original {
                    fb.forall(decls.clone(), body)
                } else {
                    // Comparisons pretend the quantifier is hoisted.
                    body
                }
            }
            NodeKind::Limp { left, right } => fb.limp(
                self.as_predicate(*left, fb, original),
                self.as_predicate(*right, fb, original),
            ),
            NodeKind::Land { children } => {
                fb.land_all(children.iter().map(|c| self.as_predicate(*c, fb, original)))
            }
            NodeKind::Leaf { original: pred } => {
                if original {
                    pred.clone()
                } else {
                    self.nodes[id]
                        .normalized
                        .clone()
                        .expect("equalized before comparison")
                }
            }
        }
    }

    /// Adds this node's normalized predicate to `set`; a node whose
    /// predicate is already present becomes subsumed instead.
    fn add_predicate_to_set(
        &mut self,
        id: usize,
        set: &mut HashSet<Predicate>,
        fb: &FormulaBuilder,
    ) {
        if self.nodes[id].subsumed {
            return;
        }
        let normalized = self.as_predicate(id, fb, false);
        if !set.insert(normalized) {
            self.nodes[id].subsumed = true;
        }
    }

    /// Collects the predicates an implication's left side contributes
    /// as hypotheses for its right side.
    fn collect_antecedents(
        &mut self,
        id: usize,
        antecedents: &mut HashSet<Predicate>,
        fb: &FormulaBuilder,
    ) {
        match &self.nodes[id].kind {
            NodeKind::Forall { child, .. } => {
                let child = *child;
                self.collect_antecedents(child, antecedents, fb);
            }
            NodeKind::Land { children } => {
                for child in children.clone() {
                    self.collect_antecedents(child, antecedents, fb);
                }
            }
            NodeKind::Limp { .. } | NodeKind::Leaf { .. } => {
                self.add_predicate_to_set(id, antecedents, fb);
            }
        }
    }

    fn simplify(
        &mut self,
        id: usize,
        known: &mut Vec<Lemma>,
        antecedents: &HashSet<Predicate>,
        fb: &FormulaBuilder,
    ) {
        if self.nodes[id].subsumed {
            return;
        }
        match &self.nodes[id].kind {
            NodeKind::Forall { child, .. } => {
                let child = *child;
                self.simplify(child, known, antecedents, fb);
            }
            NodeKind::Land { children } => {
                for child in children.clone() {
                    self.simplify(child, known, antecedents, fb);
                }
            }
            NodeKind::Limp { left, right } => {
                let (left, right) = (*left, *right);
                // The left side simplifies in its own context: lemmas
                // it produces do not hold on the right of the
                // implication.
                let mut left_known = known.clone();
                self.simplify(left, &mut left_known, &HashSet::new(), fb);
                // Its predicates become hypotheses for the right side.
                let mut right_antecedents = antecedents.clone();
                self.collect_antecedents(left, &mut right_antecedents, fb);
                self.simplify(right, known, &right_antecedents, fb);
            }
            NodeKind::Leaf { .. } => {
                let normalized = self.nodes[id]
                    .normalized
                    .clone()
                    .expect("equalized before simplification");
                if antecedents.contains(&normalized) {
                    self.nodes[id].subsumed = true;
                    return;
                }
                let lemma = Lemma {
                    antecedents: antecedents.clone(),
                    consequent: normalized,
                    origin: id,
                };
                self.add_lemma(lemma, known);
            }
        }
    }

    /// Inserts a lemma, resolving subsumption both ways: an existing
    /// stronger lemma subsumes the new one; a stronger new one evicts
    /// (and subsumes) weaker existing ones. Never marks both sides.
    fn add_lemma(&mut self, lemma: Lemma, known: &mut Vec<Lemma>) {
        let mut i = 0;
        while i < known.len() {
            if known[i].subsumes(&lemma) {
                self.nodes[lemma.origin].subsumed = true;
                return;
            }
            if lemma.subsumes(&known[i]) {
                let evicted = known.remove(i);
                self.nodes[evicted.origin].subsumed = true;
                continue;
            }
            i += 1;
        }
        known.push(lemma);
    }
}
