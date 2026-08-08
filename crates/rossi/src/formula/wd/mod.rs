//! Well-definedness lemmas.
//!
//! `wd_lemma_raw` computes the lemma of a type-checked formula with
//! only the constructive simplifications applied (tautologies never
//! materialize; the result is flattened). The subsumption-simplified
//! variant is layered on top separately.

mod computer;
mod fb;
mod improver;

use super::assignment::{Assignment, AssignmentKind};
use super::expression::{Expression, ExpressionKind};
use super::position::{FormulaRef, Position};
use super::predicate::{Predicate, PredicateKind};
use super::tag::BinaryPredOp;

use computer::{wd_assign, wd_expr, wd_pred};
use fb::FormulaBuilder;

impl Predicate {
    /// The well-definedness lemma, unsimplified beyond construction.
    /// Requires a type-checked formula.
    #[track_caller]
    pub fn wd_lemma_raw(&self) -> Predicate {
        assert!(
            self.is_type_checked(),
            "well-definedness needs a type-checked formula"
        );
        let fb = FormulaBuilder::new(self.factory().clone());
        wd_pred(&fb, self).flatten()
    }

    /// The well-definedness lemma, with redundant conjuncts removed by
    /// subsumption. Requires a type-checked formula.
    #[track_caller]
    pub fn wd_lemma(&self) -> Predicate {
        let raw = self.wd_lemma_raw();
        improver::improve(&FormulaBuilder::new(self.factory().clone()), &raw)
    }

    /// Whether this node passes its own well-definedness down to its
    /// children: knowing the node denotes implies its children denote.
    pub fn is_wd_strict(&self) -> bool {
        match self.kind() {
            PredicateKind::Literal(_)
            | PredicateKind::PredicateVariable(_)
            | PredicateKind::Relational { .. }
            | PredicateKind::Not(_)
            | PredicateKind::Simple(_)
            | PredicateKind::Multiple(_) => true,
            PredicateKind::Binary { op, .. } => *op == BinaryPredOp::LEqv,
            PredicateKind::Associative { .. } | PredicateKind::Quantified { .. } => false,
            PredicateKind::Application { .. } => false,
            // Refined when the extension mechanism lands.
            PredicateKind::Extended { .. } => false,
        }
    }

    /// Whether every node from the root down to (excluding) the node at
    /// `position` is WD-strict, i.e. the subformula's well-definedness
    /// is implied by the whole formula's.
    pub fn is_wd_strict_at(&self, position: &Position) -> bool {
        strict_path(FormulaRef::Pred(self), position)
    }
}

impl Expression {
    /// The well-definedness lemma; see [`Predicate::wd_lemma_raw`].
    #[track_caller]
    pub fn wd_lemma_raw(&self) -> Predicate {
        assert!(
            self.is_type_checked(),
            "well-definedness needs a type-checked formula"
        );
        let fb = FormulaBuilder::new(self.factory().clone());
        wd_expr(&fb, self).flatten()
    }

    /// The subsumption-simplified lemma; see [`Predicate::wd_lemma`].
    #[track_caller]
    pub fn wd_lemma(&self) -> Predicate {
        let raw = self.wd_lemma_raw();
        improver::improve(&FormulaBuilder::new(self.factory().clone()), &raw)
    }

    /// See [`Predicate::is_wd_strict`].
    pub fn is_wd_strict(&self) -> bool {
        match self.kind() {
            ExpressionKind::Quantified { .. } => false,
            // Refined when the extension mechanism lands.
            ExpressionKind::Extended { .. } => false,
            _ => true,
        }
    }

    /// See [`Predicate::is_wd_strict_at`].
    pub fn is_wd_strict_at(&self, position: &Position) -> bool {
        strict_path(FormulaRef::Expr(self), position)
    }
}

impl Assignment {
    /// The well-definedness lemma; see [`Predicate::wd_lemma_raw`].
    /// The lemma of a such-that assignment closes over its primed
    /// declarations.
    #[track_caller]
    pub fn wd_lemma_raw(&self) -> Predicate {
        assert!(
            self.is_type_checked(),
            "well-definedness needs a type-checked formula"
        );
        let fb = FormulaBuilder::new(self.factory().clone());
        wd_assign(&fb, self).flatten()
    }

    /// The subsumption-simplified lemma; see [`Predicate::wd_lemma`].
    #[track_caller]
    pub fn wd_lemma(&self) -> Predicate {
        let raw = self.wd_lemma_raw();
        improver::improve(&FormulaBuilder::new(self.factory().clone()), &raw)
    }

    /// See [`Predicate::is_wd_strict`]. All assignment forms are
    /// strict.
    pub fn is_wd_strict(&self) -> bool {
        match self.kind() {
            AssignmentKind::BecomesEqualTo { .. }
            | AssignmentKind::BecomesMemberOf { .. }
            | AssignmentKind::BecomesSuchThat { .. } => true,
        }
    }
}

fn strict_path(root: FormulaRef<'_>, position: &Position) -> bool {
    let mut current = root;
    for index in position.indices() {
        let strict = match current {
            FormulaRef::Expr(e) => e.is_wd_strict(),
            FormulaRef::Pred(p) => p.is_wd_strict(),
            FormulaRef::Decl(_) => true,
        };
        if !strict {
            return false;
        }
        match current.child(*index as usize) {
            Some(child) => current = child,
            None => return false,
        }
    }
    true
}
