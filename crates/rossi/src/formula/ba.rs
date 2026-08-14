//! Before-after and feasibility predicates of assignments.
//!
//! An assignment relates the before-state to the after-state: its
//! before-after predicate expresses the after-values (written as primed
//! identifiers, `x'`) in terms of the before-values, and its
//! feasibility predicate expresses that some after-state exists at all.

use super::assignment::{Assignment, AssignmentKind};
use super::expression::{Expression, ExpressionKind};
use super::predicate::Predicate;
use super::tag::{AssocPredOp, AtomicOp, BinaryExprOp, LiteralPredOp, QuantPredOp, RelationalOp};

impl Assignment {
    /// The before-after predicate.
    ///
    /// - `x, y ≔ E, F` gives `x' = E ∧ y' = F`;
    /// - `x :∈ S` gives `x' ∈ S`;
    /// - `x :∣ P` gives `P` with the primed declarations freed into
    ///   primed free identifiers.
    ///
    /// The assignment must be type-checked.
    pub fn ba_predicate(&self) -> Predicate {
        assert!(
            self.is_type_checked(),
            "the before-after predicate needs types"
        );
        let ff = self.factory();
        let pred = match self.kind() {
            AssignmentKind::BecomesEqualTo { idents, values } => {
                let mut eqs: Vec<Predicate> = idents
                    .iter()
                    .zip(values)
                    .map(|(x, e)| {
                        ff.relational_predicate(RelationalOp::Equal, primed(x), e.clone(), None)
                    })
                    .collect();
                if eqs.len() == 1 {
                    eqs.pop().expect("one equality")
                } else {
                    ff.associative_predicate(AssocPredOp::LAnd, eqs, None)
                }
            }
            AssignmentKind::BecomesMemberOf { idents, set } => {
                let tuple = idents
                    .iter()
                    .map(primed)
                    .reduce(|left, right| {
                        ff.binary_expression(BinaryExprOp::Mapsto, left, right, None)
                    })
                    .expect("an assignment has at least one target");
                ff.relational_predicate(RelationalOp::In, tuple, set.clone(), None)
            }
            AssignmentKind::BecomesSuchThat {
                idents: _,
                primed,
                pred,
            } => {
                let replacements: Vec<Option<Expression>> = primed
                    .iter()
                    .map(|decl| Some(ff.free_identifier(decl.name(), None, decl.ty().cloned())))
                    .collect();
                ff.quantified_predicate(QuantPredOp::Exists, primed.clone(), pred.clone(), None)
                    .instantiate(&replacements)
            }
        };
        pred.flatten()
    }

    /// The feasibility predicate — when some after-state satisfies the
    /// assignment.
    ///
    /// - `x ≔ E` gives `⊤`;
    /// - `x :∈ S` gives `S ≠ ∅`;
    /// - `x :∣ P` gives `∃x' · P`.
    ///
    /// The assignment must be type-checked.
    pub fn fis_predicate(&self) -> Predicate {
        assert!(
            self.is_type_checked(),
            "the feasibility predicate needs types"
        );
        let ff = self.factory();
        let pred = match self.kind() {
            AssignmentKind::BecomesEqualTo { .. } => {
                ff.literal_predicate(LiteralPredOp::BTrue, None)
            }
            AssignmentKind::BecomesMemberOf { set, .. } => {
                let ty = set
                    .ty()
                    .expect("the feasibility predicate needs types")
                    .clone();
                let empty = ff.atomic_expression(AtomicOp::EmptySet, None, Some(ty));
                ff.relational_predicate(RelationalOp::NotEqual, set.clone(), empty, None)
            }
            AssignmentKind::BecomesSuchThat { primed, pred, .. } => {
                ff.quantified_predicate(QuantPredOp::Exists, primed.clone(), pred.clone(), None)
            }
        };
        pred.flatten()
    }
}

/// The primed after-value of an assigned identifier: `x` becomes the
/// free identifier `x'`, keeping the type.
fn primed(ident: &Expression) -> Expression {
    let ExpressionKind::FreeIdentifier(name) = ident.kind() else {
        unreachable!("assigned identifiers are free-identifier nodes");
    };
    ident
        .factory()
        .free_identifier(format!("{name}'"), None, ident.ty().cloned())
}
