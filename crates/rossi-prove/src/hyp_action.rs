//! Hypothesis actions: the sequent adjustments a proof rule carries.
//!
//! The three action kinds. Selection actions rearrange the
//! presentational subsets only; a forward inference adds hypotheses
//! inferred from present ones; a rewrite is a forward inference that
//! also hides the rewritten-away hypotheses. Performing an action can
//! never fail: an inapplicable action leaves the sequent unchanged.

use rossi::formula::Predicate;

use crate::sequent::{ProverSequent, TypedIdent};

/// One hypothesis action, applied in list order within an antecedent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum HypAction {
    /// Select the hypotheses (un-hiding them).
    Select(Vec<Predicate>),
    /// Deselect the hypotheses.
    Deselect(Vec<Predicate>),
    /// Hide the hypotheses (deselecting them).
    Hide(Vec<Predicate>),
    /// Un-hide the hypotheses.
    Show(Vec<Predicate>),
    /// Forward inference `hyps ⊢ ∃ added_idents · inferred`.
    ForwardInf {
        /// The source hypotheses the inference needs.
        hyps: Vec<Predicate>,
        /// Identifiers the inferred hypotheses introduce.
        added_idents: Vec<TypedIdent>,
        /// The inferred hypotheses to add.
        inferred: Vec<Predicate>,
    },
    /// A forward inference whose spent sources are hidden afterwards.
    Rewrite {
        /// The source hypotheses the inference needs.
        hyps: Vec<Predicate>,
        /// Identifiers the inferred hypotheses introduce.
        added_idents: Vec<TypedIdent>,
        /// The inferred hypotheses to add.
        inferred: Vec<Predicate>,
        /// The rewritten-away sources to hide — a subset of `hyps`.
        disappearing: Vec<Predicate>,
    },
}

impl HypAction {
    /// Applies this action to `seq`. Inapplicable actions return the
    /// sequent unchanged.
    pub(crate) fn perform(&self, seq: ProverSequent) -> ProverSequent {
        match self {
            HypAction::Select(hyps) => seq.select_hypotheses(hyps),
            HypAction::Deselect(hyps) => seq.deselect_hypotheses(hyps),
            HypAction::Hide(hyps) => seq.hide_hypotheses(hyps),
            HypAction::Show(hyps) => seq.show_hypotheses(hyps),
            HypAction::ForwardInf {
                hyps,
                added_idents,
                inferred,
            } => seq.perform_fwd_inf(hyps, added_idents, inferred),
            HypAction::Rewrite {
                hyps,
                added_idents,
                inferred,
                disappearing,
            } => {
                debug_assert!(disappearing.iter().all(|hyp| hyps.contains(hyp)));
                seq.perform_rewrite(hyps, added_idents, inferred, disappearing)
            }
        }
    }

    /// The hypotheses this action acts on — the set a rule needs
    /// present to
    /// apply fully.
    pub fn hyps(&self) -> &[Predicate] {
        match self {
            HypAction::Select(hyps)
            | HypAction::Deselect(hyps)
            | HypAction::Hide(hyps)
            | HypAction::Show(hyps)
            | HypAction::ForwardInf { hyps, .. }
            | HypAction::Rewrite { hyps, .. } => hyps,
        }
    }
}
