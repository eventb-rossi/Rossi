//! Proof-status verdicts: the update decision for one obligation.
//!
//! A status row is recomputed when the obligation's stamp changed:
//! the row is *broken* when the stored proof no longer applies to the
//! regenerated sequent, decided purely
//! from the proof's recorded dependencies, and the row's confidence
//! stays a cached copy of the proof's — meaningless while broken. The
//! stamp gating itself lives with the build pipeline; this module is
//! only the per-obligation decision.

use crate::bpr::{ProofBody, ProofEntry};
use crate::deps::is_proof_reusable;
use crate::sequent::ProverSequent;

/// The recomputed status of one obligation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StatusVerdict {
    /// Whether the stored proof no longer applies to the sequent.
    pub broken: bool,
    /// The proof's recorded confidence, copied verbatim. `None` for
    /// a never-attempted proof.
    pub confidence: Option<i32>,
    /// Whether the proof is marked manual.
    pub manual: bool,
    /// Whether the proof steps through a context-dependent reasoner,
    /// which forces re-checking on every build.
    pub context_dependent: bool,
}

/// Decides the status of one obligation from its (re)generated
/// sequent and its stored proof.
///
/// A proof rossi cannot represent — old-vintage storage, an extended
/// language, unparsable content — is conservatively broken: its
/// applicability cannot be checked. The proof must have been read in
/// at least [`crate::bpr::Keep::Deps`] mode.
pub fn compute_status(seq: &ProverSequent, entry: &ProofEntry) -> StatusVerdict {
    let (broken, context_dependent) = match &entry.body {
        ProofBody::Skipped => panic!("status needs a proof read in Deps or Full mode"),
        ProofBody::Unsupported(_) => (true, false),
        ProofBody::Loaded(proof) => (
            !is_proof_reusable(&proof.deps, seq),
            proof.deps.is_context_dependent(),
        ),
    };
    StatusVerdict {
        broken,
        confidence: entry.confidence,
        manual: entry.manual,
        context_dependent,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bpr::{Keep, read_bpr};
    use crate::sequent::ProverSequent;
    use crate::test_util::{env, pred};
    use indoc::formatdoc;

    /// A discharged stored proof depending on goal `x<2` and
    /// hypothesis `x=1`.
    fn stored(reasoner: &str) -> ProofEntry {
        let xml = formatdoc!(
            r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
            <org.eventb.core.prFile version="1">
            <org.eventb.core.prProof name="evt/inv/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p1">
            <org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
            <org.eventb.core.prPred name="p0" org.eventb.core.predicate="x&lt;2"/>
            <org.eventb.core.prPred name="p1" org.eventb.core.predicate="x=1"/>
            <org.eventb.core.prReas name="r0" org.eventb.core.prRID="{reasoner}"/>
            </org.eventb.core.prProof>
            </org.eventb.core.prFile>"#
        );
        read_bpr(xml.as_bytes(), |_| Keep::Deps)
            .expect("readable")
            .remove(0)
    }

    fn sequent(goal: &str, hyp: Option<&str>) -> ProverSequent {
        let env = env(&[("x", "ℤ")]);
        let hyps: Vec<_> = hyp.map(|h| pred(&env, h)).into_iter().collect();
        ProverSequent::new(env.clone(), hyps, [], [], pred(&env, goal))
    }

    #[test]
    fn reusable_proof_keeps_its_confidence() {
        let entry = stored("org.eventb.core.seqprover.hyp");
        let verdict = compute_status(&sequent("x<2", Some("x=1")), &entry);
        assert_eq!(
            verdict,
            StatusVerdict {
                broken: false,
                confidence: Some(1000),
                manual: false,
                context_dependent: false,
            }
        );
    }

    #[test]
    fn inapplicable_or_untrusted_proofs_break() {
        let entry = stored("org.eventb.core.seqprover.hyp");
        // The goal changed.
        assert!(compute_status(&sequent("x<3", Some("x=1")), &entry).broken);
        // A used hypothesis vanished.
        assert!(compute_status(&sequent("x<2", None), &entry).broken);
        // A stale reasoner version distrusts the proof even though the
        // sequent still matches.
        let stale = stored("org.eventb.core.seqprover.eq");
        assert!(compute_status(&sequent("x<2", Some("x=1")), &stale).broken);
    }

    #[test]
    fn context_dependent_proofs_break_and_are_flagged() {
        let entry = stored("org.eventb.core.seqprover.dtDistinctCase");
        let verdict = compute_status(&sequent("x<2", Some("x=1")), &entry);
        assert!(verdict.broken);
        assert!(verdict.context_dependent);
    }

    #[test]
    fn unsupported_and_unattempted_proofs() {
        // An extended-language proof cannot be checked: broken.
        let xml = formatdoc!(
            r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
            <org.eventb.core.prFile version="1">
            <org.eventb.core.prProof name="a" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prHyps="">
            <org.eventb.core.lang name="L" org.eventb.core.scope="T"/>
            </org.eventb.core.prProof>
            <org.eventb.core.prProof name="b"/>
            </org.eventb.core.prFile>"#
        );
        let entries = read_bpr(xml.as_bytes(), |_| Keep::Deps).expect("readable");
        let seq = sequent("x<2", None);
        assert!(compute_status(&seq, &entries[0]).broken);

        // A never-attempted proof has no dependencies: not broken, no
        // confidence.
        let verdict = compute_status(&seq, &entries[1]);
        assert!(!verdict.broken);
        assert_eq!(verdict.confidence, None);
    }
}
