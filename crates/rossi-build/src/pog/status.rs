//! Proof-status update at the build boundary.
//!
//! [`super::reconcile`] carries `.bps` rows verbatim and leaves a
//! stale stamp as the signal that the recorded verdict no longer
//! matches its obligation. This module acts on that signal the way a
//! reference build does: a row whose stamp differs from its sequent's
//! (or whose proof is context-dependent) is recomputed from the
//! stored proof's dependencies — broken when the proof no longer
//! applies, its confidence a verbatim copy of the proof's — while
//! stamp-matched rows keep their exact bytes. Like reconciliation
//! this runs at the IO boundary, never inside pure `build()`, and
//! only when a caller opts in.

use std::collections::{BTreeMap, HashSet};

use rossi_prove::bpr::{Keep, ProofBody, ProofEntry, read_bpr};
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::{StatusVerdict, compute_status};

use crate::ScFile;
use crate::pog::reconcile::{
    StatusRow, assemble_status, bpo_bps_pairs, fresh_status_row, parse_status_rows, sequent_stamps,
};
use crate::xml_out::{attr, escape_attr, tag as xtag};

/// Recomputes every stale `.bps` row in `files` against the stored
/// proofs supplied by `bpr` (keyed by filename, e.g. `M0.bpr`).
///
/// A row is stale when its recorded stamp differs from its sequent's
/// stamp in the sibling `.bpo`, or when its proof is marked
/// context-dependent. An unattempted, non-broken row whose stored
/// proof records real confidence is also recomputed: such a row is
/// what reconciliation synthesizes for an obligation the recorded
/// `.bps` never mentioned, and the status update computes missing
/// statuses from the stored proofs (a status that does not exist). Stale rows are rewritten with a fresh verdict and the
/// sequent's stamp; a stale row without a stored proof becomes a
/// fresh unattempted row. Everything else keeps its exact bytes, so
/// an archive whose obligations did not change round-trips untouched.
pub fn update_statuses(files: &mut [ScFile], mut bpr: impl FnMut(&str) -> Option<String>) {
    // All generated obligation files form one project: hypothesis-set
    // chains cross component files.
    let mut project = PoProject::default();
    for file in files.iter() {
        if file.filename.ends_with(".bpo")
            && let Ok(parsed) = PoFile::read(file.contents.as_bytes())
        {
            project.insert(file.filename.clone(), parsed);
        }
    }

    for (i, j) in bpo_bps_pairs(files) {
        let stamps = sequent_stamps(&files[i].contents);
        let rows = parse_status_rows(&files[j].contents);
        let stem = files[i].filename.trim_end_matches(".bpo").to_string();
        let bpr_contents = bpr(&format!("{stem}.bpr"));
        // A cheap first pass over the proof file: which obligations
        // carry a proof with real recorded confidence, to revive the
        // unattempted rows reconciliation synthesized for them.
        let proof_confidences: BTreeMap<String, i32> = bpr_contents
            .as_deref()
            .and_then(|contents| read_bpr(contents.as_bytes(), |_| Keep::Skip).ok())
            .map(|entries| {
                entries
                    .into_iter()
                    .map(|entry| (entry.name.clone(), entry.confidence.unwrap_or(-99)))
                    .collect()
            })
            .unwrap_or_default();
        let stale = |row: &StatusRow| {
            row.context_dependent
                || stamps.get(&row.name).map(String::as_str) != row.stamp.as_deref()
                || (row.confidence.is_none_or(|c| c <= -99)
                    && !row.broken
                    && proof_confidences.get(&row.name).copied().unwrap_or(-99) > -99)
        };
        if !rows.iter().any(&stale) {
            continue;
        }

        let stale_names: HashSet<&str> = rows
            .iter()
            .filter(|row| stale(row))
            .map(|row| row.name.as_str())
            .collect();
        // The component's stored proofs, dependencies resolved only
        // for the rows needing a fresh verdict. An unreadable proof
        // file leaves no proofs, so its stale rows reset to
        // unattempted.
        let proofs: BTreeMap<String, ProofEntry> = bpr_contents
            .and_then(|contents| {
                read_bpr(contents.as_bytes(), |name| {
                    if stale_names.contains(name) {
                        Keep::Deps
                    } else {
                        Keep::Skip
                    }
                })
                .ok()
            })
            .map(|entries| {
                entries
                    .into_iter()
                    .map(|entry| (entry.name.clone(), entry))
                    .collect()
            })
            .unwrap_or_default();

        let out: Vec<String> = rows
            .iter()
            .map(|row| {
                if !stale(row) {
                    return row.row.clone();
                }
                let stamp = stamps.get(&row.name).map_or("0", String::as_str);
                match proofs.get(&row.name) {
                    Some(entry) if !matches!(entry.body, ProofBody::Skipped) => {
                        match project.load(&files[i].filename, &row.name) {
                            Ok(seq) => status_row(&row.name, &compute_status(&seq, entry), stamp),
                            // Our own generated obligation failed to
                            // load — keep the stale row, so the stamp
                            // divergence stays visible downstream.
                            Err(_) => row.row.clone(),
                        }
                    }
                    _ => fresh_status_row(&row.name, stamp),
                }
            })
            .collect();
        files[j].contents = assemble_status(&out);
    }
}

/// Renders one recomputed status row in the generator's shape.
fn status_row(name: &str, verdict: &StatusVerdict, stamp: &str) -> String {
    let mut row = format!("<{} {}=\"", xtag::PS_STATUS, attr::NAME);
    escape_attr(name, &mut row);
    row.push_str(&format!(
        "\" {}=\"{}\" {}=\"{stamp}\" {}=\"{}\"",
        attr::CONFIDENCE,
        verdict.confidence.unwrap_or(-99),
        attr::PO_STAMP,
        attr::PS_MANUAL,
        if verdict.manual { "true" } else { "false" },
    ));
    if verdict.broken {
        row.push_str(&format!(" {}=\"true\"", attr::PS_BROKEN));
    }
    if verdict.context_dependent {
        row.push_str(&format!(" {}=\"true\"", attr::CONTEXT_DEPENDENT));
    }
    row.push_str("/>");
    row
}

#[cfg(test)]
mod tests {
    use super::*;

    const BPO: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.poFile org.eventb.core.poStamp="0">
<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.poStamp="0">
<org.eventb.core.poIdentifier name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="x=1"/>
</org.eventb.core.poPredicateSet>
<org.eventb.core.poSequent name="evt/inv1/INV" org.eventb.core.poStamp="2">
<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/P/M0.bpo|org.eventb.core.poFile#M0|org.eventb.core.poPredicateSet#ALLHYP"/>
<org.eventb.core.poPredicate name="SEQG" org.eventb.core.predicate="x&lt;2"/>
</org.eventb.core.poSequent>
<org.eventb.core.poSequent name="evt/inv2/INV" org.eventb.core.poStamp="2">
<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/P/M0.bpo|org.eventb.core.poFile#M0|org.eventb.core.poPredicateSet#ALLHYP"/>
<org.eventb.core.poPredicate name="SEQG" org.eventb.core.predicate="x&lt;3"/>
</org.eventb.core.poSequent>
<org.eventb.core.poSequent name="evt/inv3/INV" org.eventb.core.poStamp="2">
<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/P/M0.bpo|org.eventb.core.poFile#M0|org.eventb.core.poPredicateSet#ALLHYP"/>
<org.eventb.core.poPredicate name="SEQG" org.eventb.core.predicate="x&lt;4"/>
</org.eventb.core.poSequent>
</org.eventb.core.poFile>
"#;

    /// inv1: fresh at the current stamp; inv2 and inv3: stale.
    const BPS: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.psFile>
<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>
<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="1" org.eventb.core.psManual="true"/>
<org.eventb.core.psStatus name="evt/inv3/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="1" org.eventb.core.psManual="false"/>
</org.eventb.core.psFile>
"#;

    /// inv2 has a proof matching its regenerated sequent; inv3 has a
    /// proof depending on a goal the sequent no longer has.
    const BPR: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.prFile version="1">
<org.eventb.core.prProof name="evt/inv2/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p1" org.eventb.core.psManual="true">
<org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.prPred name="p0" org.eventb.core.predicate="x&lt;3"/>
<org.eventb.core.prPred name="p1" org.eventb.core.predicate="x=1"/>
<org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
</org.eventb.core.prProof>
<org.eventb.core.prProof name="evt/inv3/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="">
<org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.prPred name="p0" org.eventb.core.predicate="x&lt;9"/>
<org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
</org.eventb.core.prProof>
</org.eventb.core.prFile>
"#;

    fn run(bpr: Option<&str>) -> String {
        let mut files = vec![
            ScFile {
                filename: "M0.bpo".into(),
                contents: BPO.into(),
                accurate: true,
            },
            ScFile {
                filename: "M0.bps".into(),
                contents: BPS.into(),
                accurate: true,
            },
        ];
        update_statuses(&mut files, |name| {
            assert_eq!(name, "M0.bpr");
            bpr.map(str::to_string)
        });
        files[1].contents.clone()
    }

    #[test]
    fn stale_rows_get_fresh_verdicts_and_stamps() {
        let bps = run(Some(BPR));
        // The stamp-valid row keeps its exact bytes.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>"#
        ));
        // The reusable proof keeps its confidence at the new stamp,
        // manual flag copied from the proof.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="true"/>"#
        ));
        // The inapplicable proof is broken, confidence still the
        // cached copy.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv3/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="false" org.eventb.core.psBroken="true"/>"#
        ));
    }

    #[test]
    fn missing_proofs_reset_to_unattempted() {
        let bps = run(None);
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>"#
        ));
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv3/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>"#
        ));
    }

    #[test]
    fn synthesized_unattempted_rows_revive_from_stored_proofs() {
        // Every row reads unattempted at the current stamp — the shape
        // reconciliation synthesizes when the recorded .bps had no row
        // for the obligation. The status update computes missing
        // statuses from the stored proofs, so rows with a real proof
        // revive; the proofless row keeps its exact bytes.
        let all_fresh = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.psFile>
<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>
<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>
<org.eventb.core.psStatus name="evt/inv3/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>
</org.eventb.core.psFile>
"#;
        let mut files = vec![
            ScFile {
                filename: "M0.bpo".into(),
                contents: BPO.into(),
                accurate: true,
            },
            ScFile {
                filename: "M0.bps".into(),
                contents: all_fresh.into(),
                accurate: true,
            },
        ];
        update_statuses(&mut files, |_| Some(BPR.to_string()));
        let bps = &files[1].contents;
        // No stored proof for inv1: its fresh row is genuinely
        // unattempted and stays byte-exact.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="2" org.eventb.core.psManual="false"/>"#
        ));
        // inv2's stored proof still applies: discharged, manual copied.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="true"/>"#
        ));
        // inv3's stored proof no longer applies: broken.
        assert!(bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv3/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="2" org.eventb.core.psManual="false" org.eventb.core.psBroken="true"/>"#
        ));
    }

    #[test]
    fn untouched_components_round_trip_byte_exact() {
        let fresh_bps = BPS.replace(
            "org.eventb.core.poStamp=\"1\"",
            "org.eventb.core.poStamp=\"2\"",
        );
        let mut files = vec![
            ScFile {
                filename: "M0.bpo".into(),
                contents: BPO.into(),
                accurate: true,
            },
            ScFile {
                filename: "M0.bps".into(),
                contents: fresh_bps.clone(),
                accurate: true,
            },
        ];
        // The proof file is always consulted (the revival check), but
        // stamp-valid non-unattempted rows never rewrite.
        update_statuses(&mut files, |_| Some(BPR.to_string()));
        assert_eq!(files[1].contents, fresh_bps);
    }
}
