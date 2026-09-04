//! `rossi clean` — purging orphaned proofs and emptying broken ones.

use std::path::{Path, PathBuf};

use crate::helpers::{rossi_command, tempdir_unique, write_zip};

/// One obligation, `evt/inv1/INV`, with goal and hypothesis `x=1`.
const BPO: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.poFile org.eventb.core.poStamp="7">
<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.poStamp="7">
<org.eventb.core.poIdentifier name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="x=1"/>
</org.eventb.core.poPredicateSet>
<org.eventb.core.poSequent name="evt/inv1/INV" org.eventb.core.poStamp="7">
<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/P/M0.bpo|org.eventb.core.poFile#M0|org.eventb.core.poPredicateSet#ALLHYP"/>
<org.eventb.core.poPredicate name="SEQG" org.eventb.core.predicate="x=1"/>
</org.eventb.core.poSequent>
</org.eventb.core.poFile>
"#;

/// A live proof of that obligation, plus one left over from an
/// obligation the model no longer generates.
const BPR: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.prFile version="1">
<org.eventb.core.prProof name="evt/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p0" org.eventb.core.psManual="false">
<org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="hyp" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p0"/>
<org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.prPred name="p0" org.eventb.core.predicate="x=1"/>
<org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
</org.eventb.core.prProof>
<org.eventb.core.prProof name="gone/inv9/INV" org.eventb.core.confidence="1000" org.eventb.core.prFresh="" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p0" org.eventb.core.psManual="false">
<org.eventb.core.prRule name="r0" org.eventb.core.confidence="1000" org.eventb.core.prDisplay="hyp" org.eventb.core.prGoal="p0" org.eventb.core.prHyps="p0"/>
<org.eventb.core.prIdent name="x" org.eventb.core.type="ℤ"/>
<org.eventb.core.prPred name="p0" org.eventb.core.predicate="x=1"/>
<org.eventb.core.prReas name="r0" org.eventb.core.prRID="org.eventb.core.seqprover.hyp"/>
</org.eventb.core.prProof>
</org.eventb.core.prFile>
"#;

const BPS: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.psFile>
    <org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="7" org.eventb.core.psBroken="true" org.eventb.core.psManual="true"/>
</org.eventb.core.psFile>
"#;

/// A project directory holding `M0`'s obligations, proofs and (unless
/// `with_bps` is false) statuses.
fn project_dir(name: &str, with_bps: bool) -> PathBuf {
    let dir = tempdir_unique(name);
    std::fs::write(dir.join("M0.bpo"), BPO).unwrap();
    std::fs::write(dir.join("M0.bpr"), BPR).unwrap();
    if with_bps {
        std::fs::write(dir.join("M0.bps"), BPS).unwrap();
    }
    dir
}

fn run(args: &[&str]) -> (bool, String) {
    let output = rossi_command()
        .args(args)
        .output()
        .expect("Failed to execute command");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr);
    (output.status.success(), format!("{stdout}{stderr}"))
}

fn read(path: &Path) -> String {
    std::fs::read_to_string(path).unwrap_or_else(|e| panic!("read {path:?}: {e}"))
}

#[test]
fn clean_purges_a_proof_whose_obligation_is_gone() {
    let dir = project_dir("rossi-cli-clean-purge", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--purge"]);
    assert!(ok, "{out}");
    assert!(out.contains("1 orphaned purged, 1 kept"), "{out}");

    let bpr = read(&dir.join("M0.bpr"));
    assert!(!bpr.contains("gone/inv9/INV"), "{bpr}");
    assert!(bpr.contains("evt/inv1/INV"), "{bpr}");
    // The live proof keeps everything, down to its rule tree.
    assert!(bpr.contains("org.eventb.core.seqprover.hyp"), "{bpr}");
    // Purging is not the plug-in's job: statuses are untouched.
    assert_eq!(read(&dir.join("M0.bps")), BPS);
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_empties_a_selected_proof_and_its_status() {
    let dir = project_dir("rossi-cli-clean-reset", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--reset", "evt/*"]);
    assert!(ok, "{out}");
    assert!(out.contains("1 reset, 1 kept"), "{out}");

    // Rodin's emptied entry: the handle name and nothing else.
    let bpr = read(&dir.join("M0.bpr"));
    assert!(
        bpr.contains(r#"<org.eventb.core.prProof name="evt/inv1/INV"/>"#),
        "{bpr}"
    );
    // The orphan was not selected, so it survives intact.
    assert!(
        bpr.contains(r#"name="gone/inv9/INV" org.eventb.core.confidence"#),
        "{bpr}"
    );

    // Rodin's committed status: confidence -99, the obligation's stamp
    // kept, psBroken and psManual cleared.
    let bps = read(&dir.join("M0.bps"));
    assert!(
        bps.contains(
            r#"<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="7" org.eventb.core.psManual="false"/>"#
        ),
        "{bps}"
    );
    assert!(!bps.contains("psBroken"), "{bps}");
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_selects_a_whole_component() {
    let dir = project_dir("rossi-cli-clean-component", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--component", "M0"]);
    assert!(ok, "{out}");
    assert!(out.contains("2 reset, 0 kept"), "{out}");
    assert!(!read(&dir.join("M0.bpr")).contains("confidence"));
    std::fs::remove_dir_all(&dir).ok();

    // A component that is not there selects nothing.
    let dir = project_dir("rossi-cli-clean-component-miss", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--component", "M1"]);
    assert!(ok, "{out}");
    assert_eq!(read(&dir.join("M0.bpr")), BPR);
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_all_empties_every_proof() {
    let dir = project_dir("rossi-cli-clean-all", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--all"]);
    assert!(ok, "{out}");
    assert!(out.contains("2 reset, 0 kept"), "{out}");
    assert!(!read(&dir.join("M0.bpr")).contains("confidence"));
    std::fs::remove_dir_all(&dir).ok();
}

/// `--broken` acts on exactly what `rossi prove` calls broken, and
/// leaves a proof that still applies to its obligation alone.
#[test]
fn clean_broken_empties_only_the_proofs_that_no_longer_apply() {
    let dir = project_dir("rossi-cli-clean-broken", true);
    // A proof recorded against a goal the obligation no longer has.
    let broken = BPR.replace(r#"predicate="x=1""#, r#"predicate="x=2""#);
    std::fs::write(dir.join("M0.bpr"), broken).unwrap();

    let (ok, before) = run(&["prove", "-v", dir.to_str().unwrap()]);
    assert!(!ok, "{before}");
    assert!(before.contains("evt/inv1/INV: broken"), "{before}");

    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--broken"]);
    assert!(ok, "{out}");
    assert!(out.contains("1 reset"), "{out}");

    let (ok, after) = run(&["prove", "-v", dir.to_str().unwrap()]);
    assert!(ok, "{after}");
    assert!(after.contains("evt/inv1/INV: unattempted"), "{after}");
    assert!(after.contains("0 broken"), "{after}");
    std::fs::remove_dir_all(&dir).ok();
}

/// A proof this reader cannot represent is not a broken proof. Most
/// are an older storage vintage Rodin opens perfectly well — 23% of
/// the models collection's 68k stored proofs — so `--broken` reports
/// them and leaves them alone rather than destroying working proofs
/// over a gap in rossi.
#[test]
fn clean_broken_leaves_a_proof_rossi_cannot_read_alone() {
    let dir = tempdir_unique("rossi-cli-clean-unsupported");
    // `prGoal` names an interned predicate the proof does not carry,
    // so the dependency read cannot resolve it.
    let unreadable = BPR.replace(r#"prGoal="p0""#, r#"prGoal="p9""#);
    std::fs::write(dir.join("M0.bpo"), BPO).unwrap();
    std::fs::write(dir.join("M0.bpr"), &unreadable).unwrap();

    let (_, prove) = run(&["prove", "-v", dir.to_str().unwrap()]);
    assert!(prove.contains("evt/inv1/INV: unsupported"), "{prove}");

    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--broken"]);
    assert!(ok, "{out}");
    assert!(out.contains("0 reset"), "{out}");
    assert!(
        out.contains("proof(s) rossi cannot read, left alone"),
        "{out}"
    );
    assert_eq!(read(&dir.join("M0.bpr")), unreadable);
    std::fs::remove_dir_all(&dir).ok();
}

/// A `.bpr` left with no proofs goes only when no status file is
/// beside it — Rodin's `noProofNoPS` rule.
#[test]
fn clean_removes_an_emptied_proof_file_only_without_a_status_file() {
    // Obligations that name neither stored proof, so purging empties
    // the file completely.
    let orphaned = BPO.replace("evt/inv1/INV", "other/inv1/INV");

    let with = tempdir_unique("rossi-cli-clean-keepfile");
    std::fs::write(with.join("M0.bpo"), &orphaned).unwrap();
    std::fs::write(with.join("M0.bpr"), BPR).unwrap();
    std::fs::write(with.join("M0.bps"), BPS).unwrap();
    let (ok, out) = run(&["clean", with.to_str().unwrap(), "--purge"]);
    assert!(ok, "{out}");
    assert!(out.contains("2 orphaned purged, 0 kept"), "{out}");
    assert!(
        with.join("M0.bpr").exists(),
        "a status file beside it keeps the emptied proof file: {out}"
    );
    std::fs::remove_dir_all(&with).ok();

    let without = tempdir_unique("rossi-cli-clean-dropfile");
    std::fs::write(without.join("M0.bpo"), &orphaned).unwrap();
    std::fs::write(without.join("M0.bpr"), BPR).unwrap();
    let (ok, out) = run(&["clean", without.to_str().unwrap(), "--purge"]);
    assert!(ok, "{out}");
    assert!(out.contains("file removed"), "{out}");
    assert!(!without.join("M0.bpr").exists(), "{out}");
    std::fs::remove_dir_all(&without).ok();
}

#[test]
fn clean_check_reports_without_writing_and_exits_nonzero() {
    let dir = project_dir("rossi-cli-clean-check", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--purge", "--check"]);
    assert!(
        !ok,
        "--check should exit nonzero when something would change"
    );
    assert!(out.contains("1 orphaned purged"), "{out}");
    assert!(out.contains("nothing written"), "{out}");
    assert_eq!(read(&dir.join("M0.bpr")), BPR);

    // Nothing to do: --check succeeds.
    let (ok, out) = run(&[
        "clean",
        dir.to_str().unwrap(),
        "--reset",
        "nomatch",
        "--check",
    ]);
    assert!(ok, "{out}");
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_output_leaves_the_input_alone() {
    let dir = project_dir("rossi-cli-clean-out", true);
    let out_dir = dir.with_extension("cleaned");
    let (ok, out) = run(&[
        "clean",
        dir.to_str().unwrap(),
        "--purge",
        "-o",
        out_dir.to_str().unwrap(),
    ]);
    assert!(ok, "{out}");
    assert_eq!(read(&dir.join("M0.bpr")), BPR);
    assert!(!read(&out_dir.join("M0.bpr")).contains("gone/inv9/INV"));
    // The copy is a whole project, not only the file that changed.
    assert_eq!(read(&out_dir.join("M0.bpo")), BPO);
    std::fs::remove_dir_all(&out_dir).ok();

    // A run that changes nothing still owes the caller the copy it
    // asked for.
    let (ok, out) = run(&[
        "clean",
        dir.to_str().unwrap(),
        "--reset",
        "nomatch",
        "-o",
        out_dir.to_str().unwrap(),
    ]);
    assert!(ok, "{out}");
    assert_eq!(read(&out_dir.join("M0.bpr")), BPR);
    std::fs::remove_dir_all(&dir).ok();
    std::fs::remove_dir_all(&out_dir).ok();
}

/// Writing into the project being cleaned would walk what it is still
/// copying.
#[test]
fn clean_refuses_an_output_inside_the_input() {
    let dir = project_dir("rossi-cli-clean-out-inside", true);
    let inside = dir.join("cleaned");
    let (ok, out) = run(&[
        "clean",
        dir.to_str().unwrap(),
        "--purge",
        "-o",
        inside.to_str().unwrap(),
    ]);
    assert!(!ok, "{out}");
    assert!(out.contains("inside the project being cleaned"), "{out}");
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_rewrites_an_archive_and_keeps_its_other_entries() {
    let tmp = tempdir_unique("rossi-cli-clean-zip");
    let zip = tmp.join("P.zip");
    write_zip(
        &zip,
        &[
            ("P/M0.bpo", BPO.as_bytes()),
            ("P/M0.bpr", BPR.as_bytes()),
            ("P/M0.bps", BPS.as_bytes()),
            ("P/notes.txt", b"keep me"),
        ],
    );
    let (ok, out) = run(&["clean", zip.to_str().unwrap(), "--purge"]);
    assert!(ok, "{out}");
    assert!(out.contains("1 orphaned purged, 1 kept"), "{out}");

    let dest = tmp.join("x");
    crate::helpers::extract_zip_to(&zip, &dest);
    assert!(!read(&dest.join("P/M0.bpr")).contains("gone/inv9/INV"));
    assert_eq!(read(&dest.join("P/notes.txt")), "keep me");
    assert_eq!(read(&dest.join("P/M0.bpo")), BPO);
    std::fs::remove_dir_all(&tmp).ok();
}

/// Without obligations to compare against, every proof would read as
/// an orphan; purging declines rather than discarding the lot.
#[test]
fn clean_will_not_purge_a_proof_file_with_no_obligations() {
    let dir = tempdir_unique("rossi-cli-clean-nobpo");
    std::fs::write(dir.join("M0.bpr"), BPR).unwrap();
    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--purge"]);
    assert!(ok, "{out}");
    assert!(out.contains("no .bpo alongside it"), "{out}");
    assert_eq!(read(&dir.join("M0.bpr")), BPR);
    std::fs::remove_dir_all(&dir).ok();
}

/// A damaged `.bpo` must stop the run, not read as "every proof here
/// is an orphan" — that would delete the lot.
#[test]
fn clean_refuses_to_purge_against_a_damaged_bpo() {
    let dir = project_dir("rossi-cli-clean-bad-bpo", true);
    std::fs::write(dir.join("M0.bpo"), &BPO[..BPO.len() / 2]).unwrap();

    let (ok, out) = run(&["clean", dir.to_str().unwrap(), "--purge"]);
    assert!(!ok, "{out}");
    assert!(out.contains("M0.bpo"), "{out}");
    assert_eq!(read(&dir.join("M0.bpr")), BPR);
    std::fs::remove_dir_all(&dir).ok();
}

#[test]
fn clean_needs_something_to_do() {
    let dir = project_dir("rossi-cli-clean-noop", true);
    let (ok, out) = run(&["clean", dir.to_str().unwrap()]);
    assert!(!ok, "{out}");
    assert!(out.contains("nothing to do"), "{out}");
    std::fs::remove_dir_all(&dir).ok();
}
