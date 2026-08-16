//! `rossi export --build` / `--proofs`: generated files, proof carry, and
//! exit gating.

use std::path::{Path, PathBuf};

use crate::helpers::{
    assert_cli_ok, dir_has_ext, extract_zip_to, run_cli, run_cli_with_stdin, tempdir_unique,
    zip_entry_bytes, zip_entry_names,
};

const CTX: &str = "CONTEXT Ctx\nCONSTANTS\n    cap\nAXIOMS\n    @axm1 cap = 10\nEND\n";

const MACHINE: &str = "MACHINE M0\nSEES\n    Ctx\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x : NAT\n    @inv2 x <= cap\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        x := 0\n    END\n\n    EVENT inc\n    WHERE\n        @grd1 x < cap\n    THEN\n        x := x + 1\n    END\nEND\n";

/// Write the context + machine fixture into a fresh source directory.
fn source_dir(prefix: &str) -> PathBuf {
    let tmp = tempdir_unique(prefix);
    std::fs::write(tmp.join("Ctx.eventb"), CTX).unwrap();
    std::fs::write(tmp.join("M0.eventb"), MACHINE).unwrap();
    tmp
}

/// A minimal single-machine project for the multi-project fixtures.
fn simple_machine(name: &str) -> String {
    format!(
        "MACHINE {name}\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x : NAT\nEVENTS\n    EVENT INITIALISATION\n    THEN\n        x := 0\n    END\nEND\n"
    )
}

/// A multi-project source tree: `<tmp>/models/{A,B}` holding machines MA/MB.
/// Returns `(tmp, models_root)`.
fn multi_source_dir(prefix: &str) -> (PathBuf, PathBuf) {
    let tmp = tempdir_unique(prefix);
    let root = tmp.join("models");
    for (dir, name) in [("A", "MA"), ("B", "MB")] {
        let sub = root.join(dir);
        std::fs::create_dir_all(&sub).unwrap();
        std::fs::write(sub.join(format!("{name}.eventb")), simple_machine(name)).unwrap();
    }
    (tmp, root)
}

/// The LSP shared-workspace layout: text in `<root>/model`, proofs in
/// `<root>/.rossi/rodin/model`. Returns `(root, model_dir, project_dir)`.
fn workspace_layout(prefix: &str) -> (PathBuf, PathBuf, PathBuf) {
    let root = tempdir_unique(prefix);
    let model = root.join("model");
    std::fs::create_dir_all(&model).unwrap();
    std::fs::write(model.join("Ctx.eventb"), CTX).unwrap();
    std::fs::write(model.join("M0.eventb"), MACHINE).unwrap();
    let project = root.join(".rossi").join("rodin").join("model");
    std::fs::create_dir_all(&project).unwrap();
    (root, model, project)
}

fn export(args: &[&str]) -> std::process::Output {
    let mut full = vec!["export"];
    full.extend_from_slice(args);
    run_cli(&full)
}

#[test]
fn export_build_zip_contains_generated_files() {
    let tmp = source_dir("rossi-cli-export-build-zip");
    let out_zip = tmp.join("model.zip");

    let output = export(&[
        "--build",
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "export --build should succeed");

    let names = zip_entry_names(&out_zip);
    for expected in [
        ".project", "Ctx.buc", "M0.bum", "Ctx.bcc", "M0.bcm", "M0.bpo", "M0.bps",
    ] {
        assert!(
            names.contains(&expected.to_string()),
            "missing {expected} in {names:?}"
        );
    }
    // The embedded project name comes from the output stem, same as a plain
    // export, so handle URIs and descriptor agree.
    let descriptor = String::from_utf8(zip_entry_bytes(&out_zip, ".project")).unwrap();
    assert!(descriptor.contains("<name>model</name>"), "{descriptor}");
    let bpo = String::from_utf8(zip_entry_bytes(&out_zip, "M0.bpo")).unwrap();
    assert!(bpo.contains("org.eventb.core.poSequent"), "{bpo}");

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_build_dir_writes_generated_files() {
    let tmp = source_dir("rossi-cli-export-build-dir");
    let out_dir = tmp.join("out");

    let output = export(&[
        "--build",
        tmp.to_str().unwrap(),
        "-o",
        out_dir.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "export --build to a directory should succeed");

    assert!(out_dir.join(".project").is_file());
    for ext in ["buc", "bum", "bcc", "bcm", "bpo", "bps"] {
        assert!(
            dir_has_ext(&out_dir, &[ext]),
            "missing .{ext} in loose output"
        );
    }

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_build_error_diagnostics_write_then_exit_nonzero() {
    // Mirroring `rossi build`: an error diagnostic that still leaves checked
    // output (here EB006: a constant with no typing axiom) fails the export,
    // but the filtered output is written all the same.
    let tmp = tempdir_unique("rossi-cli-export-build-error");
    std::fs::write(
        tmp.join("c.eventb"),
        "CONTEXT c\nCONSTANTS\n    x\nAXIOMS\n    @axm1 1 = 1\nEND\n",
    )
    .unwrap();
    let out_zip = tmp.join("out.zip");

    let output = export(&[
        "--build",
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert!(
        !output.status.success(),
        "error diagnostics must fail export --build"
    );
    assert!(out_zip.is_file(), "the output must still be written");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("[EB006]"), "stderr: {stderr}");
    assert!(stderr.contains("error diagnostic"), "stderr: {stderr}");

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_build_duplicate_names_write_nothing() {
    let tmp = tempdir_unique("rossi-cli-export-build-dup");
    std::fs::write(tmp.join("a.eventb"), "MACHINE M\nEND\n").unwrap();
    std::fs::write(tmp.join("b.eventb"), "MACHINE M\nEND\n").unwrap();
    let out_zip = tmp.join("out.zip");

    let output = export(&[
        "--build",
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert!(
        !output.status.success(),
        "duplicate component names must fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("EB019"), "stderr: {stderr}");
    assert!(
        !out_zip.exists(),
        "nothing may be written on an outright failure"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_proofs_implies_build() {
    let tmp = source_dir("rossi-cli-export-proofs-implies");
    let proof_dir = tmp.join("proofs");
    std::fs::create_dir_all(&proof_dir).unwrap();
    let out_zip = tmp.join("out.zip");

    let output = export(&[
        &format!("--proofs={}", proof_dir.display()),
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "--proofs without --build should still build");
    let names = zip_entry_names(&out_zip);
    assert!(names.contains(&"M0.bcm".to_string()), "{names:?}");

    std::fs::remove_dir_all(&tmp).ok();
}

/// Export `--build` once, extract the archive, and return the extraction —
/// a ready-made local Rodin project holding fresh `.bpo`/`.bps`.
fn built_project_dir(tmp: &Path) -> PathBuf {
    let first_zip = tmp.join("first.zip");
    let output = export(&[
        "--build",
        tmp.to_str().unwrap(),
        "-o",
        first_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "the seeding export --build should succeed");
    let extracted = tmp.join("rodin-project");
    extract_zip_to(&first_zip, &extracted);
    extracted
}

/// Flip the first fresh status row to a confident one, asserting the edit
/// applied so the carry assertions cannot pass vacuously.
fn discharge_first_status(text: &str) -> String {
    let out = text.replacen(
        r#"org.eventb.core.confidence="-99""#,
        r#"org.eventb.core.confidence="1000""#,
        1,
    );
    assert_ne!(out, text, "a fresh status row must be present to doctor");
    out
}

#[test]
fn export_proofs_dir_carries_statuses_and_bpr() {
    let tmp = source_dir("rossi-cli-export-proofs-dir");
    let project = built_project_dir(&tmp);

    let bps = std::fs::read_to_string(project.join("M0.bps")).unwrap();
    std::fs::write(project.join("M0.bps"), discharge_first_status(&bps)).unwrap();
    std::fs::write(project.join("M0.bpr"), b"opaque proof bytes").unwrap();

    let out_zip = tmp.join("out.zip");
    let output = export(&[
        &format!("--proofs={}", project.display()),
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "export --proofs=DIR should succeed");

    assert_eq!(
        zip_entry_bytes(&out_zip, "M0.bpr"),
        b"opaque proof bytes",
        "proofs must be carried byte-exact"
    );
    let out_bps = String::from_utf8(zip_entry_bytes(&out_zip, "M0.bps")).unwrap();
    assert!(
        out_bps.contains(r#"org.eventb.core.confidence="1000""#),
        "the doctored status must carry over: {out_bps}"
    );
    assert_eq!(
        zip_entry_bytes(&out_zip, "M0.bpo"),
        std::fs::read(project.join("M0.bpo")).unwrap(),
        "an unchanged model must reproduce the previous .bpo byte-exact"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_proofs_zip_source() {
    let tmp = source_dir("rossi-cli-export-proofs-zip");
    let project = built_project_dir(&tmp);
    let bps = std::fs::read_to_string(project.join("M0.bps")).unwrap();
    std::fs::write(project.join("M0.bps"), discharge_first_status(&bps)).unwrap();

    // Pack the doctored project as a zip and use it as the proof source.
    let source_zip = tmp.join("source.zip");
    let entries: Vec<(String, Vec<u8>)> = ["M0.bpo", "M0.bps"]
        .iter()
        .map(|n| (n.to_string(), std::fs::read(project.join(n)).unwrap()))
        .collect();
    let borrowed: Vec<(&str, &[u8])> = entries
        .iter()
        .map(|(n, b)| (n.as_str(), b.as_slice()))
        .collect();
    crate::helpers::write_zip(&source_zip, &borrowed);

    let out_zip = tmp.join("out.zip");
    let output = export(&[
        &format!("--proofs={}", source_zip.display()),
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "export --proofs=FILE.zip should succeed");
    let out_bps = String::from_utf8(zip_entry_bytes(&out_zip, "M0.bps")).unwrap();
    assert!(
        out_bps.contains(r#"org.eventb.core.confidence="1000""#),
        "{out_bps}"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_proofs_bare_next_to_inputs() {
    let tmp = source_dir("rossi-cli-export-proofs-bare");
    std::fs::write(tmp.join("M0.bpr"), b"local proof").unwrap();
    let out_zip = tmp.join("out.zip");

    let output = export(&[
        "--proofs",
        tmp.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "bare --proofs should scan next to the inputs");
    assert_eq!(zip_entry_bytes(&out_zip, "M0.bpr"), b"local proof");

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_proofs_bare_workspace_convention() {
    // Bare --proofs finds the LSP's shared-workspace project by walking up
    // from the input directory.
    let (root, model, project) = workspace_layout("rossi-cli-export-proofs-workspace");
    std::fs::write(project.join("M0.bpr"), b"workspace proof").unwrap();

    let out_zip = root.join("out.zip");
    let output = export(&[
        "--proofs",
        model.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(
        &output,
        "bare --proofs should find the .rossi/rodin project",
    );
    assert_eq!(zip_entry_bytes(&out_zip, "M0.bpr"), b"workspace proof");

    std::fs::remove_dir_all(&root).ok();
}

#[test]
fn export_proofs_precedence_next_to_inputs_wins() {
    let (root, model, project) = workspace_layout("rossi-cli-export-proofs-precedence");
    std::fs::write(model.join("M0.bpr"), b"local proof").unwrap();
    std::fs::write(project.join("M0.bpr"), b"workspace proof").unwrap();

    let out_zip = root.join("out.zip");
    let output = export(&[
        "--proofs",
        model.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "bare --proofs with both locations should succeed");
    assert_eq!(
        zip_entry_bytes(&out_zip, "M0.bpr"),
        b"local proof",
        "next-to-inputs must win over the workspace copy"
    );

    std::fs::remove_dir_all(&root).ok();
}

#[test]
fn export_proofs_bare_stdin_errors() {
    let output = run_cli_with_stdin(&["export", "-", "--proofs", "-o", "unused.zip"], CTX);
    assert!(
        !output.status.success(),
        "bare --proofs must reject stdin input"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--proofs=PATH"), "stderr: {stderr}");
    assert!(!Path::new("unused.zip").exists());
}

#[test]
fn export_multi_project_build() {
    let (tmp, root) = multi_source_dir("rossi-cli-export-build-multi");
    let out_zip = tmp.join("out.zip");

    let output = export(&[
        "--build",
        root.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "multi-project export --build should succeed");
    let names = zip_entry_names(&out_zip);
    for expected in [
        "A/.project",
        "A/MA.bum",
        "A/MA.bcm",
        "B/.project",
        "B/MB.bcm",
    ] {
        assert!(
            names.contains(&expected.to_string()),
            "missing {expected} in {names:?}"
        );
    }

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn export_multi_project_proofs_path_scopes_by_name() {
    let (tmp, root) = multi_source_dir("rossi-cli-export-proofs-multi");
    let proofs = tmp.join("proofs");
    std::fs::create_dir_all(proofs.join("A")).unwrap();
    std::fs::write(proofs.join("A").join("MA.bpr"), b"proof for A").unwrap();

    let out_zip = tmp.join("out.zip");
    let output = export(&[
        &format!("--proofs={}", proofs.display()),
        root.to_str().unwrap(),
        "-o",
        out_zip.to_str().unwrap(),
    ]);
    assert_cli_ok(&output, "multi-project --proofs=DIR should succeed");
    let names = zip_entry_names(&out_zip);
    assert!(names.contains(&"A/MA.bpr".to_string()), "{names:?}");
    assert!(
        !names
            .iter()
            .any(|n| n.starts_with("B/") && n.ends_with(".bpr")),
        "project B has no proofs to carry: {names:?}"
    );

    std::fs::remove_dir_all(&tmp).ok();
}
