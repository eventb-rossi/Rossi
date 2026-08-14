//! `rossi build`: diagnostics, output writing, and output-path containment.

use crate::helpers::{
    ASCII_CONTEXT, BuildFixture, DUP_VARIABLE_MACHINE, dir_has_ext, extract_zip_to, rossi_command,
    tempdir_unique,
};

#[test]
fn build_duplicate_component_names_fail_with_eb019() {
    // `rossi build` must fail the same project `validate` fails: the EB019
    // diagnostic, exit 1, and no output written — not a zip-writer IO error
    // about colliding entry names.
    let tmp = tempdir_unique("rossi-cli-build-dup-names");
    std::fs::write(tmp.join("a.eventb"), "MACHINE M\nEND\n").unwrap();
    std::fs::write(tmp.join("b.eventb"), "MACHINE M\nEND\n").unwrap();
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            tmp.to_str().unwrap(),
            "--output",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        !output.status.success(),
        "duplicate component names must fail the build; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("[EB019]"), "stderr: {stderr}");
    assert!(
        !stderr.contains("Duplicate filename"),
        "the zip-writer error must be unreachable: {stderr}"
    );
    assert!(!out_zip.exists(), "no output may be written");

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn build_fails_on_error_diagnostics_but_still_writes_output() {
    // An error diagnostic that still leaves checked output (here EB006: a
    // constant with no typing axiom) must fail the build, while the filtered
    // output is written all the same — matching Rodin, which drops the
    // erroneous element and still produces the checked file.
    let tmp = tempdir_unique("rossi-cli-build-error-diag");
    let src = tmp.join("c.eventb");
    std::fs::write(
        &src,
        "CONTEXT c\nCONSTANTS\n    x\nAXIOMS\n    @axm1 1 = 1\nEND\n",
    )
    .unwrap();
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            src.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        !output.status.success(),
        "error diagnostics must fail the build; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("[EB006]"), "stderr: {stderr}");
    assert!(stderr.contains("error diagnostic"), "stderr: {stderr}");
    assert!(out_zip.exists(), "filtered output must still be written");
    let extracted = tmp.join("extracted");
    std::fs::create_dir_all(&extracted).unwrap();
    extract_zip_to(&out_zip, &extracted);
    assert!(
        dir_has_ext(&extracted, &["bcc"]),
        "expected the checked output (.bcc) despite the error"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn build_fails_on_circular_refines_with_context_sibling() {
    // Regression: a REFINES cycle beside a healthy context used to exit 0
    // because the context's checked file made the project look successful.
    // The cycle's EB008 error must fail the build while the context's output
    // is still written.
    let tmp = tempdir_unique("rossi-cli-build-refines-cycle");
    let src = tmp.join("src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(src.join("m.eventb"), "MACHINE m\nREFINES m\nEND\n").unwrap();
    std::fs::write(src.join("c.eventb"), ASCII_CONTEXT).unwrap();
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            src.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        !output.status.success(),
        "a dependency cycle must fail the build; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("[EB008]"), "stderr: {stderr}");
    assert!(
        out_zip.exists(),
        "the context's output must still be written"
    );
    let extracted = tmp.join("extracted");
    std::fs::create_dir_all(&extracted).unwrap();
    extract_zip_to(&out_zip, &extracted);
    assert!(
        dir_has_ext(&extracted, &["bcc"]),
        "expected the sibling context's .bcc in the built zip"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn build_fails_on_duplicate_identifier() {
    let tmp = tempdir_unique("rossi-cli-build-dup-var");
    std::fs::write(tmp.join("M.eventb"), DUP_VARIABLE_MACHINE).unwrap();
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            tmp.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        !output.status.success(),
        "a duplicate identifier must fail the build; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("[EB021]"), "stderr: {stderr}");
    assert!(
        out_zip.exists(),
        "the filtered output is still written despite the error"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[cfg(unix)]
fn symlink_dir(target: &std::path::Path, link: &std::path::Path) {
    std::fs::create_dir_all(target).unwrap();
    std::fs::create_dir_all(link.parent().unwrap()).unwrap();
    std::os::unix::fs::symlink(target, link).unwrap();
}

#[test]
fn build_directory_output_rejects_unsafe_prefixes_before_writing() {
    let cases = [
        ("parent-prefix", ["../C.buc", "safe/D.buc"]),
        ("rooted-prefix", ["/C.buc", "safe/D.buc"]),
        ("sanitized-collision", ["../C.buc", "./D.buc"]),
    ];

    for (case, entries) in cases {
        let fixture = BuildFixture::new(&entries, "out");
        let output = fixture.run();

        assert!(!output.status.success(), "{case} should be rejected");
        assert!(
            String::from_utf8_lossy(&output.stderr).contains("unsafe archive prefix"),
            "{case}: stderr={}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert!(
            !fixture.root.join("C.bcc").exists(),
            "{case} escaped output root"
        );
        assert!(
            !fixture.output.exists(),
            "{case} preflight failure must not create the output root"
        );
    }
}

#[test]
fn build_directory_output_preserves_safe_multi_project_layout() {
    let fixture = BuildFixture::new(&["A/C.buc", "B/D.buc"], "out");
    fixture.assert_success("safe multi-project build");
    assert!(fixture.output.join("A/C.bcc").exists());
    assert!(fixture.output.join("B/D.bcc").exists());
}

#[test]
fn build_zip_output_preserves_raw_archive_prefixes() {
    let fixture = BuildFixture::new(&["../C.buc", "safe/D.buc"], "out.zip");
    fixture.assert_success("archive repacking");
    let mut archive = zip::ZipArchive::new(std::fs::File::open(&fixture.output).unwrap()).unwrap();
    assert!(archive.by_name("../C.bcc").is_ok());
    assert!(archive.by_name("safe/D.bcc").is_ok());
}

#[cfg(unix)]
#[test]
fn build_directory_output_rejects_escaping_project_symlink() {
    let fixture = BuildFixture::new(&["evil/C.buc", "safe/D.buc"], "out");
    let outside = fixture.root.join("outside");
    symlink_dir(&outside, &fixture.output.join("evil"));
    let output = fixture.run();

    assert!(
        !output.status.success(),
        "escaping symlink should be rejected"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("escapes output directory"),
        "stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(!outside.join("C.bcc").exists());
    assert!(
        !fixture.output.join("safe/D.bcc").exists(),
        "preflight must reject before writing a safe sibling"
    );
}

#[cfg(unix)]
#[test]
fn build_directory_output_allows_contained_project_symlink() {
    let fixture = BuildFixture::new(&["linked/C.buc", "safe/D.buc"], "out");
    let actual = fixture.output.join("actual");
    symlink_dir(&actual, &fixture.output.join("linked"));
    fixture.assert_success("contained symlink");
    assert!(actual.join("C.bcc").exists());
    assert!(fixture.output.join("safe/D.bcc").exists());
}

#[cfg(unix)]
#[test]
fn build_directory_output_allows_symlinked_root() {
    let fixture = BuildFixture::new(&["A/C.buc", "B/D.buc"], "out");
    let actual = fixture.root.join("actual");
    symlink_dir(&actual, &fixture.output);
    fixture.assert_success("symlinked root");
    assert!(actual.join("A/C.bcc").exists());
    assert!(actual.join("B/D.bcc").exists());
}

#[test]
fn build_eventb_file_packs_sources_and_checked() {
    let tmp = tempdir_unique("rossi-cli-build-eventb");
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            "../rossi/examples/counter.eventb",
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "build from text should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(out_zip.exists());

    let extracted = tmp.join("extracted");
    std::fs::create_dir_all(&extracted).unwrap();
    extract_zip_to(&out_zip, &extracted);
    // The output must carry both the component source and our checked file,
    // just like the old export-then-build round-trip did.
    assert!(
        dir_has_ext(&extracted, &["buc", "bum"]),
        "expected the component source (.buc/.bum) in the built zip"
    );
    assert!(
        dir_has_ext(&extracted, &["bcc", "bcm"]),
        "expected the checked output (.bcc/.bcm) in the built zip"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn build_eventb_directory() {
    let tmp = tempdir_unique("rossi-cli-build-dir");
    let src = tmp.join("src");
    std::fs::create_dir_all(&src).unwrap();
    std::fs::write(src.join("c.eventb"), ASCII_CONTEXT).unwrap();
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            src.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "build from a text directory should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let extracted = tmp.join("extracted");
    std::fs::create_dir_all(&extracted).unwrap();
    extract_zip_to(&out_zip, &extracted);
    assert!(
        dir_has_ext(&extracted, &["bcc", "bcm"]),
        "expected the checked output (.bcc/.bcm) in the built zip"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn build_zip_replaces_proof_files_with_generated_ones() {
    // A rebuilt archive carries our generated .bpo (obligations) and
    // .bps (fresh unattempted statuses); the input's stale proof
    // artifacts, .bpr included, are gone.
    let tmp = tempdir_unique("rossi-cli-build-proofs");
    let out_zip = tmp.join("out.zip");

    let output = rossi_command()
        .args([
            "build",
            "../rossi/examples/traffic-light.zip",
            "--output",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");
    assert!(
        output.status.success(),
        "stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let extracted = tmp.join("out");
    extract_zip_to(&out_zip, &extracted);
    let root = extracted.join("traffic-light");
    let m0_bpo = std::fs::read_to_string(root.join("M0.bpo")).expect("M0.bpo");
    assert!(m0_bpo.contains(r#"<org.eventb.core.poSequent name="INITIALISATION/inv3/INV""#));
    let m0_bps = std::fs::read_to_string(root.join("M0.bps")).expect("M0.bps");
    assert!(m0_bps.contains(r#"<org.eventb.core.psStatus name="INITIALISATION/inv3/INV" org.eventb.core.confidence="-99" org.eventb.core.poStamp="0" org.eventb.core.psManual="false"/>"#));
    assert!(
        !root.join("M0.bpr").exists(),
        "stale proofs must be dropped"
    );

    std::fs::remove_dir_all(&tmp).ok();
}
