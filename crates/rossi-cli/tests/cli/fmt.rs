//! `rossi fmt`: Unicode/ASCII conversion, output layout, and zip normalisation.

use std::io::Read;

use crate::helpers::{
    ASCII_CONTEXT, project_descriptor, rossi_command, run_cli_with_stdin, tempdir_unique, write_zip,
};

#[test]
fn test_fmt_stdin_inverse_operator_conversion() {
    // ASCII `~` is accepted on input; `fmt` emits Unicode ∼ (U+223C) and
    // `fmt --ascii` emits `~` (U+007E).
    let source = "CONTEXT test\nCONSTANTS\n    f r\nAXIOMS\n    @axm1 r = f~\nEND\n";

    let output = run_cli_with_stdin(&["fmt", "-"], source);
    assert!(
        output.status.success(),
        "fmt - should accept ASCII ~ inverse"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("f\u{223C}"),
        "Unicode fmt should emit ∼, got: {stdout}"
    );

    let output = run_cli_with_stdin(&["fmt", "--ascii", "-"], source);
    assert!(
        output.status.success(),
        "fmt --ascii should accept ASCII ~ inverse"
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("f~"),
        "ASCII fmt should emit ~, got: {stdout}"
    );
    assert!(
        !stdout.contains('\u{223C}'),
        "ASCII fmt output must not contain U+223C"
    );
}

#[test]
fn fmt_ascii_text_to_unicode_stdout() {
    let tmp = tempdir_unique("rossi-cli-fmt-ascii");
    let file = tmp.join("c.eventb");
    std::fs::write(&file, ASCII_CONTEXT).unwrap();

    let output = rossi_command()
        .args(["fmt", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "fmt should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.contains('∈'), "expected Unicode ∈ in: {stdout}");
    assert!(stdout.contains('ℕ'), "expected Unicode ℕ in: {stdout}");

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_indent_option_changes_indentation() {
    let tmp = tempdir_unique("rossi-cli-fmt-indent");
    let file = tmp.join("c.eventb");
    std::fs::write(&file, ASCII_CONTEXT).unwrap();

    let output = rossi_command()
        .args(["fmt", "--indent", "  ", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "fmt --indent stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\n  @axm1"),
        "expected 2-space indentation in: {stdout}"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_explicit_empty_indent_is_honored() {
    // `--indent=""` means no indentation, not "follow the preset".
    let source = "CONTEXT c\nAXIOMS\n@axm1 1 = 1\nEND\n";
    let output = run_cli_with_stdin(&["fmt", "--indent=", "-"], source);
    assert!(
        output.status.success(),
        "fmt --indent= stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\n@axm1"),
        "expected un-indented axiom in: {stdout}"
    );
}

#[test]
fn fmt_check_then_in_place() {
    let tmp = tempdir_unique("rossi-cli-fmt-check");
    let file = tmp.join("c.eventb");
    std::fs::write(&file, ASCII_CONTEXT).unwrap();

    // --check on an ASCII file (canonical form is Unicode) flags it and exits non-zero.
    let checked = rossi_command()
        .args(["fmt", "--check", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");
    assert!(
        !checked.status.success(),
        "fmt --check should flag an unformatted file"
    );
    let check_out = String::from_utf8_lossy(&checked.stdout);
    assert!(
        check_out.contains("c.eventb"),
        "expected the path in --check output: {check_out}"
    );

    // -i rewrites the file in place to Unicode.
    let fixed = rossi_command()
        .args(["fmt", "-i", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");
    assert!(
        fixed.status.success(),
        "fmt -i stderr={}",
        String::from_utf8_lossy(&fixed.stderr)
    );
    let text = std::fs::read_to_string(&file).unwrap();
    assert!(
        text.contains('∈'),
        "the in-place file should now use Unicode: {text}"
    );

    // --check now passes (exit 0).
    let recheck = rossi_command()
        .args(["fmt", "--check", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");
    assert!(
        recheck.status.success(),
        "fmt --check should pass after formatting; stderr={}",
        String::from_utf8_lossy(&recheck.stderr)
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_multiple_outputs_are_flat() {
    let tmp = tempdir_unique("rossi-cli-fmt-multiple-output");
    let first = tmp.join("first");
    let second = tmp.join("second");
    std::fs::create_dir_all(&first).unwrap();
    std::fs::create_dir_all(&second).unwrap();
    let a = first.join("a.eventb");
    let b = second.join("b.eventb");
    std::fs::write(&a, ASCII_CONTEXT).unwrap();
    std::fs::write(&b, ASCII_CONTEXT).unwrap();
    let out = tmp.join("out");

    let output = rossi_command()
        .arg("fmt")
        .arg(&a)
        .arg(&b)
        .args(["-o", out.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "fmt should write unique basenames; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    for name in ["a.eventb", "b.eventb"] {
        let text = std::fs::read_to_string(out.join(name)).unwrap();
        assert!(text.contains('∈'), "expected formatted output in {name}");
    }

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_rejects_colliding_output_basenames_before_writing() {
    let tmp = tempdir_unique("rossi-cli-fmt-output-collision");
    let first = tmp.join("first");
    let second = tmp.join("second");
    std::fs::create_dir_all(&first).unwrap();
    std::fs::create_dir_all(&second).unwrap();
    let first_model = first.join("model.eventb");
    let second_model = second.join("model.eventb");
    std::fs::write(&first_model, "CONTEXT first\nEND\n").unwrap();
    std::fs::write(&second_model, "CONTEXT second\nEND\n").unwrap();
    let out = tmp.join("out");

    let output = rossi_command()
        .arg("fmt")
        .arg(&first_model)
        .arg(&second_model)
        .args(["-o", out.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");

    assert!(!output.status.success(), "colliding outputs must fail");
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("duplicate output destination") && stderr.contains("model.eventb"),
        "expected collision error; stderr={stderr}"
    );
    assert!(
        !out.exists(),
        "collision preflight must not create the output directory"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_ascii_on_rodin_zip_is_rejected() {
    let output = rossi_command()
        .args(["fmt", "--ascii", "../rossi/examples/traffic-light.zip"])
        .output()
        .expect("Failed to execute command");
    assert!(
        !output.status.success(),
        "fmt --ascii on a Rodin zip should fail"
    );
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("Unicode"),
        "expected a Unicode-required error: {stderr}"
    );
}

#[test]
fn fmt_normalizes_rodin_zip() {
    let tmp = tempdir_unique("rossi-cli-fmt-zip");
    let out_zip = tmp.join("norm.zip");

    let output = rossi_command()
        .args([
            "fmt",
            "../rossi/examples/traffic-light.zip",
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");

    assert!(
        output.status.success(),
        "fmt zip stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let mut archive = zip::ZipArchive::new(std::fs::File::open(&out_zip).unwrap()).unwrap();
    let names: Vec<String> = (0..archive.len())
        .map(|i| archive.by_index(i).unwrap().name().to_string())
        .collect();
    assert!(
        names.iter().any(|n| n.ends_with(".buc")) && names.iter().any(|n| n.ends_with(".bum")),
        "expected .buc/.bum entries in the normalized zip: {names:?}"
    );

    std::fs::remove_dir_all(&tmp).ok();
}

#[test]
fn fmt_preserves_multi_project_archive_structure() {
    // A two-project archive with a component and a non-component (proof) entry
    // per project. fmt normalises the components under their original paths,
    // leaving the per-project layout and the proof bytes intact.
    let tmp = tempdir_unique("rossi-cli-fmt-multi");
    let in_zip = tmp.join("decomp.zip");
    let out_zip = tmp.join("out.zip");

    let machine_xml = std::fs::read("../rossi/examples/counter.bum").unwrap();
    let proofs = [("A", b"PROOF-A".to_vec()), ("B", b"PROOF-B".to_vec())];
    let proj_a = project_descriptor("A");
    let proj_b = project_descriptor("B");
    write_zip(
        &in_zip,
        &[
            ("A/.project", &proj_a),
            ("A/M.bum", &machine_xml),
            ("A/M.bpr", &proofs[0].1),
            ("B/.project", &proj_b),
            ("B/M.bum", &machine_xml),
            ("B/M.bpr", &proofs[1].1),
        ],
    );

    let output = rossi_command()
        .args([
            "fmt",
            in_zip.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");
    assert!(
        output.status.success(),
        "multi-project fmt should exit 0; stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let entry_names = |path: &std::path::Path| -> Vec<String> {
        let mut a = zip::ZipArchive::new(std::fs::File::open(path).unwrap()).unwrap();
        let mut names: Vec<String> = (0..a.len())
            .map(|i| a.by_index(i).unwrap().name().to_string())
            .collect();
        names.sort();
        names
    };
    // The per-project layout (every prefix) survives unchanged.
    assert_eq!(entry_names(&in_zip), entry_names(&out_zip));

    // Non-component proof entries are byte-identical; components stay valid XML.
    let mut out = zip::ZipArchive::new(std::fs::File::open(&out_zip).unwrap()).unwrap();
    for (proj, proof) in &proofs {
        let mut buf = Vec::new();
        out.by_name(&format!("{proj}/M.bpr"))
            .unwrap()
            .read_to_end(&mut buf)
            .unwrap();
        assert_eq!(&buf, proof, "proof entry must be preserved verbatim");
        let mut xml = String::new();
        out.by_name(&format!("{proj}/M.bum"))
            .unwrap()
            .read_to_string(&mut xml)
            .unwrap();
        assert!(
            xml.contains("machineFile"),
            "component should remain a machine file"
        );
    }

    std::fs::remove_dir_all(&tmp).ok();
}

fn zip_entry_snapshot(
    bytes: &[u8],
    name: &str,
) -> (
    zip::CompressionMethod,
    Option<zip::DateTime>,
    Option<u32>,
    String,
    bool,
    Vec<u8>,
) {
    let mut archive = zip::ZipArchive::new(std::io::Cursor::new(bytes)).unwrap();
    let entry = archive.by_name(name).unwrap();
    let start = entry.data_start().unwrap() as usize;
    let end = start + entry.compressed_size() as usize;
    (
        entry.compression(),
        entry.last_modified(),
        entry.unix_mode(),
        entry.comment().to_string(),
        entry.is_dir(),
        bytes[start..end].to_vec(),
    )
}

#[test]
fn fmt_raw_copies_non_component_entries() {
    let tmp = tempdir_unique("rossi-cli-fmt-raw-copy");
    let in_zip = tmp.join("input.zip");
    let out_zip = tmp.join("output.zip");
    let timestamp = zip::DateTime::from_date_and_time(2024, 2, 6, 12, 34, 56).unwrap();
    let machine_xml = std::fs::read("../rossi/examples/counter.bum").unwrap();

    let file = std::fs::File::create(&in_zip).unwrap();
    let mut writer = zip::ZipWriter::new(file);
    writer
        .set_raw_comment(b"archive comment".to_vec().into_boxed_slice())
        .unwrap();
    let directory_options = zip::write::SimpleFileOptions::default()
        .last_modified_time(timestamp)
        .unix_permissions(0o750)
        .into_full_options()
        .with_file_comment("directory comment");
    writer
        .add_directory("project/proofs/", directory_options)
        .unwrap();
    let proof_options = zip::write::SimpleFileOptions::default()
        .compression_method(zip::CompressionMethod::Deflated)
        .last_modified_time(timestamp)
        .unix_permissions(0o640)
        .into_full_options()
        .with_file_comment("proof comment");
    writer
        .start_file("project/proofs/M.bpr", proof_options)
        .unwrap();
    std::io::Write::write_all(&mut writer, b"retained proof payload").unwrap();
    writer
        .start_file("project/M.bum", zip::write::SimpleFileOptions::default())
        .unwrap();
    std::io::Write::write_all(&mut writer, &machine_xml).unwrap();
    writer.finish().unwrap();

    let output = rossi_command()
        .args([
            "fmt",
            in_zip.to_str().unwrap(),
            "-o",
            out_zip.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");
    assert!(
        output.status.success(),
        "fmt zip stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );

    let input = std::fs::read(&in_zip).unwrap();
    let output = std::fs::read(&out_zip).unwrap();
    let input_archive = zip::ZipArchive::new(std::io::Cursor::new(&input)).unwrap();
    let output_archive = zip::ZipArchive::new(std::io::Cursor::new(&output)).unwrap();
    assert_eq!(output_archive.comment(), input_archive.comment());
    assert_eq!(
        zip_entry_snapshot(&output, "project/proofs/"),
        zip_entry_snapshot(&input, "project/proofs/")
    );
    assert_eq!(
        zip_entry_snapshot(&output, "project/proofs/M.bpr"),
        zip_entry_snapshot(&input, "project/proofs/M.bpr")
    );

    std::fs::remove_dir_all(&tmp).ok();
}

// =========================================================================
// Style preset and toggles
// =========================================================================

const STYLE_MACHINE: &str = "MACHINE m REFINES m0\nVARIABLES x y\nINVARIANTS\n@inv1 x : NAT\nEVENTS\nEVENT e ANY p WHERE @g p > 0 THEN skip END\nEND\n";

#[test]
fn fmt_style_camille_prints_camille_layout() {
    let output = run_cli_with_stdin(&["fmt", "--style", "camille", "-"], STYLE_MACHINE);
    assert!(
        output.status.success(),
        "fmt --style camille stderr={}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8_lossy(&output.stdout);
    let expected = "machine m refines m0\n\
                    \n\
                    variables x y\n\
                    \n\
                    invariants\n\
                    \x20\x20@inv1 x ∈ ℕ\n\
                    \n\
                    events\n\
                    \x20\x20event e\n\
                    \x20\x20\x20\x20any p\n\
                    \x20\x20\x20\x20where\n\
                    \x20\x20\x20\x20\x20\x20@g p > 0\n\
                    \x20\x20\x20\x20then\n\
                    \x20\x20\x20\x20\x20\x20skip\n\
                    \x20\x20end\n\
                    end";
    assert_eq!(stdout.trim_end_matches('\n'), expected, "got:\n{stdout}");
}

#[test]
fn fmt_style_rossi_matches_the_default() {
    let styled = run_cli_with_stdin(&["fmt", "--style", "rossi", "-"], STYLE_MACHINE);
    let default = run_cli_with_stdin(&["fmt", "-"], STYLE_MACHINE);
    assert!(styled.status.success() && default.status.success());
    assert_eq!(
        styled.stdout, default.stdout,
        "--style rossi must match the current default output"
    );
    let stdout = String::from_utf8_lossy(&styled.stdout);
    assert!(
        stdout.starts_with("MACHINE m\nREFINES\n    m0\nVARIABLES\n"),
        "got:\n{stdout}"
    );
}

#[test]
fn fmt_style_toggles_override_the_preset() {
    let output = run_cli_with_stdin(
        &["fmt", "--style", "camille", "--keyword-case", "upper", "-"],
        STYLE_MACHINE,
    );
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with("MACHINE m REFINES m0\n"),
        "keyword-case override, got:\n{stdout}"
    );

    let output = run_cli_with_stdin(
        &[
            "fmt",
            "--style",
            "camille",
            "--blank-between-clauses",
            "false",
            "-",
        ],
        STYLE_MACHINE,
    );
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.starts_with("machine m refines m0\nvariables x y\ninvariants\n"),
        "blank-between-clauses override, got:\n{stdout}"
    );

    let output = run_cli_with_stdin(
        &["fmt", "--style", "rossi", "--decl-lists", "inline", "-"],
        STYLE_MACHINE,
    );
    assert!(output.status.success());
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("\nVARIABLES x y\n"),
        "decl-lists override, got:\n{stdout}"
    );
}

#[test]
fn fmt_check_respects_the_selected_style() {
    let tmp = tempdir_unique("rossi-cli-fmt-style-check");
    let file = tmp.join("m.eventb");
    std::fs::write(&file, STYLE_MACHINE).unwrap();

    let formatted = rossi_command()
        .args(["fmt", "--style", "camille", "-i", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");
    assert!(
        formatted.status.success(),
        "fmt --style camille -i stderr={}",
        String::from_utf8_lossy(&formatted.stderr)
    );

    let camille_check = rossi_command()
        .args([
            "fmt",
            "--style",
            "camille",
            "--check",
            file.to_str().unwrap(),
        ])
        .output()
        .expect("Failed to execute command");
    assert!(
        camille_check.status.success(),
        "a camille-formatted file passes --check --style camille"
    );

    let default_check = rossi_command()
        .args(["fmt", "--check", file.to_str().unwrap()])
        .output()
        .expect("Failed to execute command");
    assert!(
        !default_check.status.success(),
        "a camille-formatted file fails --check under the rossi default"
    );

    std::fs::remove_dir_all(&tmp).ok();
}
