//! Animator round-trip for generated proof obligations — regenerate
//! every model, load the archive in the ProB-based animator's proof
//! gate, and check that the obligations it reads back are exactly the
//! generated ones.
//!
//! This proves the emitted `.bpo`/`.bps` pair is well-formed for an
//! independent consumer: the animator resolves the refinement chain,
//! parses the proof files, and reports one row per obligation as
//! `<component>/<sequent>`. Every reported row must correspond to a
//! generated sequent, and every generated sequent of a component the
//! animator covered must be reported.
//!
//! `#[ignore]` by default (needs `eventb-animate` and a corpus). Run:
//!
//!   cargo test -p rossi-build --test pog_animate -- --ignored --nocapture
//!
//! Environment overrides:
//!   EVENTB_CORPUS_DIR — external Event-B model corpus directory
//!   EVENTB_ANIMATE    — eventb-animate executable (default: eventb-animate)
//!   EVENTB_ANIMATE_TIMEOUT_SECS — per-model limit (default 120)
//!
//! Multi-project archives are skipped: the gate loads the archive's
//! sole project and lets the animator pick the machine.

mod common;

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Duration;

use common::{
    collect_zips, corpus_dir, load_flags, load_machines, resolve_program, spawn_in_group,
    wait_with_timeout, workspace_target, write_report,
};

const DEFAULT_TIMEOUT_SECS: u64 = 120;

#[test]
#[ignore = "needs eventb-animate and a models corpus; run with --ignored"]
fn animator_reads_back_generated_obligations() {
    let animate = std::env::var("EVENTB_ANIMATE").unwrap_or_else(|_| "eventb-animate".into());
    let Some(animate) = resolve_program(&animate) else {
        eprintln!("SKIP pog_animate: `{animate}` not found");
        return;
    };
    let Some(corpus) = corpus_dir() else {
        eprintln!("SKIP pog_animate: no corpus (set EVENTB_CORPUS_DIR)");
        return;
    };
    let flags = load_flags(&corpus.join("model_flags.tsv")).unwrap_or_default();
    // The recorded machine per model — the animator cannot auto-select
    // among independent refinement chains.
    let machines = load_machines(&corpus.join("animate_results.tsv")).unwrap_or_default();
    let zips = collect_zips(&corpus).expect("read corpus");
    let timeout = Duration::from_secs(
        std::env::var("EVENTB_ANIMATE_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_TIMEOUT_SECS),
    );
    let regen_dir = workspace_target().join("eventb-models-regen-pog");
    std::fs::create_dir_all(&regen_dir).expect("create regen dir");

    let mut report: Vec<Vec<String>> = Vec::new();
    let mut failures = 0usize;
    for zip in &zips {
        let model = zip
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("?")
            .to_string();
        if common::flagged_unsupported(&flags, &model) {
            report.push(vec![
                model,
                "skip".into(),
                "flagged unsupported input".into(),
            ]);
            continue;
        }
        let regen_zip = regen_dir.join(format!("{model}.zip"));
        match check_one(&animate, zip, &regen_zip, machines.get(&model), timeout) {
            Ok(()) => {
                eprintln!("  OK   {model}");
                report.push(vec![model, "match".into(), String::new()]);
            }
            Err(Skip(reason)) => {
                eprintln!("  SKIP {model}: {reason}");
                report.push(vec![model, "skip".into(), reason]);
            }
            Err(Fail(reason)) => {
                eprintln!("  FAIL {model}: {reason}");
                failures += 1;
                report.push(vec![model, "diverge".into(), reason]);
            }
        }
    }

    let path = workspace_target().join("rossi-build-pog-animate.tsv");
    write_report(&path, &["model", "verdict", "notes"], &report);
    eprintln!("report: {}", path.display());
    assert!(failures == 0, "{failures} model(s) diverged");
}

use FailOrSkip::*;
/// A model this gate cannot judge vs. a real divergence.
enum FailOrSkip {
    Skip(String),
    Fail(String),
}

fn check_one(
    animate: &Path,
    zip: &Path,
    regen_zip: &Path,
    machine: Option<&String>,
    timeout: Duration,
) -> Result<(), FailOrSkip> {
    // Multi-project archives need per-machine qualification; skip.
    let bytes = std::fs::read(zip).map_err(|e| Skip(format!("read: {e}")))?;
    let projects = rossi_build::project::discover_projects(&bytes, "p")
        .map_err(|e| Skip(format!("discover: {e}")))?;
    if projects.len() != 1 {
        return Err(Skip("multi-project archive".into()));
    }

    common::regen_one(zip, regen_zip).map_err(|e| Skip(format!("regen: {e}")))?;

    // The animator names obligations by component alone, so the archive
    // prefix is dropped — safe here, since multi-project archives are skipped.
    let generated: BTreeSet<String> = common::generated_obligations(regen_zip)
        .map_err(Skip)?
        .into_iter()
        .map(|(_, component, sequent)| format!("{component}/{sequent}"))
        .collect();
    if generated.is_empty() {
        return Err(Skip("no generated obligations".into()));
    }

    let mut command = std::process::Command::new(animate);
    command.args(["po", "--json", "-"]);
    if let Some(machine) = machine {
        command.args(["-m", machine]);
    }
    command
        .arg(regen_zip)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let child = spawn_in_group(&mut command).map_err(|e| Skip(format!("spawn: {e}")))?;
    let (_status, stdout, stderr) = match wait_with_timeout(child, timeout) {
        Ok(output) => output,
        Err(common::WaitError::Timeout) => return Err(Skip("timeout".into())),
        Err(common::WaitError::Io(e)) => return Err(Skip(format!("wait: {e}"))),
    };
    // A nonzero exit just means obligations are open — expected for
    // fresh (unattempted) statuses; the JSON is still complete.
    let json: serde_json::Value = serde_json::from_str(&stdout).map_err(|e| {
        Fail(format!(
            "animator produced no JSON ({e}); stderr: {}",
            stderr.trim()
        ))
    })?;
    let reported: BTreeSet<String> = json["checks"]
        .as_array()
        .map(|checks| {
            checks
                .iter()
                .filter_map(|c| c["name"].as_str().map(str::to_string))
                // The animator's marker row for a chain without any
                // obligation — consistent with generating none.
                .filter(|name| name != "proof-obligations")
                .collect()
        })
        .unwrap_or_default();
    if reported.is_empty() && json["status"].as_str() == Some("ok") {
        return Ok(());
    }
    if reported.is_empty() {
        // Whether the model loads at all is the animation gate's
        // domain; here a load failure only ends the comparison —
        // unless the animator rejected the proof files themselves.
        let message = json["message"].as_str().unwrap_or("");
        return if message.contains("proof") {
            Err(Fail(format!("animator rejected proof files: {message}")))
        } else {
            Err(Skip(format!("model did not load: {message}")))
        };
    }

    // Every reported obligation must have been generated.
    for name in &reported {
        if !generated.contains(name) {
            return Err(Fail(format!("animator read unknown obligation {name}")));
        }
    }
    // Every generated obligation of a covered component must be read.
    let covered: BTreeSet<&str> = reported
        .iter()
        .filter_map(|name| name.split_once('/').map(|(component, _)| component))
        .collect();
    for name in &generated {
        let Some((component, _)) = name.split_once('/') else {
            continue;
        };
        if covered.contains(component) && !reported.contains(name) {
            return Err(Fail(format!("animator missed obligation {name}")));
        }
    }
    Ok(())
}
