//! Corpus integration test — regenerate every model with our static checker,
//! then model-check it in ProB via the `eventb-animate` CLI and compare the
//! outcome (`success` / `invariant_violation` / `deadlock` / `state_error` /
//! `incomplete` / `load_error` / `timeout`) against the reference
//! `animate_results.tsv`.
//!
//! Requires `eventb-animate` v7.0+ and mirrors the corpus's own recording
//! procedure (`scripts/animate-all.sh` there): a bounded consistency check
//! (`--time-limit`, default 120 s) with the outcome classified from the
//! format-4 JSON report (`--json -`), plus an outer watchdog 15 s past the
//! internal limit as a process-failure fallback.
//!
//! `#[ignore]` by default: the corpus and animate executable live outside the
//! repo. Run locally:
//!
//!   cargo test -p rossi-build --test animate_corpus -- --ignored --nocapture
//!
//! Environment overrides:
//!   EVENTB_CORPUS_DIR   — external Event-B model corpus directory
//!   EVENTB_ANIMATE      — eventb-animate executable (default: eventb-animate)
//!   EVENTB_ANIMATE_TIMEOUT_SECS — internal model-check limit (default 120)
//! Relative executable paths are resolved from the workspace root.
//!
//! Per-model metadata comes from the corpus itself: column 4 of
//! `animate_results.tsv` names the machine each reference outcome was
//! recorded with (`(auto)` = let eventb-animate pick), and
//! `model_flags.tsv` flags known-broken (`defective` / `unsupported` /
//! `rodin_rejected`) and `nondeterministic` models.
//!
//! Output:
//!   target/eventb-models-regen/<model>.zip     — regenerated archives
//!   target/rossi-build-animate-corpus.tsv     — model | expected | actual | verdict
//!
//! Verdicts:
//!   match    — actual outcome matches the reference TSV
//!   known    — mismatch on a model flagged `defective` (broken source),
//!              `unsupported` (needs an Event-B extension rossi doesn't
//!              support yet, e.g. the theory plugin), `rodin_rejected`
//!              (Rodin's own static checker rejects the pristine archive, so
//!              it ships `accurate="false"` artifacts; the pristine loads
//!              only because ProB tolerates Rodin's degraded output, and the
//!              regenerated archive's outcome is undefined), or
//!              `keyword_identifier` (declares a name rossi's textual
//!              grammar cannot express, so regeneration itself fails) in
//!              the corpus `model_flags.tsv` (does not fail)
//!   improved — the pristine archive does not load (reference `load_error`:
//!              stale statically-checked files, unsupported proof
//!              annotations, …) while the regenerated archive loads and
//!              produces a checked verdict. There is no behavioral
//!              reference to regress against — content fidelity is gated by
//!              the semantic-equivalence harness (does not fail)
//!   flaky    — drift between checked outcomes (success /
//!              invariant_violation / deadlock / state_error / incomplete)
//!              on a model flagged `nondeterministic`: a bounded check over
//!              identical semantics can cut off at a different frontier
//!              because the archives' element ordering differs, changing
//!              which finding (if any) is reached within the limit (does not
//!              fail). A structural failure (`load_error` / `regen_error`)
//!              is never tolerated.
//!   regress  — unexpected mismatch (fails the test)

mod common;

use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use common::{
    Row, WaitError, collect_zips, load_expected, load_flags, load_machines, locate_corpus,
    log_hint, regen_one, resolve_program, spawn_in_group, wait_with_timeout, workspace_target,
    write_report,
};

const DEFAULT_TIMEOUT_SECS: u64 = 120;

#[test]
#[ignore]
fn animate_regenerated_corpus_matches_reference() {
    let Some(corpus) = locate_corpus() else {
        eprintln!("EVENTB_CORPUS_DIR is not set or is not a directory — nothing to do");
        return;
    };
    let Some(animate) = locate_animate() else {
        let configured =
            std::env::var("EVENTB_ANIMATE").unwrap_or_else(|_| "eventb-animate".into());
        eprintln!(
            "EVENTB_ANIMATE command `{configured}` was not found or is not executable — nothing to do"
        );
        return;
    };
    // Skip-when-unset applies to the *environment* (no corpus, no animate
    // executable); a configured corpus with a missing or malformed reference
    // file is a loud failure — silently returning here would green-light a
    // 0-model "gate".
    let reference_tsv = corpus.join("animate_results.tsv");
    let expected = load_expected(&reference_tsv).unwrap_or_else(|| {
        panic!("{} is missing or malformed", reference_tsv.display());
    });
    let machines = load_machines(&reference_tsv).unwrap_or_else(|| {
        panic!("{} is missing or malformed", reference_tsv.display());
    });
    let flags_tsv = corpus.join("model_flags.tsv");
    let flags = load_flags(&flags_tsv).unwrap_or_else(|| {
        panic!("{} is missing or malformed", flags_tsv.display());
    });

    let regen_dir = workspace_target().join("eventb-models-regen");
    std::fs::create_dir_all(&regen_dir).expect("create regen dir");
    // The internal model-check limit; the outer watchdog adds
    // [`WATCHDOG_GRACE_SECS`] on top (see `animate_one`).
    let limit = Duration::from_secs(
        std::env::var("EVENTB_ANIMATE_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_TIMEOUT_SECS),
    );

    let zips = collect_zips(&corpus).expect("read corpus");

    let has_flag = |model: &str, flag: &str| flags.get(model).is_some_and(|f| f.contains(flag));
    let mut rows = Vec::<Row>::new();
    let mut regressions = 0usize;

    for zip in &zips {
        let model = zip
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or("?")
            .to_string();
        let regen_zip = regen_dir.join(format!("{model}.zip"));
        let outcome = match regen_one(zip, &regen_zip) {
            Ok(()) => animate_one(
                &animate,
                &regen_zip,
                machines.get(model.as_str()).map(String::as_str),
                limit,
            ),
            Err(e) => Outcome::Regen(e.to_string()),
        };
        let expected_outcome = expected
            .get(&model)
            .cloned()
            .unwrap_or_else(|| "?".to_string());
        let actual_str = outcome.label();
        let matches = actual_str == expected_outcome;
        let verdict = if matches {
            "match"
        } else if has_flag(&model, "defective")
            || has_flag(&model, "unsupported")
            || has_flag(&model, "rodin_rejected")
            || has_flag(&model, "keyword_identifier")
        {
            "known"
        } else if expected_outcome == "load_error" && is_checked_verdict(actual_str) {
            // The pristine archive does not load (stale statically-checked
            // files, unsupported proof annotations, …) while the regenerated
            // one — carrying freshly generated artifacts — loads and checks.
            // There is no behavioral reference to regress against; content
            // fidelity is gated by the semantic-equivalence harness.
            "improved"
        } else if has_flag(&model, "nondeterministic")
            && is_tolerated_drift(&expected_outcome, actual_str)
        {
            "flaky"
        } else {
            regressions += 1;
            "regress"
        };
        rows.push(Row {
            model: model.clone(),
            expected: expected_outcome,
            actual: actual_str.to_string(),
            verdict: verdict.to_string(),
            notes: outcome.notes().to_string(),
        });
    }

    let report = workspace_target().join("rossi-build-animate-corpus.tsv");
    write_report(
        &report,
        &["model", "expected", "actual", "verdict", "notes"],
        &rows.iter().map(Row::to_fields).collect::<Vec<_>>(),
    );
    println!(
        "animate-corpus: {} archives, {} regressions (report: {})",
        zips.len(),
        regressions,
        report.display()
    );
    for r in rows.iter().filter(|r| r.verdict == "regress").take(20) {
        eprintln!(
            "  REGRESS  {}: expected {}, got {} — {}",
            r.model, r.expected, r.actual, r.notes
        );
    }
    assert!(
        regressions == 0,
        "{regressions} model(s) regressed (first 20 shown above)"
    );
}

#[derive(Debug, Clone)]
enum Outcome {
    Success,
    InvariantViolation,
    Deadlock,
    StateError,
    Incomplete,
    LoadError(String),
    Timeout,
    Regen(String),
}

impl Outcome {
    fn label(&self) -> &'static str {
        match self {
            Outcome::Success => "success",
            Outcome::InvariantViolation => "invariant_violation",
            Outcome::Deadlock => "deadlock",
            Outcome::StateError => "state_error",
            Outcome::Incomplete => "incomplete",
            Outcome::LoadError(_) => "load_error",
            Outcome::Timeout => "timeout",
            Outcome::Regen(_) => "regen_error",
        }
    }

    fn notes(&self) -> &str {
        match self {
            Outcome::LoadError(s) | Outcome::Regen(s) => s.as_str(),
            _ => "",
        }
    }
}

fn locate_animate() -> Option<PathBuf> {
    let configured = std::env::var("EVENTB_ANIMATE").unwrap_or_else(|_| "eventb-animate".into());
    resolve_program(&configured)
}

/// How much longer than the internal model-check limit the outer watchdog
/// waits before declaring a process failure, matching the corpus recording
/// script's 120 s limit / 135 s watchdog split.
const WATCHDOG_GRACE_SECS: u64 = 15;

fn animate_one(animate: &Path, zip: &Path, machine: Option<&str>, limit: Duration) -> Outcome {
    let mut cmd = Command::new(animate);
    cmd.arg("--time-limit")
        .arg(limit.as_secs().to_string())
        .arg("--json")
        .arg("-");
    if let Some(m) = machine {
        cmd.arg("--machine").arg(m);
    }
    cmd.arg(zip);

    cmd.stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let child = match spawn_in_group(&mut cmd) {
        Ok(c) => c,
        Err(e) => return Outcome::LoadError(format!("spawn: {e}")),
    };
    match wait_with_timeout(child, limit + Duration::from_secs(WATCHDOG_GRACE_SECS)) {
        Ok((_status, stdout, stderr)) => classify(&stdout, &stderr),
        Err(WaitError::Timeout) => Outcome::Timeout,
        Err(WaitError::Io(e)) => Outcome::LoadError(format!("wait: {e}")),
    }
}

/// A verdict the checker produced after loading the model — as opposed to
/// the structural failures (`load_error`, `regen_error`, `timeout`).
fn is_checked_verdict(outcome: &str) -> bool {
    matches!(
        outcome,
        "success" | "invariant_violation" | "deadlock" | "state_error" | "incomplete"
    )
}

/// True when both outcomes are bounded-check verdicts over the same
/// semantics — the drift the `nondeterministic` flag tolerates. A bounded
/// check of the pristine and regenerated archives can cut off at different
/// frontiers purely because the archives' element ordering differs, changing
/// which finding (if any) falls inside the explored region. A structural
/// failure (`load_error`/`regen_error`) is never tolerated here.
fn is_tolerated_drift(expected: &str, actual: &str) -> bool {
    is_checked_verdict(expected) && is_checked_verdict(actual)
}

/// Classify a finished run from its format-4 JSON report, mirroring the
/// corpus recording script (`scripts/animate-all.sh`) so the regenerated
/// archives are judged by exactly the rules the reference was recorded
/// under. A run that produced no valid report is a load error.
///
/// The exit code is deliberately not read here, even though 7.0 now names
/// the failure kind in it: these outcomes are diffed against the reference
/// TSV, so they must keep being derived the way the script that recorded it
/// derives them.
fn classify(stdout: &str, stderr: &str) -> Outcome {
    let Ok(report) = serde_json::from_str::<serde_json::Value>(stdout) else {
        let combined = format!("{stdout}\n{stderr}");
        return Outcome::LoadError(format!(
            "No valid eventb-animate JSON report. {}",
            log_hint(&combined)
        ));
    };
    let valid = report["formatVersion"] == 4
        && report["tool"] == "eventb-animate"
        && report["command"] == "check"
        && report["completion"].is_object();
    if !valid {
        return Outcome::LoadError("Unexpected eventb-animate report shape".to_string());
    }
    match report["status"].as_str() {
        Some("ok") => Outcome::Success,
        Some("violation") => match report["finding"]["category"].as_str() {
            Some("invariant_violation") => Outcome::InvariantViolation,
            Some("deadlock") => Outcome::Deadlock,
            Some("state_evaluation_error") => Outcome::StateError,
            other => Outcome::LoadError(format!(
                "Unexpected violation report ({})",
                other.unwrap_or("?")
            )),
        },
        Some("incomplete") => Outcome::Incomplete,
        Some("error") => {
            if report["completion"]["phase"] == "load" {
                Outcome::LoadError(report["message"].as_str().unwrap_or_default().to_string())
            } else {
                Outcome::Incomplete
            }
        }
        other => Outcome::LoadError(format!(
            "Unexpected report status {:?}",
            other.unwrap_or("?")
        )),
    }
}
