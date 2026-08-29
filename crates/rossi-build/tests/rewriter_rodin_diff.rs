//! Live-oracle gate for the automatic rewriter — feed the same corpus
//! predicates to a reference rewriter (L5) and to rossi's,
//! and require the fixpoint results to be equal.
//!
//! Typed predicates are harvested from the corpus `.bpo` obligations
//! (goals and hypotheses of loadable sequents), printed in the
//! storage spelling and parsed back, so both sides start from the
//! identical print→parse-normal formula. The reference side runs
//! `$RODIN_HEADLESS rewrite-oracle <requests>` — one
//! `typenv TAB predicate` line per sample, answered by
//! `OK TAB result TAB rules` or `ERR TAB message` — and the returned
//! predicate is parsed in the same environment and compared
//! alpha-equivalently against `auto_rewrite_fixpoint` (the gate).
//! The fired rule names the reference traces are aggregated into a
//! histogram (measured only: rossi does not name its rules, and its
//! auto-flattening steps leave no trace at all).
//!
//! Samples with a unary minus directly under `∗`, `÷`, `mod` or `^`
//! are skipped: the two parsers group that spelling differently
//! (the reference leading minus takes the whole multiplicative term,
//! while rossi binds it to the adjacent operand), so no printed request
//! means the same formula to both sides. Aligning the parser is
//! tracked separately.
//!
//! `#[ignore]` by default (needs a corpus and a reference build). Run:
//!
//!   RODIN_HEADLESS=/path/to/wrapper \
//!   cargo test --release -p rossi-build --test rewriter_rodin_diff -- --ignored --nocapture
//!
//! Environment overrides:
//!   EVENTB_CORPUS_DIR — external Event-B model corpus directory
//!   ROSSI_REWRITE_SAMPLES — total predicates sampled (default 5000)
//!   ROSSI_REWRITE_TIMEOUT_SECS — oracle run limit (default 3600)

mod common;

use std::collections::{BTreeMap, BTreeSet};
use std::io::Read;
use std::path::Path;
use std::time::Duration;

use common::{
    collect_zips, corpus_dir, flagged_unsupported, load_flags, spawn_in_group, wait_with_timeout,
    workspace_target, write_report,
};
use rossi::formula::{Predicate, SealedTypeEnvironment};
use rossi::pretty::PrettyPrinter;
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::reasoners::auto_rewrite_fixpoint;

const DEFAULT_SAMPLES: usize = 5000;
const DEFAULT_TIMEOUT_SECS: u64 = 3600;

/// Problems reported before truncation.
const MAX_PROBLEMS: usize = 10;

/// One harvested request: the line sent to the oracle plus the parsed
/// forms rossi rewrites and compares in.
struct Sample {
    model: String,
    line: String,
    pred: Predicate,
    env: SealedTypeEnvironment,
}

#[test]
#[ignore = "needs a reference rewrite oracle and a models corpus; run with --ignored"]
fn auto_rewriter_matches_rodin_on_corpus_predicates() {
    let Ok(rodin) = std::env::var("RODIN_HEADLESS") else {
        eprintln!("SKIP rewriter_rodin_diff: set RODIN_HEADLESS to a rodin-headless command");
        return;
    };
    let Some(corpus) = corpus_dir() else {
        eprintln!("SKIP rewriter_rodin_diff: no corpus (set EVENTB_CORPUS_DIR)");
        return;
    };
    let samples: usize = std::env::var("ROSSI_REWRITE_SAMPLES")
        .ok()
        .and_then(|s| s.parse().ok())
        .unwrap_or(DEFAULT_SAMPLES);
    let timeout = Duration::from_secs(
        std::env::var("ROSSI_REWRITE_TIMEOUT_SECS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(DEFAULT_TIMEOUT_SECS),
    );
    let flags = load_flags(&corpus.join("model_flags.tsv")).unwrap_or_default();
    let zips = collect_zips(&corpus).expect("read corpus");

    // Round-robin across models so no archive dominates the sample.
    let mut per_model: Vec<Vec<Sample>> = Vec::new();
    let mut seen = BTreeSet::new();
    let per_model_cap = samples.div_ceil(8).max(1);
    for zip in &zips {
        let model = zip
            .file_stem()
            .and_then(|s| s.to_str())
            .unwrap_or_default()
            .to_string();
        if flagged_unsupported(&flags, &model) {
            continue;
        }
        match harvest(zip, &model, per_model_cap, &mut seen) {
            Ok(found) if !found.is_empty() => per_model.push(found),
            Ok(_) => {}
            Err(err) => eprintln!("  SKIP {model}: {err}"),
        }
    }
    let model_count = per_model.len();
    let mut queues: Vec<std::vec::IntoIter<Sample>> =
        per_model.into_iter().map(Vec::into_iter).collect();
    let mut selected: Vec<Sample> = Vec::new();
    'rounds: loop {
        let mut any = false;
        for queue in &mut queues {
            if let Some(sample) = queue.next() {
                selected.push(sample);
                any = true;
                if selected.len() == samples {
                    break 'rounds;
                }
            }
        }
        if !any {
            break;
        }
    }
    if selected.is_empty() {
        eprintln!("SKIP rewriter_rodin_diff: no usable predicates harvested");
        return;
    }
    eprintln!(
        "sampled {} predicate(s) from {} model(s)",
        selected.len(),
        model_count
    );

    // One oracle run answers every request in order.
    let workdir = workspace_target().join("rewriter-rodin-diff");
    std::fs::create_dir_all(&workdir).expect("create work dir");
    let request_file = workdir.join("requests.txt");
    let mut requests = String::new();
    for sample in &selected {
        requests.push_str(&sample.line);
        requests.push('\n');
    }
    std::fs::write(&request_file, &requests).expect("write requests");
    let mut command = std::process::Command::new(&rodin);
    command
        .arg("rewrite-oracle")
        .arg(&request_file)
        .stdout(std::process::Stdio::piped())
        .stderr(std::process::Stdio::piped());
    let child = spawn_in_group(&mut command).expect("spawn oracle");
    let (status, stdout, stderr) = match wait_with_timeout(child, timeout) {
        Ok(output) => output,
        Err(common::WaitError::Timeout) => panic!("rewrite oracle timed out"),
        Err(common::WaitError::Io(e)) => panic!("rewrite oracle wait: {e}"),
    };
    assert!(
        status.success(),
        "rewrite oracle failed ({status}): {}",
        stderr.lines().last().unwrap_or("").trim()
    );
    let responses: Vec<&str> = stdout
        .lines()
        .filter(|l| l.starts_with("OK\t") || l.starts_with("ERR\t"))
        .collect();
    assert_eq!(
        responses.len(),
        selected.len(),
        "oracle answered {} of {} requests",
        responses.len(),
        selected.len()
    );

    #[derive(Default)]
    struct Counts {
        sampled: usize,
        agree: usize,
        differ: usize,
        oracle_err: usize,
    }
    let mut by_model: BTreeMap<String, Counts> = BTreeMap::new();
    let mut rules: BTreeMap<String, usize> = BTreeMap::new();
    let mut problems = Vec::new();
    for (sample, response) in selected.iter().zip(&responses) {
        let counts = by_model.entry(sample.model.clone()).or_default();
        counts.sampled += 1;
        if let Some(message) = response.strip_prefix("ERR\t") {
            counts.oracle_err += 1;
            if counts.oracle_err == 1 {
                eprintln!("  ERR  {}: {message}: {}", sample.model, sample.line);
            }
            continue;
        }
        let body = response.strip_prefix("OK\t").unwrap();
        let (rodin_text, fired) = body.split_once('\t').unwrap_or((body, ""));
        for rule in fired.split(',').filter(|r| !r.is_empty()) {
            *rules.entry(rule.to_string()).or_default() += 1;
        }
        let rossi_result =
            auto_rewrite_fixpoint(&sample.pred).unwrap_or_else(|| sample.pred.clone());
        match parse_in_env(rodin_text, &sample.env) {
            Ok(rodin_result) if rodin_result == rossi_result => counts.agree += 1,
            Ok(_) => {
                counts.differ += 1;
                problems.push(format!(
                    "{}: `{}` rewrote to `{}`, rodin got `{rodin_text}` ({fired})",
                    sample.model,
                    sample.line,
                    print_pred(&rossi_result),
                ));
            }
            Err(err) => {
                counts.differ += 1;
                problems.push(format!(
                    "{}: rodin result `{rodin_text}` unreadable: {err}",
                    sample.model
                ));
            }
        }
    }

    let report: Vec<Vec<String>> = by_model
        .iter()
        .map(|(model, c)| {
            vec![
                model.clone(),
                c.sampled.to_string(),
                c.agree.to_string(),
                c.differ.to_string(),
                c.oracle_err.to_string(),
            ]
        })
        .collect();
    let path = workspace_target().join("rossi-build-rewriter-rodin-diff.tsv");
    write_report(
        &path,
        &["model", "sampled", "agree", "differ", "oracle_err"],
        &report,
    );
    let mut histogram: Vec<(usize, String)> = rules.into_iter().map(|(r, n)| (n, r)).collect();
    histogram.sort_unstable_by(|a, b| b.cmp(a));
    let rule_rows: Vec<Vec<String>> = histogram
        .iter()
        .map(|(n, r)| vec![r.clone(), n.to_string()])
        .collect();
    let rules_path = workspace_target().join("rossi-build-rewriter-rodin-rules.tsv");
    write_report(&rules_path, &["rule", "fired"], &rule_rows);
    let total = |f: fn(&Counts) -> usize| by_model.values().map(f).sum::<usize>();
    eprintln!(
        "rewrites: {} sampled — {} agree, {} differ, {} oracle_err; reports: {} and {}",
        total(|c| c.sampled),
        total(|c| c.agree),
        total(|c| c.differ),
        total(|c| c.oracle_err),
        path.display(),
        rules_path.display(),
    );

    problems.truncate(MAX_PROBLEMS);
    assert!(problems.is_empty(), "{}", problems.join("\n"));
}

/// Harvests up to `cap` unique typed predicates from one archive's
/// loadable sequents. Every sample is printed and parsed back, so the
/// request line is a formula both sides read identically; anything
/// that does not survive the round trip is dropped.
fn harvest(
    zip: &Path,
    model: &str,
    cap: usize,
    seen: &mut BTreeSet<String>,
) -> Result<Vec<Sample>, String> {
    let bytes = std::fs::read(zip).map_err(|e| format!("read: {e}"))?;
    let mut archive = zip::ZipArchive::new(std::io::Cursor::new(bytes.as_slice()))
        .map_err(|e| format!("zip: {e}"))?;
    let names: Vec<String> = archive.file_names().map(str::to_string).collect();
    let mut read_entry = |name: &str| -> Option<String> {
        let mut entry = archive.by_name(name).ok()?;
        let mut text = String::new();
        entry.read_to_string(&mut text).ok()?;
        Some(text)
    };

    let mut stems: Vec<String> = names
        .iter()
        .filter(|name| name.ends_with(".bpo"))
        .map(|name| name.trim_end_matches(".bpo").to_string())
        .collect();
    stems.sort();

    // One project per archive directory: hypothesis-set chains cross
    // component files and resolve by file basename.
    let mut projects: BTreeMap<String, PoProject> = BTreeMap::new();
    for stem in &stems {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem));
        let Some(bpo) = read_entry(&format!("{stem}.bpo")) else {
            continue;
        };
        // Legacy obligation vintage: not the modern storage form.
        if bpo.contains("name=\"GOAL\"") {
            continue;
        }
        if let Ok(parsed) = PoFile::read(bpo.as_bytes()) {
            projects
                .entry(dir.to_string())
                .or_default()
                .insert(format!("{file}.bpo"), parsed);
        }
    }

    let mut found = Vec::new();
    for (dir, project) in &projects {
        for stem in &stems {
            let (stem_dir, file) = stem.rsplit_once('/').unwrap_or(("", stem.as_str()));
            if stem_dir != dir {
                continue;
            }
            let path = format!("{file}.bpo");
            let Some(po_file) = project.file(&path) else {
                continue;
            };
            let sequent_names: Vec<String> = po_file.sequents().map(|s| s.name.clone()).collect();
            for name in sequent_names {
                let Ok(seq) = project.load(&path, &name) else {
                    continue;
                };
                for pred in seq.hyp_iter().chain([seq.goal()]) {
                    if found.len() >= cap {
                        return Ok(found);
                    }
                    if let Some(sample) = to_sample(model, pred, seq.type_env(), seen) {
                        found.push(sample);
                    }
                }
            }
        }
    }
    Ok(found)
}

/// Builds the request line for one predicate and re-parses it, so the
/// sample carries exactly the formula the line spells.
fn to_sample(
    model: &str,
    pred: &Predicate,
    env: &SealedTypeEnvironment,
    seen: &mut BTreeSet<String>,
) -> Option<Sample> {
    if has_minus_under_tight_arith(pred) {
        return None;
    }
    let mut env_part = String::new();
    for name in pred.free_identifiers() {
        let ty = env.get(name)?;
        if !env_part.is_empty() {
            env_part.push(';');
        }
        env_part.push_str(name);
        env_part.push('=');
        env_part.push_str(&ty.to_rodin_canonical());
    }
    let text = print_pred(pred);
    if text.contains('\t') || text.contains('\n') {
        return None;
    }
    let line = format!("{env_part}\t{text}");
    if !seen.insert(line.clone()) {
        return None;
    }
    let reparsed = parse_in_env(&text, env).ok()?;
    Some(Sample {
        model: model.to_string(),
        line,
        pred: reparsed,
        env: env.clone(),
    })
}

/// Whether a unary minus sits directly under a tight arithmetic
/// operator — the one spelling the two grammars group differently.
fn has_minus_under_tight_arith(pred: &Predicate) -> bool {
    use rossi::formula::rewrite::FormulaRewriter;
    use rossi::formula::tag::{AssocExprOp, BinaryExprOp, UnaryExprOp};
    use rossi::formula::{Expression, ExpressionKind};
    struct Scan(bool);
    impl FormulaRewriter for Scan {
        fn rewrite_expression(&mut self, expr: &Expression) -> Expression {
            let is_minus = |e: &Expression| {
                matches!(
                    e.kind(),
                    ExpressionKind::Unary {
                        op: UnaryExprOp::UnMinus,
                        ..
                    }
                )
            };
            match expr.kind() {
                ExpressionKind::Associative {
                    op: AssocExprOp::Mul,
                    children,
                } if children.iter().any(is_minus) => self.0 = true,
                ExpressionKind::Binary { op, left, right }
                    if matches!(
                        op,
                        BinaryExprOp::Div | BinaryExprOp::Mod | BinaryExprOp::Expn
                    ) && (is_minus(left) || is_minus(right)) =>
                {
                    self.0 = true
                }
                _ => {}
            }
            expr.clone()
        }
    }
    let mut scan = Scan(false);
    pred.rewrite(&mut scan);
    scan.0
}

fn print_pred(pred: &Predicate) -> String {
    PrettyPrinter::rodin_canonical().print_formula_predicate(pred)
}

fn parse_in_env(text: &str, env: &SealedTypeEnvironment) -> Result<Predicate, String> {
    let parsed = rossi::parse_predicate_str(text).map_err(|e| format!("parse: {e}"))?;
    let checked = parsed.type_check(env);
    if !checked.inferred.is_empty() {
        return Err("undeclared identifiers".into());
    }
    let typed = checked.typed.ok_or("does not type-check")?;
    Ok(typed.strip_ascriptions())
}
