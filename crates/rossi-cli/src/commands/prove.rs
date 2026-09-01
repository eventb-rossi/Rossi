//! `rossi prove` — check the stored proofs of an Event-B project
//! against its proof obligations.
//!
//! For every obligation in the input's `.bpo` files, the stored proof
//! in the sibling `.bpr` is checked by the dependency-based reuse
//! rule (the status-update decision): a proof that no longer applies to
//! its regenerated obligation reports as broken. The recorded `.bps`
//! statuses are not consulted — this command recomputes the verdicts.
//!
//! Any broken or uncheckable proof makes the exit code nonzero;
//! pending and unattempted obligations do not: open proofs are work
//! in progress rather than errors.
//!
//! With `--replay`, every checkable proof whose reasoners are all
//! implemented is additionally re-derived: each reasoner is re-run on
//! its recorded input and the reconstructed tree must complete
//! (the replay mode). Proofs using reasoners without a Rust
//! implementation are skipped, not failed — coverage grows with the
//! reasoner batches — while a replay that fails on an implemented
//! proof is an error.

use std::collections::BTreeMap;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use clap::Args;
use rayon::prelude::*;

use rossi_prove::bpr::{Keep, ProofBody, ProofEntry, visit_bpr};
use rossi_prove::confidence::Bucket;
use rossi_prove::po_loader::{PoFile, PoProject};
use rossi_prove::status::compute_status;
use rossi_prove::{Confidence, ProofTreeNode, ReasonerProvider, RegistryProvider, Skeleton};

#[derive(Args)]
pub struct ProveArgs {
    /// Input to check: an Event-B `.zip` archive or a project directory
    /// containing `.bpo` / `.bpr` files.
    pub input: PathBuf,
    /// Also list every checked obligation, not only the problematic
    /// ones.
    #[arg(short, long)]
    pub verbose: bool,
    /// Re-run each proof's reasoners on their recorded inputs and
    /// require the reconstructed tree to complete (proofs using
    /// unimplemented reasoners are skipped).
    #[arg(long)]
    pub replay: bool,
}

#[derive(Default)]
struct Summary {
    discharged: usize,
    reviewed: usize,
    pending: usize,
    unattempted: usize,
    broken: usize,
    unsupported: usize,
    errors: usize,
    replayed: usize,
    replay_skipped: usize,
    replay_failed: usize,
}

impl Summary {
    fn add(&mut self, other: &Summary) {
        self.discharged += other.discharged;
        self.reviewed += other.reviewed;
        self.pending += other.pending;
        self.unattempted += other.unattempted;
        self.broken += other.broken;
        self.unsupported += other.unsupported;
        self.errors += other.errors;
        self.replayed += other.replayed;
        self.replay_skipped += other.replay_skipped;
        self.replay_failed += other.replay_failed;
    }
}

pub fn run(args: ProveArgs) -> ExitCode {
    match prove(&args.input, args.verbose, args.replay) {
        Ok(summary) => {
            let total = summary.discharged
                + summary.reviewed
                + summary.pending
                + summary.unattempted
                + summary.broken
                + summary.unsupported
                + summary.errors;
            println!(
                "Proofs: {total} obligation(s) — {} discharged, {} reviewed, {} pending, \
                 {} unattempted, {} broken, {} unsupported, {} error(s)",
                summary.discharged,
                summary.reviewed,
                summary.pending,
                summary.unattempted,
                summary.broken,
                summary.unsupported,
                summary.errors,
            );
            if args.replay {
                println!(
                    "Replay: {} replayed, {} skipped (unimplemented reasoners), {} failed",
                    summary.replayed, summary.replay_skipped, summary.replay_failed,
                );
            }
            if summary.broken + summary.unsupported + summary.errors + summary.replay_failed > 0 {
                ExitCode::from(1)
            } else {
                ExitCode::SUCCESS
            }
        }
        Err(e) => {
            eprintln!("rossi prove: {e}");
            ExitCode::from(1)
        }
    }
}

/// The first stored reasoner in the skeleton without an implementation,
/// making the proof unreplayable for now.
fn missing_reasoner(skel: &Skeleton) -> Option<String> {
    let mut stack = vec![skel];
    while let Some(node) = stack.pop() {
        if let Some(stored) = &node.rule {
            if RegistryProvider
                .implementation(&stored.rule.reasoner)
                .is_none()
            {
                return Some(stored.rule.reasoner.id().to_string());
            }
        }
        stack.extend(node.children.iter());
    }
    None
}

/// The `(component stem, contents)` of every file with `extension`
/// in the input, stems keeping their archive directory prefix.
type FileMap = BTreeMap<String, Vec<u8>>;

fn prove(input: &Path, verbose: bool, replay: bool) -> Result<Summary, Box<dyn std::error::Error>> {
    let (bpos, bprs) = collect(input)?;
    let keep = if replay { Keep::Full } else { Keep::Deps };

    let pool = rossi_prove::thread_pool();

    // One project per archive directory: hypothesis-set chains cross
    // component files and resolve by file basename.
    let parsed: Vec<Result<PoFile, String>> = pool.install(|| {
        bpos.par_iter()
            .map(|(stem, contents)| {
                PoFile::read(contents.as_slice()).map_err(|err| format!("{stem}.bpo: {err}"))
            })
            .collect()
    });
    let mut projects: BTreeMap<&str, PoProject> = BTreeMap::new();
    for (stem, parsed) in bpos.keys().zip(parsed) {
        let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem));
        projects
            .entry(dir)
            .or_default()
            .insert(format!("{file}.bpo"), parsed?);
    }

    // Components are independent once the projects exist: check them
    // in parallel, reporting in stem order.
    let checked: Vec<(Vec<String>, Summary)> = pool.install(|| {
        bpos.par_iter()
            .map(|(stem, _)| {
                let (dir, file) = stem.rsplit_once('/').unwrap_or(("", stem));
                let bpr = bprs.get(stem).map(Vec::as_slice);
                check_component(
                    stem,
                    &projects[dir],
                    &format!("{file}.bpo"),
                    bpr,
                    keep,
                    replay,
                    verbose,
                )
            })
            .collect()
    });
    let mut summary = Summary::default();
    for (lines, counts) in &checked {
        for line in lines {
            println!("{line}");
        }
        summary.add(counts);
    }
    Ok(summary)
}

/// Checks one component's obligations against its proof file: the
/// lines to report and the verdict counts.
fn check_component(
    stem: &str,
    project: &PoProject,
    path: &str,
    bpr: Option<&[u8]>,
    keep: Keep,
    replay: bool,
    verbose: bool,
) -> (Vec<String>, Summary) {
    let mut lines = Vec::new();
    let mut summary = Summary::default();
    let Some(po) = project.file(path) else {
        return (lines, summary);
    };
    // Proofs are checked as they stream off the file, so one proof's
    // tree is in memory at a time; a later proof of the same name
    // replaces an earlier one.
    let mut verdicts: BTreeMap<String, ProofVerdict> = BTreeMap::new();
    if let Some(bytes) = bpr
        && let Err(err) = visit_bpr(
            bytes,
            |_| keep,
            |proof| {
                if po.sequent(&proof.name).is_some() {
                    verdicts.insert(
                        proof.name.clone(),
                        check_proof(project, path, &proof, replay),
                    );
                }
            },
        )
    {
        lines.push(format!("{stem}: unreadable proof file: {err}"));
        summary.errors += po.sequents().count();
        return (lines, summary);
    }
    for entry in po.sequents() {
        let name = &entry.name;
        let verdict = verdicts.get(name);
        let status = verdict.map_or("unattempted", |verdict| verdict.status);
        let replay = verdict.and_then(|verdict| verdict.replay.as_ref());
        let note = match replay {
            None => String::new(),
            Some(Replay::Skipped(id)) => {
                summary.replay_skipped += 1;
                format!(" (replay skipped: {id})")
            }
            Some(Replay::Replayed) => {
                summary.replayed += 1;
                " (replayed)".into()
            }
            Some(Replay::Failed) => {
                summary.replay_failed += 1;
                " (replay FAILED)".into()
            }
        };
        let replay_failed = matches!(replay, Some(Replay::Failed));
        match status {
            "discharged" => summary.discharged += 1,
            "reviewed" => summary.reviewed += 1,
            "pending" => summary.pending += 1,
            "unattempted" => summary.unattempted += 1,
            "broken" => summary.broken += 1,
            "unsupported" => summary.unsupported += 1,
            _ => summary.errors += 1,
        }
        if verbose || matches!(status, "broken" | "unsupported" | "error") || replay_failed {
            lines.push(format!("{stem} {name}: {status}{note}"));
        }
    }
    (lines, summary)
}

/// One proof's verdict against its obligation.
struct ProofVerdict {
    status: &'static str,
    replay: Option<Replay>,
}

/// The replay outcome of a proof whose status allowed one.
enum Replay {
    /// The named reasoner is not implemented.
    Skipped(String),
    Replayed,
    Failed,
}

fn check_proof(project: &PoProject, path: &str, proof: &ProofEntry, replay: bool) -> ProofVerdict {
    let mut outcome = None;
    let status = match &proof.body {
        ProofBody::Skipped => unreachable!("every proof is read"),
        ProofBody::Unsupported(_) => "unsupported",
        ProofBody::Loaded(stored) => match project.load(path, &proof.name) {
            Err(_) => "error",
            Ok(seq) => {
                let verdict = compute_status(&seq, proof);
                if replay && !verdict.broken {
                    let skel = stored.skeleton.as_ref().expect("full parse");
                    outcome = Some(match missing_reasoner(skel) {
                        Some(id) => Replay::Skipped(id),
                        None => {
                            let mut node = ProofTreeNode::open(seq.clone());
                            if rossi_prove::replay(&mut node, skel, &RegistryProvider) {
                                Replay::Replayed
                            } else {
                                Replay::Failed
                            }
                        }
                    });
                }
                if verdict.broken {
                    "broken"
                } else {
                    match Confidence::classify(verdict.confidence.map(i64::from)) {
                        Bucket::Discharged => "discharged",
                        Bucket::Reviewed => "reviewed",
                        Bucket::Pending => "pending",
                        Bucket::Unattempted => "unattempted",
                    }
                }
            }
        },
    };
    ProofVerdict {
        status,
        replay: outcome,
    }
}

/// Collects the `.bpo` and `.bpr` files of a `.zip` archive or a
/// project directory, keyed by component stem — through the shared
/// proof-file walkers, so the extension set and the unsafe-basename
/// filter stay in one place.
fn collect(input: &Path) -> Result<(FileMap, FileMap), Box<dyn std::error::Error>> {
    let mut bpos = FileMap::new();
    let mut bprs = FileMap::new();
    let mut insert = |name: &str, bytes: Vec<u8>| {
        if let Some((stem, ext)) = name.rsplit_once('.') {
            match ext {
                "bpo" => {
                    bpos.insert(stem.to_string(), bytes);
                }
                "bpr" => {
                    bprs.insert(stem.to_string(), bytes);
                }
                _ => {}
            }
        }
    };
    if input.is_dir() {
        for (basename, bytes) in super::proofs::proofs_in_dir(input)? {
            insert(&basename, bytes);
        }
    } else {
        let bytes = std::fs::read(input)?;
        super::proofs::visit_zip_proofs(
            &bytes,
            |_| true,
            |name, bytes| {
                insert(name, bytes);
                Ok(())
            },
        )?;
    }
    if bpos.is_empty() {
        return Err(format!("no .bpo files found in {}", input.display()).into());
    }
    Ok((bpos, bprs))
}
