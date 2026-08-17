//! Bridge proof files between the checkout and the shared Rodin workspace.
//!
//! Proof state (`.bpr` proofs, `.bps` statuses, `.bpo` obligations) has two
//! homes: next to the `.eventb` sources (where `rossi import` places it and
//! version control keeps it) and the Rodin project the lens builds under
//! `<root>/.rossi/rodin`. This module syncs the two only at the "Open in
//! Rodin" session boundaries — the checkout is authoritative when a session
//! starts (seed), the workspace when it ends (mirror-back) — never
//! continuously.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

/// Whether `name` is a proof-state file Rodin keeps next to a component.
fn is_proof_file_name(name: &str) -> bool {
    name.ends_with(".bpr") || name.ends_with(".bps") || name.ends_with(".bpo")
}

/// The proof files at `dir`'s top level: sorted, files only, missing
/// directory → empty. Proof files live flat next to their components, both
/// in the checkout and in a Rodin project directory.
fn proof_files_in(dir: &Path) -> Vec<PathBuf> {
    let Ok(entries) = std::fs::read_dir(dir) else {
        return Vec::new();
    };
    let mut paths: Vec<PathBuf> = entries
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| {
            path.file_name()
                .and_then(|n| n.to_str())
                .is_some_and(is_proof_file_name)
                && path.is_file()
        })
        .collect();
    paths.sort();
    paths
}

/// What [`seed_project`] wrote into the workspace project.
pub(crate) struct SeedReport {
    /// `(path, content hash)` of every file written, for the sync watcher's
    /// echo guard.
    pub written: Vec<(PathBuf, u64)>,
    /// Files copied because the workspace had no copy.
    pub copied: usize,
    /// Files whose differing workspace copy was overwritten — replaced data,
    /// surfaced to the user by the caller.
    pub replaced: usize,
}

/// Copy the proof files sitting next to the text sources into the workspace
/// project. The checkout is authoritative when a Rodin session starts, so a
/// differing workspace copy is overwritten (counted in
/// [`replaced`](SeedReport::replaced)). Nothing is ever deleted here: a
/// workspace file with no text-side counterpart may be the only copy of
/// proof work an interrupted session never mirrored back.
///
/// Proof files are collected from the directories holding the project's
/// text sources; on a basename collision across directories the first in
/// sorted order wins. Per-file IO failures are logged and skipped — seeding
/// must never break the lens flow.
pub(crate) fn seed_project(
    source_dir: &Path,
    workspace_dir: &Path,
    project_name: &str,
) -> std::io::Result<SeedReport> {
    let sources = super::build::collect_source_files(source_dir)?;
    let dirs: BTreeSet<PathBuf> = sources
        .iter()
        .filter_map(|path| path.parent().map(Path::to_path_buf))
        .collect();
    let mut text_files: BTreeMap<String, PathBuf> = BTreeMap::new();
    for dir in &dirs {
        for path in proof_files_in(dir) {
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };
            if let Some(winner) = text_files.get(name) {
                tracing::info!(
                    "duplicate proof file {name}: seeding {}, ignoring {}",
                    winner.display(),
                    path.display()
                );
                continue;
            }
            text_files.insert(name.to_string(), path);
        }
    }

    let mut report = SeedReport {
        written: Vec::new(),
        copied: 0,
        replaced: 0,
    };
    if text_files.is_empty() {
        return Ok(report);
    }
    let project_dir = workspace_dir.join(project_name);
    std::fs::create_dir_all(&project_dir)?;
    for (name, path) in text_files {
        let bytes = match std::fs::read(&path) {
            Ok(bytes) => bytes,
            Err(e) => {
                tracing::info!("cannot read {}: {e}; not seeded", path.display());
                continue;
            }
        };
        let dest = project_dir.join(&name);
        let existing = std::fs::read(&dest).ok();
        if existing.as_deref() == Some(bytes.as_slice()) {
            continue;
        }
        if let Err(e) = std::fs::write(&dest, &bytes) {
            tracing::info!("cannot write {}: {e}; not seeded", dest.display());
            continue;
        }
        match existing {
            Some(_) => report.replaced += 1,
            None => report.copied += 1,
        }
        report
            .written
            .push((dest, super::sync::content_hash(&bytes)));
    }
    Ok(report)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::TempDir;

    #[test]
    fn seed_copies_and_replaces_but_never_deletes() {
        let tmp = TempDir::new("rossi-proof-seed");
        let src = tmp.join("src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("m.eventb"), "MACHINE M0\nEND\n").unwrap();
        std::fs::write(src.join("M0.bpr"), "text-proof").unwrap();
        std::fs::write(src.join("M0.bps"), "text-status").unwrap();
        std::fs::write(src.join("notes.txt.bak"), "not a proof").unwrap();
        let ws = tmp.join("ws");
        let project = ws.join("proj");
        std::fs::create_dir_all(&project).unwrap();
        // A differing workspace copy is replaced; an unrelated workspace-only
        // proof file survives (it may be unmirrored work).
        std::fs::write(project.join("M0.bps"), "ws-status").unwrap();
        std::fs::write(project.join("M9.bpr"), "ws-only").unwrap();

        let report = seed_project(&src, &ws, "proj").unwrap();
        assert_eq!((report.copied, report.replaced), (1, 1));
        assert_eq!(
            std::fs::read(project.join("M0.bpr")).unwrap(),
            b"text-proof"
        );
        assert_eq!(
            std::fs::read(project.join("M0.bps")).unwrap(),
            b"text-status"
        );
        assert_eq!(std::fs::read(project.join("M9.bpr")).unwrap(), b"ws-only");
        // Echo-guard hashes match the bytes on disk.
        assert_eq!(report.written.len(), 2);
        for (path, hash) in &report.written {
            let bytes = std::fs::read(path).unwrap();
            assert_eq!(super::super::sync::content_hash(&bytes), *hash);
        }

        // Identical bytes are not rewritten on a second run.
        let again = seed_project(&src, &ws, "proj").unwrap();
        assert_eq!((again.copied, again.replaced), (0, 0));
        assert!(again.written.is_empty());
    }

    #[test]
    fn seed_first_wins_across_source_dirs() {
        let tmp = TempDir::new("rossi-proof-seed-dirs");
        let src = tmp.join("src");
        let a = src.join("a");
        let b = src.join("b");
        for (dir, machine) in [(&a, "MACHINE A0\nEND\n"), (&b, "MACHINE B0\nEND\n")] {
            std::fs::create_dir_all(dir).unwrap();
            std::fs::write(dir.join("m.eventb"), machine).unwrap();
            std::fs::write(
                dir.join("M0.bpr"),
                dir.file_name().unwrap().as_encoded_bytes(),
            )
            .unwrap();
        }

        seed_project(&src, &tmp.join("ws"), "proj").unwrap();
        // Sorted directory order decides the collision: `a` before `b`.
        assert_eq!(
            std::fs::read(tmp.join("ws").join("proj").join("M0.bpr")).unwrap(),
            b"a"
        );
    }

    #[test]
    fn seed_without_proof_files_touches_nothing() {
        let tmp = TempDir::new("rossi-proof-seed-empty");
        let src = tmp.join("src");
        std::fs::create_dir_all(&src).unwrap();
        std::fs::write(src.join("m.eventb"), "MACHINE M0\nEND\n").unwrap();

        let report = seed_project(&src, &tmp.join("ws"), "proj").unwrap();
        assert_eq!((report.copied, report.replaced), (0, 0));
        // Not even the project directory is created for an empty seed.
        assert!(!tmp.join("ws").exists());
    }
}
