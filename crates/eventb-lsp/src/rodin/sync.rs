//! Watch the shared Rodin workspace and feed Rodin's results back.
//!
//! Rodin writes proof evidence (`.bpr` proofs, `.bps` statuses) into the
//! project directories rossi builds under `<root>/.rossi/rodin`. This
//! watcher notices those writes and refreshes the per-component proof-status
//! overlay the analyzer publishes as informational diagnostics — so a proof
//! discharged in Rodin shows up in the editor moments later, without any
//! manual sync step.
//!
//! Echo-loop prevention: every file the server itself writes into the
//! workspace is recorded (path → content hash) in the shared written-file
//! map; watcher events whose on-disk content still matches that hash are the
//! server's own writes bouncing back and are dropped.
//!
//! All failure modes degrade quietly: if the watcher cannot start or an
//! event cannot be processed, proof state simply refreshes on the next
//! successful build instead. Nothing here surfaces errors to the user.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Duration;

use notify::Watcher;
use parking_lot::Mutex;

use crate::server::Analyzer;

/// Content hashes of files the server itself wrote, shared between the
/// build flow (writer) and the watcher (reader).
pub type WrittenFiles = Arc<Mutex<HashMap<PathBuf, u64>>>;

/// Quiet period after the last filesystem event before a batch is processed;
/// Rodin saves in bursts (proof file + status + builder outputs).
const DEBOUNCE: Duration = Duration::from_millis(500);

/// Hash used for the written-file echo guard. Stability across runs is not
/// needed — the map lives in memory only.
pub fn content_hash(bytes: &[u8]) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    bytes.hash(&mut hasher);
    hasher.finish()
}

/// A running watcher over one Rodin workspace directory. Dropping it stops
/// both the filesystem watcher and the processing task.
pub struct RodinSyncManager {
    workspace_dir: PathBuf,
    _watcher: notify::RecommendedWatcher,
    task: tokio::task::JoinHandle<()>,
}

impl Drop for RodinSyncManager {
    fn drop(&mut self) {
        self.task.abort();
    }
}

impl RodinSyncManager {
    /// The workspace this manager watches.
    pub fn workspace_dir(&self) -> &Path {
        &self.workspace_dir
    }

    /// Start watching `workspace_dir`. Performs one initial proof-status
    /// scan so existing Rodin results surface without waiting for a change.
    ///
    /// Watcher creation can take *minutes* when the platform's file-event
    /// service is busy (macOS fseventsd on a churning volume), so callers
    /// must invoke this off the request path — see the server's
    /// `ensure_rodin_sync`, which runs it on a detached thread. `handle` is
    /// the runtime the processing task should run on.
    pub(crate) fn start(
        handle: &tokio::runtime::Handle,
        workspace_dir: PathBuf,
        written: WrittenFiles,
        analyzer: Analyzer,
    ) -> notify::Result<Self> {
        let (tx, mut rx) = tokio::sync::mpsc::unbounded_channel::<PathBuf>();
        let mut watcher =
            notify::recommended_watcher(move |event: notify::Result<notify::Event>| {
                if let Ok(event) = event {
                    for path in event.paths {
                        let _ = tx.send(path);
                    }
                }
            })?;
        watcher.watch(&workspace_dir, notify::RecursiveMode::Recursive)?;

        let task_workspace = workspace_dir.clone();
        let task = handle.spawn(async move {
            // Initial scan: surface proof state Rodin left from earlier runs.
            refresh(&task_workspace, &analyzer).await;

            let mut pending: BTreeSet<PathBuf> = BTreeSet::new();
            loop {
                tokio::select! {
                    received = rx.recv() => {
                        match received {
                            Some(path) => { pending.insert(path); }
                            None => break,
                        }
                    }
                    // Restarted on every event above, so this fires only
                    // after DEBOUNCE of quiet — one refresh per burst.
                    _ = tokio::time::sleep(DEBOUNCE), if !pending.is_empty() => {
                        let batch = std::mem::take(&mut pending);
                        let model_changes = foreign_model_changes(&task_workspace, &batch, &written);
                        if !model_changes.is_empty() {
                            sync_model_edits(&task_workspace, model_changes, &analyzer).await;
                        }
                        if has_foreign_proof_change(&batch, &written) {
                            refresh(&task_workspace, &analyzer).await;
                        }
                    }
                }
            }
        });

        Ok(Self {
            workspace_dir,
            _watcher: watcher,
            task,
        })
    }
}

/// Whether the batch contains a proof-state change the server did not make
/// itself (see the module doc on echo prevention).
fn has_foreign_proof_change(batch: &BTreeSet<PathBuf>, written: &WrittenFiles) -> bool {
    batch
        .iter()
        .filter(|path| {
            matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("bpr") | Some("bps")
            )
        })
        .any(|path| !is_own_write(path, written))
}

/// A path whose on-disk content still hashes to what the server last wrote
/// there is the server's own write echoing back through the watcher.
fn is_own_write(path: &Path, written: &WrittenFiles) -> bool {
    let Some(expected) = written.lock().get(path).copied() else {
        return false;
    };
    match std::fs::read(path) {
        Ok(bytes) => content_hash(&bytes) == expected,
        Err(_) => false,
    }
}

/// Component XML files (`.bum`/`.buc`) changed by someone other than the
/// server, grouped as (project directory, XML filename). Only files directly
/// inside a project directory (a direct child of the workspace) count.
fn foreign_model_changes(
    workspace_dir: &Path,
    batch: &BTreeSet<PathBuf>,
    written: &WrittenFiles,
) -> Vec<(PathBuf, String)> {
    batch
        .iter()
        .filter(|path| {
            matches!(
                path.extension().and_then(|e| e.to_str()),
                Some("bum") | Some("buc")
            )
        })
        .filter(|path| {
            path.parent()
                .and_then(Path::parent)
                .is_some_and(|grandparent| grandparent == workspace_dir)
        })
        .filter(|path| path.is_file() && !is_own_write(path, written))
        .filter_map(|path| {
            let project_dir = path.parent()?.to_path_buf();
            let name = path.file_name()?.to_str()?.to_string();
            Some((project_dir, name))
        })
        .collect()
}

/// Flow Rodin's model edits back into the Event-B sources: for each affected
/// source file, 3-way merge (base snapshot / current text / re-imported
/// components) and apply the result — see [`super::model_sync`].
async fn sync_model_edits(
    workspace_dir: &Path,
    changes: Vec<(PathBuf, String)>,
    analyzer: &Analyzer,
) {
    use super::model_sync::{self, MergeOutcome};
    use crate::lsp_types::MessageType;

    // Group the changed XML files by (project, source file) via the manifest.
    let mut by_source: BTreeMap<(PathBuf, PathBuf), model_sync::BaseManifest> = BTreeMap::new();
    for (project_dir, xml_name) in changes {
        let Some(project_name) = project_dir.file_name().and_then(|n| n.to_str()) else {
            continue;
        };
        let Some(manifest) = model_sync::load_manifest(workspace_dir, project_name) else {
            tracing::info!("no build manifest for {project_name}; Rodin edit not synced");
            continue;
        };
        let Some(relative) = manifest.components.get(&xml_name).cloned() else {
            tracing::info!("{xml_name} is not in the build manifest; Rodin edit not synced");
            continue;
        };
        by_source
            .entry((project_dir.clone(), relative))
            .or_insert(manifest);
    }

    for ((project_dir, relative), manifest) in by_source {
        let absolute = manifest.source_root.join(&relative);
        let absolute = std::fs::canonicalize(&absolute).unwrap_or(absolute);
        let Some((uri, ours)) = analyzer.source_text(&absolute) else {
            tracing::info!("cannot read {}; Rodin edit not synced", absolute.display());
            continue;
        };

        let outcome = {
            let workspace_dir = workspace_dir.to_path_buf();
            let printer = analyzer.printer();
            let manifest = manifest.clone();
            let relative = relative.clone();
            let ours = ours.clone();
            tokio::task::spawn_blocking(move || {
                model_sync::sync_source_file(
                    &manifest,
                    &workspace_dir,
                    &project_dir,
                    &relative,
                    &ours,
                    &printer,
                )
            })
            .await
        };
        let outcome = match outcome {
            Ok(Ok(outcome)) => outcome,
            Ok(Err(message)) => {
                tracing::info!("Rodin edit not synced: {message}");
                continue;
            }
            Err(join_error) => {
                tracing::info!("Rodin edit sync failed: {join_error}");
                continue;
            }
        };
        let Some(text) = outcome.text() else {
            continue;
        };

        if let Err(message) = analyzer.apply_source_text(&absolute, uri, text).await {
            analyzer
                .notify_user(
                    MessageType::ERROR,
                    format!(
                        "Could not apply Rodin's edits to {}: {message}",
                        relative.display()
                    ),
                )
                .await;
            continue;
        }
        // Rodin's side is incorporated (markers and all): advance the base
        // so the next merge uses the right ancestor.
        if let Err(e) =
            model_sync::update_base_source(workspace_dir, &manifest.project_name, &relative, text)
        {
            tracing::info!("could not advance base snapshot: {e}");
        }
        match outcome {
            MergeOutcome::Merged(_) => {
                analyzer
                    .notify_user(
                        MessageType::INFO,
                        format!("Merged Rodin's model edits into {}.", relative.display()),
                    )
                    .await;
            }
            MergeOutcome::Conflict(_) => {
                analyzer
                    .notify_user(
                        MessageType::WARNING,
                        format!(
                            "Merged Rodin's model edits into {} with conflicts — resolve the <<<<<<< markers.",
                            relative.display()
                        ),
                    )
                    .await;
            }
            MergeOutcome::Unchanged | MergeOutcome::FastForward(_) => {
                tracing::info!("synced Rodin's model edits into {}", relative.display());
            }
        }
    }
}

/// Recompute the proof-status overlay for every project in the workspace and
/// republish diagnostics for the open documents.
async fn refresh(workspace_dir: &Path, analyzer: &Analyzer) {
    let workspace_dir = workspace_dir.to_path_buf();
    let status =
        tokio::task::spawn_blocking(move || proof_status_for_workspace(&workspace_dir)).await;
    match status {
        Ok(status) => analyzer.refresh_proof_status(status).await,
        Err(join_error) => tracing::info!("rodin proof-status scan failed: {join_error}"),
    }
}

/// One aggregated proof-status line per component, across every Rodin
/// project directory (a subdirectory holding a `.project`) in the workspace.
/// Fully discharged components are absent — no news is good news.
pub fn proof_status_for_workspace(workspace_dir: &Path) -> HashMap<String, String> {
    use rossi_build::rules::RuleId;

    let mut status = HashMap::new();
    let Ok(entries) = std::fs::read_dir(workspace_dir) else {
        return status;
    };
    for entry in entries.flatten() {
        let project_dir = entry.path();
        let hidden = project_dir
            .file_name()
            .and_then(|n| n.to_str())
            .is_none_or(|name| name.starts_with('.'));
        if hidden || !project_dir.is_dir() || !project_dir.join(".project").is_file() {
            continue;
        }
        let Ok(report) = rossi_build::proofs::check_directory(&project_dir) else {
            continue;
        };
        // Aggregate per component: one informational line beats one
        // diagnostic per obligation on the same header.
        let mut per_component: HashMap<String, (usize, usize)> = HashMap::new();
        for diagnostic in &report.diagnostics {
            let counts = per_component.entry(diagnostic.origin.clone()).or_default();
            match diagnostic.rule_id {
                Some(RuleId::UndischargedProof) => counts.0 += 1,
                Some(RuleId::BrokenProof) => counts.1 += 1,
                _ => {}
            }
        }
        for (component, (undischarged, broken)) in per_component {
            let mut parts = Vec::new();
            if undischarged > 0 {
                parts.push(format!("{undischarged} undischarged proof obligation(s)"));
            }
            if broken > 0 {
                parts.push(format!("{broken} broken proof(s)"));
            }
            if parts.is_empty() {
                continue;
            }
            status.insert(component, format!("Rodin: {}", parts.join(", ")));
        }
    }
    status
}

#[cfg(test)]
mod tests {
    use super::*;

    fn temp_dir(prefix: &str) -> PathBuf {
        let dir = std::env::temp_dir().join(format!(
            "{prefix}-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(&dir).unwrap();
        dir
    }

    #[test]
    fn aggregates_proof_status_per_component() {
        let ws = temp_dir("rossi-rodin-sync-status");
        let project = ws.join("proj");
        std::fs::create_dir_all(&project).unwrap();
        std::fs::write(project.join(".project"), "<projectDescription/>").unwrap();
        std::fs::write(
            project.join("M0.bpo"),
            r#"<?xml version="1.0"?><org.eventb.core.poFile>
               <org.eventb.core.poSequent name="inv1/INV"/>
               <org.eventb.core.poSequent name="inv2/INV"/>
               <org.eventb.core.poSequent name="inv3/INV"/>
               </org.eventb.core.poFile>"#,
        )
        .unwrap();
        std::fs::write(
            project.join("M0.bps"),
            r#"<?xml version="1.0"?><org.eventb.core.psFile>
               <org.eventb.core.psStatus name="inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.psBroken="false"/>
               <org.eventb.core.psStatus name="inv2/INV" org.eventb.core.confidence="-99" org.eventb.core.psBroken="false"/>
               <org.eventb.core.psStatus name="inv3/INV" org.eventb.core.confidence="1000" org.eventb.core.psBroken="true"/>
               </org.eventb.core.psFile>"#,
        )
        .unwrap();
        // A dot-directory (Eclipse .metadata) and a non-project dir are skipped.
        std::fs::create_dir_all(ws.join(".metadata")).unwrap();
        std::fs::create_dir_all(ws.join("not-a-project")).unwrap();

        let status = proof_status_for_workspace(&ws);
        assert_eq!(
            status.get("M0").map(String::as_str),
            Some("Rodin: 1 undischarged proof obligation(s), 1 broken proof(s)")
        );
        assert_eq!(status.len(), 1);
        std::fs::remove_dir_all(&ws).ok();
    }

    #[test]
    fn fully_discharged_components_are_absent() {
        let ws = temp_dir("rossi-rodin-sync-clean");
        let project = ws.join("proj");
        std::fs::create_dir_all(&project).unwrap();
        std::fs::write(project.join(".project"), "<projectDescription/>").unwrap();
        std::fs::write(
            project.join("M0.bpo"),
            r#"<?xml version="1.0"?><org.eventb.core.poFile>
               <org.eventb.core.poSequent name="inv1/INV"/>
               </org.eventb.core.poFile>"#,
        )
        .unwrap();
        std::fs::write(
            project.join("M0.bps"),
            r#"<?xml version="1.0"?><org.eventb.core.psFile>
               <org.eventb.core.psStatus name="inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.psBroken="false"/>
               </org.eventb.core.psFile>"#,
        )
        .unwrap();

        assert!(proof_status_for_workspace(&ws).is_empty());
        std::fs::remove_dir_all(&ws).ok();
    }

    #[test]
    fn own_writes_are_recognized_until_content_changes() {
        let dir = temp_dir("rossi-rodin-sync-echo");
        let path = dir.join("M0.bps");
        std::fs::write(&path, "state-a").unwrap();

        let written: WrittenFiles = Arc::new(Mutex::new(HashMap::new()));
        written
            .lock()
            .insert(path.clone(), content_hash(b"state-a"));

        let batch: BTreeSet<PathBuf> = [path.clone()].into();
        assert!(
            !has_foreign_proof_change(&batch, &written),
            "the server's own write must not trigger a refresh"
        );

        std::fs::write(&path, "state-b").unwrap();
        assert!(
            has_foreign_proof_change(&batch, &written),
            "a foreign change to the same path must trigger a refresh"
        );

        let other: BTreeSet<PathBuf> = [dir.join("M0.bcc")].into();
        assert!(
            !has_foreign_proof_change(&other, &written),
            "non-proof files never trigger a proof refresh"
        );
        std::fs::remove_dir_all(&dir).ok();
    }
}
