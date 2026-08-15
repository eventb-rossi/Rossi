//! "Open in Rodin": build the current model into a persistent Rodin
//! workspace and open the Rodin IDE on it.
//!
//! Exposed to editors as a CodeLens on every `MACHINE`/`CONTEXT` header,
//! whose command ([`COMMAND_OPEN`]) the server executes. The lens'd file's
//! whole containing directory becomes one Rodin project (sibling `SEES`
//! targets must resolve, and that is also the granularity proof state syncs
//! at) inside a *stable* workspace — by default `<root>/.rossi/rodin` — so
//! everything Rodin writes there persists: `.bpr` proofs are never touched
//! and rebuilt `.bpo`/`.bps` reconcile against the previous state, which is
//! exactly what makes proofs survive model edits.

pub mod build;
pub mod launch;
pub mod lock;
pub mod model_sync;
pub mod sync;

use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};

use crate::lsp_types::*;
use tower_lsp::Client;

/// The `workspace/executeCommand` command behind the code lens.
pub const COMMAND_OPEN: &str = "rossi.rodin.open";

/// Default shared workspace location, relative to the LSP workspace root
/// (or, in single-file mode, the document's directory).
pub fn default_workspace_dir(root: &Path) -> PathBuf {
    root.join(".rossi").join("rodin")
}

/// An Eclipse-safe project name derived from a directory or file stem:
/// mirror of the extension's former `rodinProjectName`.
pub fn sanitize_project_name(input: &str) -> String {
    let sanitized: String = input
        .chars()
        .map(|c| {
            if c.is_ascii_alphanumeric() || matches!(c, '_' | '.' | '-') {
                c
            } else {
                '_'
            }
        })
        .collect();
    let trimmed = sanitized.trim_start_matches(['.', '-']);
    if trimmed.is_empty() {
        "rossi_project".to_string()
    } else {
        trimmed.to_string()
    }
}

/// The "Open in Rodin" lenses for a document: one per component, anchored on
/// the component's name. When the parse yields no components (mid-edit
/// breakage), fall back to scanning for `MACHINE`/`CONTEXT` header lines so
/// the lens stays visible while the user types.
pub fn code_lenses(components: &[rossi::Component], text: &str, uri: &Url) -> Vec<CodeLens> {
    let lenses: Vec<CodeLens> = components
        .iter()
        .filter_map(|component| {
            let span = component.name_span().or_else(|| component.span())?;
            Some(lens_at(crate::position::span_to_range(&span, text), uri))
        })
        .collect();
    if !lenses.is_empty() {
        return lenses;
    }
    header_line_scan(text, uri)
}

fn lens_at(range: Range, uri: &Url) -> CodeLens {
    CodeLens {
        range,
        command: Some(Command {
            title: "Open in Rodin".to_string(),
            command: COMMAND_OPEN.to_string(),
            arguments: Some(vec![serde_json::json!(uri.to_string())]),
        }),
        data: None,
    }
}

fn header_line_scan(text: &str, uri: &Url) -> Vec<CodeLens> {
    let is_header = |line: &str| {
        let trimmed = line.trim_start();
        ["MACHINE", "CONTEXT"].iter().any(|kw| {
            trimmed
                .strip_prefix(kw)
                .is_some_and(|rest| rest.is_empty() || rest.starts_with(char::is_whitespace))
        })
    };
    text.lines()
        .enumerate()
        .filter(|(_, line)| is_header(line))
        .map(|(line_num, line)| {
            let range = Range {
                start: Position {
                    line: line_num as u32,
                    character: 0,
                },
                end: Position {
                    line: line_num as u32,
                    character: line.encode_utf16().count() as u32,
                },
            };
            lens_at(range, uri)
        })
        .collect()
}

/// Everything the spawned open-in-Rodin task needs, resolved up front by the
/// request handler so the task itself never touches server state.
pub struct OpenRequest {
    /// Directory whose Event-B text sources form the project.
    pub source_dir: PathBuf,
    /// In-memory text of open documents, keyed by canonicalized path.
    pub overlay: build::Overlay,
    /// The shared Rodin workspace directory (holds `.metadata` + projects).
    pub workspace_dir: PathBuf,
    /// The raw `rossi.rodin.path` setting ("" → platform default).
    pub configured_rodin_path: String,
    /// Whether the client advertised `window.workDoneProgress`.
    pub progress_supported: bool,
    /// Shared record of files the server wrote into the workspace, so the
    /// sync watcher can tell the server's own writes from Rodin's.
    pub written: sync::WrittenFiles,
}

/// Run the full flow: build into the shared project, register it in the
/// workspace on first contact, and launch (or defer to) the Rodin GUI.
/// All outcomes are reported through the client; the caller only spawns.
pub async fn open_in_rodin(client: Client, request: OpenRequest) {
    let platform = launch::Platform::current();
    let project_name = sanitize_project_name(
        request
            .source_dir
            .file_name()
            .and_then(|s| s.to_str())
            .unwrap_or_default(),
    );
    let project_dir = request.workspace_dir.join(&project_name);

    let progress = Progress::begin(&client, request.progress_supported, "Open in Rodin").await;
    progress.report("building the Rodin project").await;

    let outcome = {
        let source_dir = request.source_dir.clone();
        let overlay = request.overlay;
        let project_dir = project_dir.clone();
        let project_name = project_name.clone();
        tokio::task::spawn_blocking(move || {
            build::build_rodin_project(&source_dir, &overlay, &project_dir, &project_name)
        })
        .await
    };
    let outcome = match outcome {
        Ok(Ok(outcome)) => {
            request.written.lock().extend(outcome.written.iter().cloned());
            outcome
        }
        Ok(Err(message)) => {
            progress.end().await;
            client
                .show_message(MessageType::ERROR, format!("Open in Rodin: {message}"))
                .await;
            return;
        }
        Err(join_error) => {
            progress.end().await;
            client
                .show_message(
                    MessageType::ERROR,
                    format!("Open in Rodin failed internally: {join_error}"),
                )
                .await;
            return;
        }
    };
    if !outcome.error_diagnostics.is_empty() {
        // Matching `rossi build`: erroneous elements were dropped, the
        // checked output was still written — open Rodin on it anyway.
        client
            .show_message(
                MessageType::WARNING,
                format!(
                    "Open in Rodin: the build reported {} error diagnostic(s); \
                     erroneous elements were dropped from the checked files ({})",
                    outcome.error_diagnostics.len(),
                    outcome.error_diagnostics[0]
                ),
            )
            .await;
    }

    if lock::workspace_lock_state(&request.workspace_dir) == lock::LockState::Held {
        progress.end().await;
        client
            .show_message(
                MessageType::INFO,
                format!(
                    "Rodin is already running on this workspace — project '{project_name}' \
                     was rebuilt; Rodin picks the files up automatically (or refresh the \
                     project with F5)."
                ),
            )
            .await;
        return;
    }

    let rodin_path = launch::effective_rodin_path(&request.configured_rodin_path, platform);
    // A concrete path that does not exist gets an actionable error before any
    // spawn attempt; bare command names go straight to the spawn (PATH decides).
    if (rodin_path.contains('/') || rodin_path.contains('\\')) && !Path::new(&rodin_path).exists() {
        progress.end().await;
        client
            .show_message(
                MessageType::ERROR,
                format!(
                    "Rodin was not found at {rodin_path}. Install Rodin or point the \
                     rossi.rodin.path setting at it. (The project was still built at {}.)",
                    project_dir.display()
                ),
            )
            .await;
        return;
    }

    if !launch::project_registered(&request.workspace_dir, &project_name) {
        progress
            .report("registering the project in the Rodin workspace")
            .await;
        let registration = match launch::ant_runner_executable(&rodin_path, platform) {
            Ok(ant_runner) => {
                launch::register_project(&ant_runner, &request.workspace_dir, &project_dir).await
            }
            Err(message) => Err(message),
        };
        if let Err(message) = registration {
            progress.end().await;
            client
                .show_message(
                    MessageType::ERROR,
                    format!("Open in Rodin: {message} (check the rossi.rodin.path setting)"),
                )
                .await;
            return;
        }
    }
    launch::seed_workspace_prefs(&request.workspace_dir);

    progress.report("launching Rodin").await;
    let (command, args) = launch::launch_command(&rodin_path, &request.workspace_dir, platform);
    if let Err(message) = launch::launch_gui(&command, &args) {
        progress.end().await;
        client
            .show_message(
                MessageType::ERROR,
                format!("Open in Rodin: {message} (check the rossi.rodin.path setting)"),
            )
            .await;
        return;
    }
    progress.end().await;
    client
        .show_message(
            MessageType::INFO,
            format!("Opened {project_name} in Rodin."),
        )
        .await;
}

/// `$/progress` reporting against a client-acknowledged token, degrading to
/// log messages when the client lacks `window.workDoneProgress`.
struct Progress {
    client: Client,
    token: Option<ProgressToken>,
}

impl Progress {
    async fn begin(client: &Client, supported: bool, title: &str) -> Self {
        static NEXT_TOKEN: AtomicU64 = AtomicU64::new(0);
        let mut token = None;
        if supported {
            let candidate = ProgressToken::String(format!(
                "rossi-rodin-{}",
                NEXT_TOKEN.fetch_add(1, Ordering::Relaxed)
            ));
            let created = client
                .send_request::<request::WorkDoneProgressCreate>(WorkDoneProgressCreateParams {
                    token: candidate.clone(),
                })
                .await;
            if created.is_ok() {
                client
                    .send_notification::<notification::Progress>(ProgressParams {
                        token: candidate.clone(),
                        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Begin(
                            WorkDoneProgressBegin {
                                title: title.to_string(),
                                cancellable: Some(false),
                                message: None,
                                percentage: None,
                            },
                        )),
                    })
                    .await;
                token = Some(candidate);
            }
        }
        Self {
            client: client.clone(),
            token,
        }
    }

    async fn report(&self, message: &str) {
        match &self.token {
            Some(token) => {
                self.client
                    .send_notification::<notification::Progress>(ProgressParams {
                        token: token.clone(),
                        value: ProgressParamsValue::WorkDone(WorkDoneProgress::Report(
                            WorkDoneProgressReport {
                                cancellable: Some(false),
                                message: Some(message.to_string()),
                                percentage: None,
                            },
                        )),
                    })
                    .await;
            }
            None => {
                self.client
                    .log_message(MessageType::INFO, format!("Open in Rodin: {message}"))
                    .await;
            }
        }
    }

    async fn end(&self) {
        if let Some(token) = &self.token {
            self.client
                .send_notification::<notification::Progress>(ProgressParams {
                    token: token.clone(),
                    value: ProgressParamsValue::WorkDone(WorkDoneProgress::End(
                        WorkDoneProgressEnd { message: None },
                    )),
                })
                .await;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sanitizes_project_names() {
        assert_eq!(sanitize_project_name("cars on bridge"), "cars_on_bridge");
        assert_eq!(sanitize_project_name("..--weird"), "weird");
        assert_eq!(sanitize_project_name("...."), "rossi_project");
        assert_eq!(sanitize_project_name("ok-1.2_x"), "ok-1.2_x");
    }

    #[test]
    fn default_workspace_is_dot_rossi_rodin() {
        assert_eq!(
            default_workspace_dir(Path::new("/proj")),
            PathBuf::from("/proj/.rossi/rodin")
        );
    }

    #[test]
    fn header_scan_finds_machine_and_context_only() {
        let uri = Url::parse("file:///m.eventb").unwrap();
        let text = "CONTEXT c\nEND\nMACHINE m\nEND\nMACHINERY x\nCONTEXTUAL y\n";
        let lenses = header_line_scan(text, &uri);
        assert_eq!(lenses.len(), 2);
        assert_eq!(lenses[0].range.start.line, 0);
        assert_eq!(lenses[1].range.start.line, 2);
        let cmd = lenses[0].command.as_ref().unwrap();
        assert_eq!(cmd.command, COMMAND_OPEN);
        assert_eq!(
            cmd.arguments.as_ref().unwrap()[0],
            serde_json::json!("file:///m.eventb")
        );
    }

    #[test]
    fn parsed_components_anchor_lenses_on_name_spans() {
        let uri = Url::parse("file:///m.eventb").unwrap();
        let text = "MACHINE counters\nEND\n";
        let components = rossi::parse_components(text).unwrap();
        let lenses = code_lenses(&components, text, &uri);
        assert_eq!(lenses.len(), 1);
        assert_eq!(lenses[0].range.start.line, 0);
        // The lens anchors on the name token, not column zero.
        assert_eq!(lenses[0].range.start.character, 8);
    }
}
