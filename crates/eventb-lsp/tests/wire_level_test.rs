//! Wire-level regression tests that drive the real `LspService` end to end,
//! gathered into one binary (each `tests/*.rs` file links its own executable):
//! diagnostics debouncing, the disk-backed workspace symbol index, and the
//! `rossi/operatorTable` custom request.

use serde_json::Value;
use tower_lsp::jsonrpc::Request;

fn notification(method: &'static str, params: Value) -> Request {
    Request::build(method).params(params).finish()
}

mod debounce {
    //! Wire-level regression test for `diagnostics.debounceMs`.
    //!
    //! A burst of `textDocument/didChange` notifications must coalesce into a single
    //! `textDocument/publishDiagnostics` for the final version, rather than one
    //! publish per keystroke. Driving the real `LspService` exercises the debounced
    //! `tokio::spawn` path end to end (a unit test calling the handler would bypass
    //! the runtime that runs the deferred analysis). Each edit's task self-skips at
    //! wake-up unless its version is still the document's latest, so only the final
    //! edit of a burst analyzes.

    use super::notification;
    use eventb_lsp::server::RossiLanguageServer;
    use futures::StreamExt;
    use serde_json::{Value, json};
    use std::time::Duration;
    use tower::{Service, ServiceExt};
    use tower_lsp::LspService;
    use tower_lsp::jsonrpc::Request;

    const DEBOUNCE_MS: u64 = 120;
    const URI: &str = "file:///debounce.eventb";

    /// Read server-to-client messages until the next `publishDiagnostics`, or return
    /// `None` if none arrives within `timeout` (the channel goes quiet).
    async fn next_publish(
        messages: &mut (impl StreamExt<Item = Request> + Unpin),
        timeout: Duration,
    ) -> Option<Value> {
        while let Ok(Some(req)) = tokio::time::timeout(timeout, messages.next()).await {
            if req.method() == "textDocument/publishDiagnostics" {
                return req.params().cloned();
            }
        }
        None
    }

    #[tokio::test(flavor = "current_thread")]
    async fn rapid_edits_publish_diagnostics_once() {
        let (mut service, mut messages) = LspService::build(RossiLanguageServer::new).finish();

        // Initialize with a short, explicit debounce window.
        let init = Request::build("initialize")
            .id(1)
            .params(json!({
                "capabilities": {},
                "initializationOptions": { "diagnostics": { "debounceMs": DEBOUNCE_MS } }
            }))
            .finish();
        service.ready().await.unwrap().call(init).await.unwrap();

        // Open a document with a broken invariant. `didOpen` analyzes inline (not
        // debounced), so its diagnostics publish promptly.
        let open = notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": URI,
                    "languageId": "eventb",
                    "version": 1,
                    "text": "MACHINE m\nINVARIANTS\n@i x ∈\nEND\n"
                }
            }),
        );
        service.ready().await.unwrap().call(open).await.unwrap();

        let opened = next_publish(&mut messages, Duration::from_millis(500))
            .await
            .expect("didOpen publishes diagnostics inline");
        assert_eq!(opened["version"], json!(1), "open publishes for version 1");

        // Fire several edits back to back, faster than the debounce window. Each
        // bumps the document version, so the earlier edits' tasks will find
        // themselves superseded at wake-up.
        for version in 2..=5 {
            let change = notification(
                "textDocument/didChange",
                json!({
                    "textDocument": { "uri": URI, "version": version },
                    "contentChanges": [
                        { "text": format!("MACHINE m\nINVARIANTS\n@i x ∈ {version}\nEND\n") }
                    ]
                }),
            );
            service.ready().await.unwrap().call(change).await.unwrap();
        }

        // Let the tasks fire, then drain. Exactly one publish — for the final
        // version — should have arrived; the earlier four found a newer version at
        // wake-up and bowed out.
        tokio::time::sleep(Duration::from_millis(DEBOUNCE_MS + 150)).await;

        let mut publishes = Vec::new();
        while let Some(params) = next_publish(&mut messages, Duration::from_millis(100)).await {
            publishes.push(params);
        }

        assert_eq!(
            publishes.len(),
            1,
            "a burst of edits collapses to one diagnostics publish, got {publishes:?}"
        );
        assert_eq!(
            publishes[0]["version"],
            json!(5),
            "the surviving publish is for the latest version"
        );
    }

    #[tokio::test(flavor = "current_thread")]
    async fn zero_debounce_publishes_each_edit_inline() {
        let (mut service, mut messages) = LspService::build(RossiLanguageServer::new).finish();

        // A zero window opts out of debouncing: each edit analyzes inline.
        let init = Request::build("initialize")
            .id(1)
            .params(json!({
                "capabilities": {},
                "initializationOptions": { "diagnostics": { "debounceMs": 0 } }
            }))
            .finish();
        service.ready().await.unwrap().call(init).await.unwrap();

        let open = notification(
            "textDocument/didOpen",
            json!({
                "textDocument": {
                    "uri": URI,
                    "languageId": "eventb",
                    "version": 1,
                    "text": "MACHINE m\nINVARIANTS\n@i x ∈\nEND\n"
                }
            }),
        );
        service.ready().await.unwrap().call(open).await.unwrap();
        let opened = next_publish(&mut messages, Duration::from_millis(500)).await;
        assert_eq!(opened.expect("open publishes")["version"], json!(1));

        // Each change publishes synchronously, in order — no coalescing.
        for version in 2..=3 {
            let change = notification(
                "textDocument/didChange",
                json!({
                    "textDocument": { "uri": URI, "version": version },
                    "contentChanges": [
                        { "text": format!("MACHINE m\nINVARIANTS\n@i x ∈ {version}\nEND\n") }
                    ]
                }),
            );
            service.ready().await.unwrap().call(change).await.unwrap();
            let published = next_publish(&mut messages, Duration::from_millis(500))
                .await
                .expect("each inline edit publishes diagnostics");
            assert_eq!(published["version"], json!(version));
        }
    }

    #[tokio::test(flavor = "current_thread")]
    async fn debounce_does_not_cross_document_lifecycles() {
        const LIFECYCLE_DEBOUNCE_MS: u64 = 200;

        let (mut service, mut messages) = LspService::build(RossiLanguageServer::new).finish();
        let init = Request::build("initialize")
            .id(1)
            .params(json!({
                "capabilities": {},
                "initializationOptions": {
                    "diagnostics": { "debounceMs": LIFECYCLE_DEBOUNCE_MS }
                }
            }))
            .finish();
        service.ready().await.unwrap().call(init).await.unwrap();

        let open = |version: i32, name: &str| {
            notification(
                "textDocument/didOpen",
                json!({
                    "textDocument": {
                        "uri": URI,
                        "languageId": "eventb",
                        "version": version,
                        "text": format!("CONTEXT {name}\nEND\n")
                    }
                }),
            )
        };
        let change = |version: i32, name: &str| {
            notification(
                "textDocument/didChange",
                json!({
                    "textDocument": { "uri": URI, "version": version },
                    "contentChanges": [{ "text": format!("CONTEXT {name}\nEND\n") }]
                }),
            )
        };

        service
            .ready()
            .await
            .unwrap()
            .call(open(0, "first"))
            .await
            .unwrap();
        next_publish(&mut messages, Duration::from_millis(500))
            .await
            .expect("first open publishes");
        service
            .ready()
            .await
            .unwrap()
            .call(change(1, "first_changed"))
            .await
            .unwrap();

        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didClose",
                json!({ "textDocument": { "uri": URI } }),
            ))
            .await
            .unwrap();
        next_publish(&mut messages, Duration::from_millis(500))
            .await
            .expect("close clears diagnostics");
        service
            .ready()
            .await
            .unwrap()
            .call(open(0, "second"))
            .await
            .unwrap();
        next_publish(&mut messages, Duration::from_millis(500))
            .await
            .expect("second open publishes");

        tokio::time::sleep(Duration::from_millis(100)).await;
        service
            .ready()
            .await
            .unwrap()
            .call(change(1, "second_changed"))
            .await
            .unwrap();

        // Lifecycle A's version-1 timer wakes during this interval. It must not
        // analyze lifecycle B merely because B has independently reached version 1.
        tokio::time::sleep(Duration::from_millis(130)).await;
        assert!(
            next_publish(&mut messages, Duration::from_millis(20))
                .await
                .is_none(),
            "an old lifecycle's debounce task must not publish for the new document"
        );

        let published = next_publish(&mut messages, Duration::from_millis(150))
            .await
            .expect("the current lifecycle publishes after its own debounce");
        assert_eq!(published["version"], json!(1));
    }
}

mod workspace_symbols {
    //! Wire-level regressions for the disk-backed workspace symbol index.

    use super::notification;
    use eventb_lsp::lsp_types::Url;
    use eventb_lsp::server::RossiLanguageServer;
    use futures::StreamExt;
    use serde_json::json;
    use std::path::{Path, PathBuf};
    use tower::{Service, ServiceExt};
    use tower_lsp::LspService;
    use tower_lsp::jsonrpc::Request;

    struct TempWorkspace(PathBuf);

    impl TempWorkspace {
        fn new() -> Self {
            let path = PathBuf::from(env!("CARGO_TARGET_TMPDIR")).join(format!(
                "workspace-symbols-test-{}-{}",
                std::process::id(),
                std::time::SystemTime::now()
                    .duration_since(std::time::UNIX_EPOCH)
                    .unwrap()
                    .as_nanos()
            ));
            std::fs::create_dir_all(&path).unwrap();
            Self(path)
        }
    }

    impl AsRef<Path> for TempWorkspace {
        fn as_ref(&self) -> &Path {
            &self.0
        }
    }

    impl Drop for TempWorkspace {
        fn drop(&mut self) {
            let _ = std::fs::remove_dir_all(&self.0);
        }
    }

    #[tokio::test(flavor = "current_thread")]
    async fn disk_symbols_are_overlaid_while_open_and_restored_on_close() {
        let workspace = TempWorkspace::new();
        let path = workspace.as_ref().join("model.eventb");
        std::fs::write(
            &path,
            "CONTEXT disk_context\nCONSTANTS\n    disk_value\nEND\n",
        )
        .unwrap();
        #[cfg(unix)]
        std::os::unix::fs::symlink(&path, workspace.as_ref().join("alias.eventb")).unwrap();
        let root_uri = Url::from_file_path(workspace.as_ref()).unwrap();
        let file_uri = Url::from_file_path(&path).unwrap();

        let (mut service, mut socket) = LspService::build(RossiLanguageServer::new).finish();
        tokio::spawn(async move { while socket.next().await.is_some() {} });
        let init = Request::build("initialize")
            .id(1)
            .params(json!({
                "capabilities": {},
                "workspaceFolders": [{ "uri": root_uri, "name": "test" }]
            }))
            .finish();
        service.ready().await.unwrap().call(init).await.unwrap();
        service
            .ready()
            .await
            .unwrap()
            .call(notification("initialized", json!({})))
            .await
            .unwrap();

        macro_rules! symbol_names {
            ($id:expr, $query:expr) => {{
                let request = Request::build("workspace/symbol")
                    .id($id)
                    .params(json!({ "query": $query }))
                    .finish();
                let response = service
                    .ready()
                    .await
                    .unwrap()
                    .call(request)
                    .await
                    .unwrap()
                    .expect("workspace/symbol must produce a response");
                let (_id, result) = response.into_parts();
                result
                    .expect("workspace/symbol request must succeed")
                    .as_array()
                    .expect("workspace/symbol result must be an array")
                    .iter()
                    .map(|symbol| symbol["name"].as_str().unwrap().to_string())
                    .collect::<Vec<_>>()
            }};
        }

        assert_eq!(symbol_names!(2, "disk_context"), ["disk_context"]);
        assert_eq!(symbol_names!(3, "disk_value"), ["disk_value"]);

        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didOpen",
                json!({
                    "textDocument": {
                        "uri": file_uri,
                        "languageId": "eventb",
                        "version": 1,
                        "text": "CONTEXT open_context\nCONSTANTS\n    open_value\nEND\n"
                    }
                }),
            ))
            .await
            .unwrap();

        assert!(symbol_names!(4, "disk_value").is_empty());
        assert_eq!(symbol_names!(5, "open_value"), ["open_value"]);

        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didClose",
                json!({ "textDocument": { "uri": file_uri } }),
            ))
            .await
            .unwrap();

        assert_eq!(symbol_names!(6, "disk_value"), ["disk_value"]);
        assert!(symbol_names!(7, "open_value").is_empty());

        let saved_source = "CONTEXT saved_context\nCONSTANTS\n    saved_value\nEND\n";
        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didOpen",
                json!({
                    "textDocument": {
                        "uri": file_uri,
                        "languageId": "eventb",
                        "version": 2,
                        "text": saved_source
                    }
                }),
            ))
            .await
            .unwrap();
        std::fs::write(&path, saved_source).unwrap();
        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didSave",
                json!({ "textDocument": { "uri": file_uri } }),
            ))
            .await
            .unwrap();
        service
            .ready()
            .await
            .unwrap()
            .call(notification(
                "textDocument/didClose",
                json!({ "textDocument": { "uri": file_uri } }),
            ))
            .await
            .unwrap();

        assert_eq!(symbol_names!(8, "saved_value"), ["saved_value"]);
        assert!(symbol_names!(9, "disk_value").is_empty());
    }
}

mod operator_table {
    //! Wire-level regression test for the `rossi/operatorTable` custom request.
    //!
    //! Pins `operator_table` to a parameter-less signature: the VS Code client sends
    //! this request with no `params`, which a params-taking handler rejects (see the
    //! handler doc in `server.rs` for the tower-lsp routing detail). The test drives
    //! the real `LspService` with a params-less request so that failure is exercised
    //! end to end — a unit test calling `operator_table()` directly would bypass
    //! tower-lsp's param extraction, which is exactly where the bug lived.

    use eventb_lsp::server::RossiLanguageServer;
    use serde_json::json;
    use tower::{Service, ServiceExt};
    use tower_lsp::LspService;
    use tower_lsp::jsonrpc::Request;

    #[tokio::test(flavor = "current_thread")]
    async fn operator_table_succeeds_without_params_field() {
        let (mut service, _socket) = LspService::build(RossiLanguageServer::new)
            .custom_method("rossi/operatorTable", RossiLanguageServer::operator_table)
            .finish();

        // A real client session initializes before issuing requests.
        let init = Request::build("initialize")
            .id(1)
            .params(json!({ "capabilities": {} }))
            .finish();
        service.ready().await.unwrap().call(init).await.unwrap();

        // Exactly what vscode-languageclient emits for a paramless sendRequest:
        // a request with NO `params` field (the builder omits it by default).
        let request = Request::build("rossi/operatorTable").id(2).finish();
        let response = service
            .ready()
            .await
            .unwrap()
            .call(request)
            .await
            .unwrap()
            .expect("custom request must produce a response");

        let (_id, result) = response.into_parts();
        let value = result.expect("rossi/operatorTable must succeed when params is absent");
        let rows = value.as_array().expect("operator table is a JSON array");
        assert!(
            rows.iter()
                .any(|row| row["ascii"] == "/=" && row["unicode"] == "≠" && row["eager"] == true),
            "operator table must carry the /= -> ≠ eager mapping; got {value}"
        );
        // `,,` is an ASCII input alias for the maplet ↦ (Rodin's keyboard); it must
        // ride along as its own eager row so the editor converts it as you type.
        assert!(
            rows.iter()
                .any(|row| row["ascii"] == ",," && row["unicode"] == "↦" && row["eager"] == true),
            "operator table must carry the ,, -> ↦ eager mapping; got {value}"
        );
    }
}
