//! Configuration management for Rossi LSP Server
//!
//! This module handles:
//! - Reading configuration from the LSP client
//! - Listening for configuration changes
//! - Distributing configuration to all providers

use parking_lot::RwLock;
use serde::{Deserialize, Serialize};
use serde_json::Value;
use std::sync::Arc;

/// Complete Rossi LSP server configuration
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RossiConfig {
    /// Formatting configuration
    #[serde(default)]
    pub format: FormatConfig,

    /// Diagnostics configuration
    #[serde(default)]
    pub diagnostics: DiagnosticsConfig,

    /// Completion configuration
    #[serde(default)]
    pub completion: CompletionConfig,

    /// Rodin integration configuration
    #[serde(default)]
    pub rodin: RodinConfig,
}

impl RossiConfig {
    /// Parse configuration supplied by an LSP client.
    ///
    /// Some clients send the configured section directly (`{"format": ...}`),
    /// while others send the full settings object (`{"rossi": {"format": ...}}`).
    pub fn from_client_settings(settings: &Value) -> Result<Self, serde_json::Error> {
        match settings.get("rossi") {
            Some(rossi_settings) => serde_json::from_value(rossi_settings.clone()),
            None => serde_json::from_value(settings.clone()),
        }
    }
}

/// Formatting configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct FormatConfig {
    /// Use Unicode operators (∧, ∨, ⇒) instead of ASCII (/\, \/, =>)
    #[serde(default = "default_use_unicode")]
    pub use_unicode: bool,

    /// Indentation string (e.g., "  " or "    ")
    #[serde(default = "default_indentation")]
    pub indentation: String,
}

impl FormatConfig {
    /// The pretty-printer this configuration denotes — the single mapping
    /// used everywhere the server renders Event-B text into a user's file
    /// (`textDocument/formatting` and the Rodin model-edit sync), so the two
    /// can never format the same file differently. Every field is pinned
    /// deliberately; editor output stays portable (no private-use glyphs).
    pub fn printer(&self) -> rossi::PrettyPrinter {
        rossi::PrettyPrinter {
            use_unicode: self.use_unicode,
            indent: self.indentation.clone(),
            private_use_glyphs: false,
            formula_spacing: rossi::FormulaSpacing::Readable,
            typed_decls: false,
        }
    }
}

impl Default for FormatConfig {
    fn default() -> Self {
        Self {
            use_unicode: default_use_unicode(),
            indentation: default_indentation(),
        }
    }
}

fn default_use_unicode() -> bool {
    true
}

fn default_indentation() -> String {
    "    ".to_string()
}

/// Diagnostics configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct DiagnosticsConfig {
    /// Enable diagnostics
    #[serde(default = "default_diagnostics_enabled")]
    pub enabled: bool,

    /// Delay in milliseconds the server waits after the last edit before it
    /// reparses, refreshes the indexes, and republishes diagnostics. Coalesces
    /// rapid keystrokes into a single analysis. `0` analyzes on every edit.
    #[serde(default = "default_debounce_ms")]
    pub debounce_ms: u32,
}

impl Default for DiagnosticsConfig {
    fn default() -> Self {
        Self {
            enabled: default_diagnostics_enabled(),
            debounce_ms: default_debounce_ms(),
        }
    }
}

fn default_diagnostics_enabled() -> bool {
    true
}

fn default_debounce_ms() -> u32 {
    500
}

/// Completion configuration
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct CompletionConfig {
    /// Enable completion
    #[serde(default = "default_completion_enabled")]
    pub enabled: bool,
}

impl Default for CompletionConfig {
    fn default() -> Self {
        Self {
            enabled: default_completion_enabled(),
        }
    }
}

fn default_completion_enabled() -> bool {
    true
}

/// Rodin integration configuration ("Open in Rodin" code lens)
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(rename_all = "camelCase")]
pub struct RodinConfig {
    /// Rodin executable path, macOS `.app` bundle path, or macOS application
    /// name. Empty selects the platform default (`/Applications/Rodin.app`,
    /// `rodin.exe`, or `rodin`).
    #[serde(default)]
    pub path: String,

    /// Directory used as the shared Rodin workspace. Empty selects
    /// `<workspace-root>/.rossi/rodin`.
    #[serde(default)]
    pub workspace: String,

    /// Mutual live synchronization with a running Rodin. While Rodin is
    /// open on the shared workspace, saving a source file rebuilds its
    /// project (Rodin's seeded auto-refresh then picks the edit up within a
    /// few seconds), and edits saved in Rodin flow back into the `.eventb`
    /// sources via the workspace watcher (three-way model merge, proof
    /// status refresh). Model edits Rodin saved while no server was running
    /// are caught up when the watcher starts. On by default; turning it off
    /// also stops the watcher.
    #[serde(default = "default_sync")]
    pub sync: bool,

    /// Bridge proof files (`.bpr`/`.bps`/`.bpo`) between the checkout and
    /// the shared workspace at "Open in Rodin" session boundaries: the
    /// files sitting next to the sources are copied into the Rodin project
    /// when the lens runs (the checkout wins; nothing in the workspace is
    /// deleted), and the project's files are copied back next to the
    /// sources when the launched Rodin exits (the workspace wins; a proof
    /// deleted in Rodin is deleted next to the sources too). Captured when
    /// the lens runs — flipping it mid-session does not stop an armed
    /// mirror. The exit mirror needs the Eclipse workspace lock probe and
    /// is unavailable on Windows. On by default.
    #[serde(default = "default_mirror_proofs")]
    pub mirror_proofs: bool,
}

impl Default for RodinConfig {
    fn default() -> Self {
        Self {
            path: String::new(),
            workspace: String::new(),
            sync: default_sync(),
            mirror_proofs: default_mirror_proofs(),
        }
    }
}

fn default_sync() -> bool {
    true
}

fn default_mirror_proofs() -> bool {
    true
}

/// Configuration manager that holds the current configuration
pub struct ConfigManager {
    config: RwLock<Arc<RossiConfig>>,
}

impl ConfigManager {
    /// Create a new configuration manager with default settings
    pub fn new() -> Self {
        Self {
            config: RwLock::new(Arc::new(RossiConfig::default())),
        }
    }

    /// Get a cheap snapshot of the current configuration.
    pub fn get(&self) -> Arc<RossiConfig> {
        Arc::clone(&self.config.read())
    }

    /// Update the entire configuration
    pub fn update(&self, config: RossiConfig) {
        *self.config.write() = Arc::new(config);
    }
}

impl Default for ConfigManager {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_config() {
        let config = RossiConfig::default();

        assert!(config.format.use_unicode);
        assert_eq!(config.format.indentation, "    ");

        assert!(config.diagnostics.enabled);
        assert_eq!(config.diagnostics.debounce_ms, 500);

        assert!(config.completion.enabled);

        assert!(config.rodin.sync);
        assert!(config.rodin.mirror_proofs);
    }

    #[test]
    fn test_config_manager_get_set() {
        let manager = ConfigManager::new();

        // Check defaults
        let config = manager.get();
        assert!(config.format.use_unicode);

        // Update configuration
        let mut new_config = (*config).clone();
        new_config.format.use_unicode = false;
        new_config.format.indentation = "  ".to_string();
        manager.update(new_config);

        // Check updated values
        let updated = manager.get();
        assert!(!updated.format.use_unicode);
        assert_eq!(updated.format.indentation, "  ");
    }

    #[test]
    fn test_json_serialization() {
        let config = RossiConfig::default();

        // Serialize to JSON
        let json = serde_json::to_string(&config).unwrap();
        assert!(json.contains("format"));
        assert!(json.contains("useUnicode"));

        // Deserialize from JSON
        let deserialized: RossiConfig = serde_json::from_str(&json).unwrap();
        assert_eq!(config.format.use_unicode, deserialized.format.use_unicode);
    }

    #[test]
    fn test_json_with_custom_values() {
        let json = r#"{
            "format": {
                "useUnicode": false,
                "indentation": "  "
            },
            "diagnostics": {
                "enabled": false,
                "debounceMs": 1000
            },
            "completion": {
                "enabled": true
            }
        }"#;

        let config: RossiConfig = serde_json::from_str(json).unwrap();

        assert!(!config.format.use_unicode);
        assert_eq!(config.format.indentation, "  ");

        assert!(!config.diagnostics.enabled);
        assert_eq!(config.diagnostics.debounce_ms, 1000);

        assert!(config.completion.enabled);
    }

    #[test]
    fn test_partial_json_uses_defaults() {
        let json = r#"{
            "format": {
                "useUnicode": false
            }
        }"#;

        let config: RossiConfig = serde_json::from_str(json).unwrap();

        // Specified value
        assert!(!config.format.use_unicode);

        // Default values
        assert_eq!(config.format.indentation, "    ");
        assert!(config.diagnostics.enabled);
        assert!(config.rodin.mirror_proofs);
    }

    #[test]
    fn test_client_settings_direct_config() {
        let settings = serde_json::json!({
            "format": {
                "useUnicode": false,
                "indentation": "  "
            },
            "diagnostics": {
                "enabled": false
            }
        });

        let config = RossiConfig::from_client_settings(&settings).unwrap();
        assert!(!config.format.use_unicode);
        assert_eq!(config.format.indentation, "  ");
        assert!(!config.diagnostics.enabled);
    }

    #[test]
    fn test_client_settings_nested_rossi_config() {
        let settings = serde_json::json!({
            "rossi": {
                "format": {
                    "useUnicode": false
                },
                "diagnostics": {
                    "debounceMs": 250
                }
            }
        });

        let config = RossiConfig::from_client_settings(&settings).unwrap();
        assert!(!config.format.use_unicode);
        assert_eq!(config.diagnostics.debounce_ms, 250);
    }

    #[test]
    fn test_rodin_config_defaults_and_nested_parse() {
        let config = RossiConfig::default();
        assert_eq!(config.rodin.path, "");
        assert_eq!(config.rodin.workspace, "");
        assert!(config.rodin.sync);

        let settings = serde_json::json!({
            "rossi": {
                "rodin": {
                    "path": "/Applications/Rodin.app",
                    "workspace": "/tmp/rodin-ws",
                    "sync": false
                }
            }
        });
        let config = RossiConfig::from_client_settings(&settings).unwrap();
        assert_eq!(config.rodin.path, "/Applications/Rodin.app");
        assert_eq!(config.rodin.workspace, "/tmp/rodin-ws");
        assert!(!config.rodin.sync);

        // An absent key keeps sync on.
        let settings = serde_json::json!({ "rossi": { "rodin": {} } });
        let config = RossiConfig::from_client_settings(&settings).unwrap();
        assert!(config.rodin.sync);
    }
}
