//! Document formatting provider
//!
//! This module provides document formatting using the Event-B pretty printer.

use crate::config::FormatConfig;
use crate::lsp_types::{Position, Range, TextEdit};

/// Format a document using the supplied server configuration.
pub fn format(text: &str, config: &FormatConfig) -> Result<Vec<TextEdit>, String> {
    // Delegate to the shared formatting core so editor and `rossi fmt`
    // formatting never diverge; the printer comes from the one config
    // mapping ([`FormatConfig::printer`]) shared with the Rodin model sync.
    let printer = config.printer();
    let formatted = rossi::format_str(text, &printer).map_err(|e| format!("Parse error: {}", e))?;

    // Create a text edit that replaces the entire document
    // Use a large end position to ensure we replace everything
    Ok(vec![TextEdit {
        range: Range {
            start: Position::new(0, 0),
            end: Position::new(u32::MAX, u32::MAX),
        },
        new_text: formatted,
    }])
}

#[cfg(test)]
mod tests {
    use super::*;

    fn format_default(source: &str) -> Result<Vec<TextEdit>, String> {
        format(source, &FormatConfig::default())
    }

    #[test]
    fn test_format_simple_context() {
        let source = "CONTEXT test SETS STATUS END";

        let result = format_default(source);
        assert!(result.is_ok());

        let edits = result.unwrap();
        assert_eq!(edits.len(), 1);

        let formatted = &edits[0].new_text;
        assert!(formatted.contains("context test"));
        assert!(formatted.contains("sets STATUS"));
        assert!(formatted.ends_with("end\n"));
    }

    #[test]
    fn test_format_with_unicode() {
        let config = FormatConfig {
            use_unicode: true,
            indentation: "    ".to_string(),
            ..FormatConfig::default()
        };

        let source = r#"
        CONTEXT test
        AXIOMS
            @axm1 1 > 0
        END
        "#;

        let result = format(source, &config);
        assert!(result.is_ok());

        let formatted = result.unwrap()[0].new_text.clone();
        // Check it formatted successfully
        assert!(formatted.contains("context"));
        assert!(formatted.contains("axioms"));
    }

    #[test]
    fn test_format_with_ascii() {
        let config = FormatConfig {
            use_unicode: false,
            indentation: "    ".to_string(),
            ..FormatConfig::default()
        };

        let source = r#"
        CONTEXT test
        AXIOMS
            @axm1 true
        END
        "#;

        let result = format(source, &config);
        assert!(result.is_ok());

        let formatted = result.unwrap()[0].new_text.clone();
        assert!(formatted.contains("context"));
        assert!(formatted.contains("axioms"));
        // ASCII mode renders the predicate literal ⊤ as lowercase `true`.
        assert!(formatted.contains("true"));
    }

    #[test]
    fn test_format_with_camille_style() {
        let config = FormatConfig {
            style: "camille".to_string(),
            ..FormatConfig::default()
        };

        let source = "CONTEXT test SETS STATUS END";
        let formatted = format(source, &config).unwrap()[0].new_text.clone();
        assert!(
            formatted.starts_with("context test\n\nsets STATUS\n"),
            "expected camille-style output, got:\n{formatted}"
        );
    }

    #[test]
    fn test_format_with_custom_indentation() {
        let config = FormatConfig {
            use_unicode: true,
            indentation: "    ".to_string(),
            ..FormatConfig::default()
        };

        let source = r#"
        CONTEXT test
        SETS
            STATUS
        END
        "#;

        let result = format(source, &config);
        assert!(result.is_ok());

        let formatted = result.unwrap()[0].new_text.clone();
        // The explicit 4-space indentation overrides the preset's 2 spaces
        // for indented items (the camille sets list itself stays inline).
        assert!(formatted.contains("sets STATUS"), "got:\n{formatted}");
    }

    #[test]
    fn test_format_invalid_syntax() {
        let source = "CONTEXT"; // Invalid - missing name and END

        let result = format_default(source);
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("Parse error"));
    }

    #[test]
    fn test_format_machine() {
        let source = r#"
        MACHINE counter
        VARIABLES count
        INVARIANTS @inv1 count >= 0
        EVENTS
            EVENT INITIALISATION
            THEN
                @act1 count := 0
            END
        END
        "#;

        let result = format_default(source);
        assert!(result.is_ok());

        let formatted = result.unwrap()[0].new_text.clone();
        assert!(formatted.contains("machine counter"));
        assert!(formatted.contains("variables count"));
        assert!(formatted.contains("invariants"));
        assert!(formatted.contains("INITIALISATION"));
    }

    #[test]
    fn test_format_idempotent() {
        let source = r#"
        CONTEXT test
        SETS
            STATUS
        END
        "#;

        // Format once
        let result1 = format_default(source);
        assert!(result1.is_ok());
        let formatted1 = result1.unwrap()[0].new_text.clone();

        // Format again
        let result2 = format_default(&formatted1);
        assert!(result2.is_ok());
        let formatted2 = result2.unwrap()[0].new_text.clone();

        // Should be the same (idempotent)
        assert_eq!(formatted1, formatted2);
    }

    #[test]
    fn test_format_preserves_comments() {
        // Issue #31: Format Document must not destroy documentation.
        let source = "CONTEXT c\n// important: do not change\nAXIOMS\n    @axm1 1 = 1 // why: invariant base\nEND\n";
        let formatted = format_default(source).unwrap()[0].new_text.clone();

        assert!(formatted.contains("// important: do not change"));
        assert!(formatted.contains("// why: invariant base"));
    }
}
