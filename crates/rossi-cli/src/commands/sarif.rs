//! SARIF 2.1.0 emitter for `rossi validate`.
//!
//! Spec: <https://docs.oasis-open.org/sarif/sarif/v2.1.0/sarif-v2.1.0.html>.
//! Only the subset relevant to a single-driver validator is emitted (no
//! conversions, no graphs, no taxonomies).

use rossi_build::{RuleId, Severity};
use serde_json::{Value, json};
use std::io::{self, Write};

use crate::commands::validate::{Region, ValidationResult};

const SCHEMA_URI: &str = "https://raw.githubusercontent.com/oasis-tcs/sarif-spec/master/Schemata/sarif-schema-2.1.0.json";

const INFORMATION_URI: &str = "https://github.com/eventb-rossi/rossi";

/// Serialise `results` as a SARIF 2.1.0 document and write it to `out`.
///
/// `category` names the analysis this run belongs to. Whatever the inputs,
/// every row goes into the one run — code scanning rejects an upload whose
/// runs share a category, so a document that split rows across runs could not
/// be uploaded at all.
pub fn emit(
    results: &[ValidationResult],
    category: Option<&str>,
    mut out: impl Write,
) -> io::Result<()> {
    let doc = build_document(results, category);
    serde_json::to_writer_pretty(&mut out, &doc)
        .map_err(|e| io::Error::new(e.io_error_kind().unwrap_or(io::ErrorKind::Other), e))?;
    writeln!(out)?;
    Ok(())
}

fn build_document(results: &[ValidationResult], category: Option<&str>) -> Value {
    let rules: Vec<Value> = RuleId::all().iter().map(|r| rule_descriptor(*r)).collect();
    let sarif_results: Vec<Value> = results.iter().filter_map(result_to_sarif).collect();

    let mut run = json!({
        "tool": {
            "driver": {
                "name": "rossi",
                "version": env!("CARGO_PKG_VERSION"),
                "informationUri": INFORMATION_URI,
                "rules": rules,
            }
        },
        "results": sarif_results,
    });
    if let Some(category) = category {
        run["automationDetails"] = json!({ "id": category });
    }

    json!({
        "$schema": SCHEMA_URI,
        "version": "2.1.0",
        "runs": [run],
    })
}

fn rule_descriptor(rule: RuleId) -> Value {
    json!({
        "id": rule.code(),
        "name": rule.name(),
        "shortDescription": { "text": rule.name() },
        "fullDescription": { "text": rule.help() },
        "defaultConfiguration": { "level": sarif_level(rule.default_severity()) },
    })
}

fn result_to_sarif(result: &ValidationResult) -> Option<Value> {
    let message = result.error.as_ref()?;
    let level = sarif_level(result.severity.unwrap_or(Severity::Warning));
    let uri = uri_for(result);

    let mut location = json!({
        "physicalLocation": {
            "artifactLocation": { "uri": uri }
        }
    });
    if let Some(region) = &result.region {
        location["physicalLocation"]["region"] = region_to_sarif(region);
    }
    if let Some(origin) = &result.origin {
        location["logicalLocations"] = json!([{ "name": origin }]);
    }

    let mut sarif_result = json!({
        "level": level,
        "message": { "text": message },
        "locations": [location],
    });
    if let Some(rule) = result.rule_id {
        sarif_result["ruleId"] = json!(rule.code());
    }
    Some(sarif_result)
}

/// A SARIF `region` object (1-indexed lines/columns, character units).
fn region_to_sarif(region: &Region) -> Value {
    json!({
        "startLine": region.start_line,
        "startColumn": region.start_column,
        "endLine": region.end_line,
        "endColumn": region.end_column,
    })
}

/// The `artifactLocation.uri` for a row.
///
/// A consumer resolves this against the repository tree, so a member of a
/// directory must be the path it really is (`proj/M.eventb`); only an archive
/// member — which is not a file on disk — takes SARIF's `!/` separator. URIs
/// are `/`-separated, so a Windows path is normalised on the way out.
fn uri_for(result: &ValidationResult) -> String {
    result.portable_path()
}

fn sarif_level(severity: Severity) -> &'static str {
    match severity {
        Severity::Error => "error",
        Severity::Warning => "warning",
        Severity::Info => "note",
    }
}
