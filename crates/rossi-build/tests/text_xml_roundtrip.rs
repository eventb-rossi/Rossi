//! Pins the semantic round-trip the LSP's Rodin model-edit sync rests on:
//! text → components → Rodin XML → re-import → pretty-print → re-parse must
//! reach a `to_xml` fixed point. If an AST detail survives parsing but not
//! the XML or the pretty-printer, automatic sync-back would corrupt or
//! endlessly re-modify sources — this test makes such a regression loud.
//!
//! One normalization hop is allowed: XML attribute-value normalization
//! collapses newlines inside comments to spaces on the first import (the
//! exporter writes literal newlines, which any conformant XML parser
//! normalizes). The fixed point is therefore asserted on the *imported*
//! component's XML — everything after that first hop must be stable, and
//! the model-edit sync normalizes its comparison base the same way.

use rossi::{PrettyPrinter, component_filename, parse_components, to_xml};
use rossi_build::ProjectComponent;

#[test]
fn examples_reach_a_to_xml_fixed_point() {
    let examples = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../rossi/examples");
    let printer = PrettyPrinter::default();
    let mut checked = 0;

    let mut paths: Vec<_> = std::fs::read_dir(&examples)
        .expect("examples directory")
        .flatten()
        .map(|e| e.path())
        .filter(|p| p.extension().and_then(|e| e.to_str()) == Some("eventb"))
        .collect();
    paths.sort();

    for path in paths {
        let text = std::fs::read_to_string(&path).unwrap();
        let Ok(components) = parse_components(&text) else {
            // Error-recovery fixtures are out of scope for the round trip.
            continue;
        };
        for component in components {
            let filename = component_filename(&component);
            let exported = to_xml(&component);

            let imported =
                ProjectComponent::from_xml(filename.clone(), &exported).unwrap_or_else(|e| {
                    panic!("{}: {filename}: re-import failed: {e}", path.display())
                });
            // The normalized form (after the one allowed hop): from here on,
            // XML → import → XML must be a fixed point.
            let xml = to_xml(&imported.component);
            let reimported =
                ProjectComponent::from_xml(filename.clone(), &xml).unwrap_or_else(|e| {
                    panic!("{}: {filename}: re-import failed: {e}", path.display())
                });
            assert_eq!(
                to_xml(&reimported.component),
                xml,
                "{}: {filename}: normalized XML → import → XML is not a fixed point",
                path.display()
            );

            let printed = printer.print_component(&imported.component);
            let reparsed = parse_components(&printed).unwrap_or_else(|e| {
                panic!(
                    "{}: {filename}: pretty-printed import does not parse: {e}\n{printed}",
                    path.display()
                )
            });
            assert_eq!(reparsed.len(), 1, "{}: {filename}", path.display());
            assert_eq!(
                to_xml(&reparsed[0]),
                xml,
                "{}: {filename}: print → parse drifted from the imported XML",
                path.display()
            );
            checked += 1;
        }
    }
    assert!(
        checked >= 5,
        "expected several example components, got {checked}"
    );
}
