//! End-to-end test: a context with only carrier sets should produce a .bcc
//! whose scCarrierSet rows semantically match Rodin's output.
//!
//! Fixture is inlined so this test runs without external files.

use rossi_build::{Project, ProjectComponent, build};

/// The raw AuctionContext.buc fixture.
/// Trimmed of the `text_representation` and `text_lastmodified` attributes
/// that Rodin puts on the root and which the parser already drops.
const AUCTION_CONTEXT_BUC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.contextFile org.eventb.core.configuration="org.eventb.core.fwd;org.eventb.codegen.ui.cgConfig;de.prob.symbolic.ctxBase;de.prob.units.mchBase" version="3">
<org.eventb.core.carrierSet name="_w4LsYO5MEeSpR9iqQeSCVw" org.eventb.core.identifier="USERS"/>
<org.eventb.core.carrierSet name="_qJ3S4O5PEeSpR9iqQeSCVw" org.eventb.core.identifier="AUCTIONS"/>
<org.eventb.core.carrierSet name="_4PKc0O5TEeSpR9iqQeSCVw" org.eventb.core.identifier="ITEMS"/>
</org.eventb.core.contextFile>
"#;

fn make_project() -> Project {
    let pc = ProjectComponent::from_xml("AuctionContext.buc", AUCTION_CONTEXT_BUC).expect("parse");
    Project::new("COMP1216", vec![pc])
}

/// Matches Rodin's AuctionContext.bcc byte-for-byte, modulo trailing newline.
#[test]
fn auction_context_bcc_is_byte_exact() {
    let project = make_project();
    let result = build(&project);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].filename, "AuctionContext.bcc");
    assert!(result.files[0].accurate);
    let actual = result.files[0].contents.trim_end();
    let expected = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.scContextFile org.eventb.core.accurate="true" org.eventb.core.configuration="org.eventb.core.fwd;org.eventb.codegen.ui.cgConfig;de.prob.symbolic.ctxBase;de.prob.units.mchBase">
<org.eventb.core.scCarrierSet name="AUCTIONS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_qJ3S4O5PEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(AUCTIONS)"/>
<org.eventb.core.scCarrierSet name="ITEMS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_4PKc0O5TEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(ITEMS)"/>
<org.eventb.core.scCarrierSet name="USERS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_w4LsYO5MEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(USERS)"/>
</org.eventb.core.scContextFile>"#;
    assert_eq!(actual, expected);
}
