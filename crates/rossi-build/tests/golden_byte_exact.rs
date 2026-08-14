//! Byte-exact regression locks.
//!
//! These tests pin the three `.bcc` fixtures that currently produce
//! byte-for-byte identical output to Rodin. They run before any
//! whitespace-sensitive change (e.g. step #27's ScView rework) so that
//! silent byte-exact regressions get caught immediately rather than
//! surfacing as a drop in the corpus metric.

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

/// Rodin's AuctionContext.bcc, byte-for-byte modulo trailing newline.
const AUCTION_CONTEXT_BCC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.scContextFile org.eventb.core.accurate="true" org.eventb.core.configuration="org.eventb.core.fwd;org.eventb.codegen.ui.cgConfig;de.prob.symbolic.ctxBase;de.prob.units.mchBase">
<org.eventb.core.scCarrierSet name="AUCTIONS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_qJ3S4O5PEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(AUCTIONS)"/>
<org.eventb.core.scCarrierSet name="ITEMS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_4PKc0O5TEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(ITEMS)"/>
<org.eventb.core.scCarrierSet name="USERS" org.eventb.core.source="/COMP1216/AuctionContext.buc|org.eventb.core.contextFile#AuctionContext|org.eventb.core.carrierSet#_w4LsYO5MEeSpR9iqQeSCVw" org.eventb.core.type="ℙ(USERS)"/>
</org.eventb.core.scContextFile>"#;

/// A corpus-derived context with a single deferred carrier set USER.
const USERMODEL_C0_USERS_BUC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.contextFile org.eventb.core.configuration="org.eventb.core.fwd" org.eventb.core.generated="false" version="3">
<org.eventb.core.carrierSet name="_internal0000000000001" org.eventb.core.generated="false" org.eventb.core.identifier="USER"/>
</org.eventb.core.contextFile>
"#;

/// The corresponding `.bcc` exactly as Rodin emits it.
const USERMODEL_C0_USERS_BCC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.scContextFile org.eventb.core.accurate="true" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.scCarrierSet name="USER" org.eventb.core.source="/usermodel/c0_users.buc|org.eventb.core.contextFile#c0_users|org.eventb.core.carrierSet#_internal0000000000001" org.eventb.core.type="ℙ(USER)"/>
</org.eventb.core.scContextFile>"#;

/// Question1_C0.buc from a corpus assignment archive (two deferred
/// carrier sets, alpha-sorted).
const Q1_C0_BUC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.contextFile org.eventb.core.configuration="org.eventb.core.fwd;de.prob.symbolic.ctxBase;de.prob.units.mchBase" version="3">
<org.eventb.core.carrierSet name="'" org.eventb.core.identifier="BOOK"/>
<org.eventb.core.carrierSet name="(" org.eventb.core.identifier="CHILD"/>
</org.eventb.core.contextFile>
"#;

const Q1_C0_BCC: &str = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.scContextFile org.eventb.core.accurate="true" org.eventb.core.configuration="org.eventb.core.fwd;de.prob.symbolic.ctxBase;de.prob.units.mchBase">
<org.eventb.core.scCarrierSet name="BOOK" org.eventb.core.source="/Question1/Question1_C0.buc|org.eventb.core.contextFile#Question1_C0|org.eventb.core.carrierSet#'" org.eventb.core.type="ℙ(BOOK)"/>
<org.eventb.core.scCarrierSet name="CHILD" org.eventb.core.source="/Question1/Question1_C0.buc|org.eventb.core.contextFile#Question1_C0|org.eventb.core.carrierSet#(" org.eventb.core.type="ℙ(CHILD)"/>
</org.eventb.core.scContextFile>"#;

#[test]
fn golden_bcc_files_are_byte_exact() {
    // (project_name, buc_filename, buc_src, expected_bcc). Rodin's URIs use
    // the project name, so ours must match it: "Question1" is one of four
    // sibling projects in the zip (the filename stem is the project name).
    let cases = [
        (
            "COMP1216",
            "AuctionContext.buc",
            AUCTION_CONTEXT_BUC,
            AUCTION_CONTEXT_BCC,
        ),
        (
            "usermodel",
            "c0_users.buc",
            USERMODEL_C0_USERS_BUC,
            USERMODEL_C0_USERS_BCC,
        ),
        ("Question1", "Question1_C0.buc", Q1_C0_BUC, Q1_C0_BCC),
    ];
    for (project_name, buc_filename, buc_src, expected_bcc) in cases {
        let pc = ProjectComponent::from_xml(buc_filename, buc_src).expect("parse");
        let project = Project::new(project_name, vec![pc]);
        let result = build(&project);
        // The checked file plus the generated proof files.
        assert_eq!(result.files.len(), 3, "{project_name}: expected 3 files");
        assert_eq!(
            result.files[0].filename,
            buc_filename.replace(".buc", ".bcc"),
            "{project_name}: unexpected filename"
        );
        assert!(result.files[0].accurate, "{project_name}: not accurate");
        assert_eq!(
            result.files[0].contents.trim_end(),
            expected_bcc.trim_end(),
            "{project_name}: .bcc output differs from Rodin's"
        );
    }
}
