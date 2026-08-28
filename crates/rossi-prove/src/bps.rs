//! Reading `.bps` proof-status files.
//!
//! A status row caches its proof's confidence and manual flag, records
//! the obligation stamp it was computed against, and carries the
//! broken flag — the row's confidence is meaningless while broken.

use std::io::BufRead;

use quick_xml::Reader;
use quick_xml::events::Event;

/// One `psStatus` row.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PsStatus {
    /// The obligation's name.
    pub name: String,
    /// The cached proof confidence.
    pub confidence: Option<i32>,
    /// The obligation stamp the row was computed against.
    pub po_stamp: Option<String>,
    /// Whether the proof is marked manual.
    pub manual: bool,
    /// Whether the proof was found broken.
    pub broken: bool,
    /// Whether the proof steps through a context-dependent reasoner.
    pub context_dependent: bool,
}

/// Reads the status rows of a `.bps` document, in document order.
pub fn read_bps(reader: impl BufRead) -> Result<Vec<PsStatus>, quick_xml::Error> {
    const PS_STATUS: &str = "org.eventb.core.psStatus";
    const NAME: &str = "name";
    const CONFIDENCE: &str = "org.eventb.core.confidence";
    const PO_STAMP: &str = "org.eventb.core.poStamp";
    const PS_MANUAL: &str = "org.eventb.core.psManual";
    const PS_BROKEN: &str = "org.eventb.core.psBroken";
    const CONTEXT_DEPENDENT: &str = "org.eventb.core.contextDependent";

    let mut xml = Reader::from_reader(reader);
    let mut buf = Vec::new();
    let mut rows = Vec::new();
    loop {
        match xml.read_event_into(&mut buf)? {
            Event::Start(e) | Event::Empty(e) if e.name().as_ref() == PS_STATUS.as_bytes() => {
                let mut row = PsStatus {
                    name: String::new(),
                    confidence: None,
                    po_stamp: None,
                    manual: false,
                    broken: false,
                    context_dependent: false,
                };
                for attr in e.attributes().flatten() {
                    let raw = String::from_utf8_lossy(&attr.value);
                    let value = match quick_xml::escape::unescape(&raw) {
                        Ok(cow) => cow.into_owned(),
                        Err(_) => raw.into_owned(),
                    };
                    match attr.key.as_ref() {
                        key if key == NAME.as_bytes() => row.name = value,
                        key if key == CONFIDENCE.as_bytes() => {
                            row.confidence = value.parse().ok();
                        }
                        key if key == PO_STAMP.as_bytes() => row.po_stamp = Some(value),
                        key if key == PS_MANUAL.as_bytes() => row.manual = value == "true",
                        key if key == PS_BROKEN.as_bytes() => row.broken = value == "true",
                        key if key == CONTEXT_DEPENDENT.as_bytes() => {
                            row.context_dependent = value == "true";
                        }
                        _ => {}
                    }
                }
                rows.push(row);
            }
            Event::Eof => break,
            _ => {}
        }
        buf.clear();
    }
    Ok(rows)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reads_rows_in_order_with_defaults() {
        let xml = r#"<?xml version="1.0" encoding="UTF-8" standalone="no"?>
<org.eventb.core.psFile>
<org.eventb.core.psStatus name="evt/inv1/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="3" org.eventb.core.psManual="false"/>
<org.eventb.core.psStatus name="evt/inv2/INV" org.eventb.core.confidence="1000" org.eventb.core.poStamp="4" org.eventb.core.psManual="true" org.eventb.core.psBroken="true" org.eventb.core.contextDependent="true"/>
<org.eventb.core.psStatus name="evt/inv3/INV"/>
</org.eventb.core.psFile>"#;
        let rows = read_bps(xml.as_bytes()).expect("readable");
        assert_eq!(rows.len(), 3);
        assert_eq!(rows[0].name, "evt/inv1/INV");
        assert_eq!(rows[0].confidence, Some(1000));
        assert_eq!(rows[0].po_stamp.as_deref(), Some("3"));
        assert!(!rows[0].manual && !rows[0].broken && !rows[0].context_dependent);
        assert!(rows[1].manual && rows[1].broken && rows[1].context_dependent);
        // An unattempted row serializes with no confidence.
        assert_eq!(rows[2].confidence, None);
        assert_eq!(rows[2].po_stamp, None);
    }
}
