//! Reconcile regenerated proof-obligation files with a previous build.
//!
//! Regeneration alone resets all proof state: every stamp restarts at
//! `"0"` and every status becomes unattempted, so downstream provers
//! would treat identical obligations as new work. This module merges
//! the freshly generated `.bpo` / `.bps` pair with the files it is
//! about to replace:
//!
//! - a sequent (or top-level predicate set) that is semantically
//!   unchanged — per [`PoView::sequent_eq`] / [`PoView::set_chain_eq`]
//!   — carries its previous `poStamp` forward verbatim; changed or new
//!   elements get a stamp above every stamp in the previous file;
//! - a status row whose obligation still exists is re-emitted with all
//!   its attributes untouched (confidence, `psManual`, `psBroken`,
//!   its recorded stamp); rows for vanished obligations are dropped
//!   and new obligations get fresh unattempted rows;
//! - when nothing changed at all, the previous bytes pass through
//!   verbatim, so rebuilding an unchanged model is byte-stable.
//!
//! A status row whose recorded stamp differs from its sequent's stamp
//! is exactly the signal proof managers use to re-check the stored
//! proof, so no proof-dependency analysis happens here.

use std::collections::{BTreeSet, HashMap};

use quick_xml::Reader;
use quick_xml::events::Event;

use crate::ScFile;
use crate::po_view::PoView;

/// Reconcile every generated `.bpo` / `.bps` pair in `files` against
/// the previous contents supplied by `old` (keyed by the generated
/// filename; `None` when no previous file exists).
pub fn reconcile_build_files(files: &mut [ScFile], mut old: impl FnMut(&str) -> Option<String>) {
    for i in 0..files.len() {
        let Some(stem) = files[i].filename.strip_suffix(".bpo") else {
            continue;
        };
        let bps_name = format!("{stem}.bps");
        let Some(j) = files.iter().position(|f| f.filename == bps_name) else {
            continue;
        };
        let old_bpo = old(&files[i].filename);
        let old_bps = old(&bps_name);
        let (bpo_out, bps_out) = reconcile_pair(
            old_bpo.as_deref(),
            old_bps.as_deref(),
            &files[i].contents,
            &files[j].contents,
        );
        files[i].contents = bpo_out;
        files[j].contents = bps_out;
    }
}

/// Reconcile one component's generated `.bpo` / `.bps` contents with
/// the previous files they replace. Returns the contents to write.
pub fn reconcile_pair(
    old_bpo: Option<&str>,
    old_bps: Option<&str>,
    new_bpo: &str,
    new_bps: &str,
) -> (String, String) {
    if old_bpo.is_none() && old_bps.is_none() {
        return (new_bpo.to_string(), new_bps.to_string());
    }
    let Ok(new_view) = PoView::from_xml(new_bpo) else {
        return (new_bpo.to_string(), new_bps.to_string());
    };

    // Only a decomposition-stub component generates a file with no
    // predicate sets at all (real components always emit at least the
    // hypothesis roots). Don't wipe real previous state with a stub.
    if new_view.sets.is_empty()
        && new_view.sequents.is_empty()
        && let Some(old_bpo) = old_bpo
    {
        return (old_bpo.to_string(), old_bps.unwrap_or(new_bps).to_string());
    }

    let old_view = old_bpo.and_then(|xml| PoView::from_xml(xml).ok());
    let plan = old_view.as_ref().map(|old| plan_stamps(old, &new_view));

    let bpo_out = match &plan {
        Some(plan) if plan.all_unchanged => old_bpo.expect("plan implies old file").to_string(),
        Some(plan) => rewrite_stamps(new_bpo, plan),
        None => new_bpo.to_string(),
    };

    let old_rows = old_bps.map(parse_status_rows).unwrap_or_default();
    let new_rows = parse_status_rows(new_bps);
    let same_names = {
        let old_names: BTreeSet<&str> = old_rows.iter().map(|(name, _)| name.as_str()).collect();
        let new_names: BTreeSet<&str> = new_rows.iter().map(|(name, _)| name.as_str()).collect();
        old_names == new_names
    };
    let passthrough = plan.as_ref().is_some_and(|plan| plan.all_unchanged) && same_names;
    let bps_out = match old_bps {
        Some(old_bps) if passthrough => old_bps.to_string(),
        _ => {
            let carried: HashMap<&str, &str> = old_rows
                .iter()
                .map(|(name, row)| (name.as_str(), row.as_str()))
                .collect();
            let rows: Vec<String> = new_rows
                .iter()
                .map(|(name, row)| match carried.get(name.as_str()) {
                    Some(old_row) => (*old_row).to_string(),
                    None => {
                        let stamp = plan
                            .as_ref()
                            .and_then(|plan| plan.sequents.get(name))
                            .map_or("0", String::as_str);
                        replace_stamp(row, stamp)
                    }
                })
                .collect();
            assemble_status(&rows)
        }
    };
    (bpo_out, bps_out)
}

/// The stamp each output element should carry.
struct StampPlan {
    /// True iff the old and new files have the same sets and sequents
    /// and every one of them is semantically unchanged.
    all_unchanged: bool,
    /// The stamp for the file root and for every changed or new
    /// element: one above every stamp in the previous file, so a
    /// carried stamp can never collide with a fresh one.
    fresh: String,
    sets: HashMap<String, String>,
    sequents: HashMap<String, String>,
}

fn plan_stamps(old: &PoView, new: &PoView) -> StampPlan {
    let mut max = 0i64;
    for stamp in old
        .stamp
        .iter()
        .chain(old.sets.values().filter_map(|set| set.stamp.as_ref()))
        .chain(old.sequents.values().filter_map(|seq| seq.stamp.as_ref()))
    {
        if let Ok(value) = stamp.parse::<i64>() {
            max = max.max(value);
        }
    }
    let fresh = (max + 1).to_string();

    // Equal-sized name sets plus every new name found unchanged in the
    // old view together imply nothing was added, removed, or edited.
    let mut all_unchanged =
        old.sets.len() == new.sets.len() && old.sequents.len() == new.sequents.len();
    let mut sets = HashMap::new();
    for name in new.sets.keys() {
        match old.sets.get(name).filter(|_| new.set_chain_eq(old, name)) {
            Some(set) => {
                sets.insert(
                    name.clone(),
                    set.stamp.clone().unwrap_or_else(|| "0".into()),
                );
            }
            None => {
                all_unchanged = false;
                sets.insert(name.clone(), fresh.clone());
            }
        }
    }
    let mut sequents = HashMap::new();
    for name in new.sequents.keys() {
        match old.sequents.get(name).filter(|_| new.sequent_eq(old, name)) {
            Some(sequent) => {
                sequents.insert(
                    name.clone(),
                    sequent.stamp.clone().unwrap_or_else(|| "0".into()),
                );
            }
            None => {
                all_unchanged = false;
                sequents.insert(name.clone(), fresh.clone());
            }
        }
    }
    StampPlan {
        all_unchanged,
        fresh,
        sets,
        sequents,
    }
}

const STAMP_ZERO: &str = " org.eventb.core.poStamp=\"0\"";

/// Substitute the planned stamps into a freshly generated `.bpo`.
///
/// The emitter writes one start tag per line with `name` as the first
/// attribute and quotes escaped inside values, and only the file root,
/// the top-level predicate sets, and the sequents carry a stamp — so a
/// line pass suffices. A line that doesn't match the expected shape is
/// left alone (its stamp stays `"0"`).
fn rewrite_stamps(new_bpo: &str, plan: &StampPlan) -> String {
    let mut out = String::with_capacity(new_bpo.len() + 64);
    for line in new_bpo.lines() {
        let stamp = if !line.contains(STAMP_ZERO) {
            None
        } else if line.starts_with("<org.eventb.core.poFile") {
            Some(plan.fresh.as_str())
        } else if let Some(name) = line_name(line, "<org.eventb.core.poPredicateSet name=\"") {
            plan.sets.get(&name).map(String::as_str)
        } else if let Some(name) = line_name(line, "<org.eventb.core.poSequent name=\"") {
            plan.sequents.get(&name).map(String::as_str)
        } else {
            None
        };
        match stamp {
            Some(stamp) if stamp != "0" => out.push_str(&replace_stamp(line, stamp)),
            _ => out.push_str(line),
        }
        out.push('\n');
    }
    out
}

/// Replace the `poStamp="0"` attribute in one emitted line. Attribute
/// values escape raw quotes, so the first match is always the
/// attribute itself, never text inside a value.
fn replace_stamp(line: &str, stamp: &str) -> String {
    if stamp == "0" {
        return line.to_string();
    }
    line.replacen(
        STAMP_ZERO,
        &format!(" org.eventb.core.poStamp=\"{stamp}\""),
        1,
    )
}

/// The element name at the start of an emitted line, unescaped.
fn line_name(line: &str, prefix: &str) -> Option<String> {
    let rest = line.strip_prefix(prefix)?;
    let raw = &rest[..rest.find('"')?];
    Some(
        quick_xml::escape::unescape(raw)
            .map(std::borrow::Cow::into_owned)
            .unwrap_or_else(|_| raw.to_string()),
    )
}

/// Parse a `.bps` document into `(sequent name, rebuilt row)` pairs in
/// document order. Rows rebuild from their raw attribute bytes, so
/// carried values survive byte-for-byte; status rows are attribute-only
/// by construction, so children are not represented.
fn parse_status_rows(bps: &str) -> Vec<(String, String)> {
    let mut reader = Reader::from_str(bps);
    let mut buf = Vec::new();
    let mut rows = Vec::new();
    loop {
        match reader.read_event_into(&mut buf) {
            Ok(Event::Start(e)) | Ok(Event::Empty(e))
                if e.name().as_ref() == b"org.eventb.core.psStatus" =>
            {
                let mut name = None;
                let mut row = String::from("<org.eventb.core.psStatus");
                for attr in e.attributes().flatten() {
                    let key = String::from_utf8_lossy(attr.key.as_ref()).into_owned();
                    let raw = String::from_utf8_lossy(&attr.value).into_owned();
                    if attr.key.as_ref() == b"name" {
                        name = quick_xml::escape::unescape(&raw)
                            .map(|cow| cow.into_owned())
                            .ok()
                            .or(Some(raw.clone()));
                    }
                    row.push_str(&format!(" {key}=\"{raw}\""));
                }
                row.push_str("/>");
                rows.push((name.unwrap_or_default(), row));
            }
            Ok(Event::Eof) | Err(_) => break,
            _ => {}
        }
        buf.clear();
    }
    rows
}

/// Render a `.bps` document from finished rows, matching the
/// generator's byte format.
fn assemble_status(rows: &[String]) -> String {
    let mut out = String::from("<?xml version=\"1.0\" encoding=\"UTF-8\" standalone=\"no\"?>\n");
    if rows.is_empty() {
        out.push_str("<org.eventb.core.psFile/>\n");
    } else {
        out.push_str("<org.eventb.core.psFile>\n");
        for row in rows {
            out.push_str(row);
            out.push('\n');
        }
        out.push_str("</org.eventb.core.psFile>\n");
    }
    out
}
