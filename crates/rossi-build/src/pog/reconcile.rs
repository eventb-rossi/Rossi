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

use std::collections::{BTreeSet, HashMap, HashSet};

use quick_xml::Reader;
use quick_xml::events::Event;

use crate::ScFile;
use crate::po_view::PoView;
use crate::proofs::Confidence;
use crate::xml_out::{DOC_HEADER, attr, tag as xtag};

/// Reconcile every generated `.bpo` / `.bps` pair in `files` against
/// the previous contents supplied by `old` (keyed by the generated
/// filename; `None` when no previous file exists).
///
/// Returns, per `.bps` filename, the names of the rows that were
/// synthesized fresh rather than carried from a previous row — the
/// rows [`super::status::update_statuses`] may revive from stored
/// proofs (a missing status is computed from the proof file, but
/// never touches a recorded stamp-valid row).
pub fn reconcile_build_files(
    files: &mut [ScFile],
    mut old: impl FnMut(&str) -> Option<String>,
) -> HashMap<String, HashSet<String>> {
    let mut synthesized = HashMap::new();
    for (i, j) in bpo_bps_pairs(files) {
        let old_bpo = old(&files[i].filename);
        let old_bps = old(&files[j].filename);
        let carried: HashSet<String> = old_bps
            .as_deref()
            .map(|bps| parse_status_rows(bps).into_iter().map(|r| r.name).collect())
            .unwrap_or_default();
        let (bpo_out, bps_out) = reconcile_pair(
            old_bpo.as_deref(),
            old_bps.as_deref(),
            &files[i].contents,
            &files[j].contents,
        );
        files[i].contents = bpo_out;
        files[j].contents = bps_out;
        let fresh: HashSet<String> = parse_status_rows(&files[j].contents)
            .into_iter()
            .map(|row| row.name)
            .filter(|name| !carried.contains(name))
            .collect();
        synthesized.insert(files[j].filename.clone(), fresh);
    }
    synthesized
}

/// The `(bpo index, bps index)` of every same-stem `.bpo` / `.bps` pair —
/// the one implementation of the pairing rule, shared with
/// [`reset_stale_statuses`]. Indices, so callers keep their `&mut` access.
pub(crate) fn bpo_bps_pairs(files: &[ScFile]) -> Vec<(usize, usize)> {
    files
        .iter()
        .enumerate()
        .filter_map(|(i, file)| {
            let stem = file.filename.strip_suffix(".bpo")?;
            let bps_name = format!("{stem}.bps");
            let j = files.iter().position(|f| f.filename == bps_name)?;
            Some((i, j))
        })
        .collect()
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

    // Without a previous `.bpo` there are no stamps to carry and no
    // stub to detect, so the generated file needs no parsing at all.
    let mut plan = None;
    if let Some(old_bpo) = old_bpo {
        let Ok(new_view) = PoView::from_xml(new_bpo) else {
            return (new_bpo.to_string(), new_bps.to_string());
        };
        // Only a decomposition-stub component generates a file with no
        // predicate sets at all (real components always emit at least
        // the hypothesis roots). Don't wipe real previous state with a
        // stub.
        if new_view.sets.is_empty() && new_view.sequents.is_empty() {
            return (old_bpo.to_string(), old_bps.unwrap_or(new_bps).to_string());
        }
        plan = PoView::from_xml(old_bpo)
            .ok()
            .map(|old| plan_stamps(&old, &new_view));
    }

    let bpo_out = match &plan {
        Some(plan) if plan.all_unchanged => old_bpo.expect("plan implies old file").to_string(),
        Some(plan) => rewrite_stamps(new_bpo, plan),
        None => new_bpo.to_string(),
    };

    let old_rows = old_bps.map(parse_status_rows).unwrap_or_default();
    let new_rows = parse_status_rows(new_bps);
    let unchanged = plan.as_ref().is_some_and(|plan| plan.all_unchanged);
    let bps_out = match old_bps {
        Some(old_bps) if unchanged && same_names(&old_rows, &new_rows) => old_bps.to_string(),
        _ => {
            let carried: HashMap<&str, &str> = old_rows
                .iter()
                .map(|row| (row.name.as_str(), row.row.as_str()))
                .collect();
            let rows: Vec<String> = new_rows
                .iter()
                .map(|row| match carried.get(row.name.as_str()) {
                    Some(old_row) => (*old_row).to_string(),
                    None => {
                        let stamp = plan
                            .as_ref()
                            .and_then(|plan| plan.sequents.get(&row.name))
                            .map_or("0", String::as_str);
                        replace_stamp(&row.row, stamp)
                    }
                })
                .collect();
            assemble_status(&rows)
        }
    };
    (bpo_out, bps_out)
}

fn same_names(old_rows: &[StatusRow], new_rows: &[StatusRow]) -> bool {
    let old: BTreeSet<&str> = old_rows.iter().map(|row| row.name.as_str()).collect();
    let new: BTreeSet<&str> = new_rows.iter().map(|row| row.name.as_str()).collect();
    old == new
}

/// Reset stale proof statuses after [`reconcile_build_files`]: a `.bps`
/// row whose recorded `poStamp` differs from its sequent's stamp in the
/// sibling `.bpo` records a proof of an obligation that has since
/// changed. Rodin uses exactly that divergence as its replay signal, but
/// a consumer that cannot replay proofs (eventb-animate's po gate is
/// stamp-blind) must not trust the carried confidence — so every such
/// row is replaced by a fresh unattempted one (confidence `-99`, the
/// sequent's stamp, `psManual="false"`), dropping `psBroken` and any
/// other carried attribute. Stamp-matched rows keep their exact bytes.
///
/// Returns `(bpo filename, open count)` per pair, where open = sequents
/// minus the rows that are stamp-valid and classify as discharged
/// (broken caps a high confidence) — exactly the rows the PO gate skips.
///
/// Deliberately separate from [`reconcile_build_files`]: the persistent
/// Rodin-project writers (LSP rebuild, CLI build, repack) must carry
/// rows verbatim so Rodin itself sees the divergence; they never call
/// this.
pub fn reset_stale_statuses(files: &mut [ScFile]) -> Vec<(String, usize)> {
    let mut counts = Vec::new();
    for (i, j) in bpo_bps_pairs(files) {
        let stamps = sequent_stamps(&files[i].contents);
        let rows = parse_status_rows(&files[j].contents);
        let stamp_valid = |row: &StatusRow| {
            stamps
                .get(&row.name)
                .is_some_and(|stamp| row.stamp.as_deref() == Some(stamp.as_str()))
        };

        // `max` keeps the count conservative when a malformed `.bpo` scan
        // yields fewer sequents than there are rows: those rows all reset
        // and must count as open, not vanish from the total.
        let total = stamps.len().max(rows.len());
        let skipped = rows
            .iter()
            .filter(|row| {
                stamp_valid(row)
                    && Confidence::classify(row.confidence).cap_if_broken(row.broken)
                        == Confidence::Discharged
            })
            .count();

        if rows.iter().any(|row| !stamp_valid(row)) {
            let out: Vec<String> = rows
                .iter()
                .map(|row| {
                    if stamp_valid(row) {
                        row.row.clone()
                    } else {
                        fresh_status_row(
                            &row.name,
                            stamps.get(&row.name).map_or("0", String::as_str),
                        )
                    }
                })
                .collect();
            files[j].contents = assemble_status(&out);
        }
        counts.push((files[i].filename.clone(), total.saturating_sub(skipped)));
    }
    counts
}

/// The `name → poStamp` of every sequent in a `.bpo`, by attribute scan —
/// no formula parsing, unlike [`PoView`], so a Rodin-written predicate our
/// parser cannot reparse never voids the stamps (which would reset every
/// recorded discharge). A sequent without a stamp reads as `"0"`, the
/// generator's default. Malformed XML stops the scan; the missing entries
/// then read as open and their rows reset — conservative, never unsafe.
pub fn sequent_stamps(bpo: &str) -> HashMap<String, String> {
    let mut reader = Reader::from_str(bpo);
    let mut buf = Vec::new();
    let mut stamps = HashMap::new();
    loop {
        match reader.read_event_into(&mut buf) {
            Ok(Event::Start(e)) | Ok(Event::Empty(e))
                if e.name().as_ref() == xtag::PO_SEQUENT.as_bytes() =>
            {
                let mut name = None;
                let mut stamp = None;
                for attr in e.attributes().flatten() {
                    let unescaped = || {
                        let raw = String::from_utf8_lossy(&attr.value);
                        match quick_xml::escape::unescape(&raw) {
                            Ok(cow) => cow.into_owned(),
                            Err(_) => raw.into_owned(),
                        }
                    };
                    if attr.key.as_ref() == attr::NAME.as_bytes() {
                        name = Some(unescaped());
                    } else if attr.key.as_ref() == attr::PO_STAMP.as_bytes() {
                        stamp = Some(unescaped());
                    }
                }
                if let Some(name) = name {
                    stamps.insert(name, stamp.unwrap_or_else(|| "0".into()));
                }
            }
            Ok(Event::Eof) | Err(_) => break,
            _ => {}
        }
        buf.clear();
    }
    stamps
}

/// A fresh unattempted status row in the generator's exact shape
/// (`pog::model::into_sc_files`), escaped by the same
/// [`crate::xml_out::escape_attr`] the generator uses.
pub(crate) fn fresh_status_row(name: &str, stamp: &str) -> String {
    let mut row = format!("<{} {}=\"", xtag::PS_STATUS, attr::NAME);
    crate::xml_out::escape_attr(name, &mut row);
    row.push_str(&format!(
        "\" {}=\"-99\" {}=\"{stamp}\" {}=\"false\"/>",
        attr::CONFIDENCE,
        attr::PO_STAMP,
        attr::PS_MANUAL,
    ));
    row
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
    // Equality implies presence in both views, so indexing is safe.
    let mut all_unchanged =
        old.sets.len() == new.sets.len() && old.sequents.len() == new.sequents.len();
    let mut sets = HashMap::new();
    for name in new.sets.keys() {
        if new.set_chain_eq(old, name) {
            let stamp = old.sets[name].stamp.clone().unwrap_or_else(|| "0".into());
            sets.insert(name.clone(), stamp);
        } else {
            all_unchanged = false;
            sets.insert(name.clone(), fresh.clone());
        }
    }
    let mut sequents = HashMap::new();
    for name in new.sequents.keys() {
        if new.sequent_eq(old, name) {
            let stamp = old.sequents[name]
                .stamp
                .clone()
                .unwrap_or_else(|| "0".into());
            sequents.insert(name.clone(), stamp);
        } else {
            all_unchanged = false;
            sequents.insert(name.clone(), fresh.clone());
        }
    }
    StampPlan {
        all_unchanged,
        fresh,
        sets,
        sequents,
    }
}

/// The ` poStamp="0"` needle every generated stamp carries, built from
/// the emitter's attribute constant so the two cannot drift apart.
fn stamp_zero() -> String {
    format!(" {}=\"0\"", attr::PO_STAMP)
}

/// Substitute the planned stamps into a freshly generated `.bpo`.
///
/// The emitter writes one start tag per line with `name` as the first
/// attribute and quotes escaped inside values, and only the file root,
/// the top-level predicate sets, and the sequents carry a stamp — so a
/// line pass suffices. A line that doesn't match the expected shape is
/// left alone (its stamp stays `"0"`).
fn rewrite_stamps(new_bpo: &str, plan: &StampPlan) -> String {
    let stamp_zero = stamp_zero();
    let file_prefix = format!("<{}", xtag::PO_FILE);
    let set_prefix = format!("<{} name=\"", xtag::PO_PREDICATE_SET);
    let sequent_prefix = format!("<{} name=\"", xtag::PO_SEQUENT);
    let mut out = String::with_capacity(new_bpo.len() + 64);
    for line in new_bpo.lines() {
        let stamp = if !line.contains(&stamp_zero) {
            None
        } else if line.starts_with(&file_prefix) {
            Some(plan.fresh.as_str())
        } else if let Some(name) = line_name(line, &set_prefix) {
            plan.sets.get(&name).map(String::as_str)
        } else if let Some(name) = line_name(line, &sequent_prefix) {
            plan.sequents.get(&name).map(String::as_str)
        } else {
            None
        };
        match stamp {
            Some(stamp) => out.push_str(&replace_stamp(line, stamp)),
            None => out.push_str(line),
        }
        out.push('\n');
    }
    out
}

/// Replace the `poStamp="0"` attribute in one emitted line. Attribute
/// values escape raw quotes, so the first match is always the
/// attribute itself, never text inside a value.
fn replace_stamp(line: &str, stamp: &str) -> String {
    line.replacen(
        &stamp_zero(),
        &format!(" {}=\"{stamp}\"", attr::PO_STAMP),
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

/// One `.bps` row as parsed for reconciliation and stamp guarding.
pub(crate) struct StatusRow {
    /// Unescaped `name` attribute.
    pub(crate) name: String,
    /// The row rebuilt from its raw attribute bytes (carried verbatim).
    pub(crate) row: String,
    /// Unescaped `org.eventb.core.poStamp`, when present.
    pub(crate) stamp: Option<String>,
    /// Parsed `org.eventb.core.confidence`, when present and numeric.
    pub(crate) confidence: Option<i64>,
    /// `org.eventb.core.psBroken="true"`.
    pub(crate) broken: bool,
    /// `org.eventb.core.contextDependent="true"` — such rows are
    /// re-checked on every build, even with a matching stamp.
    pub(crate) context_dependent: bool,
}

/// Parse a `.bps` document into [`StatusRow`]s in document order. Rows
/// rebuild from their raw attribute bytes, so carried values survive
/// byte-for-byte; status rows are attribute-only by construction, so
/// children are not represented.
pub(crate) fn parse_status_rows(bps: &str) -> Vec<StatusRow> {
    let mut reader = Reader::from_str(bps);
    let mut buf = Vec::new();
    let mut rows = Vec::new();
    loop {
        match reader.read_event_into(&mut buf) {
            Ok(Event::Start(e)) | Ok(Event::Empty(e))
                if e.name().as_ref() == xtag::PS_STATUS.as_bytes() =>
            {
                let mut parsed = StatusRow {
                    name: String::new(),
                    row: format!("<{}", xtag::PS_STATUS),
                    stamp: None,
                    confidence: None,
                    broken: false,
                    context_dependent: false,
                };
                for attr in e.attributes().flatten() {
                    let key = String::from_utf8_lossy(attr.key.as_ref());
                    let raw = String::from_utf8_lossy(&attr.value);
                    let unescaped = || match quick_xml::escape::unescape(&raw) {
                        Ok(cow) => cow.into_owned(),
                        Err(_) => raw.to_string(),
                    };
                    if attr.key.as_ref() == attr::NAME.as_bytes() {
                        parsed.name = unescaped();
                    } else if attr.key.as_ref() == attr::PO_STAMP.as_bytes() {
                        parsed.stamp = Some(unescaped());
                    } else if attr.key.as_ref() == attr::CONFIDENCE.as_bytes() {
                        parsed.confidence = unescaped().parse::<i64>().ok();
                    } else if attr.key.as_ref() == attr::PS_BROKEN.as_bytes() {
                        parsed.broken = raw == "true";
                    } else if attr.key.as_ref() == attr::CONTEXT_DEPENDENT.as_bytes() {
                        parsed.context_dependent = raw == "true";
                    }
                    parsed.row.push(' ');
                    parsed.row.push_str(&key);
                    parsed.row.push_str("=\"");
                    parsed.row.push_str(&raw);
                    parsed.row.push('"');
                }
                parsed.row.push_str("/>");
                rows.push(parsed);
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
pub(crate) fn assemble_status(rows: &[String]) -> String {
    let mut out = String::from(DOC_HEADER);
    if rows.is_empty() {
        out.push_str(&format!("<{}/>\n", xtag::PS_FILE));
    } else {
        out.push_str(&format!("<{}>\n", xtag::PS_FILE));
        for row in rows {
            out.push_str(row);
            out.push('\n');
        }
        out.push_str(&format!("</{}>\n", xtag::PS_FILE));
    }
    out
}
