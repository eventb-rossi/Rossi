//! The bridge to the standalone tree-sitter grammar (`editors/tree-sitter-eventb`,
//! published as `eventb-rossi/tree-sitter-eventb`) and the Zed extension that
//! bundles its queries.
//!
//! The grammar itself is *not* generated. It is a hand-maintained structural
//! grammar living in its own repository, together with the `queries/highlights.scm`
//! that captures its nodes (whose captures use the standard ecosystem names —
//! `@keyword`, `@operator`, …). Rossi neither writes nor parses that source.
//!
//! What crosses the boundary instead is the canonical classification as *data*:
//! [`tokens_manifest`] emits `{ node_name: [spellings…] }`, byte-checked on this
//! side by `cargo xtask gen-grammars --check` and read on the other side by the
//! grammar repo's behavioural test, which places every spelling in a minimal
//! component, asserts the built parser accepts it in that role, and asserts the
//! compiled highlight query captures every token it produced. A table change
//! that the grammar has not caught up with therefore fails there, on behaviour,
//! rather than here, on source text — which is the only check that stays honest
//! once the grammar is hand-extended.
//!
//! The flow back is a verbatim copy: Zed loads queries from the extension's own
//! `languages/` directory rather than from the grammar repo, so
//! `paths::TS_HIGHLIGHTS` is copied into `paths::ZED_HIGHLIGHTS` (see
//! `paths::COPIES`).

use super::{MatchKind, Model, Scope, TokenGroup};

/// The class name a coloured group is exported under in [`tokens_manifest`],
/// split by match kind so word classes stay separable from symbol ones. The
/// grammar repo's behavioural test keys its templates off exactly these names
/// (and asserts the set has not changed), so a new [`Scope`] variant breaks
/// this `match` until it is handled. All operator words share one exact-case
/// `operator_word` class (`DOM`, `pow`, `union` are ordinary identifiers —
/// only the canonical `dom`, `POW`, `UNION` light up).
pub fn node_name(group: &TokenGroup) -> &'static str {
    match (group.scope, group.kind) {
        (Scope::KeywordControl, _) => "keyword",
        (Scope::KeywordOther, _) => "status_keyword",
        (Scope::SupportFunction, _) => "builtin",
        (Scope::ConstantLanguage, MatchKind::Word) => "constant_word",
        (Scope::ConstantLanguage, MatchKind::Symbol) => "constant_sym",
        (Scope::KeywordOperator, MatchKind::Word) => "operator_word",
        (Scope::KeywordOperator, MatchKind::Symbol) => "operator_sym",
    }
}

/// Render the canonical token manifest (`paths::TS_TOKENS`): a JSON object
/// `{ node_name: [spellings…] }` over every non-empty model group. Generated and
/// byte-checked here, then read by the standalone repo's behavioral test, which
/// parses each spelling with the built grammar and asserts it tokenizes to the
/// matching node — so "the grammar's core matches gen-grammars" stays verifiable
/// even after the grammar is hand-extended (the test asserts behavior, not text).
///
/// Keys are emitted in sorted order (a `BTreeMap`, so the ordering cannot be
/// flipped by a dependency enabling serde_json's `preserve_order` feature) and
/// each value keeps the group's own order (sorted words / longest-first symbols),
/// so the output is deterministic and byte-reproducible.
pub fn tokens_manifest(model: &Model) -> String {
    let mut map = std::collections::BTreeMap::new();
    for group in &model.groups {
        if group.members.is_empty() {
            continue;
        }
        map.insert(node_name(group), &group.members);
    }
    let mut out = serde_json::to_string_pretty(&map).expect("serialize token manifest");
    out.push('\n');
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tokens_manifest_lists_every_node_and_all_members() {
        let model = Model::build();
        let json: serde_json::Value =
            serde_json::from_str(&tokens_manifest(&model)).expect("manifest is valid JSON");
        let obj = json.as_object().expect("manifest is a JSON object");
        for group in &model.groups {
            if group.members.is_empty() {
                continue;
            }
            let name = node_name(group);
            let arr = obj
                .get(name)
                .unwrap_or_else(|| panic!("manifest missing node `{name}`"))
                .as_array()
                .unwrap_or_else(|| panic!("manifest `{name}` is not an array"));
            let listed: Vec<&str> = arr.iter().map(|v| v.as_str().unwrap()).collect();
            for m in &group.members {
                assert!(
                    listed.contains(&m.as_str()),
                    "manifest `{name}` is missing spelling `{m}`"
                );
            }
        }
        // Spot-check the contract the behavioral test relies on.
        assert!(
            obj["keyword"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v == "context")
        );
        assert!(
            obj["builtin"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v == "card")
        );
        assert!(
            obj["operator_sym"]
                .as_array()
                .unwrap()
                .iter()
                .any(|v| v == "∈")
        );
    }
}
