//! The reasoner registry: identity, versions, and trust.
//!
//! Reasoner identity is `(id, version)`; the on-disk encoding is
//! `id[:version]` — a missing suffix, a negative number, or an
//! unparsable one all mean "no version". A stored proof step is
//! *trusted* when its id is registered and its stored version equals
//! the registered one; an unknown id or a stale
//! version makes the step untrusted, which caps the proof at
//! uncertain confidence and defeats dependency-based reuse. This is
//! how a proof whose rules have since changed is invalidated.
//!
//! The core table lists the registered reasoner ids with the versions
//! their rules currently carry. The oracle rows are the external
//! provers a typical install registers; their steps can be checked
//! structurally and trusted for reuse, but never replayed. Versions
//! not fixed by a published id are inferred from stored proofs
//! (`externalML`/`externalPP` appear up to `:1`, `externalSMT` and the
//! ProB disprover only bare) and are validated by the build-oracle
//! harness, whose installation ships the ProB plugin and reuses
//! disprover steps. Dead namespaces — `com.b4free.*`, theory provers,
//! community `contributer` plugins — are intentionally absent: a
//! current installation resolves them to untrusted dummies, and so
//! does this registry.

use std::collections::HashMap;
use std::sync::LazyLock;

/// How a registered reasoner id participates in proof checking.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Registration {
    /// A core seqprover reasoner not (yet) implemented in rossi:
    /// trusted for reuse and structural checking, not replayable.
    Declared,
    /// An external prover: trusted exactly as a with-plugins
    /// installation records it, never replayable.
    Oracle,
}

#[derive(Debug)]
struct Entry {
    id: &'static str,
    version: Option<u32>,
    registration: Registration,
    context_dependent: bool,
}

const fn core(id: &'static str, version: Option<u32>) -> Entry {
    Entry {
        id,
        version,
        registration: Registration::Declared,
        context_dependent: false,
    }
}

/// The two datatype reasoners depend on context beyond their sequent.
const fn core_ctx(id: &'static str, version: Option<u32>) -> Entry {
    Entry {
        context_dependent: true,
        ..core(id, version)
    }
}

const fn oracle(id: &'static str, version: Option<u32>) -> Entry {
    Entry {
        id,
        version,
        registration: Registration::Oracle,
        context_dependent: false,
    }
}

static TABLE: &[Entry] = &[
    core("org.eventb.core.seqprover.allD", None),
    core("org.eventb.core.seqprover.allmpD", Some(0)),
    core("org.eventb.core.seqprover.allmtD", Some(0)),
    core("org.eventb.core.seqprover.allI", None),
    core("org.eventb.core.seqprover.conj", Some(0)),
    core("org.eventb.core.seqprover.contr", None),
    core("org.eventb.core.seqprover.contrL1", None),
    core("org.eventb.core.seqprover.contrHyps", Some(1)),
    core("org.eventb.core.seqprover.cut", None),
    core("org.eventb.core.seqprover.disjE", None),
    core("org.eventb.core.seqprover.doCase", None),
    core("org.eventb.core.seqprover.eq", Some(1)),
    core("org.eventb.core.seqprover.eqL1", Some(1)),
    core("org.eventb.core.seqprover.eqL2", Some(1)),
    core("org.eventb.core.seqprover.exE", None),
    core("org.eventb.core.seqprover.exI", None),
    core("org.eventb.core.seqprover.falseHyp", None),
    core("org.eventb.core.seqprover.hyp", None),
    core("org.eventb.core.seqprover.impE", Some(2)),
    core("org.eventb.core.seqprover.impCase", None),
    core("org.eventb.core.seqprover.impI", None),
    core("org.eventb.core.seqprover.mngHyp", None),
    core("org.eventb.core.seqprover.review", None),
    core("org.eventb.core.seqprover.removeNegation", None),
    core("org.eventb.core.seqprover.disjToImpl", None),
    core("org.eventb.core.seqprover.trivial", None),
    core("org.eventb.core.seqprover.typePred", None),
    core("org.eventb.core.seqprover.trueGoal", None),
    core("org.eventb.core.seqprover.exF", None),
    core("org.eventb.core.seqprover.conjF", None),
    core("org.eventb.core.seqprover.isFunGoal", None),
    core("org.eventb.core.seqprover.cardComparison", None),
    core("org.eventb.core.seqprover.cardUpTo", None),
    core("org.eventb.core.seqprover.autoRewrites", Some(4)),
    core("org.eventb.core.seqprover.autoRewritesL1", Some(1)),
    core("org.eventb.core.seqprover.autoRewritesL2", Some(2)),
    core("org.eventb.core.seqprover.autoRewritesL3", Some(2)),
    core("org.eventb.core.seqprover.autoRewritesL4", Some(1)),
    core("org.eventb.core.seqprover.autoRewritesL5", Some(0)),
    core("org.eventb.core.seqprover.typeRewrites", Some(1)),
    core("org.eventb.core.seqprover.doubleImplHypRewrites", None),
    core("org.eventb.core.seqprover.funOvr", Some(1)),
    core("org.eventb.core.seqprover.he", Some(1)),
    core("org.eventb.core.seqprover.heL1", Some(1)),
    core("org.eventb.core.seqprover.heL2", Some(1)),
    core("org.eventb.core.seqprover.mt", Some(2)),
    core("org.eventb.core.seqprover.rn", None),
    core("org.eventb.core.seqprover.rm", None),
    core("org.eventb.core.seqprover.rmL1", None),
    core("org.eventb.core.seqprover.rmL2", None),
    core("org.eventb.core.seqprover.ri", None),
    core("org.eventb.core.seqprover.sir", None),
    core(
        "org.eventb.core.seqprover.inclusionSetMinusLeftRewrites",
        None,
    ),
    core(
        "org.eventb.core.seqprover.inclusionSetMinusRightRewrites",
        None,
    ),
    core("org.eventb.core.seqprover.riUniversal", None),
    core("org.eventb.core.seqprover.autoImpE", None),
    core("org.eventb.core.seqprover.genMP", None),
    core("org.eventb.core.seqprover.genMPL1", None),
    core("org.eventb.core.seqprover.genMPL2", None),
    core("org.eventb.core.seqprover.genMPL3", None),
    core("org.eventb.core.seqprover.genMPL4", None),
    core("org.eventb.core.seqprover.disjToImplRewrites", None),
    core("org.eventb.core.seqprover.negEnum", Some(0)),
    core("org.eventb.core.seqprover.hypOr", None),
    core("org.eventb.core.seqprover.impAndRewrites", None),
    core("org.eventb.core.seqprover.impOrRewrites", None),
    core("org.eventb.core.seqprover.relImgUnionRightRewrites", None),
    core("org.eventb.core.seqprover.relImgUnionLeftRewrites", None),
    core("org.eventb.core.seqprover.setEqlRewrites", None),
    core("org.eventb.core.seqprover.eqvRewrites", None),
    core("org.eventb.core.seqprover.funInterImg", None),
    core("org.eventb.core.seqprover.funSetMinusImg", None),
    core("org.eventb.core.seqprover.funSingletonImg", None),
    core("org.eventb.core.seqprover.funCompImg", None),
    core("org.eventb.core.seqprover.convRewrites", None),
    core("org.eventb.core.seqprover.domDistLeftRewrites", Some(0)),
    core("org.eventb.core.seqprover.domDistRightRewrites", None),
    core("org.eventb.core.seqprover.ranDistLeftRewrites", None),
    core("org.eventb.core.seqprover.ranDistRightRewrites", Some(0)),
    core("org.eventb.core.seqprover.setMinusRewrites", None),
    core("org.eventb.core.seqprover.andOrDistRewrites", None),
    core("org.eventb.core.seqprover.unionInterDistRewrites", None),
    core("org.eventb.core.seqprover.compUnionDistRewrites", None),
    core("org.eventb.core.seqprover.domRanUnionDistRewrites", None),
    core("org.eventb.core.seqprover.relOvrRewrites", None),
    core("org.eventb.core.seqprover.compImgRewrites", None),
    core("org.eventb.core.seqprover.domCompRewrites", None),
    core("org.eventb.core.seqprover.ranCompRewrites", None),
    core("org.eventb.core.seqprover.finiteSet", Some(0)),
    core("org.eventb.core.seqprover.finiteInter", None),
    core("org.eventb.core.seqprover.finiteUnion", None),
    core("org.eventb.core.seqprover.finiteSetMinus", None),
    core("org.eventb.core.seqprover.finiteRelation", Some(0)),
    core("org.eventb.core.seqprover.finiteRelImg", None),
    core("org.eventb.core.seqprover.finiteDom", None),
    core("org.eventb.core.seqprover.finiteRan", None),
    core("org.eventb.core.seqprover.finiteFunction", None),
    core("org.eventb.core.seqprover.finiteFunConv", None),
    core("org.eventb.core.seqprover.finiteFunRelImg", None),
    core("org.eventb.core.seqprover.finiteFunDom", None),
    core("org.eventb.core.seqprover.finiteFunRan", None),
    core("org.eventb.core.seqprover.finiteMin", None),
    core("org.eventb.core.seqprover.finiteMax", None),
    core("org.eventb.core.seqprover.finiteNegative", None),
    core("org.eventb.core.seqprover.finitePositive", None),
    core("org.eventb.core.seqprover.finiteCompset", None),
    core("org.eventb.core.seqprover.partitionRewrites", None),
    core("org.eventb.core.seqprover.arithRewrites", Some(1)),
    core("org.eventb.core.seqprover.onePointRule", Some(2)),
    core("org.eventb.core.seqprover.finiteHypBoundedGoal", None),
    core("org.eventb.core.seqprover.totalDom", Some(2)),
    core("org.eventb.core.seqprover.funImgSimplifies", Some(0)),
    core("org.eventb.core.seqprover.funImgGoal", None),
    core_ctx("org.eventb.core.seqprover.dtDistinctCase", None),
    core_ctx("org.eventb.core.seqprover.dtInduction", Some(2)),
    core("org.eventb.core.seqprover.finiteDefRewrites", None),
    core("org.eventb.core.seqprover.mbGoal", None),
    core("org.eventb.core.seqprover.mapOvrG", None),
    core("org.eventb.core.seqprover.ae", None),
    core("org.eventb.core.seqprover.doubleImplGoalRewrites", None),
    core("org.eventb.core.seqprover.locEq", None),
    core("org.eventb.core.seqprover.eqvLR", None),
    core("org.eventb.core.seqprover.eqvRL", None),
    core("org.eventb.core.seqprover.cardDefRewrites", None),
    core("org.eventb.core.seqprover.equalCardRewrites", None),
    core("org.eventb.core.seqprover.minMaxDefRewrites", None),
    core("org.eventb.core.seqprover.bcompDefRewrites", None),
    core("org.eventb.core.seqprover.equalFunImgDefRewrites", None),
    core("org.eventb.core.seqprover.exponentiationStep", None),
    core("org.eventb.core.seqprover.funDprodImg", None),
    core("org.eventb.core.seqprover.funPprodImg", None),
    core("org.eventb.core.seqprover.derivEqualInterv", None),
    oracle("org.eventb.pp.pp", Some(1)),
    oracle("com.clearsy.atelierb.provers.core.externalML", Some(1)),
    oracle("com.clearsy.atelierb.provers.core.externalPP", Some(1)),
    oracle("org.eventb.smt.core.externalSMT", None),
    oracle("de.prob.eventb.disprover.core.disproverReasoner", None),
];

static BY_ID: LazyLock<HashMap<&'static str, &'static Entry>> =
    LazyLock::new(|| TABLE.iter().map(|entry| (entry.id, entry)).collect());

/// A stored reasoner reference resolved against the registry.
///
/// Equality is reasoner identity — `(id, stored version)` — the pair
/// rules are compared by.
#[derive(Debug, Clone)]
pub struct ReasonerDesc {
    id: String,
    stored_version: Option<u32>,
    entry: Option<&'static Entry>,
}

impl PartialEq for ReasonerDesc {
    fn eq(&self, other: &ReasonerDesc) -> bool {
        self.id == other.id && self.stored_version == other.stored_version
    }
}

impl Eq for ReasonerDesc {}

/// Resolves a stored reasoner id, decoding an `:version` suffix.
/// Unknown ids resolve to an untrusted dummy descriptor rather than
/// an error, so proofs referencing uninstalled reasoners still load.
pub fn resolve(stored_id: &str) -> ReasonerDesc {
    let (id, stored_version) = decode(stored_id);
    ReasonerDesc {
        entry: BY_ID.get(id).copied(),
        id: id.to_string(),
        stored_version,
    }
}

/// Splits `id[:version]`. The suffix parses as a signed integer; a
/// parse failure or a negative value reads as "no version".
fn decode(stored: &str) -> (&str, Option<u32>) {
    match stored.split_once(':') {
        None => (stored, None),
        Some((id, suffix)) => (
            id,
            suffix
                .parse::<i32>()
                .ok()
                .filter(|version| *version >= 0)
                .map(|version| version as u32),
        ),
    }
}

impl ReasonerDesc {
    /// The bare reasoner id, version suffix stripped.
    pub fn id(&self) -> &str {
        &self.id
    }

    /// The version decoded from the stored id.
    pub fn stored_version(&self) -> Option<u32> {
        self.stored_version
    }

    /// Whether the id is not registered at all.
    pub fn is_dummy(&self) -> bool {
        self.entry.is_none()
    }

    /// Whether the stored version differs from the registered one.
    pub fn has_version_conflict(&self) -> bool {
        self.entry
            .is_some_and(|entry| self.stored_version != entry.version)
    }

    /// Trust: registered, no version conflict, not a dummy. A
    /// metadata property, not a soundness guarantee.
    pub fn is_trusted(&self) -> bool {
        self.entry.is_some() && !self.has_version_conflict()
    }

    /// Whether the reasoner depends on context beyond its sequent
    /// (only datatype case-split and induction in core), so its stored
    /// rules must be re-checked even when the dependencies match.
    pub fn is_context_dependent(&self) -> bool {
        self.entry.is_some_and(|entry| entry.context_dependent)
    }

    /// How the id is registered, when it is.
    pub fn registration(&self) -> Option<Registration> {
        self.entry.map(|entry| entry.registration)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_ids_are_unique() {
        assert_eq!(BY_ID.len(), TABLE.len());
    }

    #[test]
    fn versioned_id_codec() {
        assert_eq!(decode("a.b.hyp"), ("a.b.hyp", None));
        assert_eq!(decode("a.b.eq:1"), ("a.b.eq", Some(1)));
        // A negative, unparsable, or doubly-suffixed version reads as
        // "no version", but the id is still split at the first colon.
        assert_eq!(decode("a.b.eq:-1"), ("a.b.eq", None));
        assert_eq!(decode("a.b.eq:2x"), ("a.b.eq", None));
        assert_eq!(decode("a.b.eq:2:3"), ("a.b.eq", None));
        assert_eq!(decode("a.b.eq:99999999999"), ("a.b.eq", None));
    }

    #[test]
    fn trust_matrix() {
        // Unversioned reasoner: bare is trusted, any version conflicts.
        let hyp = resolve("org.eventb.core.seqprover.hyp");
        assert!(hyp.is_trusted());
        assert!(!hyp.is_dummy());
        assert_eq!(hyp.registration(), Some(Registration::Declared));
        assert!(!resolve("org.eventb.core.seqprover.hyp:2").is_trusted());

        // Versioned reasoner: only the registered version is trusted.
        // A bare id means the proof predates versioning — conflict.
        assert!(resolve("org.eventb.core.seqprover.eq:1").is_trusted());
        assert!(!resolve("org.eventb.core.seqprover.eq").is_trusted());
        assert!(!resolve("org.eventb.core.seqprover.eq:2").is_trusted());
        assert!(resolve("org.eventb.core.seqprover.autoRewritesL5:0").is_trusted());
        assert!(resolve("org.eventb.core.seqprover.typeRewrites:1").is_trusted());
        assert!(!resolve("org.eventb.core.seqprover.typeRewrites:0").is_trusted());

        // Unknown ids resolve to untrusted dummies, never errors.
        let unknown = resolve("com.example.mystery:3");
        assert!(unknown.is_dummy());
        assert!(!unknown.is_trusted());
        assert!(!unknown.has_version_conflict());
        assert_eq!(unknown.registration(), None);
        // A renamed reasoner's old id and a dead plugin's namespace
        // are unknown to a current installation, and here.
        assert!(resolve("org.eventb.core.seqprover.FunImgSimplification:0").is_dummy());
        assert!(resolve("com.b4free.rodin.core.externalML").is_dummy());

        // Oracles are trusted at their registered version.
        let smt = resolve("org.eventb.smt.core.externalSMT");
        assert!(smt.is_trusted());
        assert_eq!(smt.registration(), Some(Registration::Oracle));
        assert!(resolve("com.clearsy.atelierb.provers.core.externalML:1").is_trusted());
        assert!(!resolve("com.clearsy.atelierb.provers.core.externalML:0").is_trusted());
        assert!(resolve("org.eventb.pp.pp:1").is_trusted());
        assert!(!resolve("org.eventb.pp.pp").is_trusted());
        assert!(resolve("de.prob.eventb.disprover.core.disproverReasoner").is_trusted());
    }

    #[test]
    fn context_dependence_is_flagged() {
        assert!(resolve("org.eventb.core.seqprover.dtDistinctCase").is_context_dependent());
        assert!(resolve("org.eventb.core.seqprover.dtInduction:2").is_context_dependent());
        assert!(!resolve("org.eventb.core.seqprover.hyp").is_context_dependent());
        assert!(!resolve("com.example.mystery").is_context_dependent());
    }
}
