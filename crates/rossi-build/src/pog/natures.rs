//! Proof-obligation natures: what each generated sequent asks to prove.
//!
//! The description strings are written verbatim into the `poDesc`
//! attribute; provers and status tools match on them, so they are part
//! of the file format (including the historical double space in the
//! invariant natures).

/// The nature of a proof obligation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Nature {
    ActionFeasibility,
    ActionSimulation,
    ActionWellDefinedness,
    AxiomWellDefinedness,
    CommonVariableEquality,
    EventVariant,
    EventNaturalNumberVariant,
    GuardStrengtheningMerge,
    GuardStrengtheningSplit,
    GuardWellDefinedness,
    InvariantEstablishment,
    InvariantPreservation,
    InvariantWellDefinedness,
    Theorem,
    TheoremWellDefinedness,
    VariantFiniteness,
    VariantWellDefinedness,
    WitnessFeasibility,
    WitnessWellDefinedness,
}

impl Nature {
    /// The `poDesc` attribute value.
    #[must_use]
    pub fn description(self) -> &'static str {
        match self {
            Nature::ActionFeasibility => "Feasibility of action",
            Nature::ActionSimulation => "Action simulation",
            Nature::ActionWellDefinedness => "Well-definedness of action",
            Nature::AxiomWellDefinedness => "Well-definedness of Axiom",
            Nature::CommonVariableEquality => "Equality of common variables",
            Nature::EventVariant => "Variant of event",
            Nature::EventNaturalNumberVariant => "Natural number variant of event",
            Nature::GuardStrengtheningMerge => "Guard strengthening (merge)",
            Nature::GuardStrengtheningSplit => "Guard strengthening (split)",
            Nature::GuardWellDefinedness => "Well-definedness of Guard",
            Nature::InvariantEstablishment => "Invariant  establishment",
            Nature::InvariantPreservation => "Invariant  preservation",
            Nature::InvariantWellDefinedness => "Well-definedness of Invariant",
            Nature::Theorem => "Theorem",
            Nature::TheoremWellDefinedness => "Well-definedness of Theorem",
            Nature::VariantFiniteness => "Finiteness of variant",
            Nature::VariantWellDefinedness => "Well-definedness of variant",
            Nature::WitnessFeasibility => "Feasibility of witness",
            Nature::WitnessWellDefinedness => "Well-definedness of witness",
        }
    }
}
