//! Per-event tables: actions split by determinism with the frame
//! substitutions, guard correspondences between an event and the
//! abstract events it refines, and the machine-state lookups the
//! event scope is built from.

use std::collections::{BTreeSet, HashMap};

use rossi::formula::{Assignment, AssignmentKind, Expression, FormulaFactory, Predicate, Type};

use crate::handles::HandleUri;
use crate::sc::machine_record::{ActionDecl, EventDecl, GuardDecl, MachineRecord};
use crate::sc::{CheckedMachine, ScModel};

/// A simultaneous free-identifier substitution (one batch of parallel
/// assignments).
pub(super) type Substitution = HashMap<String, Expression>;

/// Apply an optional substitution batch.
pub(super) fn apply(predicate: &Predicate, subst: Option<&Substitution>) -> Predicate {
    match subst {
        Some(map) if !map.is_empty() => predicate.substitute_free_idents(map),
        _ => predicate.clone(),
    }
}

/// The primed after-value identifier of a variable.
pub(super) fn primed(ff: &FormulaFactory, name: &str, ty: &Type) -> Expression {
    ff.free_identifier(format!("{name}'"), None, Some(ty.clone()))
}

/// The concrete machine state: every concrete variable in declaration
/// order with whether it is preserved (also present in the
/// abstraction), plus a by-name type lookup over all visible variables
/// (abstract-only ones included) — the type source for primed
/// identifiers.
pub(super) struct MachineVariables {
    pub rows: Vec<(String, Type, bool)>,
    pub types: HashMap<String, Type>,
}

impl MachineVariables {
    pub fn new(record: &MachineRecord) -> Self {
        MachineVariables {
            rows: record
                .variables
                .iter()
                .filter(|v| v.is_concrete)
                .map(|v| (v.name.clone(), v.ty.clone(), v.is_abstract && v.is_concrete))
                .collect(),
            types: record
                .variables
                .iter()
                .map(|v| (v.name.clone(), v.ty.clone()))
                .collect(),
        }
    }
}

/// The names of every variable the actions assign.
pub(super) fn assigned_variables(actions: &[ActionDecl]) -> BTreeSet<String> {
    let mut out = BTreeSet::new();
    for decl in actions {
        // `skip` assigns nothing.
        let Some(assignment) = &decl.typed else {
            continue;
        };
        for ident in assignment.assigned_identifiers() {
            if let rossi::formula::ExpressionKind::FreeIdentifier(name) = ident.kind() {
                out.insert(name.clone());
            }
        }
    }
    out
}

/// One action and its typed assignment.
pub(super) struct ActionInfo {
    pub label: String,
    pub source: HandleUri,
    pub assignment: Assignment,
}

/// An event's actions, split by determinism. `skip` actions assign
/// nothing and constrain nothing, so they carry no row.
pub(super) struct EventActionTable {
    pub actions: Vec<ActionInfo>,
    /// Indices into `actions` of the nondeterministic ones, with their
    /// before-after predicates in parallel.
    pub nondet: Vec<usize>,
    pub nondet_predicates: Vec<Predicate>,
    /// `x' ↦ E` for every deterministic action, as one batch.
    pub primed_det: Option<Substitution>,
    pub assigned_variables: BTreeSet<String>,
}

impl EventActionTable {
    pub fn new(actions: &[ActionDecl]) -> Self {
        let mut table = EventActionTable {
            actions: Vec::new(),
            nondet: Vec::new(),
            nondet_predicates: Vec::new(),
            primed_det: None,
            assigned_variables: assigned_variables(actions),
        };
        let mut primed_det = Substitution::new();
        for decl in actions {
            let Some(assignment) = &decl.typed else {
                continue;
            };
            let index = table.actions.len();
            table.actions.push(ActionInfo {
                label: decl.label.clone(),
                source: decl.source.clone(),
                assignment: assignment.clone(),
            });
            match assignment.kind() {
                AssignmentKind::BecomesEqualTo { idents, values } => {
                    for (ident, value) in idents.iter().zip(values) {
                        if let rossi::formula::ExpressionKind::FreeIdentifier(name) = ident.kind() {
                            primed_det.insert(format!("{name}'"), value.clone());
                        }
                    }
                }
                AssignmentKind::BecomesMemberOf { .. } | AssignmentKind::BecomesSuchThat { .. } => {
                    table.nondet.push(index);
                    table.nondet_predicates.push(assignment.ba_predicate());
                }
            }
        }
        table.primed_det = (!primed_det.is_empty()).then_some(primed_det);
        table
    }
}

/// The concrete event's actions plus the frame substitutions over the
/// machine state.
pub(super) struct ConcreteEventActionTable {
    pub table: EventActionTable,
    /// `v' ↦ v` for every concrete variable the event leaves alone.
    pub xi_unprime: Option<Substitution>,
    /// `v ↦ v'` for every variable the event assigns.
    pub delta_prime: Option<Substitution>,
}

impl ConcreteEventActionTable {
    pub fn new(actions: &[ActionDecl], variables: &MachineVariables, ff: &FormulaFactory) -> Self {
        let table = EventActionTable::new(actions);
        let mut xi = Substitution::new();
        let mut delta = Substitution::new();
        for (name, ty, _) in &variables.rows {
            if table.assigned_variables.contains(name) {
                delta.insert(name.clone(), primed(ff, name, ty));
            } else {
                xi.insert(
                    format!("{name}'"),
                    ff.free_identifier(name, None, Some(ty.clone())),
                );
            }
        }
        ConcreteEventActionTable {
            table,
            xi_unprime: (!xi.is_empty()).then_some(xi),
            delta_prime: (!delta.is_empty()).then_some(delta),
        }
    }
}

/// The abstract event's actions, with the correspondence to the
/// concrete action list (structural formula equality) and the
/// disappearing-variable split.
pub(super) struct AbstractEventActionTable {
    pub table: EventActionTable,
    /// For each concrete action, the index of the identical abstract
    /// action, if any.
    pub index_of_abstract: Vec<Option<usize>>,
    /// `y ↦ F` for every deterministic abstract assignment to a
    /// variable this refinement dropped — an implicit witness.
    pub disappearing_witnesses: Option<Substitution>,
}

impl AbstractEventActionTable {
    pub fn new(
        actions: &[ActionDecl],
        variables: &MachineVariables,
        concrete: &ConcreteEventActionTable,
    ) -> Self {
        let table = EventActionTable::new(actions);
        let index_of_abstract = concrete
            .table
            .actions
            .iter()
            .map(|c| {
                table
                    .actions
                    .iter()
                    .position(|a| a.assignment == c.assignment)
            })
            .collect();

        let concrete_names: BTreeSet<&str> = variables
            .rows
            .iter()
            .map(|(name, _, _)| name.as_str())
            .collect();
        let mut disappearing = Substitution::new();
        for action in &table.actions {
            if let AssignmentKind::BecomesEqualTo { idents, values } = action.assignment.kind() {
                for (ident, value) in idents.iter().zip(values) {
                    if let rossi::formula::ExpressionKind::FreeIdentifier(name) = ident.kind()
                        && !concrete_names.contains(name.as_str())
                    {
                        disappearing.insert(name.clone(), value.clone());
                    }
                }
            }
        }

        AbstractEventActionTable {
            table,
            index_of_abstract,
            disappearing_witnesses: (!disappearing.is_empty()).then_some(disappearing),
        }
    }
}

/// One witness: the witnessed identifier is its label — a parameter
/// name for a dropped abstract parameter, a primed variable for a
/// dropped abstract variable.
pub(super) struct WitnessInfo {
    pub label: String,
    pub source: HandleUri,
    pub predicate: Predicate,
    pub deterministic: bool,
}

/// An event's witnesses, classified.
///
/// A witness `w` is deterministic when its predicate is `w = E` with
/// `w` not free in `E`; it then acts as a substitution. Deterministic
/// witnesses for primed variables contribute both the unprimed
/// (`v ↦ E`) and primed (`v' ↦ E`) forms; parameter witnesses
/// contribute `p ↦ E`. Nondeterministic witnesses for primed
/// variables contribute `v ↦ v'` instead.
pub(super) struct EventWitnessTable {
    pub witnesses: Vec<WitnessInfo>,
    /// Indices of the nondeterministic witnesses.
    pub nondet: Vec<usize>,
    /// `v ↦ E` for deterministic primed-variable witnesses.
    pub machine_det: Option<Substitution>,
    /// `v' ↦ E` for deterministic primed-variable witnesses.
    pub machine_primed_det: Option<Substitution>,
    /// `p ↦ E` for deterministic parameter witnesses.
    pub event_det: Option<Substitution>,
    /// `v ↦ v'` for nondeterministic primed-variable witnesses.
    pub prime_substitution: Option<Substitution>,
}

impl EventWitnessTable {
    pub fn new(event: &EventDecl, variables: &MachineVariables, ff: &FormulaFactory) -> Self {
        let mut table = EventWitnessTable {
            witnesses: Vec::new(),
            nondet: Vec::new(),
            machine_det: None,
            machine_primed_det: None,
            event_det: None,
            prime_substitution: None,
        };
        let mut machine_det = Substitution::new();
        let mut machine_primed_det = Substitution::new();
        let mut event_det = Substitution::new();
        let mut prime = Substitution::new();

        for witness in &event.witnesses {
            let label = witness.label.clone();
            let deterministic = deterministic_value(&label, &witness.typed);
            let index = table.witnesses.len();
            table.witnesses.push(WitnessInfo {
                label: label.clone(),
                source: witness.source.clone(),
                predicate: witness.typed.clone(),
                deterministic: deterministic.is_some(),
            });
            match (deterministic, label.strip_suffix('\'')) {
                (Some(value), Some(base)) => {
                    machine_det.insert(base.to_string(), value.clone());
                    machine_primed_det.insert(label, value);
                }
                (Some(value), None) => {
                    event_det.insert(label, value);
                }
                (None, base) => {
                    table.nondet.push(index);
                    if let Some(base) = base
                        && let Some(ty) = variables.types.get(base)
                    {
                        prime.insert(base.to_string(), primed(ff, base, ty));
                    }
                }
            }
        }

        table.machine_det = (!machine_det.is_empty()).then_some(machine_det);
        table.machine_primed_det = (!machine_primed_det.is_empty()).then_some(machine_primed_det);
        table.event_det = (!event_det.is_empty()).then_some(event_det);
        table.prime_substitution = (!prime.is_empty()).then_some(prime);
        table
    }
}

/// The witnessed value when the witness is deterministic: `label = E`
/// with the label identifier not free in `E`.
fn deterministic_value(label: &str, predicate: &Predicate) -> Option<Expression> {
    use rossi::formula::{PredicateKind, tag};
    let PredicateKind::Relational {
        op: tag::RelationalOp::Equal,
        left,
        right,
    } = predicate.kind()
    else {
        return None;
    };
    let rossi::formula::ExpressionKind::FreeIdentifier(name) = left.kind() else {
        return None;
    };
    if name != label || right.free_identifiers().iter().any(|n| n == label) {
        return None;
    }
    Some(right.clone())
}

/// Merge substitution batches applied together: later entries win on a
/// shared key, matching the order they are listed in.
pub(super) fn merge_batches<'a>(
    batches: impl IntoIterator<Item = Option<&'a Substitution>>,
) -> Option<Substitution> {
    let mut merged = Substitution::new();
    for batch in batches.into_iter().flatten() {
        for (key, value) in batch {
            merged.insert(key.clone(), value.clone());
        }
    }
    (!merged.is_empty()).then_some(merged)
}

/// One guard of the effective (inherited-then-own) guard list.
pub(super) struct GuardInfo {
    pub label: String,
    /// The checked file's internal name of the guard row.
    pub internal_name: String,
    pub predicate: Predicate,
    pub source: HandleUri,
    pub is_theorem: bool,
}

/// The effective guards of an event, in checked-file order.
pub(super) struct ConcreteEventGuardTable {
    pub guards: Vec<GuardInfo>,
}

impl ConcreteEventGuardTable {
    pub fn new(machine: &CheckedMachine, event: &EventDecl) -> Self {
        let guards = effective_guards(event)
            .into_iter()
            .map(|guard| GuardInfo {
                label: guard.label.clone(),
                internal_name: machine
                    .event_child_internal_name(
                        &event.label,
                        crate::xml_out::tag::SC_GUARD,
                        &guard.label,
                    )
                    .unwrap_or(&guard.label)
                    .to_string(),
                predicate: guard.typed.clone(),
                source: guard.source.clone(),
                is_theorem: guard.is_theorem,
            })
            .collect();
        ConcreteEventGuardTable { guards }
    }
}

/// An abstract event's effective guards, with the correspondence to
/// the concrete guard list (structural formula equality).
pub(super) struct AbstractEventGuardTable {
    pub guards: Vec<AbstractGuardInfo>,
    /// For each abstract guard, the index of the identical concrete
    /// guard, if any.
    pub index_of_concrete: Vec<Option<usize>>,
}

pub(super) struct AbstractGuardInfo {
    pub predicate: Predicate,
    pub is_theorem: bool,
}

impl AbstractEventGuardTable {
    pub fn new(abstract_event: &EventDecl, concrete: &ConcreteEventGuardTable) -> Self {
        let guards: Vec<AbstractGuardInfo> = effective_guards(abstract_event)
            .into_iter()
            .map(|guard| AbstractGuardInfo {
                predicate: guard.typed.clone(),
                is_theorem: guard.is_theorem,
            })
            .collect();
        let index_of_concrete = guards
            .iter()
            .map(|a| {
                concrete
                    .guards
                    .iter()
                    .position(|c| c.predicate == a.predicate)
            })
            .collect();
        AbstractEventGuardTable {
            guards,
            index_of_concrete,
        }
    }
}

/// The abstract events an event refines, with their guard tables.
pub(super) struct AbstractEventGuardList {
    pub events: Vec<std::rc::Rc<EventDecl>>,
    pub tables: Vec<AbstractEventGuardTable>,
}

impl AbstractEventGuardList {
    pub fn new(
        model: &ScModel,
        machine: &CheckedMachine,
        event: &EventDecl,
        concrete: &ConcreteEventGuardTable,
    ) -> Self {
        let events: Vec<std::rc::Rc<EventDecl>> = model
            .abstract_event(machine, event)
            .cloned()
            .into_iter()
            .collect();
        let tables = events
            .iter()
            .map(|abstract_event| AbstractEventGuardTable::new(abstract_event, concrete))
            .collect();
        AbstractEventGuardList { events, tables }
    }

    pub fn first_abstract_event(&self) -> Option<&std::rc::Rc<EventDecl>> {
        self.events.first()
    }
}

/// The effective guard list: the inherited chain's guards (root
/// first), then the event's own, matching the checked file's order.
fn effective_guards(event: &EventDecl) -> Vec<&GuardDecl> {
    let mut out: Vec<&GuardDecl> = Vec::new();
    for ancestor in event.chain_root_first() {
        out.extend(ancestor.guards.iter());
    }
    out.extend(event.guards.iter());
    out
}
