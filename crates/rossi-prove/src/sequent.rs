//! Prover sequents: the immutable judgment proof rules apply to.
//!
//! A sealed type environment,
//! insertion-ordered hypothesis sets — global hypotheses shared by
//! every sequent derived from one proof obligation plus local ones
//! added by rules — two presentational subsets (selected, hidden,
//! with no logical meaning), and a goal. Sequents are immutable and
//! structurally shared; every mutator returns this very sequent when
//! nothing changed, so [`ProverSequent::ptr_eq`] is the cheap "the
//! rule did nothing" signal the proof builder keys on.

use std::collections::HashSet;
use std::sync::Arc;

use rossi::formula::{
    ExpressionKind, FormulaRef, Predicate, PredicateKind, SealedTypeEnvironment, Type,
};

/// A typed free identifier introduced into a sequent by a proof step.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypedIdent {
    /// The identifier's name.
    pub name: String,
    /// Its solved type.
    pub ty: Type,
}

impl TypedIdent {
    /// A typed identifier.
    pub fn new(name: impl Into<String>, ty: Type) -> TypedIdent {
        TypedIdent {
            name: name.into(),
            ty,
        }
    }
}

/// An insertion-ordered predicate set with O(1) membership — the
/// insertion-ordered set sequents are built from. Iteration order is
/// observable: it fixes hypothesis order in generated rules and in
/// stored proofs.
#[derive(Debug, Clone, Default)]
struct OrderedPredSet {
    order: Vec<Predicate>,
    index: HashSet<Predicate>,
}

impl OrderedPredSet {
    fn from_iter(preds: impl IntoIterator<Item = Predicate>) -> OrderedPredSet {
        let mut set = OrderedPredSet::default();
        for pred in preds {
            set.insert(pred);
        }
        set
    }

    /// Appends `pred` unless already present. True iff the set changed.
    fn insert(&mut self, pred: Predicate) -> bool {
        if self.index.insert(pred.clone()) {
            self.order.push(pred);
            true
        } else {
            false
        }
    }

    /// Removes `pred`, keeping the order of the rest. True iff the set
    /// changed.
    fn remove(&mut self, pred: &Predicate) -> bool {
        if self.index.remove(pred) {
            self.order.retain(|p| p != pred);
            true
        } else {
            false
        }
    }

    fn contains(&self, pred: &Predicate) -> bool {
        self.index.contains(pred)
    }

    fn iter(&self) -> std::slice::Iter<'_, Predicate> {
        self.order.iter()
    }
}

/// The applicability checks a sequent enforces: added identifiers
/// must be fresh in the environment, and every checked formula must
/// be well-formed, type-checked, and use only free identifiers the
/// (possibly extended) environment binds with the same type. Carrier
/// sets used solely inside types are not checked.
struct TypeChecker {
    env: SealedTypeEnvironment,
    env_changed: bool,
    added_fresh: bool,
    error: bool,
}

impl TypeChecker {
    fn new(env: SealedTypeEnvironment) -> TypeChecker {
        TypeChecker {
            env,
            env_changed: false,
            added_fresh: true,
            error: false,
        }
    }

    fn add_idents(&mut self, idents: &[TypedIdent]) {
        if idents.is_empty() {
            return;
        }
        self.env_changed = true;
        let mut builder = self.env.to_builder();
        for ident in idents {
            match builder.get(&ident.name) {
                None => builder.insert(&*ident.name, ident.ty.clone()),
                Some(known) => {
                    self.added_fresh = false;
                    if *known != ident.ty {
                        self.error = true;
                    }
                }
            }
        }
        self.env = builder.into_snapshot();
    }

    fn check_preds(&mut self, preds: &[Predicate]) {
        for pred in preds {
            self.check_pred(pred);
        }
    }

    fn check_pred(&mut self, pred: &Predicate) {
        if !pred.dangling_bound_indices().is_empty() || !pred.is_type_checked() {
            self.error = true;
            return;
        }
        let env = self.env.clone();
        let mut ok = true;
        pred.positions(&mut |node| {
            if let FormulaRef::Expr(expr) = node
                && let ExpressionKind::FreeIdentifier(name) = expr.kind()
                && env.get(name) != expr.ty()
            {
                ok = false;
            }
            false
        });
        if !ok {
            self.error = true;
        }
    }

    /// Whether any check failed so far.
    fn rejected(&self) -> bool {
        self.error || !self.added_fresh
    }
}

/// Whether the predicate contains a predicate variable — such
/// predicates are rejected from sequents.
fn has_predicate_variable(pred: &Predicate) -> bool {
    let mut found = false;
    pred.positions(&mut |node| {
        if let FormulaRef::Pred(p) = node
            && matches!(p.kind(), PredicateKind::PredicateVariable(_))
        {
            found = true;
        }
        false
    });
    found
}

/// An immutable prover sequent. Cloning is O(1).
#[derive(Debug, Clone)]
pub struct ProverSequent(Arc<SequentData>);

#[derive(Debug)]
struct SequentData {
    type_env: SealedTypeEnvironment,
    global: Arc<OrderedPredSet>,
    local: Arc<OrderedPredSet>,
    hidden: Arc<OrderedPredSet>,
    selected: Arc<OrderedPredSet>,
    goal: Predicate,
}

impl ProverSequent {
    /// Builds a fresh sequent with no local hypotheses.
    ///
    /// Like the constructor this trusts the caller: the predicates
    /// must be type-checked against `type_env`, and `hidden` and
    /// `selected` should be subsets of `hyps`. The checks live in the
    /// mutators every reasoner-produced change goes through.
    pub fn new(
        type_env: SealedTypeEnvironment,
        hyps: impl IntoIterator<Item = Predicate>,
        hidden: impl IntoIterator<Item = Predicate>,
        selected: impl IntoIterator<Item = Predicate>,
        goal: Predicate,
    ) -> ProverSequent {
        ProverSequent(Arc::new(SequentData {
            type_env,
            global: Arc::new(OrderedPredSet::from_iter(hyps)),
            local: Arc::new(OrderedPredSet::default()),
            hidden: Arc::new(OrderedPredSet::from_iter(hidden)),
            selected: Arc::new(OrderedPredSet::from_iter(selected)),
            goal,
        }))
    }

    /// Whether the two sequents are the same object — the "nothing
    /// changed" signal every mutator preserves.
    pub fn ptr_eq(a: &ProverSequent, b: &ProverSequent) -> bool {
        Arc::ptr_eq(&a.0, &b.0)
    }

    /// The sequent's type environment.
    pub fn type_env(&self) -> &SealedTypeEnvironment {
        &self.0.type_env
    }

    /// The goal.
    pub fn goal(&self) -> &Predicate {
        &self.0.goal
    }

    /// All hypotheses: the global ones then the rule-added local ones,
    /// each in insertion order.
    pub fn hyp_iter(&self) -> impl Iterator<Item = &Predicate> {
        self.0.global.iter().chain(self.0.local.iter())
    }

    /// The hypotheses not hidden, in [`Self::hyp_iter`] order.
    pub fn visible_hyp_iter(&self) -> impl Iterator<Item = &Predicate> {
        self.hyp_iter().filter(|hyp| !self.0.hidden.contains(hyp))
    }

    /// The selected hypotheses, in selection order.
    pub fn selected_hyp_iter(&self) -> impl Iterator<Item = &Predicate> {
        self.0.selected.iter()
    }

    /// The hidden hypotheses.
    pub fn hidden_hyp_iter(&self) -> impl Iterator<Item = &Predicate> {
        self.0.hidden.iter()
    }

    /// Whether `pred` is a hypothesis (global or local).
    pub fn contains_hypothesis(&self, pred: &Predicate) -> bool {
        self.0.local.contains(pred) || self.0.global.contains(pred)
    }

    /// Whether every given predicate is a hypothesis.
    pub fn contains_hypotheses<'a>(&self, preds: impl IntoIterator<Item = &'a Predicate>) -> bool {
        preds.into_iter().all(|pred| self.contains_hypothesis(pred))
    }

    /// Whether `hyp` is selected.
    pub fn is_selected(&self, hyp: &Predicate) -> bool {
        self.0.selected.contains(hyp)
    }

    /// Whether `hyp` is hidden.
    pub fn is_hidden(&self, hyp: &Predicate) -> bool {
        self.0.hidden.contains(hyp)
    }

    /// The incremental constructor behind every mutator: `None` keeps
    /// this sequent's field.
    fn derive(
        &self,
        type_env: Option<SealedTypeEnvironment>,
        local: Option<OrderedPredSet>,
        hidden: Option<OrderedPredSet>,
        selected: Option<OrderedPredSet>,
        goal: Option<Predicate>,
    ) -> ProverSequent {
        let data = &self.0;
        ProverSequent(Arc::new(SequentData {
            type_env: type_env.unwrap_or_else(|| data.type_env.clone()),
            global: data.global.clone(),
            local: local.map(Arc::new).unwrap_or_else(|| data.local.clone()),
            hidden: hidden.map(Arc::new).unwrap_or_else(|| data.hidden.clone()),
            selected: selected
                .map(Arc::new)
                .unwrap_or_else(|| data.selected.clone()),
            goal: goal.unwrap_or_else(|| data.goal.clone()),
        }))
    }

    /// Adds fresh identifiers and hypotheses and/or replaces the goal —
    /// The operation behind antecedent instantiation.
    ///
    /// Added hypotheses become selected unless listed in `unsel_added`
    /// (which must be a subset of `add_hyps`), and adding a hypothesis
    /// always un-hides it. `None` when the modification is ill-formed:
    /// a type error, a non-fresh identifier, or a predicate variable.
    /// Returns this very sequent when nothing changes.
    pub fn modify(
        &self,
        fresh_idents: &[TypedIdent],
        add_hyps: &[Predicate],
        unsel_added: &[Predicate],
        new_goal: Option<&Predicate>,
    ) -> Option<ProverSequent> {
        let mut checker = TypeChecker::new(self.0.type_env.clone());
        checker.add_idents(fresh_idents);
        checker.check_preds(add_hyps);
        if let Some(goal) = new_goal {
            checker.check_pred(goal);
        }
        if checker.rejected() {
            return None;
        }
        if add_hyps.iter().any(has_predicate_variable)
            || new_goal.is_some_and(has_predicate_variable)
        {
            return None;
        }
        if !unsel_added.iter().all(|pred| add_hyps.contains(pred)) {
            return None;
        }

        let mut modified = checker.env_changed;
        let new_type_env = checker.env_changed.then_some(checker.env);

        let mut sets = None;
        if !add_hyps.is_empty() {
            let mut local = (*self.0.local).clone();
            let mut selected = (*self.0.selected).clone();
            let mut hidden = (*self.0.hidden).clone();
            for hyp in add_hyps {
                if !self.contains_hypothesis(hyp) {
                    local.insert(hyp.clone());
                    modified = true;
                }
                if !unsel_added.contains(hyp) {
                    modified |= selected.insert(hyp.clone());
                }
                modified |= hidden.remove(hyp);
            }
            sets = Some((local, hidden, selected));
        }
        let new_goal = new_goal.filter(|goal| **goal != self.0.goal).cloned();
        modified |= new_goal.is_some();

        if !modified {
            return Some(self.clone());
        }
        let (local, hidden, selected) = match sets {
            Some((local, hidden, selected)) => (Some(local), Some(hidden), Some(selected)),
            None => (None, None, None),
        };
        Some(self.derive(new_type_env, local, hidden, selected, new_goal))
    }

    /// Selects the given hypotheses, un-hiding them; predicates that
    /// are not hypotheses are ignored.
    pub fn select_hypotheses(&self, to_select: &[Predicate]) -> ProverSequent {
        let mut modified = false;
        let mut selected = (*self.0.selected).clone();
        let mut hidden = (*self.0.hidden).clone();
        for hyp in to_select {
            if self.contains_hypothesis(hyp) {
                modified |= selected.insert(hyp.clone());
                modified |= hidden.remove(hyp);
            }
        }
        if modified {
            self.derive(None, None, Some(hidden), Some(selected), None)
        } else {
            self.clone()
        }
    }

    /// Deselects the given hypotheses.
    pub fn deselect_hypotheses(&self, to_deselect: &[Predicate]) -> ProverSequent {
        let mut selected = (*self.0.selected).clone();
        let mut modified = false;
        for hyp in to_deselect {
            modified |= selected.remove(hyp);
        }
        if modified {
            self.derive(None, None, None, Some(selected), None)
        } else {
            self.clone()
        }
    }

    /// Hides the given hypotheses, deselecting them; predicates that
    /// are not hypotheses are ignored.
    pub fn hide_hypotheses(&self, to_hide: &[Predicate]) -> ProverSequent {
        let mut modified = false;
        let mut selected = (*self.0.selected).clone();
        let mut hidden = (*self.0.hidden).clone();
        for hyp in to_hide {
            if self.contains_hypothesis(hyp) {
                modified |= hidden.insert(hyp.clone());
                modified |= selected.remove(hyp);
            }
        }
        if modified {
            self.derive(None, None, Some(hidden), Some(selected), None)
        } else {
            self.clone()
        }
    }

    /// Un-hides the given hypotheses.
    pub fn show_hypotheses(&self, to_show: &[Predicate]) -> ProverSequent {
        let mut hidden = (*self.0.hidden).clone();
        let mut modified = false;
        for hyp in to_show {
            modified |= hidden.remove(hyp);
        }
        if modified {
            self.derive(None, None, Some(hidden), None, None)
        } else {
            self.clone()
        }
    }

    /// Forward inference `hyps ⊢ ∃ added_idents · inf_hyps`: adds the
    /// inferred hypotheses when the inference is applicable, and
    /// silently returns this very sequent otherwise — a failed
    /// hypothesis action never fails the enclosing rule.
    ///
    /// Inferred hypotheses are selected iff any source hypothesis is
    /// selected, and hidden iff all source hypotheses are hidden — so
    /// with no source hypotheses they land hidden.
    pub fn perform_fwd_inf(
        &self,
        hyps: &[Predicate],
        added_idents: &[TypedIdent],
        inf_hyps: &[Predicate],
    ) -> ProverSequent {
        self.fwd_inf(hyps, added_idents, inf_hyps)
            .unwrap_or_else(|| self.clone())
    }

    /// A rewrite hypothesis action: the forward inference followed by
    /// hiding `to_hide` (the rewritten-away hypotheses). An
    /// inapplicable inference skips the hiding too.
    pub fn perform_rewrite(
        &self,
        hyps: &[Predicate],
        added_idents: &[TypedIdent],
        inf_hyps: &[Predicate],
        to_hide: &[Predicate],
    ) -> ProverSequent {
        match self.fwd_inf(hyps, added_idents, inf_hyps) {
            Some(next) => next.hide_hypotheses(to_hide),
            None => self.clone(),
        }
    }

    /// The shared forward-inference core: `None` means inapplicable.
    fn fwd_inf(
        &self,
        hyps: &[Predicate],
        added_idents: &[TypedIdent],
        inf_hyps: &[Predicate],
    ) -> Option<ProverSequent> {
        let mut checker = TypeChecker::new(self.0.type_env.clone());
        checker.check_preds(hyps);
        checker.add_idents(added_idents);
        checker.check_preds(inf_hyps);
        if checker.rejected() {
            return None;
        }
        if inf_hyps.iter().any(has_predicate_variable) {
            return None;
        }
        if !self.contains_hypotheses(hyps) {
            return None;
        }

        let mut modified = checker.env_changed;
        let new_type_env = checker.env_changed.then_some(checker.env);

        let select_inf = hyps.iter().any(|hyp| self.0.selected.contains(hyp));
        let hide_inf = !select_inf && hyps.iter().all(|hyp| self.0.hidden.contains(hyp));

        let mut local = (*self.0.local).clone();
        let mut selected = (*self.0.selected).clone();
        let mut hidden = (*self.0.hidden).clone();
        for inf in inf_hyps {
            if !self.contains_hypothesis(inf) {
                local.insert(inf.clone());
                if select_inf {
                    selected.insert(inf.clone());
                }
                if hide_inf {
                    hidden.insert(inf.clone());
                }
                modified = true;
            } else if select_inf && !self.0.hidden.contains(inf) {
                // Re-selecting an already-present visible inferred
                // hypothesis and counts the action as a modification
                // even when it was already selected — reproduced
                // faithfully, since the identity signal feeds the proof
                // builder's skip detection.
                selected.insert(inf.clone());
                modified = true;
            }
        }
        if modified {
            Some(self.derive(
                new_type_env,
                Some(local),
                Some(hidden),
                Some(selected),
                None,
            ))
        } else {
            Some(self.clone())
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_util::{env, pred};

    fn ints(names: &[&str]) -> SealedTypeEnvironment {
        let bindings: Vec<(&str, &str)> = names.iter().map(|n| (*n, "ℤ")).collect();
        env(&bindings)
    }

    /// x=1 ⊢ x<2 with y=3 hidden and x=1 selected.
    fn base() -> ProverSequent {
        let env = ints(&["x", "y"]);
        let h1 = pred(&env, "x=1");
        let h2 = pred(&env, "y=3");
        ProverSequent::new(
            env.clone(),
            [h1.clone(), h2.clone()],
            [h2],
            [h1],
            pred(&env, "x<2"),
        )
    }

    #[test]
    fn accessors_and_order() {
        let seq = base();
        let texts: Vec<String> = seq.hyp_iter().map(|h| format!("{h:?}")).collect();
        assert_eq!(texts.len(), 2);
        let env = seq.type_env().clone();
        assert!(seq.contains_hypothesis(&pred(&env, "x=1")));
        assert!(seq.contains_hypotheses([&pred(&env, "x=1"), &pred(&env, "y=3")]));
        assert!(!seq.contains_hypothesis(&pred(&env, "x=2")));
        assert!(seq.is_selected(&pred(&env, "x=1")));
        assert!(seq.is_hidden(&pred(&env, "y=3")));
        // Visible = all minus hidden.
        assert_eq!(seq.visible_hyp_iter().count(), 1);
    }

    #[test]
    fn selection_mutators_share_when_unchanged() {
        let seq = base();
        let env = seq.type_env().clone();
        let selected = pred(&env, "x=1");
        let unknown = pred(&env, "x=2");

        assert!(ProverSequent::ptr_eq(
            &seq,
            &seq.select_hypotheses(std::slice::from_ref(&selected))
        ));
        // A non-hypothesis is ignored by select and hide.
        assert!(ProverSequent::ptr_eq(
            &seq,
            &seq.select_hypotheses(std::slice::from_ref(&unknown))
        ));
        assert!(ProverSequent::ptr_eq(
            &seq,
            &seq.hide_hypotheses(std::slice::from_ref(&unknown))
        ));
        assert!(ProverSequent::ptr_eq(
            &seq,
            &seq.deselect_hypotheses(std::slice::from_ref(&unknown))
        ));
        assert!(ProverSequent::ptr_eq(
            &seq,
            &seq.show_hypotheses(std::slice::from_ref(&selected))
        ));
    }

    #[test]
    fn hide_deselects_and_select_unhides() {
        let seq = base();
        let env = seq.type_env().clone();
        let h1 = pred(&env, "x=1");
        let h2 = pred(&env, "y=3");

        let hidden = seq.hide_hypotheses(std::slice::from_ref(&h1));
        assert!(hidden.is_hidden(&h1));
        assert!(!hidden.is_selected(&h1));

        let selected = seq.select_hypotheses(std::slice::from_ref(&h2));
        assert!(!selected.is_hidden(&h2));
        assert!(selected.is_selected(&h2));

        let shown = seq.show_hypotheses(std::slice::from_ref(&h2));
        assert!(!shown.is_hidden(&h2));
        assert!(!shown.is_selected(&h2));
    }

    #[test]
    fn modify_adds_selected_hypotheses_and_idents() {
        let seq = base();
        let mut builder = seq.type_env().to_builder();
        builder.insert("z", Type::Int);
        let wide = builder.make_snapshot();
        let added = pred(&wide, "z=4");

        let next = seq
            .modify(
                &[TypedIdent::new("z", Type::Int)],
                std::slice::from_ref(&added),
                &[],
                None,
            )
            .expect("applicable");
        assert!(!ProverSequent::ptr_eq(&seq, &next));
        assert_eq!(next.type_env().get("z"), Some(&Type::Int));
        assert!(next.contains_hypothesis(&added));
        assert!(next.is_selected(&added));

        // The same hypothesis listed as unselected stays unselected.
        let unsel = seq
            .modify(
                &[TypedIdent::new("z", Type::Int)],
                std::slice::from_ref(&added),
                std::slice::from_ref(&added),
                None,
            )
            .expect("applicable");
        assert!(!unsel.is_selected(&added));
    }

    #[test]
    fn modify_unhides_added_hypothesis_and_replaces_goal() {
        let seq = base();
        let env = seq.type_env().clone();
        let hidden = pred(&env, "y=3");
        let goal = pred(&env, "y<4");

        let next = seq
            .modify(&[], std::slice::from_ref(&hidden), &[], Some(&goal))
            .expect("applicable");
        assert!(!next.is_hidden(&hidden));
        assert_eq!(next.goal(), &goal);
    }

    #[test]
    fn modify_shares_when_nothing_changes() {
        let seq = base();
        let env = seq.type_env().clone();
        let existing = pred(&env, "x=1");
        let goal = seq.goal().clone();

        let same = seq
            .modify(&[], std::slice::from_ref(&existing), &[], Some(&goal))
            .expect("applicable");
        assert!(ProverSequent::ptr_eq(&seq, &same));
    }

    #[test]
    fn modify_rejects_ill_formed_changes() {
        let seq = base();
        let env = seq.type_env().clone();
        let known = pred(&env, "x=1");

        // Non-fresh identifier, even at the same type.
        assert!(
            seq.modify(&[TypedIdent::new("x", Type::Int)], &[], &[], None)
                .is_none()
        );
        // Non-fresh identifier at a clashing type.
        assert!(
            seq.modify(&[TypedIdent::new("x", Type::Bool)], &[], &[], None)
                .is_none()
        );
        // A hypothesis over an unknown identifier.
        let wide = ints(&["x", "y", "w"]);
        let alien = pred(&wide, "w=5");
        assert!(
            seq.modify(&[], std::slice::from_ref(&alien), &[], None)
                .is_none()
        );
        // A hypothesis whose identifier type contradicts the environment.
        let other = env.to_builder();
        let mut other = other;
        other.insert("x", Type::Bool);
        let clashing = pred(&other.make_snapshot(), "x=TRUE");
        assert!(
            seq.modify(&[], std::slice::from_ref(&clashing), &[], None)
                .is_none()
        );
        // unsel_added must be a subset of add_hyps.
        assert!(
            seq.modify(&[], &[], std::slice::from_ref(&known), None)
                .is_none()
        );
        // Predicate variables are rejected.
        let pred_var = known.factory().predicate_variable("$P", None);
        assert!(
            seq.modify(&[], std::slice::from_ref(&pred_var), &[], None)
                .is_none()
        );
        assert!(seq.modify(&[], &[], &[], Some(&pred_var)).is_none());
    }

    #[test]
    fn fwd_inf_selection_follows_sources() {
        let seq = base();
        let env = seq.type_env().clone();
        let sel_src = pred(&env, "x=1"); // selected
        let hid_src = pred(&env, "y=3"); // hidden
        let inf = pred(&env, "x+y=4");

        // Any selected source selects the inferred hypothesis.
        let next = seq.perform_fwd_inf(
            std::slice::from_ref(&sel_src),
            &[],
            std::slice::from_ref(&inf),
        );
        assert!(next.contains_hypothesis(&inf));
        assert!(next.is_selected(&inf));

        // All-hidden sources hide the inferred hypothesis.
        let next = seq.perform_fwd_inf(
            std::slice::from_ref(&hid_src),
            &[],
            std::slice::from_ref(&inf),
        );
        assert!(next.contains_hypothesis(&inf));
        assert!(next.is_hidden(&inf));
        assert!(!next.is_selected(&inf));
    }

    #[test]
    fn fwd_inf_failures_are_silent() {
        let seq = base();
        let env = seq.type_env().clone();
        let inf = pred(&env, "x+y=4");
        let missing = pred(&env, "x=9");

        // Missing source hypothesis.
        let out = seq.perform_fwd_inf(
            std::slice::from_ref(&missing),
            &[],
            std::slice::from_ref(&inf),
        );
        assert!(ProverSequent::ptr_eq(&seq, &out));

        // Clashing introduced identifier.
        let out = seq.perform_fwd_inf(
            &[],
            &[TypedIdent::new("x", Type::Int)],
            std::slice::from_ref(&inf),
        );
        assert!(ProverSequent::ptr_eq(&seq, &out));
    }

    #[test]
    fn rewrite_hides_the_rewritten_hypothesis() {
        let seq = base();
        let env = seq.type_env().clone();
        let src = pred(&env, "x=1");
        let inf = pred(&env, "1=x");

        let next = seq.perform_rewrite(
            std::slice::from_ref(&src),
            &[],
            std::slice::from_ref(&inf),
            std::slice::from_ref(&src),
        );
        assert!(next.contains_hypothesis(&inf));
        assert!(next.is_selected(&inf));
        assert!(next.is_hidden(&src));

        // An inapplicable inference skips the hiding too.
        let missing = pred(&env, "x=9");
        let out = seq.perform_rewrite(
            std::slice::from_ref(&missing),
            &[],
            std::slice::from_ref(&inf),
            std::slice::from_ref(&src),
        );
        assert!(ProverSequent::ptr_eq(&seq, &out));
    }
}
