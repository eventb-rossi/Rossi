//! Pretty printer for converting AST back to Event-B text
//!
//! This module provides functionality to convert parsed AST structures
//! back into formatted Event-B text. It supports both Unicode and ASCII
//! operators, customizable indentation, and produces output that can be
//! parsed back into the same AST (roundtrip support).
//!
//! # Examples
//!
//! Basic usage with default settings (Unicode operators, 4-space indentation):
//!
//! ```
//! use rossi::{parse, to_string};
//!
//! let source = "CONTEXT test\nSETS\n    STATUS\nEND\n";
//! let component = parse(source).unwrap();
//! let output = to_string(&component);
//! println!("{}", output);
//! ```
//!
//! Using ASCII operators:
//!
//! ```
//! use rossi::{parse, to_string_ascii};
//!
//! let source = "CONTEXT test\nEND\n";
//! let component = parse(source).unwrap();
//! let output = to_string_ascii(&component);
//! ```
//!
//! Custom configuration:
//!
//! ```
//! use rossi::{parse, PrettyPrinter};
//!
//! let source = "CONTEXT test\nEND\n";
//! let component = parse(source).unwrap();
//!
//! let printer = PrettyPrinter::new()
//!     .with_indent("  ".to_string()); // 2-space indentation
//! let output = printer.print_component(&component);
//! ```

use crate::ast::*;
use crate::comments;
use crate::op_info;
use crate::operators::{self, OperatorId};
use crate::operators::{BinaryOp, UnaryOp};
use crate::operators::{ComparisonOp, LogicalOp, Quantifier};
use std::fmt::Write;

/// Debug guard: a structural name about to be emitted must be re-lexable by
/// the grammar's `component_name` rule, or the printed text could not be
/// parsed back (issue #28). Parser- and XML-built ASTs are validated
/// upstream; this catches programmatically constructed ones.
fn debug_assert_component_name(name: &str, role: &str) {
    debug_assert!(
        crate::names::is_valid_component_name(name),
        "{role} {name:?} is not a valid component name; printed output would not re-parse"
    );
}

/// True when a comment would actually render, i.e. it survives
/// [`comments::normalize_comment`] — the same test [`PrettyPrinter::writeln_commented`]
/// applies. Layout decisions that key on "has a comment" must use this, not a
/// bare `Option::is_some`: an imported blank comment (`Some("")` from a Rodin
/// `comment=""` attribute) prints as an empty line and reparses to `None`, so
/// treating it as a real comment makes the round-trip non-idempotent.
fn renders_comment(comment: Option<&str>) -> bool {
    comment.and_then(comments::normalize_comment).is_some()
}

/// Whitespace convention for formulas emitted by [`PrettyPrinter`].
#[derive(Debug, Default, Clone, Copy, PartialEq, Eq)]
pub enum FormulaSpacing {
    /// Readable Event-B text with spaces around operators and after commas.
    #[default]
    Readable,
    /// Rodin's compact canonical form used in static-checker XML attributes.
    RodinCanonical,
    /// Rodin's `Formula#toString()` form used in marker diagnostics.
    RodinFormulaString,
}

/// The top-level formula being rendered. Rodin formats binary type
/// ascriptions differently in predicates than in expressions and actions.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormulaContext {
    Predicate,
    Expression,
    Action,
}

/// Configuration for the pretty printer
#[derive(Debug, Clone)]
pub struct PrettyPrinter {
    /// Use Unicode operators (true) or ASCII (false)
    pub use_unicode: bool,
    /// Indentation string (default: 4 spaces)
    pub indent: String,
    /// Emit the raw Rodin private-use-area glyphs (U+E100..E103) for the
    /// relation/override operators instead of their ASCII spelling. Off by
    /// default: those glyphs render as tofu without Rodin's font, so output
    /// meant for an editor stays portable. Rodin-canonical formatting (the
    /// static checker's `canonical` form) turns this on to match Rodin's
    /// internal bcc/bcm spelling exactly; see `OperatorSpelling::emit_text`.
    pub private_use_glyphs: bool,
    /// Whitespace convention for formulas.
    pub formula_spacing: FormulaSpacing,
    /// When printing formula-model declarations, spell their solved
    /// types (`x⦂ℤ`) instead of only their source annotations — what
    /// canonical static-checker text uses.
    pub typed_decls: bool,
}

impl Default for PrettyPrinter {
    fn default() -> Self {
        Self {
            use_unicode: true,
            indent: "    ".to_string(),
            private_use_glyphs: false,
            formula_spacing: FormulaSpacing::Readable,
            typed_decls: false,
        }
    }
}

impl PrettyPrinter {
    /// Create a new pretty printer with default settings
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a pretty printer that uses ASCII operators
    pub fn ascii() -> Self {
        Self {
            use_unicode: false,
            ..Self::default()
        }
    }

    /// Spell solved declaration types when printing formula-model
    /// declarations.
    pub fn with_typed_decls(mut self, typed_decls: bool) -> Self {
        self.typed_decls = typed_decls;
        self
    }

    /// Create a printer for Rodin's compact static-checker formula form.
    pub fn rodin_canonical() -> Self {
        Self {
            private_use_glyphs: true,
            formula_spacing: FormulaSpacing::RodinCanonical,
            ..Self::default()
        }
    }

    /// Create a printer matching Rodin's formula spelling in diagnostics.
    pub fn rodin_formula_string() -> Self {
        Self::rodin_canonical().with_formula_spacing(FormulaSpacing::RodinFormulaString)
    }

    /// Set the indentation string
    pub fn with_indent(mut self, indent: String) -> Self {
        self.indent = indent;
        self
    }

    /// Emit the raw Rodin private-use glyphs for the relation/override
    /// operators (see [`PrettyPrinter::private_use_glyphs`]).
    pub fn with_private_use_glyphs(mut self, yes: bool) -> Self {
        self.private_use_glyphs = yes;
        self
    }

    /// Set the whitespace convention used for formulas.
    pub fn with_formula_spacing(mut self, formula_spacing: FormulaSpacing) -> Self {
        self.formula_spacing = formula_spacing;
        self
    }

    /// Convert a Component to formatted Event-B text
    pub fn print_component(&self, component: &Component) -> String {
        match component {
            Component::Context(ctx) => self.print_context(ctx),
            Component::Machine(mch) => self.print_machine(mch),
        }
    }

    /// Convert multiple Components to formatted Event-B text, separated by blank lines
    pub fn print_components(&self, components: &[Component]) -> String {
        let mut output = String::new();
        for (i, component) in components.iter().enumerate() {
            if i > 0 {
                output.push('\n');
            }
            output.push_str(&self.print_component(component));
        }
        output
    }

    /// Print one element line followed by its comment, Camille style.
    ///
    /// `line` is the complete element line without the trailing newline and
    /// `indent` is the element's own indentation. A single-line comment
    /// trails the element (`line // text`); a multiline comment becomes a
    /// `/* ... */` block on the following lines, one level deeper, with
    /// continuation lines aligned under the first — the same layout Rodin's
    /// Camille editor prints. Comments are normalized first, so a blank
    /// comment emits nothing and parse → print is idempotent.
    fn writeln_commented(
        &self,
        output: &mut String,
        line: &str,
        comment: Option<&str>,
        indent: &str,
    ) {
        let Some(text) = comment.and_then(comments::normalize_comment) else {
            writeln!(output, "{line}").unwrap();
            return;
        };
        if !text.contains('\n') {
            writeln!(output, "{line} // {text}").unwrap();
            return;
        }
        // `*/` inside the text (possible only via Rodin XML) would close the
        // block early; break it up, losing one byte of fidelity.
        let text = text.replace("*/", "* /");
        writeln!(output, "{line}").unwrap();
        let block_indent = format!("{indent}{}", self.indent);
        let mut lines = text.split('\n');
        let first = lines.next().unwrap();
        write!(output, "{block_indent}/* {first}").unwrap();
        for cont in lines {
            writeln!(output).unwrap();
            if !cont.is_empty() {
                write!(output, "{block_indent}   {cont}").unwrap();
            }
        }
        writeln!(output, " */").unwrap();
    }

    /// Convert a Context to formatted text
    pub fn print_context(&self, context: &Context) -> String {
        let mut output = String::new();

        debug_assert_component_name(&context.name, "context name");
        self.writeln_commented(
            &mut output,
            &format!("CONTEXT {}", context.name),
            context.comment.as_deref(),
            "",
        );

        if !context.extends.is_empty() {
            writeln!(output, "EXTENDS").unwrap();
            for ext in &context.extends {
                debug_assert_component_name(ext, "extends target");
                writeln!(output, "{}{}", self.indent, ext).unwrap();
            }
        }

        if !context.sets.is_empty() {
            writeln!(output, "SETS").unwrap();
            for set in &context.sets {
                self.writeln_commented(
                    &mut output,
                    &format!("{}{}", self.indent, set.name),
                    set.comment.as_deref(),
                    &self.indent,
                );
            }
        }

        if !context.constants.is_empty() {
            writeln!(output, "CONSTANTS").unwrap();
            for constant in &context.constants {
                self.writeln_commented(
                    &mut output,
                    &format!("{}{}", self.indent, constant.name),
                    constant.comment.as_deref(),
                    &self.indent,
                );
            }
        }

        if !context.axioms.is_empty() {
            writeln!(output, "AXIOMS").unwrap();
            for axiom in &context.axioms {
                self.print_labeled_predicate(&mut output, axiom, &self.indent);
            }
        }

        writeln!(output, "END").unwrap();
        output
    }

    /// Convert a Machine to formatted text
    pub fn print_machine(&self, machine: &Machine) -> String {
        let mut output = String::new();

        debug_assert_component_name(&machine.name, "machine name");
        self.writeln_commented(
            &mut output,
            &format!("MACHINE {}", machine.name),
            machine.comment.as_deref(),
            "",
        );

        if let Some(ref refines) = machine.refines {
            debug_assert_component_name(refines, "refines target");
            writeln!(output, "REFINES").unwrap();
            writeln!(output, "{}{}", self.indent, refines).unwrap();
        }

        if !machine.sees.is_empty() {
            writeln!(output, "SEES").unwrap();
            for sees in &machine.sees {
                debug_assert_component_name(sees, "sees target");
                writeln!(output, "{}{}", self.indent, sees).unwrap();
            }
        }

        if !machine.variables.is_empty() {
            writeln!(output, "VARIABLES").unwrap();
            for var in &machine.variables {
                self.writeln_commented(
                    &mut output,
                    &format!("{}{}", self.indent, var.name),
                    var.comment.as_deref(),
                    &self.indent,
                );
            }
        }

        if !machine.invariants.is_empty() {
            writeln!(output, "INVARIANTS").unwrap();
            for inv in &machine.invariants {
                self.print_labeled_predicate(&mut output, inv, &self.indent);
            }
        }

        if !machine.variants.is_empty() {
            writeln!(output, "VARIANT").unwrap();
            for (i, variant) in machine.variants.iter().enumerate() {
                let expr = self.print_formula_expression(&variant.expression);
                match &variant.label {
                    Some(label) => {
                        writeln!(output, "{}@{label} {expr}", self.indent).unwrap();
                    }
                    // The grammar only allows a bare expression in first
                    // position; spell out the default label elsewhere so
                    // the output stays parseable.
                    None if i == 0 => {
                        writeln!(output, "{}{expr}", self.indent).unwrap();
                    }
                    None => {
                        let label = crate::ast::DEFAULT_VARIANT_LABEL;
                        writeln!(output, "{}@{label} {expr}", self.indent).unwrap();
                    }
                }
            }
        }

        if machine.initialisation.is_some() || !machine.events.is_empty() {
            writeln!(output, "EVENTS").unwrap();

            if let Some(init) = &machine.initialisation {
                self.print_initialisation(&mut output, init);
            }

            for event in &machine.events {
                writeln!(output).unwrap();
                self.print_event(&mut output, event);
            }
        }

        writeln!(output, "END").unwrap();
        output
    }

    /// Print a labeled predicate.
    ///
    /// Theorems are always emitted in the inline `theorem @x` form within
    /// AXIOMS/INVARIANTS, never as a separate `THEOREMS` section. This is the
    /// canonical, order-preserving form and mirrors Rodin's model, where a theorem
    /// is a boolean attribute on an axiom/invariant rather than a distinct section.
    /// Parsing a `THEOREMS` section is therefore normalized to inline on output.
    fn print_labeled_predicate(&self, output: &mut String, lp: &LabeledPredicate, indent: &str) {
        let theorem_str = if lp.is_theorem { "theorem " } else { "" };
        let line = if let Some(label) = &lp.label {
            format!(
                "{}{}@{} {}",
                indent,
                theorem_str,
                label,
                self.print_formula_predicate(&lp.predicate)
            )
        } else {
            format!(
                "{}{}{}",
                indent,
                theorem_str,
                self.print_formula_predicate(&lp.predicate)
            )
        };
        self.writeln_commented(output, &line, lp.comment.as_deref(), indent);
    }

    /// Print a labeled action
    fn print_labeled_action(&self, output: &mut String, la: &LabeledAction, indent: &str) {
        let line = if let Some(label) = &la.label {
            format!(
                "{}@{} {}",
                indent,
                label,
                self.print_action_body(&la.action)
            )
        } else {
            format!("{}{}", indent, self.print_action_body(&la.action))
        };
        self.writeln_commented(output, &line, la.comment.as_deref(), indent);
    }

    /// Print an action list (one action per line, no separators).
    fn print_action_list(&self, output: &mut String, actions: &[LabeledAction], indent: &str) {
        for action in actions {
            self.print_labeled_action(output, action, indent);
        }
    }

    /// Print an initialisation event
    fn print_initialisation(&self, output: &mut String, init: &InitialisationEvent) {
        let double_indent = format!("{}{}", self.indent, self.indent);
        let header = if init.extended {
            format!("{}EVENT INITIALISATION extends INITIALISATION", self.indent)
        } else {
            format!("{}EVENT INITIALISATION", self.indent)
        };
        self.writeln_commented(output, &header, init.comment.as_deref(), &self.indent);
        if !init.actions.is_empty() {
            writeln!(output, "{}THEN", self.indent).unwrap();
            self.print_action_list(output, &init.actions, &double_indent);
        }
        writeln!(output, "{}END", self.indent).unwrap();
    }

    /// Print an event
    fn print_event(&self, output: &mut String, event: &Event) {
        let double_indent = format!("{}{}", self.indent, self.indent);

        debug_assert_component_name(&event.name, "event name");
        for target in &event.refines {
            debug_assert_component_name(&target.name, "event refines target");
        }

        // Emit status inline before EVENT keyword (Camille-compatible form):
        // `convergent EVENT name` instead of `EVENT name\nSTATUS convergent`
        let status_prefix = match &event.status {
            Some(EventStatus::Convergent) => "convergent ",
            Some(EventStatus::Anticipated) => "anticipated ",
            _ => "",
        };

        // When `extended` is true and there is a refines target, use
        // `EVENT name extends parent` syntax (Rodin extension mechanism).
        let header = match event.refines.first() {
            Some(parent) if event.extended => format!(
                "{}{}EVENT {} extends {}",
                self.indent, status_prefix, event.name, parent.name
            ),
            _ => format!("{}{}EVENT {}", self.indent, status_prefix, event.name),
        };
        self.writeln_commented(output, &header, event.comment.as_deref(), &self.indent);

        // Print REFINES clause when not extended, one target per line
        if !event.extended && !event.refines.is_empty() {
            writeln!(output, "{}REFINES", self.indent).unwrap();
            for target in &event.refines {
                writeln!(output, "{}{}", double_indent, target.name).unwrap();
            }
        }

        if !event.parameters.is_empty() {
            writeln!(output, "{}ANY", self.indent).unwrap();
            if event
                .parameters
                .iter()
                .any(|p| renders_comment(p.comment.as_deref()))
            {
                // A commented parameter needs its own line for the trailing
                // comment to re-attach to it on reparse.
                for param in &event.parameters {
                    self.writeln_commented(
                        output,
                        &format!("{}{}", double_indent, param.name),
                        param.comment.as_deref(),
                        &double_indent,
                    );
                }
            } else {
                let param_names: Vec<&str> =
                    event.parameters.iter().map(|p| p.name.as_str()).collect();
                // Parameters are whitespace-separated, not comma-separated, so
                // the line reparses under the structural-list grammar.
                writeln!(output, "{}{}", double_indent, param_names.join(" ")).unwrap();
            }
        }

        if !event.guards.is_empty() {
            writeln!(output, "{}WHERE", self.indent).unwrap();
            for guard in &event.guards {
                self.print_labeled_predicate(output, guard, &double_indent);
            }
        }

        if !event.with.is_empty() {
            writeln!(output, "{}WITH", self.indent).unwrap();
            for lp in &event.with {
                self.print_labeled_predicate(output, lp, &double_indent);
            }
        }

        if !event.witnesses.is_empty() {
            writeln!(output, "{}WITNESS", self.indent).unwrap();
            for lp in &event.witnesses {
                self.print_labeled_predicate(output, lp, &double_indent);
            }
        }

        if !event.actions.is_empty() {
            writeln!(output, "{}THEN", self.indent).unwrap();
            self.print_action_list(output, &event.actions, &double_indent);
        }

        writeln!(output, "{}END", self.indent).unwrap();
    }

    #[inline]
    fn comma_separator(&self) -> &'static str {
        match self.formula_spacing {
            FormulaSpacing::Readable => ", ",
            FormulaSpacing::RodinCanonical | FormulaSpacing::RodinFormulaString => ",",
        }
    }

    #[inline]
    fn tight_operator_separator(&self, id: OperatorId) -> &'static str {
        if self.formula_spacing != FormulaSpacing::Readable
            && (self.use_unicode || operators::spelling(id).is_symbolic())
        {
            ""
        } else {
            " "
        }
    }

    #[inline]
    fn binary_separator(&self, op: BinaryOp, context: FormulaContext) -> &'static str {
        match self.formula_spacing {
            FormulaSpacing::Readable => " ",
            FormulaSpacing::RodinCanonical if self.rodin_binary_is_tight(op, context) => "",
            FormulaSpacing::RodinFormulaString if self.formula_string_binary_is_tight(op) => "",
            FormulaSpacing::RodinCanonical | FormulaSpacing::RodinFormulaString => " ",
        }
    }

    fn formula_string_binary_is_tight(&self, op: BinaryOp) -> bool {
        matches!(
            op,
            BinaryOp::Add
                | BinaryOp::Multiply
                | BinaryOp::Union
                | BinaryOp::Intersection
                | BinaryOp::Overwrite
                | BinaryOp::Composition
                | BinaryOp::Semicolon
        )
    }

    /// Whether Rodin removes whitespace around this binary expression
    /// operator. Keep this match exhaustive so a new AST operator cannot gain
    /// an accidental default spacing policy.
    fn rodin_binary_is_tight(&self, op: BinaryOp, context: FormulaContext) -> bool {
        match op {
            BinaryOp::Add
            | BinaryOp::Multiply
            | BinaryOp::Union
            | BinaryOp::Intersection
            | BinaryOp::CartesianProduct
            | BinaryOp::Overwrite => true,
            // Rodin tightens a binary type ascription in a predicate, while
            // standalone expressions and assignments retain spaces. ASCII
            // `oftype` needs word-separating whitespace in every context.
            BinaryOp::OfType => self.use_unicode && context == FormulaContext::Predicate,
            BinaryOp::Subtract
            | BinaryOp::Divide
            | BinaryOp::Modulo
            | BinaryOp::Exponent
            | BinaryOp::Range
            | BinaryOp::Difference
            | BinaryOp::Relation
            | BinaryOp::TotalRelation
            | BinaryOp::SurjectiveRelation
            | BinaryOp::TotalSurjectiveRelation
            | BinaryOp::TotalFunction
            | BinaryOp::PartialFunction
            | BinaryOp::TotalInjection
            | BinaryOp::PartialInjection
            | BinaryOp::TotalSurjection
            | BinaryOp::PartialSurjection
            | BinaryOp::Bijection
            | BinaryOp::Composition
            | BinaryOp::Semicolon
            | BinaryOp::DomainRestriction
            | BinaryOp::DomainSubtraction
            | BinaryOp::RangeRestriction
            | BinaryOp::RangeSubtraction
            | BinaryOp::DirectProduct
            | BinaryOp::ParallelProduct
            | BinaryOp::Maplet => false,
        }
    }

    /// Pick between a Unicode and ASCII symbol based on the printer mode.
    #[inline]
    fn sym(&self, unicode: &'static str, ascii: &'static str) -> &'static str {
        if self.use_unicode { unicode } else { ascii }
    }

    /// Pick an operator spelling from the shared Event-B table. Unless
    /// `private_use_glyphs` is set, this routes through `emit_text` so the
    /// private-use relation/override operators print as ASCII (their glyph
    /// won't render without Rodin's font).
    #[inline]
    fn op(&self, id: OperatorId) -> &'static str {
        if self.private_use_glyphs {
            operators::spell(id, self.use_unicode)
        } else {
            operators::spelling(id).emit_text(self.use_unicode)
        }
    }

    #[inline]
    fn oftype_annotation(&self) -> &'static str {
        if self.use_unicode {
            self.op(OperatorId::OfType)
        } else {
            " oftype "
        }
    }

    /// True if `s` contains a `;` outside all (), [], {} delimiters —
    /// i.e. a top-level forward composition (the printer emits `;` for nothing else).
    fn has_bare_semicolon(s: &str) -> bool {
        let mut depth = 0usize;
        for c in s.chars() {
            match c {
                '(' | '[' | '{' => depth += 1,
                ')' | ']' | '}' => depth = depth.saturating_sub(1),
                ';' if depth == 0 => return true,
                _ => {}
            }
        }
        false
    }

    /// Wrap `s` in parentheses iff it has a bare `;`, so the text-format
    /// `action` rule (whose `_no_semi` expression variants reserve `;` for
    /// action boundaries) can re-parse printed actions. Parentheses are
    /// precedence-derived, not AST nodes, so the round-tripped AST is
    /// identical.
    fn guard_action_part(s: String) -> String {
        if Self::has_bare_semicolon(&s) {
            format!("({})", s)
        } else {
            s
        }
    }

    /// Format an action body: `skip`, or the modelled assignment.
    pub fn print_action_body(&self, body: &crate::ast::ActionBody) -> String {
        match body {
            crate::ast::ActionBody::Skip => "skip".to_string(),
            crate::ast::ActionBody::Assignment(assignment) => {
                self.print_formula_assignment(assignment)
            }
        }
    }
}

// ===== formula-model printing =====
//
// Formulas print through the shared operator tables (spelling,
// precedence, spacing), so text and structural printing stay in one
// configuration. Bound identifiers are
// resolved to names through a stack of enclosing declaration names;
// a declaration keeps its hint unless a name visible in its body would
// be captured, in which case it is freshened.

use crate::formula::fresh::{FreshNameSolver, resolve_idents};
use crate::formula::tag::{
    AssocExprOp, AssocPredOp, AtomicOp, BinaryExprOp, BinaryPredOp, LiteralPredOp, QuantExprOp,
    QuantPredOp, RelationalOp, UnaryExprOp,
};
use crate::formula::{self, ExpressionKind as FExprKind, Form, PredicateKind as FPredKind};

/// The legacy operator equivalent of a binary formula operator, for the
/// shared precedence/spacing tables. Function application and
/// relational image print structurally and never go through this.
fn legacy_binary(op: BinaryExprOp) -> BinaryOp {
    match op {
        BinaryExprOp::Mapsto => BinaryOp::Maplet,
        BinaryExprOp::Rel => BinaryOp::Relation,
        BinaryExprOp::TRel => BinaryOp::TotalRelation,
        BinaryExprOp::SRel => BinaryOp::SurjectiveRelation,
        BinaryExprOp::STRel => BinaryOp::TotalSurjectiveRelation,
        BinaryExprOp::PFun => BinaryOp::PartialFunction,
        BinaryExprOp::TFun => BinaryOp::TotalFunction,
        BinaryExprOp::PInj => BinaryOp::PartialInjection,
        BinaryExprOp::TInj => BinaryOp::TotalInjection,
        BinaryExprOp::PSur => BinaryOp::PartialSurjection,
        BinaryExprOp::TSur => BinaryOp::TotalSurjection,
        BinaryExprOp::TBij => BinaryOp::Bijection,
        BinaryExprOp::SetMinus => BinaryOp::Difference,
        BinaryExprOp::CProd => BinaryOp::CartesianProduct,
        BinaryExprOp::DProd => BinaryOp::DirectProduct,
        BinaryExprOp::PProd => BinaryOp::ParallelProduct,
        BinaryExprOp::DomRes => BinaryOp::DomainRestriction,
        BinaryExprOp::DomSub => BinaryOp::DomainSubtraction,
        BinaryExprOp::RanRes => BinaryOp::RangeRestriction,
        BinaryExprOp::RanSub => BinaryOp::RangeSubtraction,
        BinaryExprOp::UpTo => BinaryOp::Range,
        BinaryExprOp::Minus => BinaryOp::Subtract,
        BinaryExprOp::Div => BinaryOp::Divide,
        BinaryExprOp::Mod => BinaryOp::Modulo,
        BinaryExprOp::Expn => BinaryOp::Exponent,
        BinaryExprOp::FunImage | BinaryExprOp::RelImage => {
            unreachable!("applications and images print structurally")
        }
    }
}

fn legacy_assoc(op: AssocExprOp) -> BinaryOp {
    match op {
        AssocExprOp::BUnion => BinaryOp::Union,
        AssocExprOp::BInter => BinaryOp::Intersection,
        AssocExprOp::BComp => BinaryOp::Composition,
        AssocExprOp::FComp => BinaryOp::Semicolon,
        AssocExprOp::Ovr => BinaryOp::Overwrite,
        AssocExprOp::Plus => BinaryOp::Add,
        AssocExprOp::Mul => BinaryOp::Multiply,
    }
}

fn legacy_comparison(op: RelationalOp) -> ComparisonOp {
    match op {
        RelationalOp::Equal => ComparisonOp::Equal,
        RelationalOp::NotEqual => ComparisonOp::NotEqual,
        RelationalOp::Lt => ComparisonOp::LessThan,
        RelationalOp::Le => ComparisonOp::LessEqual,
        RelationalOp::Gt => ComparisonOp::GreaterThan,
        RelationalOp::Ge => ComparisonOp::GreaterEqual,
        RelationalOp::In => ComparisonOp::In,
        RelationalOp::NotIn => ComparisonOp::NotIn,
        // The model names the strict operator `Subset` (⊂); the legacy
        // enum uses `Subset` for ⊆.
        RelationalOp::Subset => ComparisonOp::SubsetStrict,
        RelationalOp::NotSubset => ComparisonOp::NotSubsetStrict,
        RelationalOp::SubsetEq => ComparisonOp::Subset,
        RelationalOp::NotSubsetEq => ComparisonOp::NotSubset,
    }
}

fn legacy_logical(op: AssocPredOp) -> LogicalOp {
    match op {
        AssocPredOp::LAnd => LogicalOp::And,
        AssocPredOp::LOr => LogicalOp::Or,
    }
}

fn legacy_binary_pred(op: BinaryPredOp) -> LogicalOp {
    match op {
        BinaryPredOp::LImp => LogicalOp::Implies,
        BinaryPredOp::LEqv => LogicalOp::Equivalent,
    }
}

/// The legacy binary operator a node behaves as in precedence and
/// parenthesization decisions, if any.
fn effective_binary(kind: &FExprKind) -> Option<BinaryOp> {
    match kind {
        FExprKind::Binary {
            op: BinaryExprOp::FunImage | BinaryExprOp::RelImage,
            ..
        } => None,
        FExprKind::Binary { op, .. } => Some(legacy_binary(*op)),
        FExprKind::Associative { op, .. } => Some(legacy_assoc(*op)),
        FExprKind::Ascription { .. } => Some(BinaryOp::OfType),
        _ => None,
    }
}

/// Whether a formula-model expression must be parenthesized where only
/// a pair-expression (or lower) is grammatical: lambda and the
/// quantified unions/intersections sit above that level.
fn fm_above_pair(kind: &FExprKind) -> bool {
    match kind {
        FExprKind::Quantified { op, form, .. } => match op {
            QuantExprOp::QUnion | QuantExprOp::QInter => true,
            QuantExprOp::CSet => *form == Form::Lambda,
        },
        _ => false,
    }
}

impl PrettyPrinter {
    /// Convert a formula-model expression to text.
    pub fn print_formula_expression(&self, expr: &formula::Expression) -> String {
        let mut names = Vec::new();
        self.fm_expr(expr, FormulaContext::Expression, &mut names)
    }

    /// Convert a formula-model predicate to text.
    pub fn print_formula_predicate(&self, pred: &formula::Predicate) -> String {
        let mut names = Vec::new();
        self.fm_pred(pred, FormulaContext::Predicate, &mut names)
    }

    /// The display name of a bound occurrence; an index without an
    /// enclosing declaration renders as a visible placeholder.
    fn fm_bound_name(names: &[String], index: u32) -> String {
        match names.len().checked_sub(1 + index as usize) {
            Some(i) => names[i].clone(),
            None => format!("[[{index}]]"),
        }
    }

    /// Resolves the printing names of a binding construct's
    /// declarations: the names visible in its subtree (its free
    /// identifiers plus the enclosing declarations it references) must
    /// not be captured.
    fn fm_resolve_decls(
        &self,
        decls: &[formula::BoundIdentDecl],
        free: &[String],
        dangling: &[u32],
        names: &[String],
    ) -> Vec<String> {
        let mut solver = FreshNameSolver::new(free.iter().cloned());
        for index in dangling {
            if let Some(i) = names.len().checked_sub(1 + *index as usize) {
                solver.add(names[i].clone());
            }
        }
        resolve_idents(decls, &mut solver)
    }

    /// Prints a declaration list under its resolved names, with `⦂`
    /// annotations from the solved types (in typed mode) or the source
    /// spelling. Annotations are scoped to the enclosing context.
    fn fm_decls(
        &self,
        decls: &[formula::BoundIdentDecl],
        resolved: &[String],
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        decls
            .iter()
            .zip(resolved)
            .map(|(decl, name)| self.fm_decl(decl, name, context, names))
            .collect::<Vec<_>>()
            .join(self.comma_separator())
    }

    /// Renders one declaration as `name` or `name ⦂ annotation` — the
    /// one home of the annotated-declaration spelling (declaration
    /// lists and lambda pattern leaves).
    fn fm_decl(
        &self,
        decl: &formula::BoundIdentDecl,
        name: &str,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        match self.fm_decl_annotation(decl, context, names) {
            Some(annotation) => format!("{}{}{}", name, self.oftype_annotation(), annotation),
            None => name.to_string(),
        }
    }

    fn fm_decl_annotation(
        &self,
        decl: &formula::BoundIdentDecl,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> Option<String> {
        if self.formula_spacing == FormulaSpacing::RodinFormulaString {
            return None;
        }
        if self.typed_decls {
            if let Some(ty) = decl.ty() {
                let spelled = ty.to_expression(decl.factory());
                return Some(self.fm_expr(&spelled, context, &mut Vec::new()));
            }
        }
        decl.annotation()
            .map(|annotation| self.fm_expr(annotation, context, names))
    }

    fn fm_expr(
        &self,
        expr: &formula::Expression,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let expr = self.visible_expr(expr);
        match expr.kind() {
            FExprKind::FreeIdentifier(name) => name.clone(),
            FExprKind::BoundIdentifier(index) => Self::fm_bound_name(names, *index),
            FExprKind::IntegerLiteral(value) => {
                let rendered = value.to_string();
                if self.formula_spacing == FormulaSpacing::RodinFormulaString
                    && let Some(unsigned) = rendered.strip_prefix('-')
                {
                    return format!(
                        "{}{unsigned}",
                        self.op(operators::unary_op_id(UnaryOp::Minus))
                    );
                }
                rendered
            }
            FExprKind::Atomic(op) => match op {
                AtomicOp::Integer => self.op(OperatorId::Integers).to_string(),
                AtomicOp::Natural => self.op(OperatorId::Naturals).to_string(),
                AtomicOp::Natural1 => self.op(OperatorId::Naturals1).to_string(),
                AtomicOp::Bool => "BOOL".to_string(),
                AtomicOp::True => "TRUE".to_string(),
                AtomicOp::False => "FALSE".to_string(),
                AtomicOp::EmptySet => self.op(OperatorId::EmptySet).to_string(),
                AtomicOp::KPred => "pred".to_string(),
                AtomicOp::KSucc => "succ".to_string(),
                AtomicOp::KPrj1Gen => "prj1".to_string(),
                AtomicOp::KPrj2Gen => "prj2".to_string(),
                AtomicOp::KIdGen => "id".to_string(),
            },
            FExprKind::SetExtension(members) => {
                let elems: Vec<String> = members
                    .iter()
                    .map(|m| self.fm_expr(m, context, names))
                    .collect();
                format!("{{{}}}", elems.join(self.comma_separator()))
            }
            FExprKind::Bool(pred) => {
                format!("bool({})", self.fm_pred(pred, context, names))
            }
            FExprKind::Binary {
                op: op @ (BinaryExprOp::FunImage | BinaryExprOp::RelImage),
                left,
                right,
            } => {
                let left = self.visible_expr(left);
                let mut applied = self.fm_expr(left, context, names);
                if Self::fm_parens_for_image(left.kind()) {
                    applied = format!("({applied})");
                }
                let argument = self.fm_expr(right, context, names);
                if *op == BinaryExprOp::FunImage {
                    format!("{applied}({argument})")
                } else {
                    format!("{applied}[{argument}]")
                }
            }
            FExprKind::Binary { op, left, right } => {
                let old = legacy_binary(*op);
                self.fm_binary(old, left, right, context, names)
            }
            FExprKind::Ascription { expr, type_expr } => {
                self.fm_binary(BinaryOp::OfType, expr, type_expr, context, names)
            }
            FExprKind::Associative { op, children } => {
                let old = legacy_assoc(*op);
                let op_str = self.op(operators::binary_op_id(old));
                let separator = self.binary_separator(old, context);
                let joint = format!("{separator}{op_str}{separator}");
                children
                    .iter()
                    .enumerate()
                    .map(|(i, child)| self.fm_child_expr(child, old, i > 0, context, names))
                    .collect::<Vec<_>>()
                    .join(&joint)
            }
            FExprKind::Unary { op, child } => match op {
                UnaryExprOp::KCard => self.fm_builtin("card", child, context, names),
                UnaryExprOp::KMin => self.fm_builtin("min", child, context, names),
                UnaryExprOp::KMax => self.fm_builtin("max", child, context, names),
                UnaryExprOp::KUnion => self.fm_builtin("union", child, context, names),
                UnaryExprOp::KInter => self.fm_builtin("inter", child, context, names),
                UnaryExprOp::Converse => {
                    let child = self.visible_expr(child);
                    let needs_parens = match child.kind() {
                        FExprKind::FreeIdentifier(_)
                        | FExprKind::BoundIdentifier(_)
                        | FExprKind::Atomic(_)
                        | FExprKind::IntegerLiteral(_)
                        | FExprKind::Unary {
                            op:
                                UnaryExprOp::KCard
                                | UnaryExprOp::KMin
                                | UnaryExprOp::KMax
                                | UnaryExprOp::KUnion
                                | UnaryExprOp::KInter
                                | UnaryExprOp::Converse,
                            ..
                        } => false,
                        FExprKind::Binary {
                            op: BinaryExprOp::FunImage | BinaryExprOp::RelImage,
                            ..
                        } => self.formula_spacing == FormulaSpacing::RodinFormulaString,
                        _ => true,
                    };
                    let operand = self.fm_expr(child, context, names);
                    let op_str = self.op(operators::unary_op_id(UnaryOp::Inverse));
                    if needs_parens {
                        format!("({operand}){op_str}")
                    } else {
                        format!("{operand}{op_str}")
                    }
                }
                UnaryExprOp::Pow => self.fm_prefix_unary(UnaryOp::PowerSet, child, context, names),
                UnaryExprOp::Pow1 => {
                    self.fm_prefix_unary(UnaryOp::PowerSet1, child, context, names)
                }
                UnaryExprOp::KDom => self.fm_prefix_unary(UnaryOp::Domain, child, context, names),
                UnaryExprOp::KRan => self.fm_prefix_unary(UnaryOp::Range, child, context, names),
                UnaryExprOp::UnMinus => self.fm_prefix_unary(UnaryOp::Minus, child, context, names),
            },
            FExprKind::Quantified {
                op,
                decls,
                pred,
                expr: value,
                form,
            } => {
                let resolved = self.fm_resolve_decls(
                    decls,
                    expr.free_identifiers(),
                    expr.dangling_bound_indices(),
                    names,
                );
                let mid = self.op(OperatorId::Dot);
                let bar = if self.formula_spacing == FormulaSpacing::RodinFormulaString {
                    format!(" {} ", self.op(OperatorId::Bar))
                } else {
                    self.op(OperatorId::Bar).to_string()
                };
                // The short comprehension spellings have no place to
                // carry the declarations' types, so typed printing
                // escalates them to the explicit form (the lambda
                // spelling annotates its pattern leaves instead).
                let form = if self.typed_decls && matches!(form, Form::Implicit | Form::IdentList) {
                    &Form::Explicit
                } else {
                    form
                };
                match op {
                    QuantExprOp::CSet => match form {
                        Form::Lambda => {
                            let value = self.visible_expr(value);
                            let FExprKind::Binary {
                                op: BinaryExprOp::Mapsto,
                                left: pattern,
                                right: body,
                            } = value.kind()
                            else {
                                unreachable!("lambda form implies a maplet expression")
                            };
                            let lambda = self.op(OperatorId::Lambda);
                            let pattern_str =
                                self.fm_lambda_pattern(pattern, decls, &resolved, context, names);
                            names.extend(resolved.iter().cloned());
                            let pred_str = self.fm_pred(pred, context, names);
                            let body_str = self.fm_expr(body, context, names);
                            names.truncate(names.len() - decls.len());
                            format!("{lambda} {pattern_str}{mid}{pred_str}{bar}{body_str}")
                        }
                        Form::Implicit => {
                            names.extend(resolved.iter().cloned());
                            let value_str = self.fm_expr(value, context, names);
                            let pred_str = self.fm_pred(pred, context, names);
                            names.truncate(names.len() - decls.len());
                            format!("{{{value_str}{bar}{pred_str}}}")
                        }
                        Form::IdentList => {
                            let ids = self.fm_decls(decls, &resolved, context, names);
                            names.extend(resolved.iter().cloned());
                            let pred_str = self.fm_pred(pred, context, names);
                            names.truncate(names.len() - decls.len());
                            format!("{{{ids}{bar}{pred_str}}}")
                        }
                        Form::Explicit => {
                            let ids = self.fm_decls(decls, &resolved, context, names);
                            names.extend(resolved.iter().cloned());
                            let pred_str = self.fm_pred(pred, context, names);
                            let value_str = self.fm_expr(value, context, names);
                            names.truncate(names.len() - decls.len());
                            format!("{{{ids}{mid}{pred_str}{bar}{value_str}}}")
                        }
                    },
                    QuantExprOp::QUnion | QuantExprOp::QInter => {
                        // Only the explicit spelling exists in the
                        // grammar for these.
                        let keyword = self.op(match op {
                            QuantExprOp::QUnion => OperatorId::QuantifiedUnion,
                            QuantExprOp::QInter => OperatorId::QuantifiedIntersection,
                            QuantExprOp::CSet => unreachable!(),
                        });
                        let ids = self.fm_decls(decls, &resolved, context, names);
                        names.extend(resolved.iter().cloned());
                        let pred_str = self.fm_pred(pred, context, names);
                        let value_str = self.fm_expr(value, context, names);
                        names.truncate(names.len() - decls.len());
                        format!("{keyword} {ids}{mid}{pred_str}{bar}{value_str}")
                    }
                }
            }
            FExprKind::Extended { tag, exprs, preds } => {
                self.fm_extended(expr.factory(), *tag, exprs, preds, context, names)
            }
        }
    }

    fn fm_builtin(
        &self,
        name: &str,
        child: &formula::Expression,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        format!("{}({})", name, self.fm_expr(child, context, names))
    }

    /// The expression visible in formula-string mode, where source type
    /// ascriptions are presentation-only.
    fn visible_expr<'a>(&self, mut expr: &'a formula::Expression) -> &'a formula::Expression {
        if self.formula_spacing == FormulaSpacing::RodinFormulaString {
            while let FExprKind::Ascription { expr: inner, .. } = expr.kind() {
                expr = inner;
            }
        }
        expr
    }

    fn fm_prefix_unary(
        &self,
        op: UnaryOp,
        child: &formula::Expression,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        format!(
            "{}({})",
            self.op(operators::unary_op_id(op)),
            self.fm_expr(child, context, names)
        )
    }

    fn fm_binary(
        &self,
        old: BinaryOp,
        left: &formula::Expression,
        right: &formula::Expression,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let op_str = self.op(operators::binary_op_id(old));
        let separator = self.binary_separator(old, context);
        let left_str = self.fm_child_expr(left, old, false, context, names);
        let right_str = self.fm_child_expr(right, old, true, context, names);
        format!("{left_str}{separator}{op_str}{separator}{right_str}")
    }

    /// Mirror of the legacy child-parenthesization rules.
    fn fm_child_expr(
        &self,
        child: &formula::Expression,
        parent_op: BinaryOp,
        is_right: bool,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let child = self.visible_expr(child);
        if fm_above_pair(child.kind()) {
            return format!("({})", self.fm_expr(child, context, names));
        }
        if let Some(child_op) = effective_binary(child.kind()) {
            let child_prec = op_info::binary_precedence(child_op);
            let parent_prec = op_info::binary_precedence(parent_op);
            let needs_parens = if child_prec < parent_prec {
                true
            } else if child_prec > parent_prec {
                false
            } else {
                if self.formula_spacing == FormulaSpacing::RodinFormulaString
                    && !is_right
                    && child_op == BinaryOp::DomainRestriction
                    && parent_op == BinaryOp::RangeRestriction
                {
                    false
                } else {
                    !op_info::binary_ops_compatible(child_op, parent_op)
                        || op_info::is_non_associative(parent_op)
                        || is_right
                }
            };
            if needs_parens {
                return format!("({})", self.fm_expr(child, context, names));
            }
        }
        self.fm_expr(child, context, names)
    }

    /// Mirror of the relational-image / application head rule: binary
    /// and prefix-unary operands bind looser than `f(x)` / `r[S]`.
    fn fm_parens_for_image(kind: &FExprKind) -> bool {
        match kind {
            FExprKind::Unary {
                op: UnaryExprOp::Converse,
                ..
            } => false,
            FExprKind::Unary {
                op:
                    UnaryExprOp::KCard
                    | UnaryExprOp::KMin
                    | UnaryExprOp::KMax
                    | UnaryExprOp::KUnion
                    | UnaryExprOp::KInter,
                ..
            } => false,
            FExprKind::Binary {
                op: BinaryExprOp::FunImage | BinaryExprOp::RelImage,
                ..
            } => false,
            FExprKind::Binary { .. }
            | FExprKind::Associative { .. }
            | FExprKind::Ascription { .. }
            | FExprKind::Unary { .. } => true,
            // The binder forms follow the pair-level rule.
            kind @ FExprKind::Quantified { .. } => fm_above_pair(kind),
            _ => false,
        }
    }

    /// Print an expression where only a pair-expression is grammatical.
    fn fm_pair(
        &self,
        expr: &formula::Expression,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let expr = self.visible_expr(expr);
        if fm_above_pair(expr.kind()) {
            format!("({})", self.fm_expr(expr, context, names))
        } else {
            self.fm_expr(expr, context, names)
        }
    }

    /// Renders a lambda pattern from its maplet tree: leaves are the
    /// construct's own declarations.
    fn fm_lambda_pattern(
        &self,
        pattern: &formula::Expression,
        decls: &[formula::BoundIdentDecl],
        resolved: &[String],
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let pattern = self.visible_expr(pattern);
        match pattern.kind() {
            FExprKind::BoundIdentifier(index) => {
                let position = decls.len() - 1 - *index as usize;
                self.fm_decl(&decls[position], &resolved[position], context, names)
            }
            FExprKind::Binary {
                op: BinaryExprOp::Mapsto,
                left,
                right,
            } => {
                let maplet = self.op(OperatorId::Maplet);
                let left_str = self.fm_lambda_pattern(left, decls, resolved, context, names);
                let right = self.visible_expr(right);
                let right_str = match right.kind() {
                    FExprKind::Binary {
                        op: BinaryExprOp::Mapsto,
                        ..
                    } => format!(
                        "({})",
                        self.fm_lambda_pattern(right, decls, resolved, context, names)
                    ),
                    _ => self.fm_lambda_pattern(right, decls, resolved, context, names),
                };
                format!("{left_str} {maplet} {right_str}")
            }
            _ => unreachable!("lambda patterns are maplet trees over declarations"),
        }
    }

    fn fm_pred(
        &self,
        pred: &formula::Predicate,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        match pred.kind() {
            FPredKind::Literal(op) => match op {
                LiteralPredOp::BTrue => self.sym("⊤", "true").to_string(),
                LiteralPredOp::BFalse => self.sym("⊥", "false").to_string(),
            },
            FPredKind::PredicateVariable(name) => name.clone(),
            FPredKind::Relational { op, left, right } => {
                let old = legacy_comparison(*op);
                let op_str = self.op(operators::comparison_op_id(old));
                let separator = self.tight_operator_separator(operators::comparison_op_id(old));
                let left_str = self.fm_pair(left, context, names);
                let right_str = self.fm_pair(right, context, names);
                format!("{left_str}{separator}{op_str}{separator}{right_str}")
            }
            FPredKind::Not(child) => {
                let not = self.op(OperatorId::Not);
                let rendered = self.fm_pred(child, context, names);
                if self.formula_spacing == FormulaSpacing::RodinFormulaString
                    && !matches!(
                        child.kind(),
                        FPredKind::Binary { .. }
                            | FPredKind::Associative { .. }
                            | FPredKind::Quantified { .. }
                    )
                {
                    format!("{not}{rendered}")
                } else {
                    format!("{not}({rendered})")
                }
            }
            FPredKind::Binary { op, left, right } => {
                let old = legacy_binary_pred(*op);
                let op_str = self.op(operators::logical_op_id(old));
                let separator = self.tight_operator_separator(operators::logical_op_id(old));
                let left_str = self.fm_pred_child(left, old, false, context, names);
                let right_str = self.fm_pred_child(right, old, true, context, names);
                format!("{left_str}{separator}{op_str}{separator}{right_str}")
            }
            FPredKind::Associative { op, children } => {
                let old = legacy_logical(*op);
                let op_str = self.op(operators::logical_op_id(old));
                let separator = self.tight_operator_separator(operators::logical_op_id(old));
                let joint = format!("{separator}{op_str}{separator}");
                children
                    .iter()
                    .enumerate()
                    .map(|(i, child)| self.fm_pred_child(child, old, i > 0, context, names))
                    .collect::<Vec<_>>()
                    .join(&joint)
            }
            FPredKind::Quantified {
                op,
                decls,
                pred: body,
            } => {
                let resolved = self.fm_resolve_decls(
                    decls,
                    pred.free_identifiers(),
                    pred.dangling_bound_indices(),
                    names,
                );
                let quantifier = self.op(match op {
                    QuantPredOp::Forall => operators::quantifier_id(Quantifier::ForAll),
                    QuantPredOp::Exists => operators::quantifier_id(Quantifier::Exists),
                });
                let mid = self.op(OperatorId::Dot);
                let ids = self.fm_decls(decls, &resolved, context, names);
                names.extend(resolved.iter().cloned());
                let body_str = self.fm_pred(body, context, names);
                names.truncate(names.len() - decls.len());
                format!("{quantifier}{ids}{mid}{body_str}")
            }
            FPredKind::Simple(child) => {
                format!("finite({})", self.fm_expr(child, context, names))
            }
            FPredKind::Multiple(children) => {
                let args: Vec<String> = children
                    .iter()
                    .map(|c| self.fm_expr(c, context, names))
                    .collect();
                format!("partition({})", args.join(self.comma_separator()))
            }
            FPredKind::Application { function, args, .. } => {
                let rendered: Vec<String> = args
                    .iter()
                    .map(|a| self.fm_expr(a, context, names))
                    .collect();
                format!("{}({})", function, rendered.join(self.comma_separator()))
            }
            FPredKind::Extended { tag, exprs, preds } => {
                self.fm_extended(pred.factory(), *tag, exprs, preds, context, names)
            }
        }
    }

    /// Mirror of the legacy logical-connective parenthesization rules.
    fn fm_pred_child(
        &self,
        child: &formula::Predicate,
        parent_op: LogicalOp,
        is_right: bool,
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let child_op = match child.kind() {
            FPredKind::Quantified { .. } => {
                return format!("({})", self.fm_pred(child, context, names));
            }
            FPredKind::Associative { op, .. } => Some(legacy_logical(*op)),
            FPredKind::Binary { op, .. } => Some(legacy_binary_pred(*op)),
            _ => None,
        };
        let needs_parens = match child_op {
            Some(child_op) => {
                let child_prec = op_info::logical_precedence(child_op);
                let parent_prec = op_info::logical_precedence(parent_op);
                if child_prec < parent_prec {
                    true
                } else if child_prec > parent_prec {
                    false
                } else {
                    let child_class = op_info::logical_compat_class(child_op);
                    let parent_class = op_info::logical_compat_class(parent_op);
                    if child_class == 0 || parent_class == 0 || child_class != parent_class {
                        true
                    } else {
                        is_right
                    }
                }
            }
            None => false,
        };
        if needs_parens {
            format!("({})", self.fm_pred(child, context, names))
        } else {
            self.fm_pred(child, context, names)
        }
    }

    fn fm_extended(
        &self,
        factory: &formula::FormulaFactory,
        tag: crate::formula::tag::Tag,
        exprs: &[formula::Expression],
        preds: &[formula::Predicate],
        context: FormulaContext,
        names: &mut Vec<String>,
    ) -> String {
        let symbol = factory
            .extension(tag)
            .map(|ext| ext.common().symbol().to_string())
            .unwrap_or_else(|| format!("[[ext:{tag}]]"));
        let mut args: Vec<String> = exprs
            .iter()
            .map(|e| self.fm_expr(e, context, names))
            .collect();
        args.extend(preds.iter().map(|p| self.fm_pred(p, context, names)));
        if args.is_empty() {
            symbol
        } else {
            format!("{}({})", symbol, args.join(self.comma_separator()))
        }
    }

    /// Convert a formula-model assignment to text.
    pub fn print_formula_assignment(&self, assign: &formula::Assignment) -> String {
        use formula::AssignmentKind as K;
        let context = FormulaContext::Action;
        let mut names = Vec::new();
        let targets = |idents: &[formula::Expression]| -> String {
            idents
                .iter()
                .map(|ident| match ident.kind() {
                    FExprKind::FreeIdentifier(name) => name.clone(),
                    _ => unreachable!("assignment targets are free identifiers"),
                })
                .collect::<Vec<_>>()
                .join(self.comma_separator())
        };
        match assign.kind() {
            K::BecomesEqualTo { idents, values } => {
                let rendered: Vec<String> = values
                    .iter()
                    .map(|value| Self::guard_action_part(self.fm_expr(value, context, &mut names)))
                    .collect();
                format!(
                    "{} {} {}",
                    targets(idents),
                    self.op(OperatorId::Assignment),
                    rendered.join(self.comma_separator())
                )
            }
            K::BecomesMemberOf { idents, set } => {
                format!(
                    "{} {} {}",
                    targets(idents),
                    self.op(OperatorId::BecomesIn),
                    Self::guard_action_part(self.fm_expr(set, context, &mut names))
                )
            }
            K::BecomesSuchThat {
                idents,
                primed,
                pred,
            } => {
                let resolved = self.fm_resolve_decls(
                    primed,
                    assign.free_identifiers(),
                    assign.dangling_bound_indices(),
                    &names,
                );
                names.extend(resolved);
                let condition = Self::guard_action_part(self.fm_pred(pred, context, &mut names));
                format!(
                    "{} {} {}",
                    targets(idents),
                    self.op(OperatorId::BecomesSuchThat),
                    condition
                )
            }
        }
    }
}

/// Convenience function to convert a Component to text with default settings
pub fn to_string(component: &Component) -> String {
    PrettyPrinter::new().print_component(component)
}

/// Convenience function to convert a Component to ASCII text
pub fn to_string_ascii(component: &Component) -> String {
    PrettyPrinter::ascii().print_component(component)
}

/// Convenience function to convert multiple Components to text with default settings
pub fn components_to_string(components: &[Component]) -> String {
    PrettyPrinter::new().print_components(components)
}

/// Convenience function to convert multiple Components to ASCII text
pub fn components_to_string_ascii(components: &[Component]) -> String {
    PrettyPrinter::ascii().print_components(components)
}

/// Parse Event-B text (one or more components) and re-emit it formatted with
/// `printer`.
///
/// This is the shared parse-then-print entry point: `rossi fmt` and the language
/// server both format through it, and `rossi import` prints through the same
/// [`PrettyPrinter`], so command-line and editor formatting always agree.
///
/// # Errors
///
/// Returns a [`ParseError`](crate::ParseError) if `src` is not valid Event-B.
pub fn format_str(src: &str, printer: &PrettyPrinter) -> Result<String, crate::error::ParseError> {
    let components = crate::parser::parse_components(src)?;
    Ok(printer.print_components(&components))
}
