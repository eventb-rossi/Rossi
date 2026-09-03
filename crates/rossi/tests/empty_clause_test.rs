//! A clause header with nothing under it, a label with nothing after it, and
//! an item with no label at all are reported where the mistake is — at the
//! keyword, at the label, or at the item — rather than at whatever token the
//! parser reached next.

use rossi::{ParseError, parse};

/// Parse `source`, expecting it to fail, and return the error.
fn error_of(source: &str) -> ParseError {
    parse(source).expect_err("must fail")
}

/// A machine whose event body is `body`, indented under `EVENT e`.
fn machine_with_event_body(body: &str) -> String {
    format!("MACHINE m\nVARIABLES\n    x\nEVENTS\n    EVENT e\n{body}    END\nEND\n")
}

#[test]
fn empty_event_clause_is_reported_at_its_keyword() {
    for (body, clause, line, column) in [
        ("    WHERE\n    THEN\n        @act1 x ≔ 1\n", "WHERE", 6, 5),
        ("    WHEN\n    THEN\n        @act1 x ≔ 1\n", "WHERE", 6, 5),
        (
            "    WHERE\n        @grd1 x > 0\n    WITH\n    THEN\n        @act1 x ≔ 1\n",
            "WITH",
            8,
            5,
        ),
        (
            "    WHERE\n        @grd1 x > 0\n    WITNESS\n    THEN\n        @act1 x ≔ 1\n",
            "WITNESS",
            8,
            5,
        ),
        ("    THEN\n", "THEN", 6, 5),
        ("    BEGIN\n", "THEN", 6, 5),
    ] {
        let source = machine_with_event_body(body);
        let error = error_of(&source);
        let ParseError::EmptyClause {
            clause: reported, ..
        } = &error
        else {
            panic!("expected an EmptyClause for {clause}, got: {error:?}");
        };
        assert_eq!(reported, clause, "in:\n{source}");
        assert_eq!(error.position(), Some((line, column)), "in:\n{source}");
        assert_eq!(
            error.to_string(),
            format!("`{clause}` clause is empty"),
            "in:\n{source}"
        );
    }
}

#[test]
fn empty_initialisation_then_is_reported_at_its_keyword() {
    let source =
        "MACHINE m\nVARIABLES\n    x\nEVENTS\n    EVENT INITIALISATION\n    THEN\n    END\nEND\n";
    let error = error_of(source);
    let ParseError::EmptyClause { clause, .. } = &error else {
        panic!("expected an EmptyClause, got: {error:?}");
    };
    assert_eq!(clause, "THEN");
    assert_eq!(error.position(), Some((6, 5)));
}

#[test]
fn empty_machine_and_context_predicate_clauses_are_reported_at_their_keyword() {
    for (source, clause, line) in [
        (
            "MACHINE m\nVARIABLES\n    x\nINVARIANTS\nEVENTS\n    EVENT e\n    THEN\n        @act1 x ≔ 1\n    END\nEND\n",
            "INVARIANTS",
            4,
        ),
        (
            "MACHINE m\nVARIABLES\n    x\nTHEOREMS\nEND\n",
            "THEOREMS",
            4,
        ),
        ("CONTEXT c\nSETS\n    S\nAXIOMS\nEND\n", "AXIOMS", 4),
        ("CONTEXT c\nSETS\n    S\nTHEOREMS\nEND\n", "THEOREMS", 4),
    ] {
        let error = error_of(source);
        let ParseError::EmptyClause {
            clause: reported, ..
        } = &error
        else {
            panic!("expected an EmptyClause for {clause}, got: {error:?}");
        };
        assert_eq!(reported, clause, "in:\n{source}");
        assert_eq!(error.position(), Some((line, 1)), "in:\n{source}");
    }
}

/// A clause whose items are bare names keeps parsing exactly as before, even
/// when empty: its first item may legitimately spell a structural keyword, and
/// rossi reports that as a warning (rule EB028), not a parse error.
#[test]
fn a_name_that_spells_a_keyword_is_still_a_name() {
    for source in [
        "CONTEXT c\nSETS\n    end\nAXIOMS\n    @axm1 1 = 1\nEND\n",
        "MACHINE m\nVARIABLES\n    events\nINVARIANTS\n    @inv1 events > 0\nEND\n",
        "MACHINE m\nVARIABLES\n    x\nEVENTS\n    EVENT e\n    ANY\n        then\n    WHERE\n        @grd1 then > 0\n    THEN\n        @act1 x ≔ then\n    END\nEND\n",
    ] {
        parse(source).unwrap_or_else(|e| panic!("must still parse: {e}\nsource:\n{source}"));
    }
}

#[test]
fn a_label_with_no_formula_is_reported_at_the_label() {
    for (source, label, expected, line, column) in [
        (
            "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1\nEND\n",
            "@inv1",
            "a predicate",
            5,
            5,
        ),
        (
            "CONTEXT c\nSETS\n    S\nAXIOMS\n    @axm1\nEND\n",
            "@axm1",
            "a predicate",
            5,
            5,
        ),
        (
            &machine_with_event_body("    WHERE\n        @grd1\n    THEN\n        @act1 x ≔ 1\n"),
            "@grd1",
            "a predicate",
            7,
            9,
        ),
        (
            &machine_with_event_body("    THEN\n        @act1\n"),
            "@act1",
            "an action",
            7,
            9,
        ),
    ] {
        let error = error_of(source);
        let ParseError::MissingFormula {
            label: reported,
            expected: reported_expected,
            ..
        } = &error
        else {
            panic!("expected a MissingFormula for {label}, got: {error:?}");
        };
        assert_eq!(
            (reported.as_str(), *reported_expected),
            (label, expected),
            "in:\n{source}"
        );
        assert_eq!(error.position(), Some((line, column)), "in:\n{source}");
    }
}

#[test]
fn an_item_with_no_label_is_reported_at_the_item() {
    // Rodin's textual grammar makes the label mandatory everywhere an item
    // carries one, and its static checker reports a missing one as an error.
    // The item, not the clause keyword, is where the label has to be written.
    for (source, expected, line, column) in [
        (
            "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    x ∈ ℕ\nEND\n",
            "a predicate",
            5,
            5,
        ),
        (
            "CONTEXT c\nCONSTANTS\n    c\nAXIOMS\n    c = 1\n    c = 2\nEND\n",
            "a predicate",
            5,
            5,
        ),
        (
            "CONTEXT c\nCONSTANTS\n    c\nTHEOREMS\n    c = 1\nEND\n",
            "a predicate",
            5,
            5,
        ),
        (
            &machine_with_event_body("    WHERE\n        x > 0\n    THEN\n        @act1 x ≔ 1\n"),
            "a predicate",
            7,
            9,
        ),
        (
            &machine_with_event_body(
                "    WHERE\n        @grd1 x > 0\n    WITH\n        y = 1\n    THEN\n        @act1 x ≔ 1\n",
            ),
            "a predicate",
            9,
            9,
        ),
        (
            &machine_with_event_body("    THEN\n        x ≔ 1\n"),
            "an action",
            7,
            9,
        ),
        (
            &machine_with_event_body("    THEN\n        @act1 x ≔ 1\n        x ≔ 2\n"),
            "an action",
            8,
            9,
        ),
    ] {
        let error = error_of(source);
        let ParseError::MissingLabel {
            expected: reported, ..
        } = &error
        else {
            panic!("expected a MissingLabel, got: {error:?}\nin:\n{source}");
        };
        assert_eq!(*reported, expected, "in:\n{source}");
        assert_eq!(error.position(), Some((line, column)), "in:\n{source}");
    }
}

#[test]
fn an_unlabeled_item_no_longer_swallows_the_next_clause_keyword() {
    // An unlabeled predicate may open with a keyword-permissive identifier, so
    // `WITNESS (p) = 0` used to be read as the guard `witness(p) = 0` and the
    // WITNESS clause vanished without a word. Requiring the label turns that
    // silent loss into an error on the item.
    let source = machine_with_event_body(
        "    ANY\n        p\n    WHERE\n        @grd1 x > 0\n    WITNESS\n        (p) = 0\n    THEN\n        @act1 x ≔ 1\n",
    );
    let error = error_of(&source);
    assert!(
        matches!(error, ParseError::MissingLabel { .. }),
        "expected a MissingLabel, got: {error:?}"
    );
}

#[test]
fn the_first_variant_still_needs_no_label() {
    // Rodin's own `IVariant` reads a missing label as its default (`vrn`), so
    // the first variant is the one item the text grammar leaves unlabeled.
    parse("MACHINE m\nVARIABLES\n    x\nVARIANT\n    x\nEND\n").expect("must parse");
}

#[test]
fn the_error_productions_never_leak_into_an_expected_list() {
    // The markers are zero-width rules that exist only to locate a mistake;
    // pest must never offer one as something the user could type.
    for source in [
        machine_with_event_body("    WHERE\n        @grd1 x >\n    THEN\n        @act1 x ≔ 1\n"),
        machine_with_event_body("    THEN\n        @act1 x ≔\n"),
        "MACHINE m\nVARIABLES\n    x\nINVARIANTS\n    @inv1 x >\nEND\n".to_string(),
        "MACHINE m\nVARIABLES\n    x >\nEND\n".to_string(),
        // A label followed by something that is neither a predicate nor the
        // end of the clause: the marker competes with the real production and
        // must not surface next to it.
        machine_with_event_body("    WHERE\n        @grd1 ≔ 3\n    THEN\n        @act1 x ≔ 1\n"),
        machine_with_event_body("    THEN\n        @act1 ≔ 3\n"),
    ] {
        let error = error_of(&source);
        let message = error.to_string();
        for marker in ["empty_", "missing_", "misplaced_"] {
            assert!(
                !message.contains(marker),
                "an error production leaked into: {message}\nfor source:\n{source}"
            );
        }
    }
}

#[test]
fn an_event_clause_written_out_of_order_names_both_clauses() {
    for (body, clause, before, line) in [
        (
            "    THEN\n        @act1 x ≔ 1\n    WITH\n        @w y = 1\n",
            "WITH",
            "THEN",
            8,
        ),
        (
            "    WITNESS\n        @w y = 1\n    ANY\n        p\n    THEN\n        @act1 x ≔ 1\n",
            "ANY",
            "WITNESS",
            8,
        ),
        (
            "    THEN\n        @act1 x ≔ 1\n    WHERE\n        @grd1 x > 0\n",
            "WHERE",
            "THEN",
            8,
        ),
    ] {
        let source = machine_with_event_body(body);
        let error = error_of(&source);
        let ParseError::ClauseOutOfOrder {
            clause: reported,
            before: reported_before,
            ..
        } = &error
        else {
            panic!("expected a ClauseOutOfOrder for {clause}, got: {error:?}");
        };
        assert_eq!(
            (reported.as_str(), reported_before.as_str()),
            (clause, before),
            "in:\n{source}"
        );
        assert_eq!(error.position(), Some((line, 5)), "in:\n{source}");
    }
}

#[test]
fn a_repeated_event_clause_is_reported_as_a_duplicate() {
    let source = machine_with_event_body(
        "    WHERE\n        @grd1 x > 0\n    THEN\n        @act1 x ≔ 1\n    WHERE\n        @grd2 x > 1\n",
    );
    let error = error_of(&source);
    let ParseError::ClauseError {
        clause_type,
        line,
        message,
        ..
    } = &error
    else {
        panic!("expected a ClauseError, got: {error:?}");
    };
    assert_eq!((clause_type.as_str(), *line), ("WHERE", 10));
    assert_eq!(message, "Duplicate WHERE clause");
}
