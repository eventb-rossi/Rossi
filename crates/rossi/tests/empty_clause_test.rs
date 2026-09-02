//! A clause header with nothing under it, and a label with nothing after it,
//! are reported where the mistake is — at the keyword or the label — rather
//! than at whatever token the parser reached next.

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
