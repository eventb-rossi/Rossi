//! Context proof obligations: axiom well-definedness, theorems, and
//! the EXTENDS hypothesis closure.

mod common;
use common::{generate, xml};

#[test]
fn axiom_wd_and_theorem_obligations() {
    let context = xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_n" org.eventb.core.identifier="n"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="n ∈ ℤ"/>
<org.eventb.core.axiom name="_a2" org.eventb.core.label="axm2" org.eventb.core.predicate="10 ÷ n &gt; 0"/>
<org.eventb.core.axiom name="_t1" org.eventb.core.label="thm1" org.eventb.core.predicate="n + 1 &gt; n" org.eventb.core.theorem="true"/>
</org.eventb.core.contextFile>"#,
    );
    let files = generate("prj", vec![context]);
    assert_eq!(files.len(), 2);
    assert_eq!(files[0].filename, "C.bpo");
    assert_eq!(files[1].filename, "C.bps");
    let contents = &files[0].contents;

    // axm1 is a typing axiom: no obligations. axm2 needs its divisor
    // guarded; the WD obligation hypothesizes exactly the axioms before
    // it — the cut point named after axm1's checked internal name.
    for needle in [
        r#"<org.eventb.core.poSequent name="axm2/WD" org.eventb.core.accurate="true" org.eventb.core.poDesc="Well-definedness of Axiom" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYP'"/>"#,
        r#"org.eventb.core.predicate="n≠0" org.eventb.core.source="/prj/C.buc|org.eventb.core.contextFile#C|org.eventb.core.axiom#_a2""#,
        // thm1 restates its own claim, hypothesizing axm1 and axm2.
        r#"<org.eventb.core.poSequent name="thm1/THM" org.eventb.core.accurate="true" org.eventb.core.poDesc="Theorem" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poPredicateSet name="SEQHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYP("/>"#,
        r#"org.eventb.core.predicate="n+1&gt;n""#,
        // ABSHYP holds the constant; the chain materializes only the
        // requested cuts and finishes at ALLHYP with global numbering.
        r#"<org.eventb.core.poPredicateSet name="ABSHYP" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poIdentifier name="n" org.eventb.core.type="ℤ"/>"#,
        r#"<org.eventb.core.poPredicateSet name="HYP'" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#ABSHYP" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poPredicateSet name="HYP(" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYP'" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poPredicateSet name="ALLHYP" org.eventb.core.parentSet="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYP(" org.eventb.core.poStamp="0">"#,
        r#"<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="n∈ℤ""#,
        r#"<org.eventb.core.poPredicate name="PRD1" org.eventb.core.predicate="10 ÷ n&gt;0""#,
        r#"<org.eventb.core.poPredicate name="PRD2" org.eventb.core.predicate="n+1&gt;n""#,
        // The interval hint selects the chain from the cut point up to
        // (excluding) the root.
        r#"org.eventb.core.poSelHintFst="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#ABSHYP" org.eventb.core.poSelHintSnd="/prj/C.bpo|org.eventb.core.poFile#C|org.eventb.core.poPredicateSet#HYP'"/>"#,
    ] {
        assert!(
            contents.contains(needle),
            "missing {needle} in:\n{contents}"
        );
    }

    // No WD obligation for the typing axiom or the total theorem.
    assert!(!contents.contains(r#"name="axm1/WD""#));
    assert!(!contents.contains(r#"name="thm1/WD""#));
}

#[test]
fn theorem_wd_uses_the_theorem_nature() {
    let context = xml(
        "C.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.constant name="_n" org.eventb.core.identifier="n"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="n ∈ ℤ"/>
<org.eventb.core.axiom name="_t1" org.eventb.core.label="thm1" org.eventb.core.predicate="10 ÷ n &gt; 0" org.eventb.core.theorem="true"/>
</org.eventb.core.contextFile>"#,
    );
    let files = generate("prj", vec![context]);
    let contents = &files[0].contents;
    assert!(contents.contains(
        r#"<org.eventb.core.poSequent name="thm1/WD" org.eventb.core.accurate="true" org.eventb.core.poDesc="Well-definedness of Theorem" org.eventb.core.poStamp="0">"#
    ));
    assert!(contents.contains(r#"name="thm1/THM""#));
}

#[test]
fn extends_closure_lands_in_abshyp() {
    let abstract_context = xml(
        "A.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.carrierSet name="_s" org.eventb.core.identifier="S"/>
<org.eventb.core.constant name="_k" org.eventb.core.identifier="k"/>
<org.eventb.core.axiom name="_a1" org.eventb.core.label="axm1" org.eventb.core.predicate="k ∈ S"/>
</org.eventb.core.contextFile>"#,
    );
    let concrete = xml(
        "B.buc",
        r#"<?xml version="1.0"?>
<org.eventb.core.contextFile version="3" org.eventb.core.configuration="org.eventb.core.fwd">
<org.eventb.core.extendsContext name="_x" org.eventb.core.target="A"/>
<org.eventb.core.constant name="_m" org.eventb.core.identifier="m"/>
<org.eventb.core.axiom name="_b1" org.eventb.core.label="axm1" org.eventb.core.predicate="m ∈ ℤ"/>
<org.eventb.core.axiom name="_b2" org.eventb.core.label="axm2" org.eventb.core.predicate="10 ÷ m &gt; 0"/>
</org.eventb.core.contextFile>"#,
    );
    let files = generate("prj", vec![abstract_context, concrete]);
    let b = files.iter().find(|f| f.filename == "B.bpo").unwrap();

    for needle in [
        // Abstract identifiers and axiom, then B's own constant, all in
        // ABSHYP; the axiom row's generated name continues from the
        // longest identifier observed (S, k → the fresh name "l").
        r#"<org.eventb.core.poIdentifier name="S" org.eventb.core.type="ℙ(S)"/>"#,
        r#"<org.eventb.core.poIdentifier name="k" org.eventb.core.type="S"/>"#,
        r#"<org.eventb.core.poPredicate name="l" org.eventb.core.predicate="k∈S" org.eventb.core.source="/prj/A.buc|org.eventb.core.contextFile#A|org.eventb.core.axiom#_a1"/>"#,
        r#"<org.eventb.core.poIdentifier name="m" org.eventb.core.type="ℤ"/>"#,
        // B's own WD obligation cuts after its first axiom.
        r#"<org.eventb.core.poSequent name="axm2/WD""#,
    ] {
        assert!(
            b.contents.contains(needle),
            "missing {needle} in:\n{}",
            b.contents
        );
    }

    // The abstract context's own PO file has no obligations, only the
    // hypothesis chain.
    let a = files.iter().find(|f| f.filename == "A.bpo").unwrap();
    assert!(!a.contents.contains("poSequent"));
    assert!(
        a.contents.contains(
            r#"<org.eventb.core.poPredicate name="PRD0" org.eventb.core.predicate="k∈S""#
        )
    );
}
