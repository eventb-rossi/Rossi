//! Lexical comment scanning shared by the recovery parser and the LSP.
//!
//! The strict pest grammar consumes comments silently, but every consumer
//! that scans raw source text (error recovery, semantic token placement)
//! must not mistake comment content for code — e.g. the colon in
//! `@axm1 1 = 1 // note: positive` must never act as a label separator
//! (issue #24). Camille and CamilleX avoid this class of bug by lexing
//! comments before any structural decision; this module is the equivalent
//! tokenization step for rossi's string-scanning paths.

use crate::ast::Span;

/// Comment and label byte spans of `source`, from a single lexical scan.
///
/// Each vector is sorted and disjoint by construction, and labels never
/// overlap comments. This struct is the one encoding of "which bytes are
/// opaque tokens": keyword and identifier scans consult it instead of
/// re-deriving label or comment extents themselves.
pub struct LexicalSpans {
    /// Every `//...` and `/*...*/` comment. A line comment ends before the
    /// terminating newline (unlike the grammar's `COMMENT` rule, which may
    /// consume it) so that masking preserves line structure. An unterminated
    /// block comment extends to the end of input.
    pub comments: Vec<Span>,
    /// Every `@`-label, `@` included. The grammar's compound-atomic `label`
    /// rule makes everything from `@` to the next whitespace opaque label
    /// text, so a keyword spelled inside a label (`@safety-END`) is not
    /// structural.
    pub labels: Vec<Span>,
    /// Every component and event name: the words in the grammar's
    /// `component_name` positions. Name text, not code — a name joins its
    /// segments with `-`, which is not subtraction, and `-` is not a word
    /// character, so a segment between two hyphens (`CTX-INT-1`, `A-or-B`)
    /// is word-bounded and an operator scan would rewrite it.
    pub names: Vec<Span>,
}

impl LexicalSpans {
    /// Position-preserving copy of `source` with every comment byte replaced
    /// by a space.
    ///
    /// Newlines (and carriage returns) inside comments are kept, so the
    /// result has the same byte length and the same line layout as the
    /// input: any byte offset or (line, column) position computed on the
    /// masked text is valid in the original.
    pub fn mask_comments(&self, source: &str) -> String {
        mask_spans(source, &self.comments)
    }

    /// Position-preserving copy of `source` with every comment **and label**
    /// byte replaced by a space: the code-only view for operator scans, in
    /// which a label's `-` or `.` is name text rather than an operator. Same
    /// byte-length and line-layout guarantees as [`Self::mask_comments`].
    pub fn mask_opaque(&self, source: &str) -> String {
        mask_spans(source, &self.opaque_spans())
    }

    /// Position-preserving copy of `source` with every comment **char**
    /// replaced by a space.
    ///
    /// Unlike [`LexicalSpans::mask_comments`] (one space per *byte*, for
    /// byte-offset consumers like the recovery parser and semantic tokens),
    /// this keeps the char count of every line: a multi-byte char inside a
    /// comment becomes a single space, so (line, char-column) positions
    /// computed on the masked text are valid in the original. This is the
    /// mask for the LSP's char-column line scanners.
    pub fn mask_comments_chars(&self, source: &str) -> String {
        let mut out = String::with_capacity(source.len());
        let mut spans = self.comments.iter().peekable();
        for (i, c) in source.char_indices() {
            while spans.next_if(|s| s.end <= i).is_some() {}
            let in_comment = spans.peek().is_some_and(|s| s.contains(i));
            if in_comment && c != '\n' && c != '\r' {
                out.push(' ');
            } else {
                out.push(c);
            }
        }
        out
    }

    /// The comment, label and name spans merged into one sorted, disjoint
    /// list: every byte a code rewrite must copy through untouched.
    fn opaque_spans(&self) -> Vec<Span> {
        let mut spans: Vec<Span> = self
            .comments
            .iter()
            .chain(&self.labels)
            .chain(&self.names)
            .copied()
            .collect();
        spans.sort_by_key(|s| s.start);
        spans
    }
}

/// Position-preserving copy of `source` with every byte of `spans` replaced
/// by a space, newlines (and carriage returns) kept, so byte offsets and line
/// layout computed on the result are valid in the original.
fn mask_spans(source: &str, spans: &[Span]) -> String {
    let mut bytes = source.as_bytes().to_vec();
    for span in spans {
        for b in &mut bytes[span.start..span.end] {
            if *b != b'\n' && *b != b'\r' {
                *b = b' ';
            }
        }
    }
    // Comment delimiters and the whitespace ending a label are ASCII, so
    // spans cover whole UTF-8 sequences and blanking them cannot split a
    // multi-byte character.
    String::from_utf8(bytes).expect("masking spans preserves UTF-8 validity")
}

/// Lexically scan `source` for comments and labels.
///
/// Comment markers inside labels are ignored, matching the grammar: the
/// compound-atomic `label` rule consumes any non-whitespace after `@`
/// (Rodin-imported labels like `@SAF5"` or `@inv//1` are plain label text).
pub fn lexical_spans(source: &str) -> LexicalSpans {
    let bytes = source.as_bytes();
    let mut comments = Vec::new();
    let mut labels = Vec::new();
    let mut names = Vec::new();
    // Set by a keyword that introduces `component_name`s, cleared by the next
    // structural keyword — the grammar ends each name list at its section's
    // follow-set. Whitespace and comments may sit inside a list, so only a
    // word or a token that cannot start a name clears it.
    let mut expecting_names = false;
    let mut i = 0;

    while i < bytes.len() {
        match bytes[i] {
            b'@' => {
                // Label: everything up to the next whitespace is label text
                // (the grammar's `label_text`), never a comment.
                let start = i;
                i += 1;
                while i < bytes.len() && !matches!(bytes[i], b' ' | b'\t' | b'\n' | b'\r') {
                    i += 1;
                }
                labels.push(Span { start, end: i });
                expecting_names = false;
            }
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'/' => {
                let start = i;
                while i < bytes.len() && bytes[i] != b'\n' {
                    i += 1;
                }
                comments.push(Span { start, end: i });
            }
            b'/' if i + 1 < bytes.len() && bytes[i + 1] == b'*' => {
                let start = i;
                i += 2;
                while i < bytes.len() && !(bytes[i] == b'*' && bytes.get(i + 1) == Some(&b'/')) {
                    i += 1;
                }
                i = (i + 2).min(bytes.len());
                comments.push(Span { start, end: i });
            }
            b' ' | b'\t' | b'\n' | b'\r' => i += 1,
            c if c.is_ascii_alphabetic() || c == b'_' => {
                // One whole structural word: hyphen-joined, so `end-to-end` is
                // a single name and not a keyword with a tail.
                let start = i;
                while i < bytes.len() && is_structural_word_byte(bytes[i]) {
                    i += 1;
                }
                let word = &source[start..i];
                if expecting_names && !crate::keywords::is_keyword(word) {
                    names.push(Span { start, end: i });
                } else {
                    expecting_names = introduces_names(word);
                }
            }
            _ => {
                expecting_names = false;
                i += 1;
            }
        }
    }

    LexicalSpans {
        comments,
        labels,
        names,
    }
}

/// Whether `byte` continues a `component_name`: [`crate::keywords::
/// is_structural_word_char`] over bytes, so the scan stays byte-based. A name
/// is ASCII, so a continuation byte of a multi-byte character never matches
/// and a name span always covers whole characters.
fn is_structural_word_byte(byte: u8) -> bool {
    byte.is_ascii_alphanumeric() || byte == b'_' || byte == b'-'
}

/// Whether the words after `word` name a component or event.
///
/// These are the grammar's `component_name` positions — `kw_context`,
/// `kw_machine`, `kw_refines`, `kw_sees`, `kw_extends` and `kw_event`. The
/// first three take one name and the rest a list, but the distinction costs
/// nothing here: a list ends at the next structural keyword either way.
fn introduces_names(word: &str) -> bool {
    use crate::keywords::KeywordId::{Context, Event, Extends, Machine, Refines, Sees};
    matches!(
        crate::keywords::lookup(word).map(|k| k.id),
        Some(Context | Machine | Refines | Sees | Extends | Event)
    )
}

/// Byte spans of every `//...` and `/*...*/` comment in `source`.
/// See [`lexical_spans`] for the scanning rules.
pub fn comment_spans(source: &str) -> Vec<Span> {
    lexical_spans(source).comments
}

/// Position-preserving copy of `source` with every comment byte replaced
/// by a space. See [`LexicalSpans::mask_comments`].
pub fn mask_comments(source: &str) -> String {
    lexical_spans(source).mask_comments(source)
}

/// Position-preserving copy of `source` with every comment **char** replaced
/// by a space. See [`LexicalSpans::mask_comments_chars`].
pub fn mask_comments_chars(source: &str) -> String {
    lexical_spans(source).mask_comments_chars(source)
}

/// Position-preserving copy of `source` with every comment and label byte
/// replaced by a space. See [`LexicalSpans::mask_opaque`].
pub fn mask_opaque(source: &str) -> String {
    lexical_spans(source).mask_opaque(source)
}

/// The span in `spans` (sorted and disjoint) containing byte `offset`,
/// if any. Binary search.
pub fn span_containing(spans: &[Span], offset: usize) -> Option<Span> {
    let i = spans.partition_point(|s| s.end <= offset);
    spans.get(i).copied().filter(|s| s.contains(offset))
}

/// Whether byte `offset` falls inside a `//` or `/* */` comment in `source`.
///
/// Convenience for the LSP providers that suppress a feature when the cursor
/// is in a comment (hover, completion). Callers that already hold a
/// [`LexicalSpans`] should reuse it via [`span_containing`] instead of
/// re-lexing here.
pub fn offset_in_comment(source: &str, offset: usize) -> bool {
    span_containing(&comment_spans(source), offset).is_some()
}

/// Normalize comment text for storage in an AST `comment` field.
///
/// Each line is trimmed, leading and trailing blank lines are dropped, and
/// the rest are rejoined with `\n`. Returns `None` when nothing remains
/// (whitespace-only comments — Rodin models in the wild carry `" "` comment
/// attributes — are not worth a `//` in the output). The printer applies
/// the same normalization before emitting, so parse → print is idempotent
/// even for ragged XML-sourced comments.
pub fn normalize_comment(text: &str) -> Option<String> {
    let lines: Vec<&str> = text.split('\n').map(str::trim).collect();
    let first = lines.iter().position(|l| !l.is_empty())?;
    let last = lines.iter().rposition(|l| !l.is_empty())?;
    Some(lines[first..=last].join("\n"))
}

/// The normalized text of one raw comment token (delimiters included), or
/// `None` if it is blank.
///
/// `raw` is a `//...` line comment or a `/*...*/` block comment exactly as
/// sliced from a [`comment_spans`] span; an unterminated block comment (no
/// closing `*/`) is tolerated.
pub fn comment_text(raw: &str) -> Option<String> {
    let inner = if let Some(rest) = raw.strip_prefix("//") {
        rest
    } else if let Some(rest) = raw.strip_prefix("/*") {
        rest.strip_suffix("*/").unwrap_or(rest)
    } else {
        raw
    };
    normalize_comment(inner)
}

/// Apply `f` to the code between comments and labels, leaving comment text
/// and label text untouched.
///
/// The transformed code segments and the verbatim comments and labels are
/// reassembled in order. Used by rewrites that must never alter comment
/// prose or a label's spelling, e.g. the LSP's ASCII ⇄ Unicode operator
/// conversion: `@inv1.1` and `@safety-END` are names, not a dot and a minus.
pub fn map_code_segments(source: &str, f: impl Fn(&str) -> String) -> String {
    map_code_segments_in_range(source, 0, source.len(), f)
}

/// Like [`map_code_segments`] but transforms only the byte range
/// `[start, end)` of `source`, using the comment and label spans of the
/// **whole** `source`.
///
/// Because comment extents come from the full text, a range that begins or
/// ends inside a comment is still treated as comment text — essential when
/// transforming an editor selection whose `/*` or `//` opener lies outside
/// the selected range. `start` and `end` must be char boundaries.
pub fn map_code_segments_in_range(
    source: &str,
    start: usize,
    end: usize,
    f: impl Fn(&str) -> String,
) -> String {
    let mut out = String::with_capacity(end.saturating_sub(start));
    let mut pos = start;
    for span in lexical_spans(source).opaque_spans() {
        // Intersect this comment or label with the requested range.
        let c_lo = span.start.max(start);
        let c_hi = span.end.min(end);
        if c_lo >= c_hi {
            continue; // no overlap
        }
        if pos < c_lo {
            out.push_str(&f(&source[pos..c_lo]));
        }
        out.push_str(&source[c_lo..c_hi]);
        pos = c_hi;
    }
    if pos < end {
        out.push_str(&f(&source[pos..end]));
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn masks_line_comment_preserving_layout() {
        let src = "@axm1 1 = 1 // note: positive\n@axm2 2 = 2\n";
        let masked = mask_comments(src);
        assert_eq!(masked.len(), src.len());
        let lines: Vec<&str> = masked.lines().collect();
        assert_eq!(lines[0].trim_end(), "@axm1 1 = 1");
        assert_eq!(lines[0].len(), "@axm1 1 = 1 // note: positive".len());
        assert_eq!(lines[1], "@axm2 2 = 2");
    }

    #[test]
    fn line_comment_span_excludes_newline() {
        let spans = comment_spans("x // c\ny");
        assert_eq!(spans.len(), 1);
        assert_eq!(&"x // c\ny"[spans[0].start..spans[0].end], "// c");
    }

    #[test]
    fn masks_block_comment_preserving_newlines() {
        let src = "a /* note:\n   spans lines */ b\n";
        let masked = mask_comments(src);
        assert_eq!(masked.len(), src.len());
        assert_eq!(masked.lines().count(), src.lines().count());
        let lines: Vec<&str> = masked.lines().collect();
        assert_eq!(lines[0].trim_end(), "a");
        assert_eq!(lines[1].trim_start(), "b");
        assert!(!masked.contains("note") && !masked.contains("*/"));
    }

    #[test]
    fn opaque_mask_blanks_labels_and_comments() {
        let src = "@inv-1 x - 1 // a - b\n";
        let masked = mask_opaque(src);
        assert_eq!(masked.len(), src.len());
        assert_eq!(masked, format!("{:6} x - 1 {:8}\n", "", ""));
    }

    #[test]
    fn label_spans_cover_at_tokens() {
        let src = "@inv//1 x > 0 // note: real\n";
        let spans = lexical_spans(src);
        let labels: Vec<&str> = spans.labels.iter().map(|s| &src[s.start..s.end]).collect();
        assert_eq!(labels, ["@inv//1"]);
        let comments: Vec<&str> = spans
            .comments
            .iter()
            .map(|s| &src[s.start..s.end])
            .collect();
        assert_eq!(comments, ["// note: real"]);
        assert_eq!(span_containing(&spans.labels, 4).map(|s| s.start), Some(0));
        assert_eq!(span_containing(&spans.labels, 8), None);
    }

    #[test]
    fn comment_markers_inside_label_are_label_text() {
        // The compound-atomic `label` rule consumes any non-whitespace, so
        // `@inv//1` is a complete label and `@SAF5"` (a Rodin-imported label
        // with a stray quote) does not hide the real comment.
        let src = "@inv//1 x > 0\n@SAF5\" y > 0 // note: real\n";
        let spans = comment_spans(src);
        assert_eq!(spans.len(), 1);
        assert_eq!(&src[spans[0].start..spans[0].end], "// note: real");
    }

    #[test]
    fn unterminated_block_comment_masked_to_eof() {
        let src = "a /* never: closed\nmore";
        let spans = comment_spans(src);
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].end, src.len());
        assert_eq!(mask_comments(src), "a                 \n    ");
    }

    #[test]
    fn char_mask_keeps_char_columns() {
        // One space per char (not byte): the masked line has the same char
        // count as the original, so char-column scans stay aligned.
        let src = "x /* тип */ ∈ S // ℕ\n";
        let masked = mask_comments_chars(src);
        assert_eq!(masked.chars().count(), src.chars().count());
        assert_eq!(masked, "x           ∈ S     \n");
    }

    #[test]
    fn char_mask_keeps_newlines_in_block_comments() {
        let src = "a /* первая\nвторая */ b\n";
        let masked = mask_comments_chars(src);
        assert_eq!(masked.lines().count(), src.lines().count());
        assert_eq!(masked, "a          \n          b\n");
    }

    #[test]
    fn normalize_trims_and_drops_blank_edges() {
        assert_eq!(normalize_comment(" a "), Some("a".to_string()));
        assert_eq!(
            normalize_comment("\n  first\n   second  \n\n"),
            Some("first\nsecond".to_string())
        );
        assert_eq!(normalize_comment("a\n\nb"), Some("a\n\nb".to_string()));
        assert_eq!(normalize_comment("   "), None);
        assert_eq!(normalize_comment("\n \n"), None);
        assert_eq!(normalize_comment(""), None);
    }

    #[test]
    fn comment_text_strips_delimiters() {
        assert_eq!(comment_text("// note"), Some("note".to_string()));
        assert_eq!(comment_text("//"), None);
        assert_eq!(comment_text("/* a\n   b */"), Some("a\nb".to_string()));
        assert_eq!(comment_text("/* open"), Some("open".to_string()));
        assert_eq!(comment_text("/*   */"), None);
    }

    #[test]
    fn map_code_segments_leaves_comments_verbatim() {
        let src = "x <= 1 // keep <= as is\ny <= 2 /* and <= here */\n";
        let out = map_code_segments(src, |code| code.replace("<=", "≤"));
        assert_eq!(out, "x ≤ 1 // keep <= as is\ny ≤ 2 /* and <= here */\n");
    }

    #[test]
    fn map_code_segments_leaves_labels_verbatim() {
        // A label is a name: the `-` in `@safety-END` and the `.` in `@inv1.1`
        // are label text, never the subtraction or dot operator.
        let src = "@safety-END x - 1\n@inv1.1 y . z // a - b\n";
        let out = map_code_segments(src, |code| code.replace('-', "−").replace('.', "·"));
        assert_eq!(out, "@safety-END x − 1\n@inv1.1 y · z // a - b\n");
    }

    #[test]
    fn map_code_segments_in_range_respects_comments_opened_outside_range() {
        // A range starting inside a block comment whose `/*` is before the
        // range: the in-range prose must stay verbatim, only trailing code
        // is transformed.
        let src = "a <= b /* note <= here */ c <= d";
        //         0123456789...
        // Select from inside the comment ("note <=...") to the end.
        let start = src.find("note").unwrap();
        let out = map_code_segments_in_range(src, start, src.len(), |code| code.replace("<=", "≤"));
        // The `<=` inside the comment is untouched; the `<=` in `c <= d` is converted.
        assert_eq!(out, "note <= here */ c ≤ d");
    }

    /// A component or event name is name text, not code: its hyphen is not
    /// subtraction, and a segment between two hyphens is not an operator
    /// however it is spelled. `-` is not a word character, so `INT` in
    /// `CTX-INT-1` is word-bounded and an operator scan would rewrite it.
    #[test]
    fn component_names_are_opaque_to_a_code_rewrite() {
        for (source, name) in [
            ("MACHINE A-C0\nEND\n", "A-C0"),
            ("CONTEXT ctx-1\nEND\n", "ctx-1"),
            ("MACHINE m\nREFINES end-to-end\nEND\n", "end-to-end"),
            ("MACHINE m\nSEES CTX-INT-1\nEND\n", "CTX-INT-1"),
            ("CONTEXT c\nEXTENDS A-or-B\nEND\n", "A-or-B"),
            ("MACHINE m\nEVENTS\nEVENT do-step\nEND\nEND\n", "do-step"),
        ] {
            let masked = mask_opaque(source);
            let start = source.find(name).expect("name occurs in source");
            assert_eq!(
                &masked[start..start + name.len()],
                " ".repeat(name.len()),
                "{name:?} must be masked in {source:?}"
            );
        }
    }

    /// Masking names must not swallow the formulas around them: a name list
    /// ends at the next structural keyword, and an operator in a formula is
    /// still code.
    #[test]
    fn masking_names_stops_at_the_next_clause() {
        let source = "MACHINE m-1\nSEES c-1 c-2\nVARIABLES x\nINVARIANTS\n  @i x - 1 ∈ ℕ\nEND\n";
        let masked = mask_opaque(source);
        for name in ["m-1", "c-1", "c-2"] {
            let at = source.find(name).unwrap();
            assert_eq!(
                &masked[at..at + name.len()],
                " ".repeat(name.len()),
                "{name}"
            );
        }
        // The clause keywords and the formula survive.
        assert!(masked.contains("VARIABLES x"), "masked: {masked:?}");
        assert!(masked.contains("x - 1"), "subtraction is code: {masked:?}");
    }

    #[test]
    fn unicode_inside_comment_masked_without_panic() {
        // Each multi-byte char inside the comment becomes one space per byte;
        // byte length and line layout are preserved, code is untouched.
        let src = "x ∈ S // тип: ℕ\n";
        let masked = mask_comments(src);
        assert_eq!(masked.len(), src.len());
        assert!(masked.starts_with("x ∈ S "));
        assert_eq!(masked.trim_end(), "x ∈ S");
        assert!(masked.ends_with('\n'));
    }
}
