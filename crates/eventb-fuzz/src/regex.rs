//! Sampling strings from the regular expressions a tree-sitter grammar uses.
//!
//! `grammar.json` spells its terminals as regexes. Rather than special-case
//! each one, this module parses the dialect they actually use — literals and
//! escapes, character classes with ranges and negation, groups, and the three
//! quantifiers — and draws a matching string from it. Anything outside that
//! dialect is refused rather than mis-sampled, so a grammar that grows a
//! construct says so instead of quietly generating the wrong text.
//!
//! Two deliberate biases keep the output usable: repetitions stay short, and a
//! class that is exactly one letter in both cases — which is how tree-sitter
//! spells a case-insensitive keyword — yields lowercase most of the time, so
//! generated models read like models while still exercising the
//! case-insensitive path.

use crate::choice::{ByteSource, ByteSourceExt};

/// A parsed regular expression.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Re {
    /// The empty string.
    Empty,
    /// One literal character.
    Literal(char),
    /// A character class, possibly negated.
    Class { negated: bool, items: Vec<Item> },
    /// Concatenation.
    Concat(Vec<Re>),
    /// A bounded repetition of `node`.
    Repeat {
        node: Box<Re>,
        min: usize,
        max: usize,
    },
}

/// One member of a character class: a single character or an inclusive range.
#[derive(Debug, Clone, PartialEq, Eq)]
enum Item {
    Char(char),
    Range(char, char),
}

/// The alphabet a negated class draws from.
///
/// Printable ASCII plus a couple of characters that have bitten this parser
/// before (a non-breaking space, a Rodin operator glyph), minus nothing: the
/// class's own exclusions are applied on top.
const NEGATED_ALPHABET: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_ .,;:!?'\"()[]{}<>=+-*/\\|&^%$#@~`\u{00a0}\u{2208}";

/// Characters `\s` matches, for the purpose of sampling.
const SPACE_CHARS: &str = " \t\n\r";

/// The most repetitions a `*` or `+` produces.
///
/// Terminals in this grammar are words and punctuation; long runs add nothing
/// but slow the parser down, and unbounded ones would let a single terminal
/// swamp an input's size budget.
const MAX_REPEATS: usize = 3;

/// Sample a string matching `pattern`.
///
/// An unparsable pattern yields `None` rather than a panic: the fuzzer must
/// keep running when a grammar it reads at runtime moves ahead of it, and the
/// caller reports the rule that could not be sampled.
pub fn sample(pattern: &str, source: &mut dyn ByteSource) -> Option<String> {
    let parsed = Parser::new(pattern).parse()?;
    let mut out = String::new();
    emit(&parsed, source, &mut out);
    Some(out)
}

fn emit(node: &Re, source: &mut dyn ByteSource, out: &mut String) {
    match node {
        Re::Empty => {}
        Re::Literal(c) => out.push(*c),
        Re::Class { negated, items } => {
            if let Some(c) = sample_class(*negated, items, source) {
                out.push(c);
            }
        }
        Re::Concat(parts) => {
            for part in parts {
                emit(part, source, out);
            }
        }
        Re::Repeat { node, min, max } => {
            let count = source.between(*min, *max);
            for _ in 0..count {
                emit(node, source, out);
            }
        }
    }
}

fn sample_class(negated: bool, items: &[Item], source: &mut dyn ByteSource) -> Option<char> {
    if negated {
        let excluded: Vec<char> = NEGATED_ALPHABET
            .chars()
            .filter(|c| !items.iter().any(|item| item.contains(*c)))
            .collect();
        return source.pick(&excluded).copied();
    }

    // A case-insensitive keyword letter: `[cC]`. Prefer the canonical
    // lowercase spelling so most generated text reads naturally, and take the
    // uppercase arm often enough to keep exercising case-insensitivity.
    if let [Item::Char(first), Item::Char(second)] = items
        && first.to_lowercase().eq(second.to_lowercase())
        && first != second
    {
        let lower = if first.is_lowercase() { first } else { second };
        let upper = if first.is_lowercase() { second } else { first };
        return Some(if source.ratio(7, 8) { *lower } else { *upper });
    }

    let choices: Vec<char> = items.iter().flat_map(Item::chars).collect();
    source.pick(&choices).copied()
}

impl Item {
    fn contains(&self, c: char) -> bool {
        match self {
            Item::Char(x) => *x == c,
            Item::Range(low, high) => (*low..=*high).contains(&c),
        }
    }

    fn chars(&self) -> Vec<char> {
        match self {
            Item::Char(c) => vec![*c],
            Item::Range(low, high) => (*low..=*high).collect(),
        }
    }
}

struct Parser {
    chars: Vec<char>,
    position: usize,
}

impl Parser {
    fn new(source: &str) -> Self {
        Self {
            chars: source.chars().collect(),
            position: 0,
        }
    }

    fn parse(mut self) -> Option<Re> {
        let node = self.parse_concat()?;
        if self.position == self.chars.len() {
            Some(node)
        } else {
            // Trailing input means the dialect grew a construct this parser
            // does not know; refuse rather than sample something wrong.
            None
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.position).copied()
    }

    fn bump(&mut self) -> Option<char> {
        let c = self.peek()?;
        self.position += 1;
        Some(c)
    }

    fn parse_concat(&mut self) -> Option<Re> {
        let mut parts = Vec::new();
        while !matches!(self.peek(), None | Some(')')) {
            parts.push(self.parse_repeat()?);
        }
        Some(match parts.len() {
            0 => Re::Empty,
            1 => parts.pop()?,
            _ => Re::Concat(parts),
        })
    }

    fn parse_repeat(&mut self) -> Option<Re> {
        let atom = self.parse_atom()?;
        let (min, max) = match self.peek() {
            Some('*') => (0, MAX_REPEATS),
            Some('+') => (1, MAX_REPEATS),
            Some('?') => (0, 1),
            _ => return Some(atom),
        };
        self.position += 1;
        Some(Re::Repeat {
            node: Box::new(atom),
            min,
            max,
        })
    }

    fn parse_atom(&mut self) -> Option<Re> {
        match self.bump()? {
            // A group exists here only to scope a quantifier: no pattern in
            // this grammar uses alternation.
            '(' => {
                let inner = self.parse_concat()?;
                (self.bump() == Some(')')).then_some(inner)
            }
            '[' => self.parse_class(),
            '\\' => Some(self.parse_escape()?),
            // Metacharacters this dialect does not implement, and which are
            // not literals either: an unescaped quantifier or bracket is a
            // malformed pattern, `{` opens a counted repetition, `|` an
            // alternation, `.` the any-character class. Refusing beats
            // mis-sampling.
            '*' | '+' | '?' | ')' | ']' | '{' | '|' | '.' => None,
            c => Some(Re::Literal(c)),
        }
    }

    fn parse_escape(&mut self) -> Option<Re> {
        let escaped = self.bump()?;
        Some(match escaped {
            's' => Re::Class {
                negated: false,
                items: SPACE_CHARS.chars().map(Item::Char).collect(),
            },
            'd' => Re::Class {
                negated: false,
                items: vec![Item::Range('0', '9')],
            },
            'n' => Re::Literal('\n'),
            't' => Re::Literal('\t'),
            'r' => Re::Literal('\r'),
            // An escaped punctuation mark is that mark. An escaped letter is a
            // class shorthand or an assertion; the ones above are implemented
            // and the rest are refused, because reading `\b` as the letter `b`
            // would silently generate the wrong text.
            other if !other.is_alphanumeric() => Re::Literal(other),
            _ => return None,
        })
    }

    fn parse_class(&mut self) -> Option<Re> {
        let negated = self.peek() == Some('^');
        if negated {
            self.position += 1;
        }
        let mut items = Vec::new();
        loop {
            let c = match self.bump()? {
                ']' if !items.is_empty() => break,
                // A `]` in first position is a literal, as in POSIX classes.
                ']' => ']',
                '\\' => match self.parse_escape()? {
                    Re::Literal(c) => c,
                    Re::Class {
                        items: escaped_items,
                        negated: false,
                    } => {
                        items.extend(escaped_items);
                        continue;
                    }
                    // A negated shorthand inside a class would need set
                    // algebra this dialect never uses.
                    _ => return None,
                },
                c => c,
            };
            // A `-` that is not between two characters is a literal.
            if self.peek() == Some('-')
                && !matches!(self.chars.get(self.position + 1), None | Some(']'))
            {
                self.position += 1;
                let high = match self.bump()? {
                    '\\' => match self.parse_escape()? {
                        Re::Literal(c) => c,
                        _ => return None,
                    },
                    c => c,
                };
                items.push(Item::Range(c, high));
            } else {
                items.push(Item::Char(c));
            }
        }
        Some(Re::Class { negated, items })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::choice::SplitMix64;

    fn samples(pattern: &str, count: usize) -> Vec<String> {
        let mut rng = SplitMix64::new(0xF022);
        (0..count)
            .map(|_| sample(pattern, &mut rng).expect("pattern is supported"))
            .collect()
    }

    #[test]
    fn a_keyword_pattern_yields_that_keyword_in_some_case() {
        for text in samples("[cC][oO][nN][tT][eE][xX][tT]", 200) {
            assert_eq!(text.to_lowercase(), "context");
        }
    }

    #[test]
    fn a_keyword_pattern_prefers_lowercase_but_reaches_uppercase() {
        let texts = samples("[eE][nN][dD]", 400);
        assert!(texts.iter().any(|text| text == "end"), "no canonical form");
        assert!(
            texts.iter().any(|text| text != "end"),
            "case-insensitivity never exercised"
        );
    }

    #[test]
    fn identifier_and_number_patterns_match_their_shape() {
        for text in samples("[a-zA-Z_][a-zA-Z0-9_]*'?", 200) {
            let mut chars = text.chars();
            let first = chars.next().expect("non-empty");
            assert!(first.is_ascii_alphabetic() || first == '_', "{text:?}");
            let body: String = chars.collect();
            let body = body.strip_suffix('\'').unwrap_or(&body);
            assert!(
                body.chars().all(|c| c.is_ascii_alphanumeric() || c == '_'),
                "{text:?}"
            );
        }
        for text in samples("[0-9]+", 200) {
            assert!(!text.is_empty() && text.chars().all(|c| c.is_ascii_digit()));
        }
    }

    #[test]
    fn a_negated_class_excludes_its_members() {
        for text in samples("@[^\\s]+", 200) {
            assert!(text.starts_with('@'));
            assert!(text.chars().count() > 1);
            assert!(
                !text.chars().skip(1).any(|c| SPACE_CHARS.contains(c)),
                "{text:?}"
            );
        }
    }

    #[test]
    fn repetition_bounds_are_respected() {
        for text in samples("-[a-zA-Z0-9_]+", 200) {
            assert!(text.starts_with('-'));
            assert!((1..=1 + MAX_REPEATS).contains(&text.chars().count()));
        }
        for text in samples("x?", 100) {
            assert!(text.is_empty() || text == "x");
        }
    }

    #[test]
    fn a_group_scopes_the_quantifier_that_follows_it() {
        for text in samples("(ab)+", 100) {
            assert!(!text.is_empty());
            let mut rest = text.as_str();
            while let Some(tail) = rest.strip_prefix("ab") {
                rest = tail;
            }
            assert!(rest.is_empty(), "{text:?}");
        }
    }

    #[test]
    fn the_block_comment_body_pattern_is_supported() {
        // The most involved pattern in the grammar: the inside of `/* … */`.
        for text in samples("[^*]*\\*+([^/*][^*]*\\*+)*", 100) {
            assert!(!text.contains("*/"), "{text:?} would close the comment");
        }
    }

    #[test]
    fn unsupported_patterns_are_refused_rather_than_mis_sampled() {
        let mut rng = SplitMix64::new(1);
        for pattern in [
            "a{2,3}", "[a", "(a", "a)", "*a", "[\\S]", "a|b", "a.b", "\\wx", "\\bx",
        ] {
            assert!(
                sample(pattern, &mut rng).is_none(),
                "{pattern:?} should be refused"
            );
        }
    }

    #[test]
    fn sampling_is_reproducible_for_a_seed() {
        let mut first = SplitMix64::new(99);
        let mut second = SplitMix64::new(99);
        for _ in 0..50 {
            assert_eq!(
                sample("[a-z]+[0-9]?", &mut first),
                sample("[a-z]+[0-9]?", &mut second)
            );
        }
    }
}
