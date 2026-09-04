# rossi-prove

Sequent-prover kernel for Event-B — part of the
[Rossi](https://github.com/eventb-rossi/rossi) toolchain. It reads the proof
state a Rodin project stores next to its obligations and checks that the stored
proofs still discharge them.

## What it does

- Reads the Rodin proof formats: obligations from `.bpo`, stored proofs from
  `.bpr`, and recorded statuses from `.bps`.
- Checks a stored proof by *reuse* — re-applying its recorded rules — and by
  *replay* — re-running its reasoners on their recorded inputs.
- Decides the status of an obligation from its proof's recorded dependencies: a
  proof that no longer applies to the regenerated sequent is broken.
- Reports the Rodin confidence scale (discharged, reviewed, uncertain, pending,
  unattempted), taking a tree's confidence as the minimum over its nodes.
- Rewrites a `.bpr` entry by entry — dropping a proof or emptying it in place —
  as one verbatim streaming pass, so a proof too old or too damaged to load can
  still be cleaned out and everything else stays byte-identical.
- Registers the implemented reasoner families: the auto-rewriter, generalized
  modus ponens, the one-point rule, inference and structural rules, and manual
  steps.

The kernel is trusting: applying a rule performs structural checks only — the
needed hypotheses are present, the goal matches, the antecedents are
well-formed — and never re-derives logical entailment. Soundness lives in the
reasoners that produce the rules.

## Usage

```sh
cargo add rossi-prove
```

See the [API documentation](https://docs.rs/rossi-prove) for the checking entry
points. For command-line use, the same kernel is exposed as `rossi prove` in the
[`rossi-cli`](https://crates.io/crates/rossi-cli) tool.

## License

Licensed under either of [MIT](../../LICENSE-MIT) or
[Apache-2.0](../../LICENSE-APACHE) at your option.
