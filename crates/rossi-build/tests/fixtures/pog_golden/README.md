# Reference proof obligations

The `.bpo` files under this directory are the reference output for two of the
example archives in `crates/rossi/examples/`. `pog_golden.rs` locks rossi's
generated obligations against them, so the comparison runs in CI without a
toolchain runtime or the external model corpus.

Produced 2026-08-27 with the `org.eventb.core` 3.8.0 obligation generator,
driven headlessly:

```sh
cp crates/rossi/examples/traffic-light.zip crates/rossi/examples/binary-search.zip /tmp/ref/
cd /tmp/ref && rodin-headless build traffic-light.zip binary-search.zip
unzip -o traffic-light.zip 'traffic-light/*.bpo'
unzip -o binary-search.zip 'binary-search/*.bpo'
```

`rodin-headless build` rewrites each archive in place, so it must run on a
copy. Together the two models carry 64 obligations over 11 of the 19 natures
in `pog/natures.rs`: invariant establishment and preservation, guard
strengthening, action simulation and feasibility, witness feasibility, guard,
action and axiom well-definedness, and both variant forms.

Only `.bpo` is checked in. The reference `.bps` is not comparable: its updater
seeds status rows from the `.bpr` confidences these archives ship, while rossi
emits unattempted rows and only carries status forward from a previous `.bps`
(`pog/reconcile.rs`). `.bps` generation is covered by `pog_reconcile.rs` and
the CLI build tests instead.
