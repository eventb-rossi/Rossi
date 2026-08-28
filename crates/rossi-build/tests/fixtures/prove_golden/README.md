# prove_golden fixtures

The `.bps` files a reference build wrote for the bundled example
archives with their `.bps` entries stripped — the pure status-update
pass, every status derived from the stored `.bpr` proofs against the
regenerated obligations, with the automatic prover disabled.

Produced with rodin-headless (image
`ghcr.io/eventb-rossi/rodin-headless`, plugin
`org.eventb.core 3.8.0.202607010932-881664d81`):

```sh
# in a scratch directory holding copies of crates/rossi/examples/*.zip
for z in *.zip; do
  zip -d "$z" $(unzip -l "$z" | awk '{print $4}' | grep '\.bps$')
done
rodin-headless build --auto-tactics off
# extract every .bps entry of the rebuilt archives into <model>/<component>.bps
```

Regenerate the same way after refreshing the example archives'
proofs; the archives' `.bpr`/`.bpo` state and these fixtures must
come from the same refresh.
