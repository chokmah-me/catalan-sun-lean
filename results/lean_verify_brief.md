# Lean proof verification — pass

- project: `C:\Users\danie\Projects\catalan-sun-lean`
- target: `CatalanSun` (full import root)
- build_exit: 0 (2957 jobs)
- sorry/admit hits: 0
- native_decide hits: 0
- axiom violations: 0

All 140 `#print axioms` lines in `CatalanSun.lean` report axioms within
`[propext, Classical.choice, Quot.sound]` — the classical three, nothing else
(two of the new `Cor52` lemmas need strictly less). No `axiom` declarations
anywhere under `CatalanSun/`.

Note: `lean-proof-forge/scripts/verify_lean_project.py` is not present on this
machine; the checks above were run directly (build exit status, a
`sorry`/`admit`/`native_decide` scan, an `^axiom ` scan, and an audit of every
`#print axioms` report).

## Headline results verified

- `CatalanSun.Thm51.thm_5_1` — Theorem 5.1, unconditional.
- `CatalanSun.Lemma55.lemma_5_5_row_stability_holds` — **paper (5.2)**, both
  directions, absolute constant `C = 210`, unconditional.
- `CatalanSun.Lemma55.abs_a0QB_sub_aQB_le` — the `a0QB`/`aQB` companion bound.
- `CatalanSun.Lemma55.lemma_5_5_ledger_little_o_holds` — **paper (5.3)**, the
  `o(B²)` ledger bound over `layerIndex B`, unconditional, with no prime number
  theory.
- `CatalanSun.Cor52.posPart_layer_eq` / `posPartLedger_eq_raw` — **Corollary
  5.2's positive-part collapse**: Theorem 5.1 gives `aQB ≥ mAQ` on every layer,
  so `[a − m]₊ = a − m` and (5.24)'s ledger loses nothing to the positive part.
  This is where the paper's cited-but-undisplayed "Lemma 5.3"
  (`posPart_eq_self_of_nonneg`) is applied.
- `CatalanSun.Cor52.layerIndex_subset_layerIndexFull` — records that Lemma
  5.5's `5B` cutoff is strictly inside Cor 5.2's correct threshold
  `layerBound B S = 6B+2S+5`.

## Explicitly not established

`Cor52` defines (5.24)'s right-hand side and proves its structural properties.
It says **nothing** about `H_B^min`, integerizers, or `q̂_B`: that bridge needs
the §4→§5 odd-`p` valuation lemma, which does not exist here (neither
`Thm51.lean` nor `Lemma55.lean` contains any `padicVal`). Nothing is named
`logHmin`.

Also open: (5.3) is proved over `layerIndex B` (cutoff `5B`), but Cor 5.2's
ledger needs the larger `layerIndexFull B S` (cutoff `6B+2S+5`). The band
between them carries a measured `≈ 0.627·B²` — `Θ(B²)`, not `o(B²)` — so
Lemma 5.5's (5.3) cannot yet be consumed for the corrected-model comparison.
See `docs/FORMALIZATION-NOTES.md#cor-52-cutoff`.

Still open (not attempted): Props 6.3/7.4, Mertens/PNT, Theorem 1.1.
