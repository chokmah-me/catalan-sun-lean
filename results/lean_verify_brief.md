# Lean proof verification — pass

- project: `C:\Users\danie\Projects\catalan-sun-lean`
- target: `CatalanSun` (full import root)
- build_exit: 0
- sorry/admit hits: 0
- native_decide hits: 0
- axiom violations: 0

All `#print axioms` lines in `CatalanSun.lean` report
`[propext, Classical.choice, Quot.sound]` — the classical three, nothing else.
No `axiom` declarations anywhere under `CatalanSun/`.

## Headline results verified

- `CatalanSun.Thm51.thm_5_1` — Theorem 5.1, unconditional.
- `CatalanSun.Lemma55.lemma_5_5_row_stability_holds` — **paper (5.2)**, both
  directions, absolute constant `C = 210`, unconditional. Assembled from
  `mAQ_le_m0AQ_add_sharp` (easy) and `m0AQ_le_mAQ_add` (hard).
- `CatalanSun.Lemma55.abs_a0QB_sub_aQB_le` — the `a0QB`/`aQB` companion bound.

Still open in Lemma 5.5: `lemma_5_5_ledger_little_o` (paper (5.3)).
