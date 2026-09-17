# Lean proof verification — pass

- project: `C:\Users\danie\Projects\catalan-sun-lean`
- target: `CatalanSun` (full import root)
- build_exit: 0 (2957 jobs)
- sorry/admit hits: 0
- native_decide hits: 0
- axiom violations: 0

All 150 `#print axioms` lines in `CatalanSun.lean` report axioms within
`[propext, Classical.choice, Quot.sound]` — the classical three, nothing else
(two of the new `Cor52` lemmas need strictly less). No `axiom` declarations
anywhere under `CatalanSun/`.

`lean-proof-forge` run (2026-09-17, synced skill at
`~/.claude/skills/synced/221a11f0-…/lean-proof-forge/scripts/verify_lean_project.py`,
`--target CatalanSun`): verdict **CAPABILITY_LIMITED**. `project_shape`,
`no_sorry_admit`, `native_decide`, `local_axiom_declarations`, `lake_build`
and `build_sorry_warnings` all PASS; `axiom_audit` is UNKNOWN because 38 of
544 declarations (34 `private`, 4 with a trailing prime) cannot be addressed
by the script's name resolver. Those are helpers used only by public
theorems, whose `#print axioms` output is transitive, so they are covered by
the 150 curated lines in `CatalanSun.lean`. The run must be made with the
gitignored `_tmp/` (vendored lean4export) moved aside, or the scanner flags a
`sorryAx` string inside its test file. `results/lean_verify_meta.json` holds
the report.

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
- `CatalanSun.Cor52.ledgerFull_little_o` — **paper (5.3) over the full index
  set** `layerIndexFull B (B/20)`, unconditional, same elementary route with
  caps at `12B`.
- `CatalanSun.Cor52.posPartLedger_sub_little_o` — **Cor 5.2's model
  comparison**: the exact-model and `(0)`-model (5.24) ledgers agree to
  `o(B²)` at `S = B/20`, for every `f`.

## Explicitly not established

`Cor52` defines (5.24)'s right-hand side and proves its structural properties.
It says **nothing** about `H_B^min`, integerizers, or `q̂_B`: that bridge needs
the §4→§5 odd-`p` valuation lemma, which does not exist here (neither
`Thm51.lean` nor `Lemma55.lean` contains any `padicVal`). Nothing is named
`logHmin`.

The index-set gap noted previously ((5.3) over `layerIndex B` vs the ledger
over `layerIndexFull B S`) is closed: (5.3) is now also proved over the larger
set (`ledgerFull_little_o`), and the model comparison
(`posPartLedger_sub_little_o`) is proved against it. See
`docs/FORMALIZATION-NOTES.md#cor-52-cutoff`.

Still open (not attempted): Props 6.3/7.4, Mertens/PNT, Theorem 1.1.
