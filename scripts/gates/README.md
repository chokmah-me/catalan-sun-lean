# Numeric gates

Python mirrors of the Lean layer definitions, used to **check a statement
before proving it**. This repo's standing rule — recorded in
`docs/FORMALIZATION-NOTES.md` — is that no scaffolded target gets a Lean proof
until it has been gated numerically, because four statement-level bugs have
been found this way and at least one of them (`m0AQ` as a fixed set) made a
stated lemma outright false.

These were scratch scripts; they are committed because the findings in
`FORMALIZATION-NOTES.md` are only as trustworthy as the instrument that
produced them, and because the next person to touch a layer definition needs a
way to tell whether they broke something.

## Run the regression check first

```text
cd scripts/gates
python check.py
```

Exit 0 means the Python mirror still agrees with the Lean definitions. It
asserts:

1. `fast2.py` reproduces `layers.py` exactly (189 layers, 0 mismatches).
2. `thm_5_1` holds numerically (`aQB ≥ mAQ`) — a free check of the mirror
   against proved Lean. **If this fails, the mirror has drifted, not the Lean.**
3. The support threshold `6B+2S+5` still bounds the nonzero layers.

Re-run it after any change to `Thm51.lean`'s `NKQ` / `phiQ` / `nQr` / `CAQ` /
`FNQ` / `ellAQN` / `mAQ` / `aQB`, or `Lemma55.lean`'s `Ndim0` / `a0QB` / `m0AQ`.

## The files

| file | what it is |
|---|---|
| `layers.py` | Verbatim brute-force mirror of the Lean defs. Readable, slow, the reference. `mAQ` enumerates all `C(2B+S+3, S)` subsets, so it dies past B≈80. |
| `fast2.py` | Same quantities, fast. `NKQ` in O(1) via modular inverse (`h ≡ 2⁻¹(−2i−1) mod Q`); `mAQ` by an **exact** DP over residue classes (within a class, take the `k` smallest `g`-values; collision cost is `2·C(k,2)`; then knapsack over classes). Reaches B=1200 in ~70s. |
| `check.py` | The regression check above. |
| `gate_support.py` | Finds the exact support of `[aQB − mAQ]₊` in `Q`, against the `5B` and `6B+2S+5` candidates. |
| `gate_threshold.py` | Confirms the threshold is exact: every odd prime power in `[5B, thr]` is nonzero, everything above is zero. |
| `gate_mass.py` | How much ledger mass the `Q < 5B` truncation drops (S=1, so it reaches larger B). |
| `gate_ratio2.py` | The same at the paper's regime `S = B/20`, via `fast2`. This produced the `drop/B² ≈ 0.627` figure. |
| `gate_ledger_vs_paper.py` | `compute` writes one row per nonzero layer at `S = B/20` (`data/ledger_S_B20_B200-1200.csv`, ~1 min at B=1200); `analyze` compares the exact `m/B` profile with the paper's `Λ_mid` (7.14), (8.2), and the tail above `(2+ρ)B` that §8 does not integrate. See `FORMALIZATION-NOTES.md#tail-band`. |
| `gate_scalar.py` | **The verdict gate.** Computes `SCALAR(B) = log\|det R[A,J]\| + v₂(F_B) log 2 − ∑_{odd Q} m_Q log p`, which is what (3.5), (5.13) and (5.24) reduce Theorem 9.1's left side to. `layers` recomputes all odd prime-power layers including `a = m` rows (the ledger CSV keeps only `a > m`); `detR` evaluates `det R` in fixed point; `detR-exact` does it with exact integers as a slow reference; `scalar` prints the verdict table. See `FORMALIZATION-NOTES.md#scalar-verdict`. |
| `gate_full53.py` | Sanity gate for the widened (5.3) bound used in `Cor52.ledgerFull_little_o`: checks `layerBound B (B/20) ≤ 12B` and that `111·B·log(12B)·(13+log 12B)/B²` decays to 0. A gate on the *bound*, not on the layer defs. |

## What these established

- `Lemma55.layerIndex`'s `p^ν < 5B` cutoff is too small for Cor 5.2's (5.24):
  the exact support runs to `6B + 2S + 5`, and the truncated band carries
  `≈ 0.627·B²` — `Θ(B²)`, not `o(B²)`.
- ~~That band is nonetheless covered by the paper's §8.~~ **Withdrawn**: §8
  integrates only to `(2+ρ)B`. See `FORMALIZATION-NOTES.md#tail-band`.
- **The paper's `B²` claim, measured directly, fails.** `SCALAR/B²` is
  `+1.826, +1.846, +1.851` at `B = 200, 400, 800`, converging to `≈ +1.86`,
  where Theorem 9.1 needs `≤ −0.0097`. Dominant term `v₂(F_B) log 2 → 2 log 2`.
  See `FORMALIZATION-NOTES.md#scalar-verdict`.
- `∑ aQB·log p ≈ 2.5·B²·log(5B)` — the ledger is `Θ(B² log B)`, so bounding
  `aQB` and discarding `mAQ` is not a viable proof route.

## Caveat

These are gates, not proofs. They check finitely many `(B, S, Q)` and are only
evidence about asymptotic claims. Their job is to stop a false statement before
it costs a session — not to substitute for the Lean.
