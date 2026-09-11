# Lean proof verification — pass (CatalanSun / lean-proof-forge)

- project: `Documents/00Dev/catalan-sun-lean`
- paper: Zhi-Wei Sun, arXiv:2609.04176v1
- lake: elan `lake` / Lean **4.32.2** / Mathlib **v4.32.2**
- build_exit: **0**
- sorry/admit: **0**
- native_decide: **0**
- axiom entries audited: **12**
- axiom violations: **0** (all ⊆ `{propext, Classical.choice, Quot.sound}`)
- status: **`pass`** (`results/lean_verify_meta.json`)

**Does not claim Theorem 1.1 (`G` irrational).**

---

## Forge phases completed

| Phase | Result |
|-------|--------|
| 1 Intake | `lakefile.toml` + `lean-toolchain` present; targets P1–P4 |
| 2 Statement design | ClearedEq / Cauchy / 2-adic / ledger defs locked |
| 3 Author | `Ledger`, `TwoAdic`, `Cauchy`, `FunctionalEq` |
| 4 Verify | `verify_lean_project.py --project .` → exit 0 |
| 5 Repair | Import path fixes; Cauchy injective proofs; FunctionalEq constant-denom |
| 6 Hand-off | This brief |

---

## Lemma chain (load-bearing)

### P4 — Exact ledger (`CatalanSun/Ledger.lean`)
1. `rawQuadratic_at_one_twentieth` — `4ρ−2ρ² = 39/200` at `ρ=1/20`
2. `deltaLarge_at_one_twentieth` — `Δ_{>B} = 83/2400` at `ρ=1/20`

### P1 — Lemma 5.4 toolkit (`CatalanSun/TwoAdic.lean`)
1. `odd_two_mul_add_one` / `odd_PiFactor` / `padicValNat_two_PiFactor`
2. `isTwoIntegral_of_odd_den` / `isTwoIntegral_div_odd`
3. `lemma_5_4_positive_part` / `lemma_5_4_from_layers`

### P2 — Cauchy (`CatalanSun/Cauchy.lean`)
1. `det_cauchy_fin_one`, `det_cauchy_fin_two` — classical formula for `n≤2`
2. `oddDenom_*` — paper `2(i+j)+1` odd, positive, injective in each index
3. `lemma_4_2_S_one` / `lemma_4_2_odd_entry` — Remark 4.1 applicability

### P3 — Functional equation fragments (`CatalanSun/FunctionalEq.lean`)
1. `X_sq_mul_eq_C_false` — `4X²·p = C c` impossible for `c≠0`
2. `no_constant_denom_solution` / `no_polynomial_cleared_solution`
3. `thm_2_1_polynomial_fragment` — polynomial case of Thm 2.1 core

---

## Axiom audit (all green)

Every `#print axioms` name depends only on `[propext, Classical.choice, Quot.sound]`.

---

## Still open (honest scope)

| Item | Status |
|------|--------|
| Full RatFunc pole-chain for Thm 2.1 | **blocked** next increment (polynomial fragment done) |
| General `n` Cauchy determinant | **blocked** (Mathlib gap; `n≤2` done) |
| Full residual matrix + complete Lem 5.4 | partial (arithmetic core done) |
| Props 6.3 / 7.4 (`c_odd`, `Λ_mid`) | **deferred-computational** |
| Mertens / PNT / Thm 1.1 | **deferred-analytic** / long horizon |

---

## Re-verify

```text
cd Documents/00Dev/catalan-sun-lean
python ../lean-proof-forge/scripts/verify_lean_project.py --project .
```
