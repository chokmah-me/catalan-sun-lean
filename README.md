# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1 (G irrational).** It locks arithmetic
and linear-algebra facts that the paper's proof depends on. It also does **not**
yet claim Theorem 2.1 (full column rank) or absolute Corollary 2.1.

## Status

| ID / topic | Content | File | Forge status |
|------------|---------|------|--------------|
| P4 | `4ρ−2ρ² = 39/200`, `Δ_{>B} = 83/2400` at `ρ=1/20` | `CatalanSun/Ledger.lean` | proved |
| P1 | Lemma 5.4 positive-part + 2-integrality toolkit | `CatalanSun/TwoAdic.lean` | proved (toolkit) |
| P2 | Cauchy `n≤2` + odd-denom applicability | `CatalanSun/Cauchy.lean` | proved |
| P3 | Full `no_rational_solution` for cleared `1/(4X²)` form | `CatalanSun/FunctionalEq.lean` | proved |
| P3 / M7 | Cleared `(2X+3)²` form → ClearedEq; no-solution over ℚ/ℂ/ℝ | `CatalanSun/FunctionalEq.lean` | proved |
| eq. 1.4 | Catalan tail `T_m + T_{m+1} = 1/(2m+1)²` | `CatalanSun/Tail.lean` | proved |
| eq. 2.1 / entry Lemma 5.4 | `R_{α,j}` from `weightedTail`; `q·R` 2-integral when `G∈ℚ` | `CatalanSun/Residual.lean` | proved (entry-level; **not** det-level Lemma 5.4) |
| Rank bridge | `RmatrixFin`; full column rank ⇒ nonvanishing maximal minor | `CatalanSun/Rank.lean` | proved |
| Cor 2.1 (conditional) | Nonvanishing minor **assuming** rank = S | `CatalanSun/Rank.lean` | proved (conditional) |
| Thm 2.1 / M0 | Rank ↔ injective `mulVec` / nontrivial kernel | `CatalanSun/Rank.lean` | proved |
| Thm 2.1 / M1–M2 | Finite-diff alternating sum vanishing; `paperFwdDiff` | `CatalanSun/NewtonDiff.lean` | proved |
| Thm 2.1 / M3 | Column dependence ⇒ vanishing high Δ of `fSeq` | `CatalanSun/Thm21.lean` | proved |
| **Thm 2.1** | `(RmatrixFin B S).rank = S` for `B > S > 0` | — | **open** (M4–M6 remain) |
| **Cor 2.1 (absolute)** | Nonvanishing minor without rank hypothesis | — | **open** (needs Thm 2.1) |

`lean-proof-forge` verify: **pass** (0 sorry, axioms ⊆ classical three). See `results/lean_verify_brief.md`.

Continuation plan: `docs/WORKPLAN-CONTINUATION.md`.

### Next toward Theorem 2.1

1. **M4** (hardest): structure `f_i = T_i D_λ(i) + P_λ(i)` with degree bounds
2. **M5–M6**: Newton degree ≤ 2B−1; build `K(X)` and prove `K ≡ 0`
3. Assemble `thm_2_1_full_column_rank`, then absolute Cor 2.1 via the existing bridge

### Deferred (later sessions)

Det-level Lemma 5.4 / Theorem 5.1 (needs Pascal–Cauchy factorization, §§2–4);
general-`n` Cauchy determinant; Cauchy–Binet (not in Mathlib v4.32.2);
Props 6.3/7.4; Mertens/PNT; Theorem 1.1.

## Build

```text
lake build
```

Or via lean-proof-forge:

```text
python ../lean-proof-forge/scripts/verify_lean_project.py --project .
```

Toolchain: Lean 4.32.2 / Mathlib v4.32.2 (same pin as `aria-moebius`).

## Incoming (not on the default target)

Sun eq. 1.4 (Catalan tail recurrence) lives in `CatalanSun/Tail.lean` (sorry-free).
The original Downloads draft is archived as a stub under `incoming/`.

Paper notes: `docs/catalan-constant-irrational.md`, `docs/robustness-check-catalan.md`.

Repo: https://github.com/chokmah-me/catalan-sun-lean (public).
