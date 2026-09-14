# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1 (G irrational).** It locks arithmetic
and linear-algebra facts that the paper's proof depends on. Theorem 2.1 (full
column rank) and absolute Corollary 2.1 are proved; det-level Lemma 5.4 /
Theorem 5.1 / Theorem 1.1 remain open.

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
| Thm 2.1 / M4 | `f_i = −T_{i+1} D_λ(i) + P_λ(i)`; deg bounds (`Structure.lean`) | `Structure` / `Thm21` | proved (revised vs paper’s written `T_i` form) |
| Thm 2.1 / M5 | Newton interpolant of `fSeq` has deg ≤ 2B−1; `A = P − f = T_{i+1} D` | `NewtonDiff` / `Thm21` | proved |
| Thm 2.1 / M6 | `Kpoly ≡ 0` under column dep (ℕ zeros + `G0 ∣ K` + `K(−3/2)=0`) | `Structure` / `Thm21` | proved |
| **Thm 2.1** | `(RmatrixFin B S).rank = S` for `B > S > 0` | `Thm21.lean` | proved |
| **Cor 2.1 (absolute)** | Nonvanishing minor without rank hypothesis | `Thm21.lean` | proved |
| **Prop 3.1** | `det Atilde = ± F_B · det R[A,J]` via DiffMat + fromBlocks | `NewtonCompletion.lean` | proved |

`lean-proof-forge` verify: **pass** (0 sorry, axioms ⊆ classical three). See `results/lean_verify_brief.md`.

Continuation plan: `docs/WORKPLAN-CONTINUATION.md`.

**Note:** paper’s written `f_i = T_i D + P` cannot yield a polynomial `P` under `Π_i = ∏_{h=1}^B`; Lean uses the `T_{i+1}` form. M5/M6 take `A = P − f = T_{i+1} D` so ClearedEq23 matches with positive sign.

### Deferred (later sessions)

Optional `qhat_ne_zero` (Cor 2.1 + Prop 3.1 + `F_B_ne_zero` + `Π ≠ 0`);
det-level Lemma 5.4 / Theorem 5.1 (needs Pascal–Cauchy factorization, §§2–4);
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
