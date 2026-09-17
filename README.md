# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1 (G irrational).** It locks arithmetic
and linear-algebra facts that the paper's proof depends on. Theorem 2.1 (full
column rank), absolute Corollary 2.1, det-level Lemma 5.4, and now **Theorem
5.1** are proved; Theorem 1.1 remains open.

## Status

| ID / topic | Content | File | Forge status |
|------------|---------|------|--------------|
| P4 | `4ρ−2ρ² = 39/200`, `Δ_{>B} = 83/2400` at `ρ=1/20` | `CatalanSun/Ledger.lean` | proved |
| P1 | Lemma 5.4 positive-part + 2-integrality toolkit | `CatalanSun/TwoAdic.lean` | proved (toolkit) |
| P2 | Cauchy determinant (general `n`) + odd-denom applicability | `CatalanSun/Cauchy.lean` | proved |
| P3 | Full `no_rational_solution` for cleared `1/(4X²)` form | `CatalanSun/FunctionalEq.lean` | proved |
| P3 / M7 | Cleared `(2X+3)²` form → ClearedEq; no-solution over ℚ/ℂ/ℝ | `CatalanSun/FunctionalEq.lean` | proved |
| eq. 1.4 | Catalan tail `T_m + T_{m+1} = 1/(2m+1)²` | `CatalanSun/Tail.lean` | proved |
| eq. 2.1 / entry Lemma 5.4 | `R_{α,j}` from `weightedTail`; `q·R` 2-integral when `G∈ℚ` | `CatalanSun/Residual.lean` | proved (entry-level) |
| **Det-level Lemma 5.4** | `[A₂ − R₂]₊ = 0` via entry 2-int → det 2-int and `v₂(F_B) > 0` | `CatalanSun/Lemma54.lean` | proved |
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
| **`qhat_ne_zero`** | ∃ injective `o` with `det (Ahat B S o) ≠ 0` | `Qhat.lean` | proved |
| **Cauchy–Binet** | `det(A*B) = ∑` over size-`m` subsets `s`, `det(cols_s A)·det(rows_s B)` | `CauchyBinet.lean` | proved |
| **PC0–PC1** | Pascal×Diag×Cauchy factorization of residual minor; CB → `∑ Ξ_I` | `PascalCauchy.lean` | proved |
| **PC2** | Lemma 4.2 odd-Cauchy instance (`lemma_4_2_odd_cauchy`) + row-minor bridge | `PascalCauchy.lean` | proved |
| **PC3** | Lemma 4.1 factorization via `paperP` / integer `PsiA : ℤ` (`det_polyEval_dvd_vandermonde`) | `PascalCauchy.lean` | proved |
| **(4.5) signed** | `Xi_closed_form` (no `q`, no absolute value): ABS-A DiagCauchy factor + two `V(I)` + `PsiA` + weights | `PascalCauchy.lean` | proved |
| **Thm 5.1 scaffold** | Layer defs `phiQ`/`NKQ`/`nQr`/`CAQ`/`FNQ`/`ellAQ`/`mAQ`/`aQB` + `thm_5_1_statement` | `Thm51.lean` | defs |
| **Thm 5.1 COMB** | Φ_Q remainder (5.3); consecutive collision (5.15); balanced occupancy minimizes collisions | `Thm51.lean` | proved |
| **Thm 5.1 PROOF-A/B/C** | `mAQ_le_ellAQ`; (5.16) `aQB_sub_ellAQ_consecutive`; (5.17) `phiQ_add_CAQ_le_phiQ_N` | `Thm51.lean` | proved |
| **Thm 5.1 PROOF-D** | Exact `NKQ`/`sumT` reduction to `phiQ` shifted evaluations (`NKQ_eq_PsiQ_sub`, `sum_NKQ_tail_eq`) | `Thm51.lean` | proved |
| **Thm 5.1 PROOF-E** | (KI) target `sum_NKQ_tail_ge`, now **unconditional**: dispatches over `Q ≤ 2·B`, `Q ≥ 2·Ndim B S + 2·B`, and (splitting the middle gap in two) `sum_NKQ_tail_ge_of_gap` / `sum_NKQ_tail_ge_of_gap2` | `Thm51.lean` | **proved** |
| **Thm 5.1** | `thm_5_1 : thm_5_1_statement`, assembled from PROOF-A–E via `linarith` | `Thm51.lean` | **proved** |
| **Lemma 5.5 scaffold** | `Ndim0`/`ell0AQ`/`m0AQ`/`a0QB` (consecutive-row analogues); `lemma_5_5_row_stability` (5.2) + `lemma_5_5_ledger_little_o` (5.3) targets | `Lemma55.lean` | defs |

`lean-proof-forge` verify: **pass** (0 sorry, axioms ⊆ classical three). See `results/lean_verify_brief.md`.

Continuation plan: `docs/WORKPLAN-CONTINUATION.md`. Derivation history of `thm_5_1`
(now complete) is in `docs/THM51-REDUCTION-NOTES.md`.

**Note:** paper’s written `f_i = T_i D + P` cannot yield a polynomial `P` under `Π_i = ∏_{h=1}^B`; Lean uses the `T_{i+1}` form. M5/M6 take `A = P − f = T_{i+1} D` so ClearedEq23 matches with positive sign. PC0 uses the matching `T_{i+1}` leading sign `(-1)^{j-1}`.

### Deferred (later sessions)

Theorem 5.1 is now fully proved. Remaining work: Lemma 5.5 (the `o(B^2)`
row-replacement ledger bound; Corollary 5.2 uses a "Lemma 5.3" that is cited
but never displayed in the arXiv v1 PDF — almost certainly the trivial
`[x]_+ = x` fact for `x ≥ 0`, content-free for Lean purposes); Props 6.3/7.4;
Mertens/PNT; Theorem 1.1.

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
