# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1 (G irrational).** It locks arithmetic
and linear-algebra facts that the paper's proof depends on. Theorem 2.1 (full
column rank), absolute Corollary 2.1, det-level Lemma 5.4, **Theorem 5.1**, and
now **Lemma 5.5 in full** — both the row-stability bound (5.2) and the ledger
bound (5.3) — are proved; Theorem 1.1 remains open. Next targets are
Props 6.3/7.4.

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
| **Lemma 5.5, (5.2) easy** | `m0AQ` corrected to a **minimum** over card-`S` subsets at `Ndim0 B S` (not the fixed consecutive set — see divergence note below); `mAQ_le_m0AQ_add_sharp` (easy direction with a genuine `O(1+B/Q)` constant, `9*(1+B/Q)`, superseding `mAQ_le_m0AQ_add`'s too-weak `O(S)` constant); `m0AQ_le_ell0AQ` | `Lemma55.lean` | **proved** |
| **Lemma 5.5, (5.2) hard** | `m0AQ_le_mAQ_add`: `m0AQ ≤ mAQ + 105(1+B/Q)`, via termwise swap costs (`nQr_le`, `FNQ_le`, `abs_gTerm_le`), the single-swap collision bound `abs_collTerm_swap_le` (direct `Finset` splitting — **not** `collisionSum_move`, whose hypothesis only covers balance-improving moves), and the `≤3`-step descent `swap_descent_aux` out of `topBlock` | `Lemma55.lean` | **proved** |
| **Lemma 5.5 (5.2)** | `lemma_5_5_row_stability_holds` — both directions, absolute `C = 210` | `Lemma55.lean` | **proved** |
| **`a0QB`/`aQB` bound** | `abs_a0QB_sub_aQB_le`: `\|a0QB − aQB\| ≤ 6(1+B/Q)`, exact and unconditional (no minimization), via `NKQ_le` (arithmetic-progression count bound) | `Lemma55.lean` | **proved** |
| **Lemma 5.5 (5.3)** | `lemma_5_5_ledger_little_o_holds` — the layer sum is `o(B²)`. Elementary: layer injectivity (`layer_pow_injOn`) gives `≤ 5B` layers and `∑ 1/Q ≤ harmonic(5B)`; **no Chebyshev / prime counting needed** | `Lemma55.lean` | **proved** |
| **Lemma 5.5** | both (5.2) and (5.3) — **complete** | `Lemma55.lean` | **proved** |
| **Cor 5.2 "Lemma 5.3"** | `posPart_eq_self_of_nonneg` — the paper's cited-but-never-displayed lemma (`[x]₊ = x` for `x ≥ 0`), plus 1-Lipschitzness `abs_posPart_sub_le` | `Cor52.lean` | proved |
| **Cor 5.2 index set** | `layerBound B S = 6B+2S+5` (the exact cutoff, `= 2(N−1)+2B+1`) and `layerIndexFull`; `layerIndex_subset_layerIndexFull`. **Diverges from `layerIndex`'s `5B`** — see notes | `Cor52.lean` | proved |
| **Cor 5.2 ledger** | `posPartLedger` = (5.24) RHS; `posPartLedger_nonneg` | `Cor52.lean` | defs + proved |
| **Cor 5.2 core** | `posPart_layer_eq` / `posPartLedger_eq_raw` — Thm 5.1 ⇒ `[a−m]₊ = a−m`, the ledger loses nothing to the positive part | `Cor52.lean` | **proved** |

Verification: **pass** (0 sorry, 0 native_decide, axioms ⊆ classical three,
2957 jobs). See `results/lean_verify_brief.md`.

**Corollary 5.2 is partly landed** (`Cor52.lean`): (5.24)'s right-hand side is
defined and its positive parts are discharged via Theorem 5.1. It establishes
**nothing** about `H_B^min` or integerizers — that bridge needs the §4→§5 odd-`p`
valuation lemma, which does not exist here. While scoping it, a third
transcription-class finding surfaced: `layerIndex`'s `5B` cutoff is too small
for (5.24) and truncates a `Θ(B²)` band. Details in `FORMALIZATION-NOTES.md`.

**Picking this up fresh? Start with
[`docs/HANDOFF-NEXT-SESSION.md`](docs/HANDOFF-NEXT-SESSION.md)** — current
verified state, the one open gap and exactly how to close it, the settled
questions not worth redoing, and the tooling notes.

Continuation plan: `docs/WORKPLAN-CONTINUATION.md`. Derivation history of `thm_5_1`
(now complete) is in `docs/THM51-REDUCTION-NOTES.md`.

**Formalization notes — divergences from the paper, and traps:**
[`docs/FORMALIZATION-NOTES.md`](docs/FORMALIZATION-NOTES.md). Worth reading
before touching `Lemma55.lean` or `Thm51.lean`: it records two scaffolded
statements that were **false as written** (`m0AQ` as a fixed set; (5.3)'s layer
index), the `T_{i+1}` divergence, and the `ℕ`-division cast traps.

### Deferred (later sessions)

Theorem 5.1 and **Lemma 5.5 are now fully proved** — (5.2) in both directions
with an absolute constant, and (5.3) as an unconditional `o(B²)` bound. Neither
needed Chebyshev: (5.3) follows from layer injectivity (at most `5B` layers,
`∑ 1/Q ≤ harmonic(5B)`) plus `log²x/x → 0`, using no prime number theory, so
the paper's undercounted `O(√B log B)` layer claim never has to be reproduced
or repaired. Corollary 5.2 uses a "Lemma 5.3" that is cited but never displayed
in the arXiv v1 PDF — almost certainly the trivial `[x]_+ = x` fact for
`x ≥ 0`, content-free for Lean purposes. Remaining: Props 6.3/7.4;
Mertens/PNT; Theorem 1.1. (`Mathlib.NumberTheory.Chebyshev` **is** available at
this toolchain pin — `theta_le_log4_mul_x`, `pi_le_log4_mul_div`,
`psi_le_const_mul_self` — which should help those later targets.)

## Numeric gates

Before proving a scaffolded statement, this repo gates it numerically — four
statement-level bugs have been found that way. The Python mirrors of the Lean
layer definitions live in [`scripts/gates/`](scripts/gates/):

```text
python scripts/gates/check.py
```

Exit 0 means the mirror still agrees with the Lean definitions (it also
re-checks `thm_5_1` numerically). Re-run it after touching any layer def.

## Build

```text
lake build
```

Or via lean-proof-forge:

```text
python ../lean-proof-forge/scripts/verify_lean_project.py --project .
```

Toolchain: Lean 4.32.2 / Mathlib v4.32.2 (same pin as `aria-moebius`).

## External kernel check (con-leche)

Independent re-check of the exported library (not a proof of Theorem 1.1).
What it is, why we run it, and what CI accepted: [`docs/con-leche.md`](docs/con-leche.md).
Workflow: `.github/workflows/con-leche.yml`.

## Incoming (not on the default target)

Sun eq. 1.4 (Catalan tail recurrence) lives in `CatalanSun/Tail.lean` (sorry-free).
The original Downloads draft is archived as a stub under `incoming/`.

Paper notes: `docs/catalan-constant-irrational.md`, `docs/robustness-check-catalan.md`.

Repo: https://github.com/chokmah-me/catalan-sun-lean (public).
