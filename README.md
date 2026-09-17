# CatalanSun (Lean slice of arXiv:2609.04176v1)

Lean 4 / Mathlib formalization of **high-ROI structural lemmas** from
Zhi-Wei Sun, *Catalan's constant is irrational* (arXiv:2609.04176v1).

**This project does not claim Theorem 1.1 (G irrational).** It locks arithmetic
and linear-algebra facts that the paper's proof depends on. Theorem 2.1 (full
column rank), absolute Corollary 2.1, det-level Lemma 5.4, **Theorem 5.1**, and
now **Lemma 5.5's row-stability bound (5.2)** are proved; Theorem 1.1 remains
open. Lemma 5.5's ledger bound (5.3) is the next target.

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

`lean-proof-forge` verify: **pass** (0 sorry, axioms ⊆ classical three). See `results/lean_verify_brief.md`.

Continuation plan: `docs/WORKPLAN-CONTINUATION.md`. Derivation history of `thm_5_1`
(now complete) is in `docs/THM51-REDUCTION-NOTES.md`.

**Note:** paper’s written `f_i = T_i D + P` cannot yield a polynomial `P` under `Π_i = ∏_{h=1}^B`; Lean uses the `T_{i+1}` form. M5/M6 take `A = P − f = T_{i+1} D` so ClearedEq23 matches with positive sign. PC0 uses the matching `T_{i+1}` leading sign `(-1)^{j-1}`.

**Note (Lemma 5.5, `m0AQ`):** the paper's `m^{(0)}_{Q,B}` is formalized as a
**minimum** over card-`S` subsets at dimension `Ndim0 B S`, mirroring `mAQ`,
not as the value at the fixed consecutive row set alone (an earlier scaffold
used the fixed-set reading; it makes (5.2) demonstrably false — the fixed set
is far from optimal once `Q` is large relative to `S`, so the gap grows like
`S` rather than `1+B/Q`; see `docs/WORKPLAN-CONTINUATION.md` for the
numerics). `docs/catalan-constant-irrational.md`'s reading of the paper
independently supports the minimized version. Separately, the paper's claim
of `O(√B log B)` odd prime powers below `5B` undercounts — it omits the
primes themselves (`~5B/log 5B` of them); the `o(B²)` conclusion of (5.3)
still appears to survive via Chebyshev (`∑ log p ≈ 5B`), but Lean should
derive it that way rather than reproduce the paper's count. **Re-verified
2026-09-17:** re-ran the (5.3) ledger sum with `m0` minimized on both sides
(the prior numerics used the since-refuted fixed-set `m0`) and `SUM/B²`
decays monotonically (0.32 → 0.06 for `B` from 100 to 800), consistent with
`o(B²)`.

**Note (Lemma 5.5, easy-direction constant):** the first easy-direction proof
landed (`mAQ_le_m0AQ_add`, `S*(3/Q+1)`) was too weak to establish (5.2) as
stated — for `Q > 3` its constant is `S ≈ B/20`, not `O(1+B/Q)`. The
per-index `FNQ` shift between `Ndim` and `Ndim0` is actually always `0` or
`1` (never the `2` that bound allowed) and nonzero on only 3 residue classes
mod `Q`, giving a genuine `O(1+B/Q)` bound (`mAQ_le_m0AQ_add_sharp`,
`sum_FNQ_shift_le`) — see `docs/WORKPLAN-CONTINUATION.md` for the full
derivation and a list of `ℕ`-division arithmetic pitfalls hit while proving
it (`Nat.div_lt_iff_lt_mul`'s argument order, `omega`'s inability to unify
differently-ordered products, etc.), worth reading before further div-heavy
Lean work in this file.

**Note (Lemma 5.5, hard direction):** `m0AQ ≤ mAQ + 105(1+B/Q)` is proved by
swapping the `≤ 3` indices of `mAQ`'s minimizer that lie in `topBlock` — the
indices of `Fin (Ndim B S)` with no counterpart in `Fin (Ndim0 B S)` — for
free indices of the common range. **Any** free index works: no greedy choice,
occupancy pigeonhole, or minimizer characterization is needed, because each
swap's cost is bounded *termwise* (`nQr_le`/`FNQ_le`/`NKQ_le` for the additive
part, `abs_collTerm_swap_le` for the collision part). This was checked
numerically before any Lean was written — the *adversarially worst*
replacement still saturates at `≈ 10(1+B/Q)` across `B ≤ 6000`, and the
end-to-end gap at `≈ 0.5(1+B/Q)` — and it collapsed what earlier scoping had
budgeted as the main combinatorial stage. Note `Thm51.lean`'s
`collisionSum_move` is *not* usable here: its hypothesis `c b + 2 ≤ c a` only
covers balance-improving moves, whereas an arbitrary swap can go either way;
`abs_collTerm_swap_le` proves the two-sided bound by direct `Finset` splitting
instead.

**Note (Lemma 5.5, a sign trap):** the `FNQ` shift sum runs *opposite* ways in
(5.2)'s two directions. The easy direction gets it free from
`FNQ_shift_nonneg`; in the hard direction that same lemma yields the bound in
the useless direction, and the genuine counting bound `sum_FNQ_shift_le` is
required. Worth knowing before touching either direction.

### Deferred (later sessions)

Theorem 5.1 and **Lemma 5.5's (5.2) are now fully proved** (both directions,
absolute constant, unconditional). Remaining work: **(5.3)** itself
(`lemma_5_5_ledger_little_o`) — now the only open piece of Lemma 5.5, to be
derived by summing the proved (5.2) bound over `layerIndex` via Chebyshev
(`∑ log p ≈ 5B`) rather than reproducing the paper's undercounted
`O(√B log B)` layer count; its numerics look favorable (`SUM/B²` decays
0.32 → 0.06 for `B` from 100 to 800). Corollary 5.2 uses a "Lemma 5.3" that is
cited but never displayed in the arXiv v1 PDF — almost certainly the trivial
`[x]_+ = x` fact for `x ≥ 0`, content-free for Lean purposes. Then Props
6.3/7.4; Mertens/PNT; Theorem 1.1.

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

`con-leche` is an external Lean kernel checker with a machine-checked
consistency argument. It does not read `.lean` files; it reads a raw
`lean4export` NDJSON of the compiled library.

```text
lake exe cache get
lake build
# lean4export at tag v4.32.2 (same as lean-toolchain)
lean4export CatalanSun > catalan-sun.ndjson
con-leche --verified catalan-sun.ndjson
```

Exit 0 = accept. Exit 1 = reject (the stream is not a valid kernel
environment). Exit 2 = decline (checker does not yet support some
feature in the stream). Exit 3 = error / OOM.

CI: `.github/workflows/con-leche.yml` runs this on every push and PR.
It pins `leanprover/con-leche` at `CON_LECHE_REV` and `lean4export` at
`LEAN4EXPORT_REF`. GitHub-hosted runners have ~7 GB RAM; a Mathlib-scale
export may OOM (exit 3) until a larger runner is used.

## Incoming (not on the default target)

Sun eq. 1.4 (Catalan tail recurrence) lives in `CatalanSun/Tail.lean` (sorry-free).
The original Downloads draft is archived as a stub under `incoming/`.

Paper notes: `docs/catalan-constant-irrational.md`, `docs/robustness-check-catalan.md`.

Repo: https://github.com/chokmah-me/catalan-sun-lean (public).
