# Workplan: continuing toward Theorem 5.1

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## Next session pointer

**Landed:** Pascal–Cauchy PC0–PC3; signed (4.5) `Xi_closed_form`; Thm 5.1
scaffold; COMB-A/B/C; and PROOF-A/B/C in `Thm51.lean`:
`mAQ_le_ellAQ`, (5.16) `aQB_sub_ellAQ_consecutive`, (5.17)
`phiQ_add_CAQ_le_phiQ_N`, `phiQ_superadditive`. Scratchpads include
`.scratchpad/geneval-thm51-comb/` and `.scratchpad/geneval-thm51-proof/`.

**New (analysis-only, unverified — see `docs/THM51-REDUCTION-NOTES.md`):** a
2026-09-16 session with no Lean toolchain available (sandboxed, could not
reach `release.lean-lang.org`) worked out — but could not type-check — that
finishing `thm_5_1` needs exactly **one** further fact plus a `linarith`
assembly over `mAQ_le_ellAQ_consecutive` + (5.16) + `second_line_nonneg` +
(5.17). It also confirms (independently of paper access) that
`thm_5_1_statement`'s current hypotheses are too weak: it needs
`Injective f` (used by (5.17)) and the ratio bound `S * 20 ≤ B` (not just
`S < B` — a leading-order estimate in the notes shows the unconditional
statement isn't plausible from the existing lemmas alone). The one missing
piece is a single named target, `sum_NKQ_tail_ge` (the "(KI)" inequality in
the notes) — an exact, `S*20≤B`-dependent bound on
`∑_{i=S}^{Ndim B S - 1} NKQ B Q i` against `phiQ Q (Ndim B S) + 2*phiQ Q S`.
**Read `docs/THM51-REDUCTION-NOTES.md` first** — it has the exact target
statement, a suggested double-counting/convolution proof strategy, and why
the naive asymptotic bounds (`phiQ_sub_quadratic_*`) are too coarse to close it.

Start here next:

**2026-09-16 update:** narrowed the gap further. `sum_NKQ_tail_ge_of_Q_le_2B`
(`Thm51.lean`) extends the "small Q" regime from `Q ≤ B` to `Q ≤ 2*B` — same
crude `phiQ_poly_le/ge` machinery, but with the exact `r0Q`-independent
identity `A1²-A2²-A3²+A4² = 4B²+6B` making the remaining pure-polynomial
inequality closable by a concavity argument (`g` concave in `Q`, check both
endpoints `Q=0` and `Q=2B`, combine via convexity). **The crude bound is
provably maxed out here** — hand analysis (see chat/agent notes, not yet a
doc) shows the same style of bound fails once `Q` exceeds roughly `2.2*B`.
**Remaining open gap: `2*B < Q < 2*Ndim B S + 2*B`** (was `B < Q < 6B`).
Closing it needs the *exact* `phiQ_formula` (not the `±Q/8`-slop relaxation)
via finite case-splits on the quotient `n / Q` for each of the six arguments
— see the plan sketch referenced below.

Start here next:

1. `docs/THM51-REDUCTION-NOTES.md` — the precise reduction and open target.
2. This file (`docs/WORKPLAN-CONTINUATION.md`)
3. **Finish Theorem 5.1 proof** — close `2*B < Q < 2*Ndim B S + 2*B` in
   `sum_NKQ_tail_ge` via exact `phiQ_formula`-based case splits (paper's
   (5.18)–(5.21) residue engine), mirroring `sum_NKQ_tail_ge_of_Q_le_2B`'s
   proof shape but without the `±Q/8` relaxation; then land the `thm_5_1`
   assembly sketched in the reduction notes; then Lemma 5.3. **Still not**
   Theorem 1.1.
4. Evidence: `.scratchpad/geneval-thm51-proof/`,
   `.scratchpad/geneval-thm51-comb/`,
   `.scratchpad/geneval-abs45-thm51-scaffold/`,
   `.scratchpad/geneval-psia-integrality/`,
   `.scratchpad/geneval-pascal-cauchy-pc3/`

## What landed

Sorry-free prefix toward Theorem 2.1 (adversarial verifier PASS; lake build green;
axioms ⊆ classical three):

- **M0** (`CatalanSun/Rank.lean`): `rank_eq_card_iff_mulVec_injective`,
  `exists_nontrivial_column_dependence_of_rank_lt`
- **M1–M2** (`CatalanSun/NewtonDiff.lean`): paper alternating binomial sum
  vanishes for `natDegree p < n`; `paperFwdDiff`; Pochhammer/choose helpers
- **M3** (`CatalanSun/Thm21.lean`): column dependence ⇒
  `paperFwdDiff fSeq n = 0` for all `2B ≤ n ≤ 2B+S+2`
- **M4** (`CatalanSun/Structure.lean` + `Thm21` / `Tail`):
  `Dlam`/`Plam`, deg bounds, and
  `fSeq_eq_neg_tail_succ_mul_Dlam_add_Plam`:
  `f_i = −T_{i+1} D_λ(i) + P_λ(i)`.
  **Paper correction:** written `T_i` form is impossible for polynomial `P`
  under `Π_i = ∏_{h=1}^B` (k=0 needs `(2i+1)²`); Lean uses `T_{i+1}`
  (aligns with ClearedEq23 / `(2X+3)²`).
- **M5** (`NewtonDiff` + `Thm21`): Newton interpolant deg ≤ 2B−1;
  `ASeq = Plam.eval − fSeq = T_{i+1} D` (sign chosen for ClearedEq23)
- **M6** (`Structure` + `Thm21`): `G0`, `Kpoly`,
  `Kpoly_eq_zero_of_column_dep` (ℕ zeros + `G0 ∣ K` + `K(−3/2)=0`)
- **M7** (`CatalanSun/FunctionalEq.lean`): `ClearedEq23`,
  `clearedEq23_to_clearedEq`, `no_clearedEq23_solution_*`

Still present: `RmatrixFin`, rank→minor bridge, conditional `cor_2_1_of_thm_2_1`.

**Landed (M8):** Theorem 2.1 (`thm_2_1_full_column_rank`) and absolute
Corollary 2.1 (`cor_2_1`) are proved in `Thm21.lean`.

## Prior session context

`CatalanSun/FunctionalEq.lean`: the full "no rational solution" theorem —

```lean
theorem no_rational_solution (P Q : ℚ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q
```

i.e. no nonzero rational function `P/Q` satisfies the cleared form of Sun's
functional equation. This is the obstruction Theorem 2.1 will use (now also via
`no_clearedEq23_solution_real` for the paper's `(2X+3)²` form).

## What's already in the repo

- `CatalanSun/Ledger.lean` — P4, exact rational ledger identities. Done.
- `CatalanSun/TwoAdic.lean` — P1, 2-adic toolkit. Done (toolkit only).
- `CatalanSun/Cauchy.lean` — P2, general-`n` Cauchy determinant
  (`det_cauchyMatrix` / Remark 4.1). Done.
- `CatalanSun/CauchyBinet.lean` — Cauchy–Binet `det_mul_eq_sum_minors`. Done.
- `CatalanSun/FunctionalEq.lean` — P3, full `no_rational_solution` + M7 ClearedEq23. Done.
- `CatalanSun/Tail.lean` — Sun eq. 1.4. Done, sorry-free.
- `CatalanSun/Residual.lean` — residual entries `R_{α,j}` (eq. 2.1); **entry-level**
  Lemma 5.4 + `RmatrixRatFin`. Done.
- `CatalanSun/Lemma54.lean` — **det-level Lemma 5.4** (`lemma_5_4_det`). Done.
- `CatalanSun/PascalCauchy.lean` — **PC0–PC3 complete** Pascal×Diag×Cauchy +
  `∑ Ξ_I` + Lemma 4.2 + Lemma 4.1 via `paperP`/`PsiA : ℤ`
  (`det_polyEval_dvd_vandermonde`) + signed `Xi_closed_form` (Lean (4.5) without
  `q`). Done.
- `CatalanSun/Thm51.lean` — §5 layer defs + combinatorial core (COMB-A/B/C) +
  `thm_5_1_statement` (unproved). Done (scaffold + COMB; Thm 5.1 not proved).
- `CatalanSun/Rank.lean` — `RmatrixFin`; rank→minor bridge; conditional Cor 2.1; M0. Done.
- `CatalanSun/NewtonDiff.lean` — M1–M2 finite-diff / Newton helpers. Done.
- `CatalanSun/Structure.lean` — M4 `Dlam`/`Plam` + degree bounds. Done.
- `CatalanSun/Thm21.lean` — M3–M8: structure, Newton deg, `K≡0`,
  `Dlam ≠ 0`, `thm_2_1_full_column_rank`, absolute `cor_2_1`. Done.

## M8 status: Theorem 2.1 assembled

Proved for integers `B > S > 0`:
`(RmatrixFin B S).rank = Fintype.card (Fin S)`, and absolute Cor 2.1 via
`cor_2_1_of_thm_2_1`.

Scratchpad: `.scratchpad/geneval-m8/`.

## Known gap after Theorem 2.1

**Prop 3.1 proved** in `CatalanSun/NewtonCompletion.lean`:
`prop_3_1_det_Atilde` — `det Atilde = ± F_B · det (RmatrixFin.submatrix selectedRows id)`,
via `M = DiffMat * Atilde`, column facts, reindex to nested `fromBlocks`,
`det_fromBlocks_zero₂₁` / `det_fromBlocks_zero₁₂`, then `det_mul` back to `Atilde`.
**`qhat_ne_zero` proved** in `CatalanSun/Qhat.lean`: some injective omitted-row
map `o` has `(Ahat B S o).det ≠ 0`.

**General-`n` Cauchy proved** in `CatalanSun/Cauchy.lean`: `det_cauchyMatrix`
(Remark 4.1 product form).

**Cauchy–Binet proved** in `CatalanSun/CauchyBinet.lean`: `det_mul_eq_sum_minors`
(plus `m=0`/`m=1`/`square` specializations and `m > n ⇒ det = 0`).

**Det-level Lemma 5.4 landed** (no Pascal–Cauchy required for the positive-part
vanishing: entry 2-integrality ⇒ det 2-integrality ⇒ `R₂ ≥ 0`, and
`v₂(F_B) > 0` for `B ≥ 2`).

**PC0–PC3 complete** in `CatalanSun/PascalCauchy.lean`: residual minor =
Pascal × DiagCauchy, then Cauchy–Binet → `∑ Ξ_I` (paper (4.1) without `q^S`);
Lemma 4.2 odd-Cauchy closed form; Lemma 4.1 with integer `PsiA : ℤ`
via `paperPPoly` / `paperPMatrixZ` / `det_polyEval_dvd_vandermonde`
(column ops + constructive `/ₘ` + induction + Laplace).
**Signed (4.5) packaging landed:** `det_rowsSubmatrix_diagCauchy` (ABS-A) and
`Xi_closed_form` (ABS-B; two copies of `V(I)`, no `q`/`|·|`).
**Thm 5.1 scaffolding landed** in `Thm51.lean` (defs + statement Prop).
**Thm 5.1 combinatorial core landed** in `Thm51.lean` (COMB-A/B/C:
`phiQ_sub_quadratic_nonneg`/`_le`, `sum_choose_nQr_consecutive`,
`collisionSum_eq_phiQ_of_balanced`/`collisionSum_ge_phiQ`).
**PROOF-A/B/C landed** in `Thm51.lean`: `mAQ_le_ellAQ`,
`aQB_sub_ellAQ_consecutive` (5.16), `phiQ_add_CAQ_le_phiQ_N` (5.17),
`phiQ_superadditive`. **Next:** residue engine (5.18)–(5.21) + assemble
`thm_5_1` under `S*20 ≤ B` and `Injective f`; then Lemma 5.3. Still not
Theorem 1.1. See `docs/THM51-REDUCTION-NOTES.md` for a (2026-09-16,
type-check-unverified) reduction of this to one named target lemma,
`sum_NKQ_tail_ge`, plus a ready `linarith` assembly.

## Process notes

- Plan-agent Mathlib pass before implementer; isolated worktree; adversarial
  verifier before merge.
- `lake build` is slow (~2890 jobs, mostly cached Mathlib) — budget several
  minutes, run in background.
- Zero tolerance for `sorry`/`admit`.
