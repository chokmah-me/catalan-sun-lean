# Workplan: continuing toward det-level Lemma 5.4 / Theorem 5.1

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## Next session pointer

**Landed:** Cauchy–Binet **`det_mul_eq_sum_minors`** (CB0–CB3 PASS) in
`CatalanSun/CauchyBinet.lean`. Scratchpad: `.scratchpad/geneval-cauchy-binet/`.

Start here next:

1. This file (`docs/WORKPLAN-CONTINUATION.md`)
2. **Pascal–Cauchy factorization** of residual minors (paper §4) using
   Cauchy–Binet + `det_cauchyMatrix` + Pascal/Vandermonde factors → toward
   det-level Lemma 5.4 / Theorem 5.1
3. Evidence: `.scratchpad/geneval-cauchy-binet/`, `.scratchpad/geneval-cauchy-general-n/`,
   `.scratchpad/geneval-qhat/`, `.scratchpad/geneval-prop31-finish/`

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
  Lemma 5.4. Done. **Det-level Lemma 5.4 is NOT here.**
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

Det-level Lemma 5.4 / Theorem 5.1: next is **Pascal–Cauchy factorization** of
the residual minor summands (paper §4), combining CB + Cauchy det + Pascal
alternants — not yet in this repo.

## Process notes

- Plan-agent Mathlib pass before implementer; isolated worktree; adversarial
  verifier before merge.
- `lake build` is slow (~2890 jobs, mostly cached Mathlib) — budget several
  minutes, run in background.
- Zero tolerance for `sorry`/`admit`.
