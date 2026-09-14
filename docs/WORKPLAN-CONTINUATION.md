# Workplan: continuing toward det-level Lemma 5.4 / Theorem 5.1

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## What landed (Thm 2.1 milestone session)

Sorry-free prefix toward Theorem 2.1 (adversarial verifier PASS; lake build green;
axioms ⊆ classical three):

- **M0** (`CatalanSun/Rank.lean`): `rank_eq_card_iff_mulVec_injective`,
  `exists_nontrivial_column_dependence_of_rank_lt`
- **M1–M2** (`CatalanSun/NewtonDiff.lean`, new): paper alternating binomial sum
  vanishes for `natDegree p < n`; `paperFwdDiff`; Pochhammer/choose helpers
- **M3** (`CatalanSun/Thm21.lean`, new): column dependence ⇒
  `paperFwdDiff fSeq n = 0` for all `2B ≤ n ≤ 2B+S+2`
- **M7** (`CatalanSun/FunctionalEq.lean`): `ClearedEq23` (cleared `(2X+3)²` form),
  `clearedEq23_to_clearedEq` via `z = X+3/2`, and
  `no_clearedEq23_solution` / `_complex` / `_real`

Still present from prior session: `RmatrixFin`, rank→minor bridge,
conditional `cor_2_1_of_thm_2_1`.

**Explicit non-claims:** Theorem 2.1 (`thm_2_1_full_column_rank`) is **not**
proved. Absolute Corollary 2.1 is **not** claimed. Do not write “Corollary 2.1 proved”
until Theorem 2.1 is kernel-green.

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
- `CatalanSun/Cauchy.lean` — P2, Cauchy determinant for `n ≤ 2` only.
  **General-`n` Cauchy determinant is NOT proved.**
- `CatalanSun/FunctionalEq.lean` — P3, full `no_rational_solution` + M7 ClearedEq23. Done.
- `CatalanSun/Tail.lean` — Sun eq. 1.4. Done, sorry-free.
- `CatalanSun/Residual.lean` — residual entries `R_{α,j}` (eq. 2.1); **entry-level**
  Lemma 5.4. Done. **Det-level Lemma 5.4 is NOT here.**
- `CatalanSun/Rank.lean` — `RmatrixFin`; rank→minor bridge; conditional Cor 2.1; M0. Done.
- `CatalanSun/NewtonDiff.lean` — M1–M2 finite-diff / Newton helpers. Done.
- `CatalanSun/Thm21.lean` — M3 dependence ⇒ vanishing Δ. Done.
  **Theorem 2.1 / absolute Cor 2.1 are NOT here.**

## Next increment: finish Theorem 2.1 (M4–M6 + assemble)

**Still open:** for integers `B > S > 0`,
`(RmatrixFin B S).rank = Fintype.card (Fin S)`.

Remaining paper steps:

1. **M4 (hardest):** structure `f_i = T_i D_λ(i) + P_λ(i)` with
   `deg D_λ ≤ 2B−1`, `deg P_λ ≤ 2B−3`
2. **M5:** Newton interpolant through `f_0..f_{2B+S+2}` has `deg ≤ 2B−1`
3. **M6:** build `K(X)`; prove `K ≡ 0` (too many zeros vs deg ≤ 4B)
4. **M8:** `K ≡ 0` + M7 ⇒ contradict nontrivial dependence ⇒
   `thm_2_1_full_column_rank`; then absolute Cor 2.1 via
   `cor_2_1_of_thm_2_1 h hS (thm_2_1_full_column_rank h hS)`

**Target Lean statement** (document only until proved — no `sorry`):

```lean
theorem thm_2_1_full_column_rank {B S : ℕ} (h : S < B) (hS : 0 < S) :
    (RmatrixFin B S).rank = Fintype.card (Fin S)
```

## Known gap after Theorem 2.1

Proposition 3.1 / det-level Lemma 5.4 / Theorem 5.1: Mathlib (pinned v4.32.2)
has **no Cauchy–Binet** and **no general-`n` Cauchy determinant**. Those each
need substantial from-scratch work — treat as separate multi-session efforts.

## Process notes

- Plan-agent Mathlib pass before implementer; isolated worktree; adversarial
  verifier before merge.
- `lake build` is slow (~2890 jobs, mostly cached Mathlib) — budget several
  minutes, run in background.
- Zero tolerance for `sorry`/`admit`.
