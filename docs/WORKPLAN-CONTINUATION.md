# Workplan: continuing toward det-level Lemma 5.4 / Theorem 5.1

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## What landed (rank bridge session)

`CatalanSun/Rank.lean`:

- `RmatrixFin B S` — Mathlib packaging of `Residual.Rmatrix` as
  `Matrix (Fin (S+3)) (Fin S) ℝ` with paper column indexing `j ↦ j+1`.
- **Proved** (sorry-free): abstract bridge
  `exists_nonvanishing_minor_of_full_column_rank` —
  full column rank ⇒ injective row reindexing with nonzero square minor.
- **Proved** (sorry-free): `cor_2_1_of_thm_2_1` — Corollary 2.1 **conditional**
  on the rank hypothesis `(RmatrixFin B S).rank = Fintype.card (Fin S)`.

**Explicit non-claims:** Theorem 2.1 (`thm_2_1_full_column_rank`) is **not**
proved. Absolute Corollary 2.1 (existence of a nonvanishing minor without
assuming rank) is **not** claimed. Do not write “Corollary 2.1 proved” in
README/memory until Theorem 2.1 is kernel-green.

## Prior session context

`CatalanSun/FunctionalEq.lean`: the full "no rational solution" theorem —

```lean
theorem no_rational_solution (P Q : ℚ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q
```

i.e. no nonzero rational function `P/Q` satisfies the cleared form of Sun's
functional equation. This is the obstruction Theorem 2.1 will use.

## What's already in the repo

- `CatalanSun/Ledger.lean` — P4, exact rational ledger identities. Done.
- `CatalanSun/TwoAdic.lean` — P1, 2-adic toolkit. Done (toolkit only).
- `CatalanSun/Cauchy.lean` — P2, Cauchy determinant for `n ≤ 2` only.
  **General-`n` Cauchy determinant is NOT proved.**
- `CatalanSun/FunctionalEq.lean` — P3, full `no_rational_solution`. Done.
- `CatalanSun/Tail.lean` — Sun eq. 1.4. Done, sorry-free.
- `CatalanSun/Residual.lean` — residual entries `R_{α,j}` (eq. 2.1); **entry-level**
  Lemma 5.4. Done. **Det-level Lemma 5.4 is NOT here.**
- `CatalanSun/Rank.lean` — `RmatrixFin`; rank→minor bridge; conditional Cor 2.1.
  Done. **Theorem 2.1 / absolute Cor 2.1 are NOT here.**

## Next increment: Theorem 2.1 (full column rank)

**Paper statement:** for integers `B > S > 0`,
`(RmatrixFin B S).rank = Fintype.card (Fin S)`.

Once that is proved, absolute Corollary 2.1 is the one-liner
`cor_2_1_of_thm_2_1 h hS (thm_2_1_full_column_rank h hS)`.

Informal argument: a nontrivial column dependence of `R` would produce a
nonzero rational function solving the functional equation ruled out by
`no_rational_solution`. Intermediate paper steps (finite-diff vanishing for
deg ≤ 2B−3 polys; `f_i` / `D_λ` / `P_λ`; Newton degree; `K(X)` zeros + deg ≤ 4B
contradiction) are still open formalization work.

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
