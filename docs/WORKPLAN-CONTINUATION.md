# Workplan: continuing toward det-level Lemma 5.4 / Theorem 5.1

**Repo:** https://github.com/chokmah-me/catalan-sun-lean (public)
**As of:** commit `357dbac` (2026-09-14), `main`, forge-green, 0 `sorry`/`admit`.
**Paper:** Z.-W. Sun, *Catalan's constant is irrational*, arXiv:2609.04176v1.
This repo does **not** claim Theorem 1.1 (G irrational); it locks structural/arithmetic
lemmas the paper's proof depends on.

## What this session added

`CatalanSun/FunctionalEq.lean`: the full "no rational solution" theorem —

```lean
theorem no_rational_solution (P Q : ℚ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q
```

i.e. no nonzero rational function `P/Q` (any nonzero `Q`, not just a constant)
satisfies the cleared form of Sun's functional equation
`4X²(P·Q(X+1) + P(X+1)·Q) = Q·Q(X+1)`. Previously only the constant-denominator
case was proved.

**Proof shape** (see the file for full detail): generalize `shiftPoly`/`ClearedEq`
to an arbitrary characteristic-zero field `K`; prove a common-linear-factor
cancellation lemma (`shiftEq_cancel_common_root`); find a genuine common root of
`P` and `Q` over `ℂ` via an extremal-real-part-root argument
(`common_root_exists`, using algebraic closedness — no infinite descent needed);
strong-induct on `Q.natDegree` to rule out every positive-degree `Q` over `ℂ`
(`no_rational_solution_complex`); descend back to `ℚ` via
`Polynomial.map (algebraMap ℚ ℂ)`.

Verified independently (adversarial check: statement fidelity, non-vacuous
hypotheses, each proof step, blast radius) — PASS, no defects. Sorry-free,
axioms ⊆ `{propext, Classical.choice, Quot.sound}`, unchanged from before.

## Why this mattered now

This result is an explicit prerequisite for the paper's **Corollary 2.1**
(existence of a nonvanishing `S×S` minor of the residual matrix — a rank
statement), which the blog-post-level extraction of the paper states relies on
"a polynomial-defect argument (no rational function satisfies the associated
functional equation ... proves `rank R = S`)". Corollary 2.1 is itself a
prerequisite (via **Proposition 3.1**, a Newton-completion + determinant-
factorization result) for the paper's **determinant-level Lemma 5.4** and
**Theorem 5.1** (the "local saturation" theorem). None of Corollary 2.1,
Proposition 3.1, det-level Lemma 5.4, or Theorem 5.1 are in this repo yet.

## What's already in the repo (context for the next session)

- `CatalanSun/Ledger.lean` — P4, exact rational ledger identities. Done.
- `CatalanSun/TwoAdic.lean` — P1, 2-adic toolkit (positive-part collapse,
  2-integrality closure under +,-,×,÷-odd, finite sums). Done (toolkit only).
- `CatalanSun/Cauchy.lean` — P2, Cauchy determinant for `n ≤ 2` only, plus
  odd-denominator nonvanishing. **General-`n` Cauchy determinant is NOT proved.**
- `CatalanSun/FunctionalEq.lean` — P3, now fully done (this session).
- `CatalanSun/Tail.lean` — Sun eq. 1.4 (`T_m + T_{m+1} = 1/(2m+1)²`),
  summability, positivity. Done, sorry-free.
- `CatalanSun/Residual.lean` — residual matrix entries `R_{α,j}` (eq. 2.1) via
  `weightedTail`; **entry-level** Lemma 5.4 (every `q·R_{α,j}` is 2-integral
  when `G = a/q ∈ ℚ`). Done. **Det-level Lemma 5.4 is NOT here.**

## Next increment: Corollary 2.1

**Paper statement** (extracted from the HTML rendering of the paper — treat as
approximate, re-derive/verify against the actual paper before formalizing):

> For integers `B > S > 0`, there exists a set `A ⊂ {0,...,S+2}` with `|A| = S`
> such that `det(R_{α,j})_{α∈A, 1≤j≤S} ≠ 0`, where `R_{α,j}` is eq. (2.1).

This is a linear-algebra rank statement over the `(S+3)×S` residual matrix
`R` from `Residual.lean`. The informal argument (per the paper's own
description) is: the columns of `R` can't satisfy a nontrivial linear
dependency, because such a dependency would produce a nonzero rational
function solving the functional equation just proved impossible — i.e.
`no_rational_solution` (this session's result) is the base case / obstruction
that makes the rank argument go through.

**Concrete Lean task for the next session:**

1. Re-fetch and carefully re-read the paper's actual §2 (not just the lossy
   HTML-extraction summary used to plan this session) to get Corollary 2.1's
   precise hypotheses/proof idea right before writing any Lean.
   `arxiv.org/abs/2609.04176` (abstract only) and
   `arxiv.org/html/2609.04176v1` (full HTML rendering) are both fetchable.
2. Formalize the "columns of `R` are linearly independent as functions of the
   weighted tail sequence" argument, using `Residual.Rmatrix` (already defined)
   and `FunctionalEq.no_rational_solution` as the key obstruction.
3. Land it as a `Matrix.rank` or "exists nonvanishing `S×S` minor" statement —
   check Mathlib's `Matrix.rank` API (`Mathlib/LinearAlgebra/Matrix/Rank.lean`,
   vendored at `.lake/packages/mathlib/`) for the right vocabulary
   (`Matrix.exists_...` / working with `Matrix.submatrix` + `Matrix.det`).

**Known gap for the increment after that** (Proposition 3.1 / det-level
Lemma 5.4 / Theorem 5.1): Mathlib (pinned v4.32.2, vendored in this repo) has
**no Cauchy–Binet expansion formula** and **no general-`n` Cauchy determinant**
— confirmed by grepping `.lake/packages/mathlib/Mathlib/LinearAlgebra/Matrix/`
for "Binet"/"Cauchy" (only hits are unrelated: `CrossProduct.lean`,
`SesquilinearForm/Basic.lean`). It does have `Matrix.rank` machinery and
`Mathlib/LinearAlgebra/Vandermonde.lean`. The paper's Newton-completion +
Pascal–Cauchy–Binet determinant factorization (Prop 3.1) and Theorem 5.1's
residue-occupancy combinatorics would each need to be built substantially from
scratch — treat each as its own multi-session effort, not something to
attempt in the same pass as Corollary 2.1.

## Process notes for whoever picks this up

- Use a Plan-agent pass to verify any nontrivial proof strategy against actual
  vendored Mathlib lemma names (`.lake/packages/mathlib/Mathlib/...`, readable
  directly — the project's own working directory) before dispatching an
  implementer; this caught a subtle correction to the naive pole-chain
  argument (extremal-root vs. infinite-descent) before any Lean was written.
- Dispatch implementation to an isolated worktree (`Agent` tool,
  `isolation: "worktree"`), then run an independent `verifier` agent
  (adversarial, blind to the implementer's own report) before merging.
- `lake build` on this project is slow (~2890 jobs total, mostly cached
  Mathlib) — budget several minutes per full build, run in background.
- Zero tolerance for `sorry`/`admit`. If a sub-step turns out harder than
  planned, land a smaller but fully honest sorry-free milestone rather than
  faking completion.
