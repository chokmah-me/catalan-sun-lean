/-
  CatalanSun/Rank.lean

  Rank packaging for the residual matrix (Sun arXiv:2609.04176v1 §2) and the
  abstract linear-algebra bridge

    full column rank  ⇒  existence of a nonvanishing maximal minor

  that turns Theorem 2.1 into Corollary 2.1.

  This file proves the bridge and the *conditional* Corollary 2.1 (assuming the
  rank hypothesis). It does **not** prove Theorem 2.1 itself, nor the absolute
  form of Corollary 2.1.
-/

import CatalanSun.Residual
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Algebra.GroupWithZero.Units.Basic

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.Rank

open CatalanSun Matrix Function

/-! ## Residual matrix as a Mathlib `Matrix`

Paper indexing (eq. (2.1)): rows `α ∈ {0,…,S+2}`, columns `j ∈ {1,…,S}`.
`Fin`-packaging uses `j.val + 1` so column `0 : Fin S` is paper column 1. -/

/-- Paper's residual matrix `ℛ` as a Mathlib matrix: rows `Fin (S+3)`,
columns `Fin S` (column index `j` ↔ paper `j+1 ∈ {1,…,S}`). -/
def RmatrixFin (B S : ℕ) : Matrix (Fin (S + 3)) (Fin S) ℝ :=
  Matrix.of fun α j => Residual.Rmatrix B α.val (j.val + 1)

/-! ## Abstract bridge: full column rank ⇒ nonvanishing minor

Mathlib has no packaged “exists nonvanishing maximal minor” lemma; the argument
below extracts a linearly independent set of rows of cardinality `card n` via
`exists_linearIndependent'`, then uses the square-field chain
`LinearIndependent rows ↔ IsUnit ↔ IsUnit det ↔ det ≠ 0`. -/

/-- If an `m × n` matrix over a field has full column rank, then some injective
row-reindexing `f : n → m` yields a square submatrix with nonzero determinant. -/
theorem exists_nonvanishing_minor_of_full_column_rank
    {m n : Type*} [Fintype m] [Fintype n] [DecidableEq n]
    {K : Type*} [Field K]
    (A : Matrix m n K) (hrank : A.rank = Fintype.card n) :
    ∃ f : n → m, Function.Injective f ∧ (A.submatrix f id).det ≠ 0 := by
  classical
  obtain ⟨κ, a, ha_inj, hsp, hli⟩ := exists_linearIndependent' K A.row
  haveI : Finite κ := LinearIndependent.finite (R := K) (M := n → K) hli
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ = Fintype.card n := by
    rw [linearIndependent_iff_card_eq_finrank_span.mp hli, Set.finrank, hsp,
      ← A.rank_eq_finrank_span_row, hrank]
  let e : n ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨a ∘ e, ha_inj.comp e.injective, ?_⟩
  set f : n → m := a ∘ e
  have hrow : LinearIndependent K (A.submatrix f id).row := by
    have : (A.submatrix f id).row = A.row ∘ f := by
      ext i j; simp [row_submatrix_eq_comp]
    rw [this]
    exact hli.comp e e.injective
  have hunit : IsUnit (A.submatrix f id) :=
    linearIndependent_rows_iff_isUnit.mp hrow
  exact isUnit_iff_ne_zero.mp ((isUnit_iff_isUnit_det _).mp hunit)

/-! ## Conditional Corollary 2.1

Paper Corollary 2.1: for `B > S > 0` there is an `S`-element row set whose
`S × S` minor of `RmatrixFin B S` is nonzero. That statement is immediate from
Theorem 2.1 (`rank = S`) via the bridge above. Until Theorem 2.1 is proved, we
package the corollary with an explicit rank hypothesis. -/

/-- Corollary 2.1, conditional on the rank conclusion of Theorem 2.1. -/
theorem cor_2_1_of_thm_2_1 {B S : ℕ} (_h : S < B) (_hS : 0 < S)
    (hthm : (RmatrixFin B S).rank = Fintype.card (Fin S)) :
    ∃ f : Fin S → Fin (S + 3), Function.Injective f ∧
      ((RmatrixFin B S).submatrix f id).det ≠ 0 :=
  exists_nonvanishing_minor_of_full_column_rank (RmatrixFin B S) hthm

/-! ### TODO: Theorem 2.1 (not proved here)

Paper Theorem 2.1: for integers `B > S > 0`,
`(RmatrixFin B S).rank = Fintype.card (Fin S)`
(full column rank of the `(S+3) × S` residual matrix).

Target statement (do **not** introduce with `sorry`/`admit`):

```lean
theorem thm_2_1_full_column_rank {B S : ℕ} (h : S < B) (hS : 0 < S) :
    (RmatrixFin B S).rank = Fintype.card (Fin S)
```

Proof sketch from the paper (deferred): a nontrivial column dependence would
produce a nonzero rational function solving the cleared functional equation
ruled out by `FunctionalEq.no_rational_solution`; the intermediate steps use
finite-difference vanishing, Newton interpolants, and a degree contradiction in
`K(X)`. Absolute Corollary 2.1 is then
`cor_2_1_of_thm_2_1 h hS (thm_2_1_full_column_rank h hS)`. -/

end CatalanSun.Rank
