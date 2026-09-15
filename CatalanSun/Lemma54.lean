/-
  CatalanSun/Lemma54.lean

  Det-level Lemma 5.4 (Sun arXiv:2609.04176v1): for `B ≥ 1` and any row map
  `f : Fin S → Fin (S+3)`,

    [A₂ − R₂]₊ = 0

  with `A₂ = −v₂(F_B)` and `R₂ = v₂(det (RmatrixRatFin.submatrix f id))`.

  Lives in its own module to avoid a Residual ↔ NewtonCompletion import cycle
  (NewtonCompletion already imports Residual).
-/

import CatalanSun.Residual
import CatalanSun.NewtonCompletion
import CatalanSun.TwoAdic

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun

open Matrix Residual NewtonCompletion TwoAdic

/-- **Det-level Lemma 5.4.** Every entry of `RmatrixRatFin` is 2-integral, so the
selected minor's determinant is 2-integral (`R₂ ≥ 0`). Combined with
`A₂ = −v₂(F_B) ≤ 0` (strict for `B ≥ 2`), the positive part vanishes.
Injectivity of `f` is not required. -/
theorem lemma_5_4_det (q a B S : ℕ) (hB : 1 ≤ B)
    (f : Fin S → Fin (S + 3)) :
    TwoAdic.posPart (
      (-(padicValNat 2 (F_B B) : ℤ))
        - padicValRat 2 ((RmatrixRatFin q a B S).submatrix f id).det
    ) = 0 := by
  classical
  set A2 : ℤ := -(padicValNat 2 (F_B B) : ℤ)
  set R2 : ℤ := padicValRat 2 ((RmatrixRatFin q a B S).submatrix f id).det
  have hR : 0 ≤ R2 := by
    change IsTwoIntegral ((RmatrixRatFin q a B S).submatrix f id).det
    refine isTwoIntegral_det _ ?_
    intro i j
    simpa [RmatrixRatFin, submatrix_apply] using
      RmatrixRatWitness_twoIntegral q a B (f i).val (j.val + 1)
  by_cases hB2 : 2 ≤ B
  · exact lemma_5_4_from_layers (padicValNat 2 (F_B B)) R2
      (padicValNat_two_F_B_pos hB2) hR
  · have hB1 : B = 1 := by omega
    have hv : padicValNat 2 (F_B B) = 0 := by
      subst hB1
      have hF : F_B 1 = 1 := by
        simp [F_B, Nat.factorial_zero, Nat.factorial_one]
      simp [hF]
    have hA0 : A2 = 0 := by simp [A2, hv]
    rw [hA0]
    unfold TwoAdic.posPart
    exact max_eq_right (by linarith)

end CatalanSun
