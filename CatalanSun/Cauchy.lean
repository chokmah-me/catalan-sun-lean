/-
  CatalanSun/Cauchy.lean

  P2 targets from Sun arXiv:2609.04176v1 Remark 4.1 / Lemma 4.2.
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.unusedSimpArgs false

/-!
# Cauchy determinant toolkit (P2)
-/

namespace CatalanSun.Cauchy

open Matrix

variable {R : Type*} [Field R]

/-- Square Cauchy matrix with entries `1 / (x i + y j)`. -/
def cauchyMatrix {n : Type*} (x y : n → R) : Matrix n n R :=
  Matrix.of fun i j => (x i + y j)⁻¹

/-- `n = 1` Cauchy determinant. -/
theorem det_cauchy_fin_one (x y : Fin 1 → R) :
    (cauchyMatrix x y).det = (x 0 + y 0)⁻¹ := by
  rw [det_fin_one]
  rfl

/-- `n = 2` Cauchy determinant. -/
theorem det_cauchy_fin_two (x y : Fin 2 → R)
    (h00 : x 0 + y 0 ≠ 0) (h01 : x 0 + y 1 ≠ 0)
    (h10 : x 1 + y 0 ≠ 0) (h11 : x 1 + y 1 ≠ 0) :
    (cauchyMatrix x y).det =
      (x 0 - x 1) * (y 0 - y 1) /
        ((x 0 + y 0) * (x 0 + y 1) * (x 1 + y 0) * (x 1 + y 1)) := by
  rw [det_fin_two]
  simp only [cauchyMatrix, Matrix.of_apply]
  field_simp [h00, h01, h10, h11]
  ring

/-! ## Paper applicability (Remark 4.1) -/

/-- Paper Cauchy denominators: `2(i + j) + 1`. -/
def oddDenom (i j : ℕ) : ℕ := 2 * (i + j) + 1

theorem oddDenom_odd (i j : ℕ) : Odd (oddDenom i j) :=
  ⟨i + j, rfl⟩

theorem oddDenom_pos (i j : ℕ) : 0 < oddDenom i j :=
  Nat.succ_pos _

theorem oddDenom_injective_left {i₁ i₂ j : ℕ} (h : i₁ ≠ i₂) :
    oddDenom i₁ j ≠ oddDenom i₂ j := by
  intro hEq
  apply h
  have h' : 2 * (i₁ + j) + 1 = 2 * (i₂ + j) + 1 := by simpa [oddDenom] using hEq
  have h'' : 2 * (i₁ + j) = 2 * (i₂ + j) := Nat.succ.inj h'
  exact Nat.add_right_cancel (Nat.mul_left_cancel (by decide : 0 < 2) h'')

theorem oddDenom_injective_right {i j₁ j₂ : ℕ} (h : j₁ ≠ j₂) :
    oddDenom i j₁ ≠ oddDenom i j₂ := by
  intro hEq
  apply h
  have h' : 2 * (i + j₁) + 1 = 2 * (i + j₂) + 1 := by simpa [oddDenom] using hEq
  have h'' : 2 * (i + j₁) = 2 * (i + j₂) := Nat.succ.inj h'
  exact Nat.add_left_cancel (Nat.mul_left_cancel (by decide : 0 < 2) h'')

theorem oddDenom_cast_ne_zero (i j : ℕ) : ((oddDenom i j : ℕ) : ℚ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (oddDenom_pos i j))

theorem paper_cauchy_entry_ne_zero (i j : ℕ) :
    (((oddDenom i j : ℕ) : ℚ))⁻¹ ≠ 0 :=
  inv_ne_zero (oddDenom_cast_ne_zero i j)

/-- `S = 1` specialization: det equals the single reciprocal entry. -/
theorem lemma_4_2_S_one (x y : ℚ) :
    (cauchyMatrix (R := ℚ) (fun _ : Fin 1 => x) (fun _ : Fin 1 => y)).det =
      (x + y)⁻¹ :=
  det_cauchy_fin_one (fun _ => x) (fun _ => y)

/-- Paper shape: entry `1/(2(i+j)+1)` is the `S=1` Cauchy determinant. -/
theorem lemma_4_2_odd_entry (i j : ℕ) :
    (cauchyMatrix (R := ℚ)
      (fun _ : Fin 1 => ((2 * i : ℕ) : ℚ))
      (fun _ : Fin 1 => ((2 * j + 1 : ℕ) : ℚ))).det =
      ((oddDenom i j : ℕ) : ℚ)⁻¹ := by
  rw [lemma_4_2_S_one]
  simp [oddDenom, Nat.cast_add, Nat.cast_mul]
  ring

end CatalanSun.Cauchy
