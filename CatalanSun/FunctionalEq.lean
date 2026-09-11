/-
  CatalanSun/FunctionalEq.lean

  P3 fragments from Sun arXiv:2609.04176v1 Theorem 2.1:
  polynomial / constant-denominator obstruction for
  `S₀(z) + S₀(z+1) = 1/(4z²)`.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Functional equation impossibility fragments (P3)
-/

namespace CatalanSun.FunctionalEq

open Polynomial

/-- Polynomial shift `p(X) ↦ p(X+1)`. -/
noncomputable def shiftPoly (p : ℚ[X]) : ℚ[X] :=
  p.comp (X + C 1)

@[simp] theorem shiftPoly_C (a : ℚ) : shiftPoly (C a) = C a := by
  simp [shiftPoly]

@[simp] theorem shiftPoly_X : shiftPoly X = X + C 1 := by
  simp [shiftPoly]

/-- Cleared form of `P/Q + P(X+1)/Q(X+1) = 1/(4X²)`. -/
def ClearedEq (P Q : ℚ[X]) : Prop :=
  (C (4 : ℚ) * X ^ 2) * (P * shiftPoly Q + shiftPoly P * Q) = Q * shiftPoly Q

/-- A factor of `X²` cannot equal a nonzero constant. -/
theorem X_sq_mul_eq_C_false (p : ℚ[X]) {c : ℚ} (hc : c ≠ 0)
    (h : (C (4 : ℚ) * X ^ 2) * p = C c) : False := by
  have hz := congrArg (eval 0) h
  simp at hz
  exact hc hz.symm

/-- Constant-denominator case of `ClearedEq` fails. -/
theorem no_constant_denom_solution (P : ℚ[X]) {c : ℚ} (hc : c ≠ 0) :
    ¬ ClearedEq P (C c) := by
  intro h
  have h' :
      (C (4 : ℚ) * X ^ 2) * (C c * (P + shiftPoly P)) = C (c * c) := by
    unfold ClearedEq at h
    -- expand using shiftPoly_C
    have h1 : shiftPoly (C c) = C c := shiftPoly_C c
    rw [h1] at h
    -- goal algebra
    convert h using 1
    · ring
    · simp
  exact X_sq_mul_eq_C_false _ (mul_ne_zero hc hc) h'

/-- Specialization `Q = 1`. -/
theorem no_polynomial_cleared_solution (P : ℚ[X]) : ¬ ClearedEq P 1 :=
  no_constant_denom_solution P (by norm_num : (1 : ℚ) ≠ 0)

/-- `4 X² (P + P(X+1)) = 1` is impossible. -/
theorem no_polynomial_average_eq_inv_X_sq (P : ℚ[X]) :
    ¬ ((C (4 : ℚ) * X ^ 2) * (P + shiftPoly P) = 1) := by
  intro h
  exact X_sq_mul_eq_C_false (P + shiftPoly P) (by norm_num : (1 : ℚ) ≠ 0)
    (by simpa using h)

/-- Theorem 2.1 polynomial fragment. -/
theorem thm_2_1_polynomial_fragment (P : ℚ[X]) :
    ¬ ((C (4 : ℚ) * X ^ 2) * (P + shiftPoly P) = 1) :=
  no_polynomial_average_eq_inv_X_sq P

/-- If `Q = C c` with `c ≠ 0`, then `ClearedEq` fails (repackaging). -/
theorem clearedEq_of_eq_C {P Q : ℚ[X]} {c : ℚ}
    (hQ : Q = C c) (hc : c ≠ 0) : ¬ ClearedEq P Q := by
  rw [hQ]
  exact no_constant_denom_solution P hc

end CatalanSun.FunctionalEq
