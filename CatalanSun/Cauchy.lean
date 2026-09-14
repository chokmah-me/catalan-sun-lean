/-
  CatalanSun/Cauchy.lean

  P2 targets from Sun arXiv:2609.04176v1 Remark 4.1 / Lemma 4.2.
  General-`n` Cauchy determinant (C0–C3).
-/

import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Fin
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false

/-!
# Cauchy determinant toolkit (P2)

Sun Remark 4.1:
`det (1/(x_i+y_j)) = ∏_{i<j}(x_j-x_i)(y_j-y_i) / ∏_{i,j}(x_i+y_j)`.
-/

namespace CatalanSun.Cauchy

open Matrix Finset
open scoped BigOperators

variable {R : Type*} [Field R]

/-- Square Cauchy matrix with entries `1 / (x i + y j)`. -/
def cauchyMatrix {n : Type*} (x y : n → R) : Matrix n n R :=
  Matrix.of fun i j => (x i + y j)⁻¹

@[simp] theorem cauchyMatrix_apply {n : Type*} (x y : n → R) (i j : n) :
    cauchyMatrix x y i j = (x i + y j)⁻¹ :=
  rfl

/-! ## C0: numerator / denominator of the closed form -/

/-- Paper/Mathlib numerator `∏_{i<j} (x_j-x_i)(y_j-y_i)`. -/
def cauchyDetNum {n : ℕ} (x y : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j ∈ Ioi i, (x j - x i) * (y j - y i)

/-- Denominator `∏_{i,j} (x_i + y_j)`. -/
def cauchyDetDen {n : ℕ} (x y : Fin n → R) : R :=
  ∏ i : Fin n, ∏ j : Fin n, (x i + y j)

theorem cauchyDetNum_zero (x y : Fin 0 → R) : cauchyDetNum x y = 1 := by
  simp [cauchyDetNum]

theorem cauchyDetDen_zero (x y : Fin 0 → R) : cauchyDetDen x y = 1 := by
  simp [cauchyDetDen]

theorem det_cauchy_fin_zero (x y : Fin 0 → R) : (cauchyMatrix x y).det = 1 := by
  exact det_fin_zero

/-- `n = 1` Cauchy determinant. -/
theorem det_cauchy_fin_one (x y : Fin 1 → R) :
    (cauchyMatrix x y).det = (x 0 + y 0)⁻¹ := by
  rw [det_fin_one]
  rfl

theorem cauchyDetNum_one (x y : Fin 1 → R) : cauchyDetNum x y = 1 := by
  simp [cauchyDetNum]

theorem cauchyDetDen_one (x y : Fin 1 → R) : cauchyDetDen x y = x 0 + y 0 := by
  simp [cauchyDetDen]

theorem det_cauchy_fin_one_eq_general (x y : Fin 1 → R) (_h : x 0 + y 0 ≠ 0) :
    (cauchyMatrix x y).det = cauchyDetNum x y / cauchyDetDen x y := by
  rw [det_cauchy_fin_one, cauchyDetNum_one, cauchyDetDen_one, one_div]

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

theorem cauchyDetNum_two (x y : Fin 2 → R) :
    cauchyDetNum x y = (x 1 - x 0) * (y 1 - y 0) := by
  have hIoi1 : Ioi (1 : Fin 2) = ∅ := by decide
  simp [cauchyDetNum, Fin.prod_univ_two, hIoi1, Fin.Ioi_zero_eq_map, Finset.prod_map,
    Fin.succEmb]

theorem cauchyDetDen_two (x y : Fin 2 → R) :
    cauchyDetDen x y =
      (x 0 + y 0) * (x 0 + y 1) * (x 1 + y 0) * (x 1 + y 1) := by
  simp [cauchyDetDen, Fin.prod_univ_two]
  ring

theorem det_cauchy_fin_two_eq_general (x y : Fin 2 → R)
    (h00 : x 0 + y 0 ≠ 0) (h01 : x 0 + y 1 ≠ 0)
    (h10 : x 1 + y 0 ≠ 0) (h11 : x 1 + y 1 ≠ 0) :
    (cauchyMatrix x y).det = cauchyDetNum x y / cauchyDetDen x y := by
  rw [det_cauchy_fin_two (x := x) (y := y) h00 h01 h10 h11, cauchyDetNum_two,
    cauchyDetDen_two]
  ring

/-! ## C1: vanishing, submatrix, product splits -/

theorem det_cauchyMatrix_eq_zero_of_eq_x {n : ℕ} (x y : Fin n → R)
    {i j : Fin n} (hij : i ≠ j) (hx : x i = x j) :
    (cauchyMatrix x y).det = 0 := by
  refine det_zero_of_row_eq hij ?_
  ext k
  simp [hx]

theorem det_cauchyMatrix_eq_zero_of_eq_y {n : ℕ} (x y : Fin n → R)
    {i j : Fin n} (hij : i ≠ j) (hy : y i = y j) :
    (cauchyMatrix x y).det = 0 :=
  det_zero_of_column_eq hij fun k => by simp [hy]

theorem cauchyDetNum_eq_zero_of_eq_x {n : ℕ} (x y : Fin n → R)
    {i j : Fin n} (hij : i ≠ j) (hx : x i = x j) :
    cauchyDetNum x y = 0 := by
  obtain hlt | heq | hgt := lt_trichotomy i j
  · simp only [cauchyDetNum]
    refine prod_eq_zero (mem_univ i) ?_
    refine prod_eq_zero (mem_Ioi.mpr hlt) ?_
    simp [hx]
  · exact (hij heq).elim
  · simp only [cauchyDetNum]
    refine prod_eq_zero (mem_univ j) ?_
    refine prod_eq_zero (mem_Ioi.mpr hgt) ?_
    simp [hx]

theorem cauchyDetNum_eq_zero_of_eq_y {n : ℕ} (x y : Fin n → R)
    {i j : Fin n} (hij : i ≠ j) (hy : y i = y j) :
    cauchyDetNum x y = 0 := by
  obtain hlt | heq | hgt := lt_trichotomy i j
  · simp only [cauchyDetNum]
    refine prod_eq_zero (mem_univ i) ?_
    refine prod_eq_zero (mem_Ioi.mpr hlt) ?_
    simp [hy]
  · exact (hij heq).elim
  · simp only [cauchyDetNum]
    refine prod_eq_zero (mem_univ j) ?_
    refine prod_eq_zero (mem_Ioi.mpr hgt) ?_
    simp [hy]

theorem cauchyMatrix_submatrix_succ {n : ℕ} (x y : Fin (n + 1) → R) :
    (cauchyMatrix x y).submatrix Fin.succ Fin.succ =
      cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  ext i j
  simp [Function.comp]

theorem cauchyDetDen_ne_zero {n : ℕ} (x y : Fin n → R)
    (h : ∀ i j, x i + y j ≠ 0) : cauchyDetDen x y ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => prod_ne_zero_iff.mpr fun j _ => h i j

theorem cauchyDetDen_succ {n : ℕ} (x y : Fin (n + 1) → R) :
    cauchyDetDen x y =
      (∏ j : Fin (n + 1), (x 0 + y j)) *
        (∏ i : Fin n, (x i.succ + y 0)) *
          cauchyDetDen (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  unfold cauchyDetDen
  rw [Fin.prod_univ_succ]
  have hsplit :
      (∏ i : Fin n, ∏ j : Fin (n + 1), (x i.succ + y j)) =
        (∏ i : Fin n, (x i.succ + y 0)) *
          (∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) := by
    calc
      (∏ i : Fin n, ∏ j : Fin (n + 1), (x i.succ + y j)) =
          ∏ i : Fin n, ((x i.succ + y 0) *
            ∏ j : Fin n, (x i.succ + y j.succ)) := by
              refine prod_congr rfl fun i _ => ?_
              rw [Fin.prod_univ_succ]
      _ = (∏ i : Fin n, (x i.succ + y 0)) *
            (∏ i : Fin n, ∏ j : Fin n, (x i.succ + y j.succ)) := by
              rw [← prod_mul_distrib]
  rw [hsplit]
  simp [Function.comp, mul_assoc]

theorem cauchyDetNum_succ {n : ℕ} (x y : Fin (n + 1) → R) :
    cauchyDetNum x y =
      (∏ i : Fin n, (x i.succ - x 0) * (y i.succ - y 0)) *
        cauchyDetNum (x ∘ Fin.succ) (y ∘ Fin.succ) := by
  unfold cauchyDetNum
  rw [Fin.prod_univ_succ]
  have h0 :
      (∏ j ∈ Ioi (0 : Fin (n + 1)), (x j - x 0) * (y j - y 0)) =
        ∏ i : Fin n, (x i.succ - x 0) * (y i.succ - y 0) := by
    simp [Fin.Ioi_zero_eq_map, Finset.prod_map, Fin.succEmb]
  rw [h0]
  congr 1
  refine prod_congr rfl fun i _ => ?_
  simp [Fin.Ioi_succ, Finset.prod_map, Fin.succEmb, Function.comp]

theorem cauchy_rowDiff {n : ℕ} (x y : Fin (n + 1) → R) (i : Fin n) (j : Fin (n + 1))
    (h0j : x 0 + y j ≠ 0) (hij : x i.succ + y j ≠ 0) :
    (x i.succ + y j)⁻¹ - (x 0 + y j)⁻¹ =
      (x 0 - x i.succ) * ((x i.succ + y j) * (x 0 + y j))⁻¹ := by
  field_simp [h0j, hij]
  ring

theorem cauchy_colDiff {n : ℕ} (x y : Fin (n + 1) → R) (i j : Fin n)
    (hi0 : x i.succ + y 0 ≠ 0) (hij : x i.succ + y j.succ ≠ 0) :
    (x i.succ + y j.succ)⁻¹ - (x i.succ + y 0)⁻¹ =
      (y 0 - y j.succ) * ((x i.succ + y j.succ) * (x i.succ + y 0))⁻¹ := by
  field_simp [hi0, hij]
  ring

/-! ## C2: recursive Cauchy determinant identity -/

/-- Column analogue of `det_eq_of_forall_row_eq_smul_add_const`. -/
theorem det_eq_of_forall_col_eq_smul_add_const
    {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}
    (c : n → R) (k : n) (hk : c k = 0)
    (A_eq : ∀ i j, A i j = B i j + c j * B i k) : A.det = B.det := by
  rw [← det_transpose A, ← det_transpose B]
  exact det_eq_of_forall_row_eq_smul_add_const c k hk fun i j => A_eq j i

theorem cauchy_succ_factor_sign {n : ℕ} (x y : Fin (n + 1) → R) :
    (∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) =
      ∏ i : Fin n, (x i.succ - x 0) * (y i.succ - y 0) := by
  refine prod_congr rfl fun i _ => ?_
  ring

theorem det_cauchyMatrix_succ {n : ℕ} (x y : Fin (n + 1) → R)
    (h : ∀ i j : Fin (n + 1), x i + y j ≠ 0) :
    (cauchyMatrix x y).det =
      (∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) *
        (∏ j : Fin (n + 1), (x 0 + y j))⁻¹ *
          (∏ i : Fin n, (x i.succ + y 0))⁻¹ *
            (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det := by
  by_cases hx : ∃ i : Fin n, x i.succ = x 0
  · obtain ⟨i, hi⟩ := hx
    have hdet : (cauchyMatrix x y).det = 0 :=
      det_cauchyMatrix_eq_zero_of_eq_x x y (Fin.succ_ne_zero i).symm hi.symm
    have hprod : (∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) = 0 := by
      refine prod_eq_zero (mem_univ i) ?_
      simp [hi]
    simp [hdet, hprod]
  by_cases hy : ∃ i : Fin n, y i.succ = y 0
  · obtain ⟨i, hi⟩ := hy
    have hdet : (cauchyMatrix x y).det = 0 :=
      det_cauchyMatrix_eq_zero_of_eq_y x y (Fin.succ_ne_zero i).symm hi.symm
    have hprod : (∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) = 0 := by
      refine prod_eq_zero (mem_univ i) ?_
      simp [hi]
    simp [hdet, hprod]
  -- Row ops: subtract row 0 from later rows.
  let A : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    .of fun i j =>
      Fin.cases (x 0 + y j)⁻¹ (fun i => (x i.succ + y j)⁻¹ - (x 0 + y j)⁻¹) i
  have hA_det : (cauchyMatrix x y).det = A.det := by
    refine det_eq_of_forall_row_eq_smul_add_const
      (fun i : Fin (n + 1) => Fin.cases (0 : R) (fun _ => 1) i) 0 ?_ ?_
    · rfl
    · intro i j
      refine Fin.cases ?_ (fun i => ?_) i
      · simp [A, cauchyMatrix]
      · simp only [cauchyMatrix_apply, A, of_apply, Fin.cases_succ, Fin.cases_zero]
        ring
  -- Factor `(x 0 + y j)⁻¹` from columns of `A`.
  let B : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    .of fun i j =>
      Fin.cases (1 : R) (fun i => (x 0 - x i.succ) * (x i.succ + y j)⁻¹) i
  have hAB : A = .of fun i j => (x 0 + y j)⁻¹ * B i j := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [A, B]
    · have hrow := cauchy_rowDiff x y i j (h 0 j) (h i.succ j)
      simp only [A, B, of_apply, Fin.cases_succ]
      rw [hrow, mul_inv]
      ring
  have hA_factor : A.det = (∏ j : Fin (n + 1), (x 0 + y j)⁻¹) * B.det := by
    rw [hAB]
    exact det_mul_row (fun j => (x 0 + y j)⁻¹) B
  -- Factor `(x 0 - x i.succ)` from later rows of `B`.
  let r : Fin (n + 1) → R := Fin.cases 1 (fun i => x 0 - x i.succ)
  let C : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    .of fun i j => Fin.cases (1 : R) (fun i => (x i.succ + y j)⁻¹) i
  have hBC : B = .of fun i j => r i * C i j := by
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [B, C, r]
    · simp [B, C, r]
  have hB_factor : B.det = (∏ i : Fin (n + 1), r i) * C.det := by
    rw [hBC]
    exact det_mul_column r C
  have hr_prod : (∏ i : Fin (n + 1), r i) = ∏ i : Fin n, (x 0 - x i.succ) := by
    rw [Fin.prod_univ_succ]
    simp [r]
  -- Column ops on `C`: subtract column 0 from later columns.
  let D : Matrix (Fin (n + 1)) (Fin (n + 1)) R :=
    .of fun i j => Fin.cases (C i 0) (fun j => C i j.succ - C i 0) j
  have hC_det : C.det = D.det := by
    refine det_eq_of_forall_col_eq_smul_add_const
      (fun j : Fin (n + 1) => Fin.cases (0 : R) (fun _ => 1) j) 0 ?_ ?_
    · rfl
    · intro i j
      refine Fin.cases ?_ (fun j => ?_) j
      · simp [D]
      · simp only [D, of_apply, Fin.cases_succ, Fin.cases_zero]
        ring
  have hD00 : D 0 0 = 1 := by
    simp [D, C]
  have hD0 : ∀ j : Fin n, D 0 j.succ = 0 := by
    intro j
    simp [D, C]
  have hD_expand : D.det = (D.submatrix Fin.succ Fin.succ).det := by
    rw [det_succ_row_zero]
    refine (sum_eq_single (0 : Fin (n + 1)) ?_ ?_).trans ?_
    · intro j _ hj
      obtain ⟨j, rfl⟩ := Fin.eq_succ_of_ne_zero hj
      simp [hD0]
    · intro h0
      exact (h0 (mem_univ _)).elim
    · simp [hD00, Fin.succAbove_zero]
  -- Remaining block: factor `(y 0 - y j.succ)` and `(x i.succ + y 0)⁻¹`.
  have hP :
      D.submatrix Fin.succ Fin.succ =
        .of fun i j =>
          (x i.succ + y 0)⁻¹ * (y 0 - y j.succ) *
            cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j := by
    ext i j
    have hcol := cauchy_colDiff x y i j (h i.succ 0) (h i.succ j.succ)
    simp only [submatrix_apply, of_apply, cauchyMatrix_apply, Function.comp_apply, D, C,
      Fin.cases_succ]
    rw [hcol, mul_inv]
    ring
  have hP_det :
      (D.submatrix Fin.succ Fin.succ).det =
        (∏ i : Fin n, (x i.succ + y 0)⁻¹) *
          (∏ j : Fin n, (y 0 - y j.succ)) *
            (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det := by
    rw [hP]
    have hshape :
        (Matrix.of fun i j =>
          (x i.succ + y 0)⁻¹ * (y 0 - y j.succ) *
            cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j) =
        Matrix.of fun i j =>
          (x i.succ + y 0)⁻¹ *
            (Matrix.of fun i j =>
              (y 0 - y j.succ) * cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ) i j) i j := by
      ext i j
      simp [mul_assoc]
    rw [hshape, det_mul_column (fun i : Fin n => (x i.succ + y 0)⁻¹),
      det_mul_row (fun j : Fin n => y 0 - y j.succ)
        (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)), ← mul_assoc]
  rw [hA_det, hA_factor, hB_factor, hr_prod, hC_det, hD_expand, hP_det]
  simp only [prod_mul_distrib, prod_inv_distrib, mul_assoc, mul_left_comm, mul_comm]

/-! ## C3: general-`n` Cauchy determinant -/

theorem det_cauchyMatrix_mul {n : ℕ} (x y : Fin n → R)
    (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det * cauchyDetDen x y = cauchyDetNum x y := by
  induction n with
  | zero =>
    simp [det_cauchy_fin_zero, cauchyDetDen_zero, cauchyDetNum_zero]
  | succ n ih =>
    have hQ : (∏ j : Fin (n + 1), (x 0 + y j)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun j _ => h 0 j
    have hU : (∏ i : Fin n, (x i.succ + y 0)) ≠ 0 :=
      prod_ne_zero_iff.mpr fun i _ => h i.succ 0
    rw [det_cauchyMatrix_succ x y h, cauchyDetDen_succ, cauchyDetNum_succ]
    have hcancel :
        ((∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) *
            (∏ j : Fin (n + 1), (x 0 + y j))⁻¹ *
              (∏ i : Fin n, (x i.succ + y 0))⁻¹ *
                (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det) *
          ((∏ j : Fin (n + 1), (x 0 + y j)) *
            (∏ i : Fin n, (x i.succ + y 0)) *
              cauchyDetDen (x ∘ Fin.succ) (y ∘ Fin.succ)) =
        (∏ i : Fin n, (x 0 - x i.succ) * (y 0 - y i.succ)) *
          (cauchyMatrix (x ∘ Fin.succ) (y ∘ Fin.succ)).det *
            cauchyDetDen (x ∘ Fin.succ) (y ∘ Fin.succ) := by
      field_simp [hQ, hU]
    rw [hcancel, mul_assoc,
      ih (x ∘ Fin.succ) (y ∘ Fin.succ) (fun i j => h i.succ j.succ),
      cauchy_succ_factor_sign]

theorem det_cauchyMatrix {n : ℕ} (x y : Fin n → R)
    (h : ∀ i j, x i + y j ≠ 0) :
    (cauchyMatrix x y).det = cauchyDetNum x y / cauchyDetDen x y := by
  rw [eq_div_iff (cauchyDetDen_ne_zero x y h)]
  exact det_cauchyMatrix_mul x y h

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
