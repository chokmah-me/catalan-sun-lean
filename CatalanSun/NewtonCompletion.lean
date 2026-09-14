/-
  CatalanSun/NewtonCompletion.lean

  Sorry-free prefix of Proposition 3.1 (Newton completion / fixed scalar) from
  Sun arXiv:2609.04176v1 §3. Does **not** prove the full identity
  `det Atilde = ± F_B * det R[A,J]` (needs permutation + 3× Laplace expansion).
-/

import CatalanSun.NewtonDiff
import CatalanSun.Residual
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.NewtonCompletion

open Matrix Finset Nat
open scoped fwdDiff
open CatalanSun

/-! ## Dimensions and the fixed factorial scalar `F_B` -/

/-- Matrix size `N = 2B + S + 3` (paper (3.1)). -/
def Ndim (B S : ℕ) : ℕ := 2 * B + S + 3

/-- Reference-block width `D = 2B`. -/
def Dref (B : ℕ) : ℕ := 2 * B

/-- Paper scalar `F_B = ∏_{r=0}^{2B-1} r!` (eq. (3.3)). -/
def F_B (B : ℕ) : ℕ :=
  ∏ r ∈ range (2 * B), r.factorial

theorem F_B_ne_zero (B : ℕ) : ((F_B B : ℕ) : ℝ) ≠ 0 := by
  refine Nat.cast_ne_zero.mpr ?_
  refine prod_ne_zero_iff.mpr ?_
  intro r _
  exact factorial_ne_zero r

/-! ## Finite-difference transform `DiffMat` -/

/-- Lower-triangular finite-difference matrix: row `n`, column `i` is
`(-1)^i C(n,i)` when `i ≤ n`, else `0`. Applying `DiffMat *ᵥ f` recovers the
paper operator `(Df)_n = ∑_{i=0}^n (-1)^i C(n,i) f_i`. -/
def DiffMat (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  Matrix.of fun n i =>
    if i.val ≤ n.val then (-1 : ℝ) ^ i.val * (n.val.choose i.val : ℝ) else 0

theorem DiffMat_diag {N : ℕ} (n : Fin N) :
    DiffMat N n n = (-1 : ℝ) ^ n.val := by
  simp [DiffMat, choose_self]

/-- `DiffMat` is lower-triangular (`BlockTriangular ⇑toDual`). -/
theorem blockTriangular_DiffMat (N : ℕ) :
    (DiffMat N).BlockTriangular (⇑OrderDual.toDual : Fin N → (Fin N)ᵒᵈ) := by
  intro i j hij
  have : j.val > i.val := (OrderDual.toDual_lt_toDual).1 hij
  simp only [DiffMat, of_apply, ite_eq_right_iff]
  intro hle
  omega

/-- `det DiffMat = ∏_n (-1)^n`, hence `±1`. -/
theorem det_DiffMat (N : ℕ) :
    (DiffMat N).det = ∏ n : Fin N, (-1 : ℝ) ^ n.val := by
  rw [det_of_lowerTriangular (DiffMat N) (blockTriangular_DiffMat N)]
  exact prod_congr rfl fun n _ => DiffMat_diag n

theorem sum_fin_val (N : ℕ) : (∑ n : Fin N, n.val) = N * (N - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range (fun k => k) N, sum_range_id]

theorem det_DiffMat_eq_neg_one_pow (N : ℕ) :
    (DiffMat N).det = (-1 : ℝ) ^ (N * (N - 1) / 2) := by
  rw [det_DiffMat, prod_pow_eq_pow_sum, sum_fin_val]

theorem isUnit_det_DiffMat (N : ℕ) : IsUnit (DiffMat N).det := by
  rw [det_DiffMat]
  refine IsUnit.prod_univ_iff.mpr ?_
  intro n
  exact (isUnit_neg_one (α := ℝ)).pow _

/-! ## Paper alternating sum on `ℕ → ℝ`, linked to `DiffMat *ᵥ` -/

/-- Paper finite-difference sum `(Df)_n = ∑_{i=0}^n (-1)^i C(n,i) f(i)`. -/
def paperSum (f : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ i ∈ range (n + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) * f i

/-- Extend a `Fin N → ℝ` vector by zero outside `0..N-1`. -/
def extendFin {N : ℕ} (f : Fin N → ℝ) : ℕ → ℝ :=
  fun i => if h : i < N then f ⟨i, h⟩ else 0

theorem DiffMat_mulVec_eq_paperSum {N : ℕ} (f : Fin N → ℝ) (n : Fin N) :
    (DiffMat N *ᵥ f) n = paperSum (extendFin f) n.val := by
  simp only [mulVec, dotProduct, DiffMat, of_apply, paperSum, extendFin, ite_mul,
    zero_mul]
  have hfilter :
      (∑ j : Fin N,
          if j.val ≤ n.val then
            (-1 : ℝ) ^ j.val * (n.val.choose j.val : ℝ) * f j
          else 0) =
        ∑ j ∈ univ.filter (fun j : Fin N => j.val ≤ n.val),
          (-1 : ℝ) ^ j.val * (n.val.choose j.val : ℝ) * f j := by
    simp [sum_filter]
  rw [hfilter]
  refine sum_bij (fun j _ => j.val) ?mem ?inj ?surj ?eq
  · intro j hj
    simp only [mem_filter, mem_univ, true_and, mem_range] at hj ⊢
    omega
  · intro a _ha b _hb h
    exact Fin.ext h
  · intro i hi
    simp only [mem_range] at hi
    refine ⟨⟨i, by omega⟩, ?_, rfl⟩
    simp only [mem_filter, mem_univ, true_and]
    omega
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    have : j.val < N := j.isLt
    simp [this]

/-! ## Power-column pivots on the `D`-block -/

/-- Monomial column `i ↦ i^r` as a sequence on `ℕ`. -/
def powSeq (r : ℕ) : ℕ → ℝ :=
  fun i => (i : ℝ) ^ r

theorem paperSum_pow_eq_fwdDiff (n r : ℕ) :
    paperSum (powSeq r) n =
      (-1 : ℝ) ^ n * (fwdDiff (1 : ℝ))^[n] (fun x : ℝ => x ^ r) 0 := by
  simpa [paperSum, powSeq] using
    NewtonDiff.alternating_sum_at_zero_eq_neg_pow_fwdDiff
      (fun x : ℝ => x ^ r) n

theorem DiffMat_mulVec_pow {N r : ℕ} (n : Fin N) :
    (DiffMat N *ᵥ fun i : Fin N => (i.val : ℝ) ^ r) n =
      paperSum (powSeq r) n.val := by
  rw [DiffMat_mulVec_eq_paperSum]
  unfold paperSum
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ n.val := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hiN : i < N := Nat.lt_of_le_of_lt hi' n.isLt
  simp [extendFin, powSeq, hiN]

theorem DiffMat_mulVec_pow_of_lt {N r : ℕ} {n : Fin N} (hr : r < n.val) :
    (DiffMat N *ᵥ fun i : Fin N => (i.val : ℝ) ^ r) n = 0 := by
  rw [DiffMat_mulVec_pow, paperSum_pow_eq_fwdDiff,
    fwdDiff_iter_pow_eq_zero_of_lt (R := ℝ) hr]
  simp

theorem DiffMat_mulVec_pow_diag {N r : ℕ} (hr : r < N) :
    (DiffMat N *ᵥ fun i : Fin N => (i.val : ℝ) ^ r) ⟨r, hr⟩ =
      (-1 : ℝ) ^ r * (r.factorial : ℝ) := by
  rw [DiffMat_mulVec_pow, paperSum_pow_eq_fwdDiff]
  have h := congrFun (fwdDiff_iter_eq_factorial (R := ℝ) (n := r)) (0 : ℝ)
  -- `n!` as ℝ-valued constant function at 0
  have h' : (fwdDiff (1 : ℝ))^[r] (fun x : ℝ => x ^ r) 0 = (r.factorial : ℝ) := by
    simpa [nsmul_eq_mul] using h
  rw [h']

/-- `D × D` block of power columns after `DiffMat` (upper-triangular).
Zeros below the diagonal: entry `(n,r) = 0` when `r < n`. -/
def powerDiffBlock (D : ℕ) : Matrix (Fin D) (Fin D) ℝ :=
  Matrix.of fun n r =>
    (DiffMat D *ᵥ fun i : Fin D => (i.val : ℝ) ^ r.val) n

theorem powerDiffBlock_triangular (D : ℕ) :
    (powerDiffBlock D).BlockTriangular (id : Fin D → Fin D) := by
  intro i j hij
  simp only [powerDiffBlock, of_apply]
  exact DiffMat_mulVec_pow_of_lt hij

theorem powerDiffBlock_diag {D : ℕ} (r : Fin D) :
    powerDiffBlock D r r = (-1 : ℝ) ^ r.val * (r.val.factorial : ℝ) := by
  simp only [powerDiffBlock, of_apply]
  exact DiffMat_mulVec_pow_diag r.isLt

/-- Sign convention: `det(powerDiffBlock D) = (-1)^{D(D-1)/2} · ∏_{r<D} r!`. -/
theorem det_powerDiffBlock (D : ℕ) :
    (powerDiffBlock D).det =
      (-1 : ℝ) ^ (D * (D - 1) / 2) * (∏ r ∈ range D, (r.factorial : ℝ)) := by
  rw [det_of_upperTriangular (powerDiffBlock_triangular D)]
  have hdiag :
      (∏ r : Fin D, powerDiffBlock D r r) =
        ∏ r : Fin D, ((-1 : ℝ) ^ r.val * (r.val.factorial : ℝ)) :=
    prod_congr rfl fun r _ => powerDiffBlock_diag r
  rw [hdiag, prod_mul_distrib, prod_pow_eq_pow_sum, sum_fin_val]
  congr 1
  exact Fin.prod_univ_eq_prod_range (fun r => (r.factorial : ℝ)) D

/-- Specialization at `D = 2B`: det equals `(-1)^{B(2B-1)} · (F_B : ℝ)`. -/
theorem det_powerDiffBlock_Dref (B : ℕ) :
    (powerDiffBlock (Dref B)).det =
      (-1 : ℝ) ^ (B * (2 * B - 1)) * (F_B B : ℝ) := by
  rw [det_powerDiffBlock, Dref, F_B]
  push_cast
  have hexp : (2 * B) * (2 * B - 1) / 2 = B * (2 * B - 1) := by
    cases B with
    | zero => simp
    | succ b =>
      have hodd : 2 * (b + 1) - 1 = 2 * b + 1 := by omega
      rw [hodd]
      -- 2*(b+1)*(2b+1)/2 = (b+1)*(2b+1)
      have hassoc : 2 * (b + 1) * (2 * b + 1) = 2 * ((b + 1) * (2 * b + 1)) := by
        ring
      rw [hassoc, Nat.mul_div_cancel_left _ (by omega : 0 < 2)]
  rw [hexp]

/-! ## Auxiliary binomial columns → signed unit vectors -/

/-- Binomial sequence `i ↦ C(i, m)`. -/
def binomSeq (m : ℕ) : ℕ → ℝ :=
  fun i => (i.choose m : ℝ)

private theorem fwdDiff_iter_choose_cast (m n : ℕ) :
    (fwdDiff (1 : ℕ))^[n] (fun x : ℕ => (x.choose m : ℝ)) 0 =
      (((fwdDiff (1 : ℕ))^[n] (fun x : ℕ => (x.choose m : ℤ)) 0 : ℤ) : ℝ) := by
  rw [fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)),
      fwdDiff_iter_eq_sum_shift (h := (1 : ℕ))]
  push_cast
  refine sum_congr rfl fun k _ => ?_
  simp only [nsmul_one, zero_add, zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- Paper alternating sum on binomial columns:
`∑_i (-1)^i C(n,i) C(i,m) = (-1)^n δ_{n,m}`. -/
theorem alternating_sum_choose (n m : ℕ) :
    paperSum (binomSeq m) n =
      if n = m then (-1 : ℝ) ^ n else 0 := by
  have hNC :=
    NewtonDiff.newtonCoeff_eq_paperFwdDiff (K := ℝ) (binomSeq m) n
  have hpaper :
      NewtonDiff.paperFwdDiff (binomSeq m) n =
        (-1 : ℝ) ^ n * NewtonDiff.newtonCoeff (binomSeq m) n := by
    calc NewtonDiff.paperFwdDiff (binomSeq m) n
        = ((-1 : ℝ) ^ n * (-1 : ℝ) ^ n) *
            NewtonDiff.paperFwdDiff (binomSeq m) n := by
            rw [NewtonDiff.neg_one_pow_mul_self, one_mul]
      _ = (-1 : ℝ) ^ n *
            ((-1 : ℝ) ^ n * NewtonDiff.paperFwdDiff (binomSeq m) n) := by
            ring
      _ = (-1 : ℝ) ^ n * NewtonDiff.newtonCoeff (binomSeq m) n := by
            rw [← hNC]
  -- paperSum = paperFwdDiff on binomSeq
  have hdef : paperSum (binomSeq m) n = NewtonDiff.paperFwdDiff (binomSeq m) n := by
    rfl
  have hΔ : NewtonDiff.newtonCoeff (binomSeq m) n =
      (fwdDiff (1 : ℕ))^[n] (fun x : ℕ => (x.choose m : ℝ)) 0 := rfl
  rw [hdef, hpaper, hΔ, fwdDiff_iter_choose_cast, fwdDiff_iter_choose_zero]
  split_ifs <;> simp

theorem DiffMat_mulVec_binom {N m : ℕ} (_hm : m < N) (n : Fin N) :
    (DiffMat N *ᵥ fun i : Fin N => (i.val.choose m : ℝ)) n =
      if n.val = m then (-1 : ℝ) ^ m else 0 := by
  rw [DiffMat_mulVec_eq_paperSum]
  have hEq : paperSum (extendFin (fun i : Fin N => (i.val.choose m : ℝ))) n.val =
      paperSum (binomSeq m) n.val := by
    unfold paperSum
    refine sum_congr rfl fun i hi => ?_
    have hi' : i ≤ n.val := Nat.lt_succ_iff.mp (mem_range.mp hi)
    have hiN : i < N := Nat.lt_of_le_of_lt hi' n.isLt
    simp [extendFin, binomSeq, hiN]
  rw [hEq, alternating_sum_choose]
  split_ifs with h0
  · rw [h0]
  · rfl

/-- After `DiffMat`, the binomial column of order `m` is the signed standard
basis vector `(-1)^m e_m`. -/
theorem DiffMat_mulVec_binom_eq_signed_basis {N m : ℕ} (hm : m < N) :
    (fun n : Fin N =>
        (DiffMat N *ᵥ fun i : Fin N => (i.val.choose m : ℝ)) n) =
      fun n : Fin N => if n.val = m then (-1 : ℝ) ^ m else 0 := by
  ext n
  exact DiffMat_mulVec_binom hm n

/-- Column form of the signed-basis fact. -/
def binomCol (N m : ℕ) : Fin N → ℝ :=
  fun i => (i.val.choose m : ℝ)

theorem DiffMat_mulVec_binomCol {N m : ℕ} (hm : m < N) :
    DiffMat N *ᵥ binomCol N m =
      fun n : Fin N => if n.val = m then (-1 : ℝ) ^ m else 0 :=
  DiffMat_mulVec_binom_eq_signed_basis hm

/-! ## Omitted residual rows and Newton-completed matrices -/

/-- Three omitted residual-row indices `Ac = {c₁,c₂,c₃} ⊂ {0,…,S+2}`,
packaged as an injective map `Fin 3 → Fin (S+3)`. -/
def OmittedRows (S : ℕ) : Type :=
  { o : Fin 3 → Fin (S + 3) // Function.Injective o }

/-- Column index decoding for the Newton-completed `N × N` layout:
reference powers `0..D-1`, residual targets `D..D+S-1`, binomial aux
`D+S..D+S+2`. -/
def colKind (B S : ℕ) (j : Fin (Ndim B S)) :
    (Fin (Dref B)) ⊕ (Fin S) ⊕ (Fin 3) :=
  if hj : j.val < Dref B then Sum.inl ⟨j.val, hj⟩
  else if hj' : j.val < Dref B + S then
    Sum.inr (Sum.inl ⟨j.val - Dref B, by omega⟩)
  else
    Sum.inr (Sum.inr ⟨j.val - Dref B - S, by
      have : j.val < Ndim B S := j.isLt
      simp only [Ndim, Dref] at this ⊢
      omega⟩)

/-- Paper matrix `Ã_B` (eAB): columns are powers `i^r` (`r < D`), residual
targets `Πᵢ u_{i+j}` (`1 ≤ j ≤ S`), and binomials `C(i, D+cₜ)`. -/
def Atilde (B S : ℕ) (o : Fin 3 → Fin (S + 3)) :
    Matrix (Fin (Ndim B S)) (Fin (Ndim B S)) ℝ :=
  Matrix.of fun i j =>
    match colKind B S j with
    | Sum.inl r => (i.val : ℝ) ^ r.val
    | Sum.inr (Sum.inl jj) =>
        (TwoAdic.PiFactor B i.val : ℝ) *
          Tail.weightedTail (i.val + (jj.val + 1))
    | Sum.inr (Sum.inr t) =>
        (i.val.choose (Dref B + (o t).val) : ℝ)

/-- Paper matrix `A_B` (Ahat): row-`i` reference/aux entries of `Atilde`
divided by `Πᵢ`; target columns left as `u_{i+j}`. -/
def Ahat (B S : ℕ) (o : Fin 3 → Fin (S + 3)) :
    Matrix (Fin (Ndim B S)) (Fin (Ndim B S)) ℝ :=
  Matrix.of fun i j =>
    match colKind B S j with
    | Sum.inl r =>
        (i.val : ℝ) ^ r.val / (TwoAdic.PiFactor B i.val : ℝ)
    | Sum.inr (Sum.inl jj) =>
        Tail.weightedTail (i.val + (jj.val + 1))
    | Sum.inr (Sum.inr t) =>
        (i.val.choose (Dref B + (o t).val) : ℝ) /
          (TwoAdic.PiFactor B i.val : ℝ)

theorem PiFactor_cast_ne_zero (B i : ℕ) :
    ((TwoAdic.PiFactor B i : ℕ) : ℝ) ≠ 0 := by
  obtain ⟨k, hk⟩ := TwoAdic.odd_PiFactor B i
  exact Nat.cast_ne_zero.mpr (by omega)

theorem Atilde_eq_Pi_mul_Ahat (B S : ℕ) (o : Fin 3 → Fin (S + 3)) :
    Atilde B S o =
      Matrix.of fun i j =>
        (TwoAdic.PiFactor B i.val : ℝ) * Ahat B S o i j := by
  ext i j
  simp only [Atilde, Ahat, of_apply]
  cases h : colKind B S j with
  | inl r =>
      simp only [h]
      have hπ := PiFactor_cast_ne_zero B i.val
      field_simp [hπ]
  | inr rest =>
      cases rest with
      | inl jj =>
          simp [h]
      | inr t =>
          simp only [h]
          have hπ := PiFactor_cast_ne_zero B i.val
          field_simp [hπ]

/-- Row-scaling identity (paper (3.2)):
`det Atilde = (∏ᵢ Πᵢ) · det Ahat`. -/
theorem det_Atilde_eq_Pi_mul_det_Ahat (B S : ℕ) (o : Fin 3 → Fin (S + 3)) :
    (Atilde B S o).det =
      (∏ i : Fin (Ndim B S), (TwoAdic.PiFactor B i.val : ℝ)) *
        (Ahat B S o).det := by
  have h := congrArg Matrix.det (Atilde_eq_Pi_mul_Ahat B S o)
  rw [h]
  exact det_mul_column
    (fun i : Fin (Ndim B S) => (TwoAdic.PiFactor B i.val : ℝ))
    (Ahat B S o)

/-! ## Target bridge: residual rows of `DiffMat *ᵥ (Π · u_{·+j})` -/

theorem DiffMat_mulVec_Pi_u_eq_Rmatrix (B S α j : ℕ) (hα : α ≤ S + 2) :
    (DiffMat (Ndim B S) *ᵥ fun i : Fin (Ndim B S) =>
        (TwoAdic.PiFactor B i.val : ℝ) * Tail.weightedTail (i.val + j))
      ⟨α + 2 * B, by simp only [Ndim]; omega⟩ =
      Residual.Rmatrix B α j := by
  set f : Fin (Ndim B S) → ℝ :=
    fun i => (TwoAdic.PiFactor B i.val : ℝ) * Tail.weightedTail (i.val + j)
  set n : Fin (Ndim B S) := ⟨α + 2 * B, by simp only [Ndim]; omega⟩
  have hn : n.val = α + 2 * B := rfl
  rw [DiffMat_mulVec_eq_paperSum f n]
  simp only [Residual.Rmatrix, paperSum, extendFin, f, n, hn]
  refine sum_congr rfl fun i hi => ?_
  have hi' : i ≤ α + 2 * B := Nat.lt_succ_iff.mp (mem_range.mp hi)
  have hiN : i < Ndim B S := by simp only [Ndim]; omega
  simp [hiN]
  ring

end CatalanSun.NewtonCompletion
