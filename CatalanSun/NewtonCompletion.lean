/-
  CatalanSun/NewtonCompletion.lean

  Proposition 3.1 (Newton completion / fixed scalar) from Sun arXiv:2609.04176v1 §3.
  Spine: `M = DiffMat * Atilde` → column facts → reindex to fromBlocks →
  `det_fromBlocks` → `det_mul` back to `Atilde`.
-/

import CatalanSun.NewtonDiff
import CatalanSun.Residual
import CatalanSun.Rank
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Sum.Basic
import Mathlib.Logic.Equiv.Fin.Basic
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

/-- For `B ≥ 2`, `2 ∈ range (2B)` and `2 ∣ 2!`, so `2 ∣ F_B` and `v₂(F_B) > 0`.
(Spec wrote `1 ≤ B`; at `B = 1` one has `F_B = 1` and the valuation is zero.) -/
theorem padicValNat_two_F_B_pos {B : ℕ} (hB : 2 ≤ B) :
    0 < padicValNat 2 (F_B B) := by
  have h2mem : 2 ∈ range (2 * B) := by
    rw [mem_range]
    omega
  have hfac : 2 ∣ Nat.factorial 2 := Nat.dvd_factorial (by decide : 0 < 2) le_rfl
  have hdiv : 2 ∣ F_B B :=
    dvd_trans hfac (dvd_prod_of_mem (fun r : ℕ => r.factorial) h2mem)
  have hne : F_B B ≠ 0 := Nat.cast_ne_zero.mp (F_B_ne_zero B)
  exact Nat.pos_of_ne_zero
    (one_le_iff_ne_zero.mp (one_le_padicValNat_of_dvd (p := 2) hne hdiv))

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

/-! ## P0: selected residual rows and block index equivalences -/

lemma Ndim_eq_Dref_add (B S : ℕ) : Dref B + (S + 3) = Ndim B S := by
  simp only [Ndim, Dref]; omega

/-- The three omitted residual-row indices as a finset. -/
def omittedFinset {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Finset (Fin (S + 3)) :=
  Finset.univ.map ⟨o, ho⟩

theorem omittedFinset_card {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    (omittedFinset o ho).card = 3 := by
  simp [omittedFinset, card_map, Fintype.card_fin]

/-- Selected residual rows `A = {0,…,S+2} \ Ac`. -/
def selectedFinset {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Finset (Fin (S + 3)) :=
  Finset.univ \ omittedFinset o ho

theorem selectedFinset_card {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    (selectedFinset o ho).card = S := by
  simp only [selectedFinset]
  rw [card_sdiff_of_subset (subset_univ _), omittedFinset_card]
  simp [Fintype.card_fin]

/-- Ordered enumeration of the selected residual rows (`Finset.orderEmbOfFin`). -/
def selectedRows {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Fin S → Fin (S + 3) :=
  (selectedFinset o ho).orderEmbOfFin (selectedFinset_card o ho)

theorem selectedRows_mem {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (j : Fin S) : selectedRows o ho j ∈ selectedFinset o ho :=
  (selectedFinset o ho).orderEmbOfFin_mem (selectedFinset_card o ho) j

theorem selectedRows_not_omitted {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (j : Fin S) : selectedRows o ho j ∉ omittedFinset o ho := by
  have h := selectedRows_mem o ho j
  simp only [selectedFinset, mem_sdiff] at h
  exact h.2

theorem o_mem_omitted {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (t : Fin 3) : o t ∈ omittedFinset o ho :=
  mem_map.mpr ⟨t, mem_univ t, rfl⟩

theorem selectedRows_ne_o {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (j : Fin S) (t : Fin 3) : selectedRows o ho j ≠ o t := by
  intro h
  exact selectedRows_not_omitted o ho j (h ▸ o_mem_omitted o ho t)

theorem selectedRows_injective {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Function.Injective (selectedRows o ho) :=
  ((selectedFinset o ho).orderEmbOfFin (selectedFinset_card o ho)).injective

/-- Embed a residual index `α ∈ Fin (S+3)` as matrix row `D+α`. -/
def residualRow (B S : ℕ) (α : Fin (S + 3)) : Fin (Ndim B S) :=
  ⟨α.val + Dref B, by simp only [Ndim, Dref]; omega⟩

theorem residualRow_val (B S : ℕ) (α : Fin (S + 3)) :
    (residualRow B S α).val = α.val + Dref B :=
  rfl

/-- `Fin S ⊕ Fin 3 ≃ Fin (S+3)` via selected rows and omitted map `o`. -/
def selectedOmitEquiv {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Fin S ⊕ Fin 3 ≃ Fin (S + 3) := by
  classical
  refine Equiv.ofBijective (Sum.elim (selectedRows o ho) o) ⟨?inj, ?surj⟩
  · exact (selectedRows_injective o ho).sumElim ho fun j t => selectedRows_ne_o o ho j t
  · intro α
    by_cases hα : α ∈ omittedFinset o ho
    · obtain ⟨t, _, ht⟩ := mem_map.mp hα
      exact ⟨Sum.inr t, ht⟩
    · have hsel : α ∈ selectedFinset o ho := by
        simp only [selectedFinset, mem_sdiff, mem_univ, true_and, hα, not_false_eq_true]
      have hrang : α ∈ Set.range (selectedRows o ho) := by
        change α ∈ Set.range ((selectedFinset o ho).orderEmbOfFin (selectedFinset_card o ho))
        rw [(selectedFinset o ho).range_orderEmbOfFin (selectedFinset_card o ho)]
        exact hsel
      obtain ⟨j, hj⟩ := hrang
      exact ⟨Sum.inl j, hj⟩

theorem selectedOmitEquiv_inl {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (j : Fin S) : selectedOmitEquiv o ho (Sum.inl j) = selectedRows o ho j :=
  rfl

theorem selectedOmitEquiv_inr {S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (t : Fin 3) : selectedOmitEquiv o ho (Sum.inr t) = o t :=
  rfl

/-- Natural size-cast `Fin (D+(S+3)) ≃ Fin N`. -/
def ndimCast (B S : ℕ) : Fin (Dref B + (S + 3)) ≃ Fin (Ndim B S) where
  toFun i := ⟨i.val, by have := i.isLt; simp only [Ndim, Dref] at this ⊢; omega⟩
  invFun i := ⟨i.val, by have := i.isLt; simp only [Ndim, Dref] at this ⊢; omega⟩
  left_inv i := Fin.ext rfl
  right_inv i := Fin.ext rfl

theorem ndimCast_val (B S : ℕ) (i : Fin (Dref B + (S + 3))) :
    (ndimCast B S i).val = i.val :=
  rfl

/-- Column index equiv matching `colKind` (powers / targets / aux). -/
def colEquiv (B S : ℕ) :
    Fin (Dref B) ⊕ (Fin S ⊕ Fin 3) ≃ Fin (Ndim B S) :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans
    (finSumFinEquiv.trans (ndimCast B S))

theorem colEquiv_inl (B S : ℕ) (r : Fin (Dref B)) :
    colEquiv B S (Sum.inl r) = ⟨r.val, by simp only [Ndim, Dref]; omega⟩ := by
  apply Fin.ext
  simp [colEquiv, ndimCast_val, finSumFinEquiv_apply_left]

theorem colEquiv_inr_inl (B S : ℕ) (j : Fin S) :
    colEquiv B S (Sum.inr (Sum.inl j)) =
      ⟨Dref B + j.val, by simp only [Ndim, Dref]; omega⟩ := by
  apply Fin.ext
  simp [colEquiv, ndimCast_val, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right]

theorem colEquiv_inr_inr (B S : ℕ) (t : Fin 3) :
    colEquiv B S (Sum.inr (Sum.inr t)) =
      ⟨Dref B + S + t.val, by simp only [Ndim, Dref]; omega⟩ := by
  apply Fin.ext
  simp [colEquiv, ndimCast_val, finSumFinEquiv_apply_right, Nat.add_assoc]

theorem colKind_colEquiv (B S : ℕ) (x : Fin (Dref B) ⊕ (Fin S ⊕ Fin 3)) :
    colKind B S (colEquiv B S x) = x := by
  cases x with
  | inl r =>
      have hr : (colEquiv B S (Sum.inl r)).val = r.val := by simp [colEquiv_inl]
      have hrlt : (colEquiv B S (Sum.inl r)).val < Dref B := by rw [hr]; exact r.isLt
      simp only [colKind, hrlt, ↓reduceDIte]
      exact congrArg Sum.inl (Fin.ext hr.symm)
  | inr y =>
      cases y with
      | inl j =>
          have hj : (colEquiv B S (Sum.inr (Sum.inl j))).val = Dref B + j.val := by
            simp [colEquiv_inr_inl]
          have h1 : ¬ (colEquiv B S (Sum.inr (Sum.inl j))).val < Dref B := by rw [hj]; omega
          have h2 : (colEquiv B S (Sum.inr (Sum.inl j))).val < Dref B + S := by rw [hj]; omega
          simp only [colKind, h1, ↓reduceDIte, h2]
          refine congrArg (fun z => Sum.inr (Sum.inl z)) (Fin.ext ?_)
          simp [hj]
      | inr t =>
          have ht : (colEquiv B S (Sum.inr (Sum.inr t))).val = Dref B + S + t.val := by
            simp [colEquiv_inr_inr]
          have h1 : ¬ (colEquiv B S (Sum.inr (Sum.inr t))).val < Dref B := by rw [ht]; omega
          have h2 : ¬ (colEquiv B S (Sum.inr (Sum.inr t))).val < Dref B + S := by rw [ht]; omega
          simp only [colKind, h1, ↓reduceDIte, h2]
          refine congrArg (fun z => Sum.inr (Sum.inr z)) (Fin.ext ?_)
          simp [ht]
          omega

theorem colEquiv_colKind (B S : ℕ) (j : Fin (Ndim B S)) :
    colEquiv B S (colKind B S j) = j := by
  simp only [colKind]
  split_ifs with hj hj' <;> apply Fin.ext
  · simp [colEquiv_inl]
  · simp [colEquiv_inr_inl]; omega
  · simp [colEquiv_inr_inr]
    have hjN : j.val < Ndim B S := j.isLt
    simp only [Ndim, Dref] at hjN hj hj' ⊢
    omega

theorem colEquiv_symm_eq_colKind (B S : ℕ) :
    ⇑(colEquiv B S).symm = colKind B S := by
  ext j
  apply (colEquiv B S).injective
  rw [Equiv.apply_symm_apply, colEquiv_colKind]

/-- Row index equiv: reference / selected residual / omitted residual. -/
def rowEquiv {B S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Fin (Dref B) ⊕ (Fin S ⊕ Fin 3) ≃ Fin (Ndim B S) :=
  (Equiv.sumCongr (Equiv.refl _) (selectedOmitEquiv o ho)).trans
    (finSumFinEquiv.trans (ndimCast B S))

theorem rowEquiv_inl {B S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (r : Fin (Dref B)) :
    rowEquiv (B := B) (S := S) o ho (Sum.inl r) =
      ⟨r.val, by simp only [Ndim, Dref]; omega⟩ := by
  apply Fin.ext
  simp [rowEquiv, ndimCast_val, finSumFinEquiv_apply_left]

theorem rowEquiv_inr_inl {B S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (j : Fin S) :
    rowEquiv (B := B) (S := S) o ho (Sum.inr (Sum.inl j)) =
      residualRow B S (selectedRows o ho j) := by
  apply Fin.ext
  simp [rowEquiv, ndimCast_val, residualRow, selectedOmitEquiv_inl,
    finSumFinEquiv_apply_right, Nat.add_comm]

theorem rowEquiv_inr_inr {B S : ℕ} (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o)
    (t : Fin 3) :
    rowEquiv (B := B) (S := S) o ho (Sum.inr (Sum.inr t)) =
      residualRow B S (o t) := by
  apply Fin.ext
  simp [rowEquiv, ndimCast_val, residualRow, selectedOmitEquiv_inr,
    finSumFinEquiv_apply_right, Nat.add_comm]

/-! ## P1: `AtildeDiff` and column characterizations -/

def AtildeDiff (B S : ℕ) (o : Fin 3 → Fin (S + 3)) :
    Matrix (Fin (Ndim B S)) (Fin (Ndim B S)) ℝ :=
  DiffMat (Ndim B S) * Atilde B S o

theorem AtildeDiff_apply (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (n j : Fin (Ndim B S)) :
    AtildeDiff B S o n j =
      (DiffMat (Ndim B S) *ᵥ fun i : Fin (Ndim B S) => Atilde B S o i j) n := by
  simp only [AtildeDiff, mul_apply', mulVec, dotProduct]

theorem Atilde_col_pow (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (r : Fin (Dref B)) (i : Fin (Ndim B S)) :
    Atilde B S o i (colEquiv B S (Sum.inl r)) = (i.val : ℝ) ^ r.val := by
  have hj : colKind B S (colEquiv B S (Sum.inl r)) = Sum.inl r := colKind_colEquiv B S _
  simp only [Atilde, of_apply, hj]

theorem Atilde_col_target (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (jj : Fin S) (i : Fin (Ndim B S)) :
    Atilde B S o i (colEquiv B S (Sum.inr (Sum.inl jj))) =
      (TwoAdic.PiFactor B i.val : ℝ) * Tail.weightedTail (i.val + (jj.val + 1)) := by
  have hj : colKind B S (colEquiv B S (Sum.inr (Sum.inl jj))) =
      Sum.inr (Sum.inl jj) := colKind_colEquiv B S _
  simp only [Atilde, of_apply, hj]

theorem Atilde_col_aux (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (t : Fin 3) (i : Fin (Ndim B S)) :
    Atilde B S o i (colEquiv B S (Sum.inr (Sum.inr t))) =
      (i.val.choose (Dref B + (o t).val) : ℝ) := by
  have hj : colKind B S (colEquiv B S (Sum.inr (Sum.inr t))) =
      Sum.inr (Sum.inr t) := colKind_colEquiv B S _
  simp only [Atilde, of_apply, hj]

theorem AtildeDiff_pow_residual (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (r : Fin (Dref B)) (α : Fin (S + 3)) :
    AtildeDiff B S o (residualRow B S α) (colEquiv B S (Sum.inl r)) = 0 := by
  rw [AtildeDiff_apply]
  have hcol :
      (fun i : Fin (Ndim B S) => Atilde B S o i (colEquiv B S (Sum.inl r))) =
        fun i => (i.val : ℝ) ^ r.val := by
    ext i; exact Atilde_col_pow B S o r i
  rw [hcol]
  exact DiffMat_mulVec_pow_of_lt (by simp [residualRow, Dref]; omega)

theorem AtildeDiff_pow_ref (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (n r : Fin (Dref B)) :
    AtildeDiff B S o ⟨n.val, by simp only [Ndim, Dref]; omega⟩
      (colEquiv B S (Sum.inl r)) =
      powerDiffBlock (Dref B) n r := by
  rw [AtildeDiff_apply, powerDiffBlock, of_apply]
  have hcol :
      (fun i : Fin (Ndim B S) => Atilde B S o i (colEquiv B S (Sum.inl r))) =
        fun i => (i.val : ℝ) ^ r.val := by
    ext i; exact Atilde_col_pow B S o r i
  rw [hcol]
  have hnN : n.val < Ndim B S := by simp only [Ndim, Dref]; omega
  have h1 := DiffMat_mulVec_pow (N := Ndim B S) (r := r.val) ⟨n.val, hnN⟩
  have h2 := DiffMat_mulVec_pow (N := Dref B) (r := r.val) n
  exact h1.trans h2.symm

theorem AtildeDiff_aux (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (t : Fin 3) (n : Fin (Ndim B S)) :
    AtildeDiff B S o n (colEquiv B S (Sum.inr (Sum.inr t))) =
      if n.val = Dref B + (o t).val then
        (-1 : ℝ) ^ (Dref B + (o t).val)
      else 0 := by
  rw [AtildeDiff_apply]
  have hcol :
      (fun i : Fin (Ndim B S) => Atilde B S o i (colEquiv B S (Sum.inr (Sum.inr t)))) =
        fun i => (i.val.choose (Dref B + (o t).val) : ℝ) := by
    ext i; exact Atilde_col_aux B S o t i
  rw [hcol]
  have hm : Dref B + (o t).val < Ndim B S := by simp only [Ndim, Dref]; omega
  simpa using DiffMat_mulVec_binom (N := Ndim B S) (m := Dref B + (o t).val) hm n

theorem AtildeDiff_aux_at_omitted (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (ho : Function.Injective o) (t t' : Fin 3) :
    AtildeDiff B S o (residualRow B S (o t)) (colEquiv B S (Sum.inr (Sum.inr t'))) =
      (if t = t' then (-1 : ℝ) ^ (Dref B + (o t).val) else 0) := by
  rw [AtildeDiff_aux, residualRow_val]
  by_cases ht : t = t'
  · subst ht
    simp [Nat.add_comm]
  · have hne : (o t).val ≠ (o t').val := fun hv => ht (ho (Fin.ext hv))
    have : (o t).val + Dref B ≠ Dref B + (o t').val := by intro h; exact hne (by omega)
    simp [ht, this]

theorem AtildeDiff_aux_at_selected (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (ho : Function.Injective o) (j : Fin S) (t : Fin 3) :
    AtildeDiff B S o (residualRow B S (selectedRows o ho j))
      (colEquiv B S (Sum.inr (Sum.inr t))) = 0 := by
  rw [AtildeDiff_aux, residualRow_val]
  have hne : (selectedRows o ho j).val ≠ (o t).val :=
    fun hv => selectedRows_ne_o o ho j t (Fin.ext hv)
  have : (selectedRows o ho j).val + Dref B ≠ Dref B + (o t).val := by
    intro h; exact hne (by omega)
  simp [this]

theorem AtildeDiff_target_residual (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (α : Fin (S + 3)) (jj : Fin S) :
    AtildeDiff B S o (residualRow B S α) (colEquiv B S (Sum.inr (Sum.inl jj))) =
      Residual.Rmatrix B α.val (jj.val + 1) := by
  rw [AtildeDiff_apply]
  have hcol :
      (fun i : Fin (Ndim B S) => Atilde B S o i (colEquiv B S (Sum.inr (Sum.inl jj)))) =
        fun i => (TwoAdic.PiFactor B i.val : ℝ) *
          Tail.weightedTail (i.val + (jj.val + 1)) := by
    ext i; exact Atilde_col_target B S o jj i
  rw [hcol]
  have hα : α.val ≤ S + 2 := Nat.le_of_lt_succ α.isLt
  have hrow : residualRow B S α = ⟨α.val + 2 * B, by simp only [Ndim]; omega⟩ := by
    apply Fin.ext; simp [residualRow, Dref]
  rw [hrow]
  exact DiffMat_mulVec_Pi_u_eq_Rmatrix B S α.val (jj.val + 1) hα

theorem AtildeDiff_target_selected (B S : ℕ) (o : Fin 3 → Fin (S + 3))
    (ho : Function.Injective o) (j jj : Fin S) :
    AtildeDiff B S o (residualRow B S (selectedRows o ho j))
      (colEquiv B S (Sum.inr (Sum.inl jj))) =
      Rank.RmatrixFin B S (selectedRows o ho j) jj := by
  rw [AtildeDiff_target_residual, Rank.RmatrixFin, of_apply]

/-! ## P2: reindex to nested `fromBlocks` -/

lemma neg_one_pow_eq_one_or_neg_one (n : ℕ) :
    (-1 : ℝ) ^ n = 1 ∨ (-1 : ℝ) ^ n = -1 := by
  cases Nat.even_or_odd n with
  | inl h => rw [Even.neg_one_pow h]; exact Or.inl rfl
  | inr h => rw [Odd.neg_one_pow h]; exact Or.inr rfl

lemma mul_one_or_neg_one {a b : ℝ}
    (ha : a = 1 ∨ a = -1) (hb : b = 1 ∨ b = -1) :
    a * b = 1 ∨ a * b = -1 := by
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> simp [ha, hb]

theorem prod_aux_sign_eq_one_or_neg_one (B : ℕ) {S : ℕ} (o : Fin 3 → Fin (S + 3)) :
    (∏ t : Fin 3, (-1 : ℝ) ^ (Dref B + (o t).val)) = 1 ∨
      (∏ t : Fin 3, (-1 : ℝ) ^ (Dref B + (o t).val)) = -1 := by
  classical
  simp only [Fin.prod_univ_three]
  exact mul_one_or_neg_one
    (mul_one_or_neg_one (neg_one_pow_eq_one_or_neg_one _) (neg_one_pow_eq_one_or_neg_one _))
    (neg_one_pow_eq_one_or_neg_one _)

def auxDiag (B : ℕ) {S : ℕ} (o : Fin 3 → Fin (S + 3)) : Matrix (Fin 3) (Fin 3) ℝ :=
  diagonal fun t => (-1 : ℝ) ^ (Dref B + (o t).val)

theorem det_auxDiag (B : ℕ) {S : ℕ} (o : Fin 3 → Fin (S + 3)) :
    (auxDiag B o).det = ∏ t : Fin 3, (-1 : ℝ) ^ (Dref B + (o t).val) := by
  simp [auxDiag, det_diagonal]

def junkTop (B S : ℕ) (o : Fin 3 → Fin (S + 3)) (_ho : Function.Injective o) :
    Matrix (Fin (Dref B)) (Fin S ⊕ Fin 3) ℝ :=
  Matrix.of fun n k =>
    AtildeDiff B S o ⟨n.val, by simp only [Ndim, Dref]; omega⟩ (colEquiv B S (Sum.inr k))

def junkBot (B S : ℕ) (o : Fin 3 → Fin (S + 3)) (_ho : Function.Injective o) :
    Matrix (Fin 3) (Fin S) ℝ :=
  Matrix.of fun t jj =>
    AtildeDiff B S o (residualRow B S (o t)) (colEquiv B S (Sum.inr (Sum.inl jj)))

def innerBlock (B S : ℕ) (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Matrix (Fin S ⊕ Fin 3) (Fin S ⊕ Fin 3) ℝ :=
  fromBlocks
    ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id)
    0
    (junkBot B S o ho)
    (auxDiag B o)

def outerBlock (B S : ℕ) (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    Matrix (Fin (Dref B) ⊕ (Fin S ⊕ Fin 3)) (Fin (Dref B) ⊕ (Fin S ⊕ Fin 3)) ℝ :=
  fromBlocks (powerDiffBlock (Dref B)) (junkTop B S o ho) 0 (innerBlock B S o ho)

theorem AtildeDiff_submatrix_eq_outerBlock (B S : ℕ)
    (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    (AtildeDiff B S o).submatrix
        (rowEquiv (B := B) (S := S) o ho) (colEquiv B S) =
      outerBlock B S o ho := by
  ext i j
  simp only [submatrix_apply, outerBlock, innerBlock, junkTop, junkBot]
  rcases i with r | rs <;> rcases j with c | cs
  · rw [fromBlocks_apply₁₁, rowEquiv_inl, AtildeDiff_pow_ref]
  · rw [fromBlocks_apply₁₂, rowEquiv_inl, of_apply]
  · rw [fromBlocks_apply₂₁, Matrix.zero_apply]
    rcases rs with jsel | tom
    · rw [rowEquiv_inr_inl, AtildeDiff_pow_residual]
    · rw [rowEquiv_inr_inr, AtildeDiff_pow_residual]
  · rw [fromBlocks_apply₂₂]
    rcases rs with jsel | tom <;> rcases cs with jtar | taux
    · rw [fromBlocks_apply₁₁, submatrix_apply, id_eq, rowEquiv_inr_inl,
        AtildeDiff_target_selected]
    · rw [fromBlocks_apply₁₂, Matrix.zero_apply, rowEquiv_inr_inl,
        AtildeDiff_aux_at_selected]
    · rw [fromBlocks_apply₂₁, rowEquiv_inr_inr, of_apply]
    · rw [fromBlocks_apply₂₂, rowEquiv_inr_inr, auxDiag, diagonal_apply]
      exact AtildeDiff_aux_at_omitted B S o ho tom taux

theorem det_outerBlock (B S : ℕ) (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    (outerBlock B S o ho).det =
      (powerDiffBlock (Dref B)).det *
        ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det *
          (auxDiag B o).det := by
  simp only [outerBlock, det_fromBlocks_zero₂₁, innerBlock, det_fromBlocks_zero₁₂]
  ring

theorem det_AtildeDiff_submatrix (B S : ℕ)
    (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      ((AtildeDiff B S o).submatrix
          (rowEquiv (B := B) (S := S) o ho) (colEquiv B S)).det =
        ε * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by
  rw [AtildeDiff_submatrix_eq_outerBlock, det_outerBlock, det_powerDiffBlock_Dref, det_auxDiag]
  refine ⟨(-1 : ℝ) ^ (B * (2 * B - 1)) *
      (∏ t : Fin 3, (-1 : ℝ) ^ (Dref B + (o t).val)), ?sign, by ring⟩
  exact mul_one_or_neg_one (neg_one_pow_eq_one_or_neg_one _)
    (prod_aux_sign_eq_one_or_neg_one B o)

/-! ## P3: transfer to `det Atilde` -/

lemma sign_cast_eq_one_or_neg_one {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) = 1 ∨
      (((Equiv.Perm.sign σ : ℤˣ) : ℤ) : ℝ) = -1 := by
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;> simp [h]

theorem det_AtildeDiff_eq_signed_F_B_det_R {B S : ℕ}
    (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (AtildeDiff B S o).det =
        ε * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by
  classical
  obtain ⟨ε₀, hε₀, hsub⟩ := det_AtildeDiff_submatrix B S o ho
  let eR := rowEquiv (B := B) (S := S) o ho
  let eC := colEquiv B S
  have hreindex :
      (AtildeDiff B S o).submatrix eR eC =
        (reindex eR.symm eC.symm) (AtildeDiff B S o) := by
    simp [reindex_apply]
  have hdet := det_reindex (R := ℝ) eR.symm eC.symm (AtildeDiff B S o)
  set σsign : ℝ := (((Equiv.Perm.sign (eC.symm.trans eR) : ℤˣ) : ℤ) : ℝ)
  have hσ : σsign = 1 ∨ σsign = -1 := sign_cast_eq_one_or_neg_one _
  have hmul : σsign * (AtildeDiff B S o).det =
      ε₀ * (F_B B : ℝ) *
        ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by
    calc σsign * (AtildeDiff B S o).det
        = ((AtildeDiff B S o).reindex eR.symm eC.symm).det := by
            simpa [σsign] using hdet.symm
      _ = ((AtildeDiff B S o).submatrix eR eC).det := by rw [← hreindex]
      _ = _ := hsub
  have hσ2 : σsign * σsign = 1 := by rcases hσ with h | h <;> simp [h]
  refine ⟨σsign * ε₀, mul_one_or_neg_one hσ hε₀, ?_⟩
  calc (AtildeDiff B S o).det
      = (σsign * σsign) * (AtildeDiff B S o).det := by rw [hσ2, one_mul]
    _ = σsign * (σsign * (AtildeDiff B S o).det) := by ring
    _ = σsign * (ε₀ * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det) := by rw [hmul]
    _ = (σsign * ε₀) * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by ring

theorem prop_3_1_det_Atilde {B S : ℕ} (_h : S < B) (_hS : 0 < S)
    (o : Fin 3 → Fin (S + 3)) (ho : Function.Injective o) :
    ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧
      (Atilde B S o).det =
        ε * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by
  obtain ⟨ε₁, hε₁, hM⟩ := det_AtildeDiff_eq_signed_F_B_det_R o ho
  have hmul : (AtildeDiff B S o).det =
      (DiffMat (Ndim B S)).det * (Atilde B S o).det := by
    simp only [AtildeDiff, det_mul]
  set d : ℝ := (DiffMat (Ndim B S)).det
  have hd : d = 1 ∨ d = -1 := by
    simpa [d, det_DiffMat_eq_neg_one_pow] using
      (neg_one_pow_eq_one_or_neg_one (Ndim B S * (Ndim B S - 1) / 2))
  have hd2 : d * d = 1 := by rcases hd with hd | hd <;> simp [d, hd]
  have hmul' : d * (Atilde B S o).det =
      ε₁ * (F_B B : ℝ) *
        ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by
    rw [← hM, hmul]
  refine ⟨d * ε₁, mul_one_or_neg_one hd hε₁, ?_⟩
  calc (Atilde B S o).det
      = (d * d) * (Atilde B S o).det := by rw [hd2, one_mul]
    _ = d * (d * (Atilde B S o).det) := by ring
    _ = d * (ε₁ * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det) := by rw [hmul']
    _ = (d * ε₁) * (F_B B : ℝ) *
          ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det := by ring

end CatalanSun.NewtonCompletion
