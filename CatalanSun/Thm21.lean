/-
  CatalanSun/Thm21.lean

  Assembly milestones toward Theorem 2.1 (Sun arXiv:2609.04176v1 §2).

  Status: M3–M8 proved. `thm_2_1_full_column_rank` and absolute `cor_2_1`
  are sorry-free in this file.
-/

import CatalanSun.Rank
import CatalanSun.NewtonDiff
import CatalanSun.FunctionalEq
import CatalanSun.TwoAdic
import CatalanSun.Tail
import CatalanSun.Structure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 800000

noncomputable section

namespace CatalanSun.Thm21

open CatalanSun Matrix Finset Polynomial
open CatalanSun.Rank

/-! ## Column dependence data

Given `lam : Fin S → ℝ`, write
`U_i(lam) := ∑_j lam_j u_{i+j+1}` and `f_i(lam) := Π_i · U_i(lam)`. -/

/-- Weighted-tail column combination `∑_j lam_j u_{i+(j+1)}`. -/
def Ucombo (S : ℕ) (lam : Fin S → ℝ) (i : ℕ) : ℝ :=
  ∑ j : Fin S, lam j * Tail.weightedTail (i + (j.val + 1))

/-- Paper sequence `f_i := Π_i · ∑_j lam_j u_{i+j}` (column index shift `j ↦ j+1`). -/
def fSeq (B S : ℕ) (lam : Fin S → ℝ) (i : ℕ) : ℝ :=
  (TwoAdic.PiFactor B i : ℝ) * Ucombo S lam i

/-- Unfolding: residual row·lam equals the paper alternating sum of `f_i`. -/
theorem RmatrixFin_mulVec_eq_alternating_fSeq {B S : ℕ} (lam : Fin S → ℝ)
    (α : Fin (S + 3)) :
    (RmatrixFin B S *ᵥ lam) α =
      ∑ i ∈ range (α.val + 2 * B + 1),
        (-1 : ℝ) ^ i * ((α.val + 2 * B).choose i : ℝ) * fSeq B S lam i := by
  -- LHS expands to ∑_j (∑_i c_i Π_i u_{i+j+1}) * lam_j
  simp only [RmatrixFin, mulVec, dotProduct, Matrix.of_apply, Residual.Rmatrix, fSeq, Ucombo]
  -- Pull `lam j` inside the inner sum, then swap summation order.
  simp_rw [Finset.sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  -- ∑_j c_i Π_i u_{i+j+1} * lam_j = c_i Π_i * ∑_j lam_j u_{i+j+1}
  set c : ℝ := (-1 : ℝ) ^ i * ((α.val + 2 * B).choose i : ℝ) * (TwoAdic.PiFactor B i : ℝ)
  -- After simp_rw sum_mul / sum_comm the goal is ∑_j c * u * lam = c * ∑_j lam * u,
  -- up to reassociation; rewrite explicitly.
  calc ∑ j : Fin S,
        (-1 : ℝ) ^ i * ((α.val + 2 * B).choose i : ℝ) * (TwoAdic.PiFactor B i : ℝ) *
          Tail.weightedTail (i + (j.val + 1)) * lam j
      = ∑ j : Fin S, c * (Tail.weightedTail (i + (j.val + 1)) * lam j) := by
          refine sum_congr rfl fun j _ => ?_
          simp [c]; ring
    _ = c * ∑ j : Fin S, Tail.weightedTail (i + (j.val + 1)) * lam j := by
          rw [← Finset.mul_sum]
    _ = c * ∑ j : Fin S, lam j * Tail.weightedTail (i + (j.val + 1)) := by
          congr 1
          refine sum_congr rfl fun j _ => mul_comm _ _
    _ = (-1 : ℝ) ^ i * ((α.val + 2 * B).choose i : ℝ) *
          ((TwoAdic.PiFactor B i : ℝ) *
            ∑ j : Fin S, lam j * Tail.weightedTail (i + (j.val + 1))) := by
          simp [c]; ring

/-! ## M3: column dependence ⇒ vanishing high alternating sums of `f_i` -/

/-- If `lam` is a column dependence, every residual row contracts to zero, hence
the paper alternating sum of `f_i` of order `α + 2B` vanishes for each
`α ∈ {0,…,S+2}`. -/
theorem column_dep_paperFwdDiff_fSeq_eq_zero {B S : ℕ} {lam : Fin S → ℝ}
    (hker : RmatrixFin B S *ᵥ lam = 0) (α : Fin (S + 3)) :
    NewtonDiff.paperFwdDiff (fSeq B S lam) (α.val + 2 * B) = 0 := by
  unfold NewtonDiff.paperFwdDiff
  have hrow := congrArg (fun v : Fin (S + 3) → ℝ => v α) hker
  simp only [Pi.zero_apply] at hrow
  rwa [RmatrixFin_mulVec_eq_alternating_fSeq lam α] at hrow

/-- Same statement in unbundled sum form. -/
theorem column_dep_alternating_sum_eq_zero {B S : ℕ} {lam : Fin S → ℝ}
    (hker : RmatrixFin B S *ᵥ lam = 0) (α : Fin (S + 3)) :
    ∑ i ∈ range (α.val + 2 * B + 1),
      (-1 : ℝ) ^ i * ((α.val + 2 * B).choose i : ℝ) * fSeq B S lam i = 0 := by
  simpa [NewtonDiff.paperFwdDiff] using column_dep_paperFwdDiff_fSeq_eq_zero hker α

/-- In particular, for every order `n` with `2B ≤ n ≤ 2B + S + 2` there is a
row index realizing that order, so the corresponding alternating sum vanishes. -/
theorem column_dep_high_fwdDiff_eq_zero {B S : ℕ} {lam : Fin S → ℝ}
    (hker : RmatrixFin B S *ᵥ lam = 0) {n : ℕ}
    (hn_lo : 2 * B ≤ n) (hn_hi : n ≤ 2 * B + S + 2) :
    NewtonDiff.paperFwdDiff (fSeq B S lam) n = 0 := by
  set a : ℕ := n - 2 * B
  have hn : n = a + 2 * B := by omega
  let α : Fin (S + 3) := ⟨a, by omega⟩
  have hα : α.val + 2 * B = n := by simp [α, hn]
  simpa [hα] using column_dep_paperFwdDiff_fSeq_eq_zero hker α

/-! ## Rank-defect entry point

If Theorem 2.1 failed, rank-nullity would supply a nontrivial `lam` to which the
M3 vanishing applies. Closing the contradiction needs M4–M6 (structure of
`f_i`, Newton degree, `K(X) ≡ 0`) before invoking M7. -/

theorem exists_column_dep_with_vanishing_fwdDiff {B S : ℕ}
    (h : (RmatrixFin B S).rank < Fintype.card (Fin S)) :
    ∃ lam : Fin S → ℝ, lam ≠ 0 ∧ RmatrixFin B S *ᵥ lam = 0 ∧
      (∀ n, 2 * B ≤ n → n ≤ 2 * B + S + 2 →
        NewtonDiff.paperFwdDiff (fSeq B S lam) n = 0) := by
  obtain ⟨lam, hlam0, hker⟩ := exists_nontrivial_column_dependence_of_rank_lt h
  exact ⟨lam, hlam0, hker, fun n hlo hhi => column_dep_high_fwdDiff_eq_zero hker hlo hhi⟩

/-! ## M4 Phase C+D: structure identity through `T_{i+1}`

Expanding `weightedTail (i+j)` from base `T_{i+1}` (rather than `T_i`) makes the
remainder a polynomial evaluation: denominators start at `2i+3`, inside `Π_i`.
Phase A keeps `Dlam`/`Pstar` signs `(-1)^j`; the minus sits on `T_{i+1}`. -/

open CatalanSun.Structure

/--
Revised structure identity (paper's written `T_i` form corrected to `T_{i+1}`):
`f_i = - T_{i+1} · D_λ(i) + P_λ(i)`.
-/
theorem fSeq_eq_neg_tail_succ_mul_Dlam_add_Plam {B S : ℕ} (h : S < B) (hS : 0 < S)
    (lam : Fin S → ℝ) (i : ℕ) :
    fSeq B S lam i =
      - Tail.tail (i + 1) * (Dlam B S lam).eval (i : ℝ) +
        (Plam B S lam).eval (i : ℝ) := by
  have hSB : S ≤ B := Nat.le_of_lt h
  have _hS := hS
  -- Expand each weighted tail from `T_{i+1}`.
  have hwt : ∀ j : Fin S,
      Tail.weightedTail (i + (j.val + 1)) =
        (-1 : ℝ) ^ j.val * Tail.tail (i + 1) / Tail.oddReal (i + (j.val + 1)) +
          (1 / Tail.oddReal (i + (j.val + 1))) *
            ∑ m ∈ range j.val,
              (-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2 := by
    intro j
    have hj : 1 ≤ j.val + 1 := Nat.succ_pos _
    simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      Tail.weightedTail_shift_succ (i := i) (j := j.val + 1) hj
  -- Per-summand expansion of `Πᵢ · λⱼ · u_{i+j}`.
  have hterm : ∀ j : Fin S,
      (TwoAdic.PiFactor B i : ℝ) * (lam j * Tail.weightedTail (i + (j.val + 1))) =
        (TwoAdic.PiFactor B i : ℝ) * lam j *
            ((-1 : ℝ) ^ j.val * Tail.tail (i + 1) /
              Tail.oddReal (i + (j.val + 1))) +
          ∑ m ∈ range j.val,
            (TwoAdic.PiFactor B i : ℝ) * lam j *
              ((1 / Tail.oddReal (i + (j.val + 1))) *
                ((-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2)) := by
    intro j
    have hodd : Tail.oddReal (i + (j.val + 1)) ≠ 0 := Tail.oddReal_ne_zero _
    rw [hwt j]
    set A : ℝ :=
      (-1 : ℝ) ^ j.val * Tail.tail (i + 1) / Tail.oddReal (i + (j.val + 1))
    set s : ℝ :=
      ∑ m ∈ range j.val,
        (-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2
    have hdistrib :
        (TwoAdic.PiFactor B i : ℝ) * (lam j * (A + (1 / Tail.oddReal (i + (j.val + 1))) * s)) =
          (TwoAdic.PiFactor B i : ℝ) * lam j * A +
            (TwoAdic.PiFactor B i : ℝ) * lam j *
              ((1 / Tail.oddReal (i + (j.val + 1))) * s) := by ring
    rw [hdistrib]
    congr 1
    -- Pull `Π λ / odd` through the inner sum.
    calc
      (TwoAdic.PiFactor B i : ℝ) * lam j *
          ((1 / Tail.oddReal (i + (j.val + 1))) * s)
          = ((TwoAdic.PiFactor B i : ℝ) * lam j *
              (1 / Tail.oddReal (i + (j.val + 1)))) * s := by ring
      _ = ∑ m ∈ range j.val,
            ((TwoAdic.PiFactor B i : ℝ) * lam j *
              (1 / Tail.oddReal (i + (j.val + 1)))) *
              ((-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2) := by
            dsimp [s]
            rw [Finset.mul_sum]
      _ = ∑ m ∈ range j.val,
            (TwoAdic.PiFactor B i : ℝ) * lam j *
              ((1 / Tail.oddReal (i + (j.val + 1))) *
                ((-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2)) := by
            refine Finset.sum_congr rfl fun m _ => ?_
            ring
  -- Assemble the double-sum form of `fSeq`.
  have hsplit :
      fSeq B S lam i =
        (∑ j : Fin S,
            (TwoAdic.PiFactor B i : ℝ) * lam j *
              ((-1 : ℝ) ^ j.val * Tail.tail (i + 1) /
                Tail.oddReal (i + (j.val + 1)))) +
          ∑ j : Fin S,
            ∑ m ∈ range j.val,
              (TwoAdic.PiFactor B i : ℝ) * lam j *
                ((1 / Tail.oddReal (i + (j.val + 1))) *
                  ((-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2)) := by
    simp only [fSeq, Ucombo, Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hterm j
  -- Identify the first sum with `- T_{i+1} · D_λ(i)`.
  have hD :
      ∑ j : Fin S,
          (TwoAdic.PiFactor B i : ℝ) * lam j *
            ((-1 : ℝ) ^ j.val * Tail.tail (i + 1) /
              Tail.oddReal (i + (j.val + 1))) =
        - Tail.tail (i + 1) * (Dlam B S lam).eval (i : ℝ) := by
    rw [eval_Dlam hSB lam i, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hsign : (-1 : ℝ) ^ j.val = -((-1 : ℝ) ^ (j.val + 1)) := by
      rw [pow_succ]; ring
    rw [hsign]
    ring
  -- Identify the second (double) sum with `P_λ(i)`.
  have hP :
      ∑ j : Fin S,
          ∑ m ∈ range j.val,
            (TwoAdic.PiFactor B i : ℝ) * lam j *
              ((1 / Tail.oddReal (i + (j.val + 1))) *
                ((-1 : ℝ) ^ (j.val - 1 - m) / Tail.oddReal (i + 1 + m) ^ 2)) =
        (Plam B S lam).eval (i : ℝ) := by
    rw [eval_Plam h lam i]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun m hm => ?_
    have hodd : Tail.oddReal (i + (j.val + 1)) ≠ 0 := Tail.oddReal_ne_zero _
    have hidx : i + 1 + m = i + (m + 1) := by omega
    rw [hidx]
    field_simp [hodd]
  rw [hsplit, hD, hP]

/-! ## M5: Newton interpolant of degree ≤ 2B−1

Column dependence kills paper forward differences of `fSeq` on
`[2B, 2B+S+2]`, so the Newton interpolant through those values has
degree at most `2B−1`. Setting `A := Plam − p` recovers the sign
`A(i) = T_{i+1} D_λ(i)` matching ClearedEq23. -/

theorem exists_poly_natDegree_le_two_B_sub_one_of_column_dep
    {B S : ℕ} (h : S < B) (hS : 0 < S) {lam : Fin S → ℝ}
    (hker : RmatrixFin B S *ᵥ lam = 0) :
    ∃ p : ℝ[X], p.natDegree ≤ 2 * B - 1 ∧
      ∀ i ≤ 2 * B + S + 2, p.eval (i : ℝ) = fSeq B S lam i := by
  have _h := h
  have _hS := hS
  set N : ℕ := 2 * B + S + 2
  set M : ℕ := 2 * B
  have hM : 1 ≤ M := by
    have : 0 < B := Nat.pos_of_ne_zero (by omega)
    omega
  have hMN : M ≤ N := by omega
  have hvan : ∀ k, M ≤ k → k ≤ N → NewtonDiff.paperFwdDiff (fSeq B S lam) k = 0 := by
    intro k hkM hkN
    exact column_dep_high_fwdDiff_eq_zero hker hkM hkN
  -- `natDegree ≤ M - 1 = 2B - 1`
  obtain ⟨p, hpdeg, hpeval⟩ :=
    NewtonDiff.exists_newtonInterpolant_of_high_vanishing (K := ℝ)
      (f := fSeq B S lam) hM hMN hvan
  have hpdeg' : p.natDegree ≤ 2 * B - 1 := by
    simpa [M] using hpdeg
  exact ⟨p, hpdeg', fun i hi => by simpa [N] using hpeval i hi⟩

/-- `ASeq i = Plam.eval i - fSeq i = Tail.tail(i+1) * Dlam.eval i`. -/
def ASeq (B S : ℕ) (lam : Fin S → ℝ) (i : ℕ) : ℝ :=
  (Plam B S lam).eval (i : ℝ) - fSeq B S lam i

theorem ASeq_eq_tail_succ_mul_Dlam {B S : ℕ} (h : S < B) (hS : 0 < S)
    (lam : Fin S → ℝ) (i : ℕ) :
    ASeq B S lam i = Tail.tail (i + 1) * (Dlam B S lam).eval (i : ℝ) := by
  have hid := fSeq_eq_neg_tail_succ_mul_Dlam_add_Plam h hS lam i
  simp only [ASeq]
  linarith

theorem exists_Apoly_of_column_dep
    {B S : ℕ} (h : S < B) (hS : 0 < S) {lam : Fin S → ℝ}
    (hker : RmatrixFin B S *ᵥ lam = 0) :
    ∃ A : ℝ[X], A.natDegree ≤ 2 * B - 1 ∧
      (∀ i ≤ 2 * B + S + 2,
        A.eval (i : ℝ) = (Plam B S lam).eval (i : ℝ) - fSeq B S lam i) ∧
      (∀ i ≤ 2 * B + S + 2,
        A.eval (i : ℝ) =
          Tail.tail (i + 1) * (Dlam B S lam).eval (i : ℝ)) := by
  obtain ⟨p, hpdeg, hpeval⟩ :=
    exists_poly_natDegree_le_two_B_sub_one_of_column_dep h hS hker
  set A : ℝ[X] := Plam B S lam - p
  have hAdeg : A.natDegree ≤ 2 * B - 1 := by
    have hP : (Plam B S lam).natDegree ≤ 2 * B - 3 := natDegree_Plam_le h lam
    have hle : (Plam B S lam - p).natDegree ≤
        max (Plam B S lam).natDegree p.natDegree := natDegree_sub_le _ _
    refine hle.trans ?_
    exact max_le (hP.trans (by omega)) hpdeg
  refine ⟨A, hAdeg, ?_, ?_⟩
  · intro i hi
    simp only [A, eval_sub, hpeval i hi]
  · intro i hi
    have h1 : A.eval (i : ℝ) = ASeq B S lam i := by
      simp only [A, ASeq, eval_sub, hpeval i hi]
    rw [h1, ASeq_eq_tail_succ_mul_Dlam h hS lam i]

/-! ## M6: K ≡ 0 under column dependence

`Kpoly A D` is the cleared numerator of
`A/D + A(X+1)/D(X+1) − 1/(2X+3)²`. Natural zeros alone do not beat
`deg ≤ 4B`; the argument also uses `G₀ ∣ K` (`deg G₀ = 2B−S−2`) and
`K(−3/2) = 0`. -/

/-- Cleared numerator of `A/D + A∘shift − 1/(2X+3)²`. -/
noncomputable def Kpoly (A D : ℝ[X]) : ℝ[X] :=
  (C (2 : ℝ) * X + C (3 : ℝ)) ^ 2 * (A * FunctionalEq.shiftPoly D +
      FunctionalEq.shiftPoly A * D) -
    D * FunctionalEq.shiftPoly D

theorem natDegree_shiftPoly_le (p : ℝ[X]) :
    (FunctionalEq.shiftPoly p).natDegree ≤ p.natDegree := by
  have h := natDegree_comp_le (p := p) (q := X + C (1 : ℝ))
  have hq : (X + C (1 : ℝ)).natDegree = 1 := natDegree_X_add_C 1
  rw [FunctionalEq.shiftPoly]
  exact h.trans (by rw [hq, mul_one])

theorem natDegree_Kpoly_le {A D : ℝ[X]} {B : ℕ} (hB : 1 ≤ B)
    (hA : A.natDegree ≤ 2 * B - 1) (hD : D.natDegree ≤ 2 * B - 1) :
    (Kpoly A D).natDegree ≤ 4 * B := by
  have hshiftA : (FunctionalEq.shiftPoly A).natDegree ≤ 2 * B - 1 :=
    (natDegree_shiftPoly_le A).trans hA
  have hshiftD : (FunctionalEq.shiftPoly D).natDegree ≤ 2 * B - 1 :=
    (natDegree_shiftPoly_le D).trans hD
  have hsum :
      (A * FunctionalEq.shiftPoly D + FunctionalEq.shiftPoly A * D).natDegree ≤
        (2 * B - 1) + (2 * B - 1) :=
    (natDegree_add_le _ _).trans
      (max_le (natDegree_mul_le.trans (add_le_add hA hshiftD))
        (natDegree_mul_le.trans (add_le_add hshiftA hD)))
  have hlin1 : (C (2 : ℝ) * X + C (3 : ℝ)).natDegree ≤ 1 := by
    have hX : (C (2 : ℝ) * X).natDegree ≤ 1 :=
      (natDegree_C_mul_le (2 : ℝ) X).trans (by simp [natDegree_X])
    have hC : (C (3 : ℝ)).natDegree ≤ 0 := le_of_eq (natDegree_C 3)
    exact (natDegree_add_le _ _).trans (max_le hX (hC.trans (Nat.zero_le _)))
  have hlin : ((C (2 : ℝ) * X + C (3 : ℝ)) ^ 2).natDegree ≤ 2 :=
    (natDegree_pow_le (p := C (2 : ℝ) * X + C (3 : ℝ)) (n := 2)).trans
      (Nat.mul_le_mul_left 2 hlin1)
  have harith : 2 + ((2 * B - 1) + (2 * B - 1)) = 4 * B := by omega
  have hmain :
      ((C (2 : ℝ) * X + C (3 : ℝ)) ^ 2 *
          (A * FunctionalEq.shiftPoly D + FunctionalEq.shiftPoly A * D)).natDegree ≤
        4 * B := by
    refine (natDegree_mul_le).trans ?_
    exact (add_le_add hlin hsum).trans (le_of_eq harith)
  have hsub : (D * FunctionalEq.shiftPoly D).natDegree ≤ 4 * B :=
    (natDegree_mul_le.trans (add_le_add hD hshiftD)).trans (by omega)
  exact (natDegree_sub_le _ _).trans (max_le hmain hsub)

theorem eval_shiftPoly (p : ℝ[X]) (x : ℝ) :
    (FunctionalEq.shiftPoly p).eval x = p.eval (x + 1) := by
  simp [FunctionalEq.shiftPoly, eval_comp]

theorem Kpoly_eval_eq_zero_of_tail {A D : ℝ[X]} {i : ℕ}
    (hA0 : A.eval (i : ℝ) = Tail.tail (i + 1) * D.eval (i : ℝ))
    (hA1 : A.eval ((i + 1 : ℕ) : ℝ) =
      Tail.tail (i + 2) * D.eval ((i + 1 : ℕ) : ℝ)) :
    (Kpoly A D).eval (i : ℝ) = 0 := by
  have htail := Tail.tail_add_succ (i + 1)
  have hodd : Tail.oddReal (i + 1) = (2 : ℝ) * (i : ℝ) + 3 := by
    simp only [Tail.oddReal, Nat.cast_add, Nat.cast_one]
    ring
  have hne : (2 : ℝ) * (i : ℝ) + 3 ≠ 0 :=
    ne_of_gt (by positivity)
  have hi1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by simp
  have heval :
      (Kpoly A D).eval (i : ℝ) =
        (2 * (i : ℝ) + 3) ^ 2 *
            (A.eval (i : ℝ) * D.eval ((i + 1 : ℕ) : ℝ) +
              A.eval ((i + 1 : ℕ) : ℝ) * D.eval (i : ℝ)) -
          D.eval (i : ℝ) * D.eval ((i + 1 : ℕ) : ℝ) := by
    simp only [Kpoly, eval_sub, eval_mul, eval_add, eval_pow, eval_X, eval_C,
      eval_shiftPoly, hi1]
  rw [heval, hA0, hA1]
  set Di : ℝ := D.eval (i : ℝ)
  set Di1 : ℝ := D.eval ((i + 1 : ℕ) : ℝ)
  have hsum : Tail.tail (i + 1) + Tail.tail (i + 2) =
      1 / ((2 : ℝ) * (i : ℝ) + 3) ^ 2 := by
    rw [← hodd]; exact htail
  calc
    (2 * (i : ℝ) + 3) ^ 2 *
          (Tail.tail (i + 1) * Di * Di1 + Tail.tail (i + 2) * Di1 * Di) -
        Di * Di1
        = (2 * (i : ℝ) + 3) ^ 2 * (Di * Di1) *
            (Tail.tail (i + 1) + Tail.tail (i + 2)) - Di * Di1 := by ring
    _ = (2 * (i : ℝ) + 3) ^ 2 * (Di * Di1) *
            (1 / ((2 : ℝ) * (i : ℝ) + 3) ^ 2) - Di * Di1 := by rw [hsum]
    _ = Di * Di1 - Di * Di1 := by field_simp [hne]
    _ = 0 := by ring

theorem G0_dvd_Kpoly {B S : ℕ} (h : S < B) (hS : 0 < S)
    (lam : Fin S → ℝ) (A : ℝ[X]) :
    G0 B S ∣ Kpoly A (Dlam B S lam) := by
  have hD : G0 B S ∣ Dlam B S lam := G0_dvd_Dlam h hS lam
  have hDs : G0 B S ∣ FunctionalEq.shiftPoly (Dlam B S lam) :=
    G0_dvd_shiftPoly_Dlam h hS lam
  refine dvd_sub ?_ ?_
  · exact dvd_mul_of_dvd_right
      (dvd_add (dvd_mul_of_dvd_right hDs A) (dvd_mul_of_dvd_right hD _)) _
  · obtain ⟨q, hq⟩ := hD
    obtain ⟨r, hr⟩ := hDs
    refine ⟨G0 B S * q * r, ?_⟩
    calc Dlam B S lam * FunctionalEq.shiftPoly (Dlam B S lam)
        = (G0 B S * q) * FunctionalEq.shiftPoly (Dlam B S lam) := by nth_rw 1 [hq]
      _ = (G0 B S * q) * (G0 B S * r) := by rw [hr]
      _ = G0 B S * (G0 B S * q * r) := by ring

theorem Kpoly_eval_neg_three_halves {B S : ℕ} (hS : 0 < S)
    (lam : Fin S → ℝ) (A : ℝ[X]) :
    (Kpoly A (Dlam B S lam)).eval (-(3 / 2 : ℝ)) = 0 := by
  have hD := Dlam_eval_neg_three_halves (B := B) hS lam
  have hfac :
      ((C (2 : ℝ) * X + C (3 : ℝ) : ℝ[X]).eval (-(3 / 2 : ℝ))) = 0 := by
    simp [eval_add, eval_mul, eval_X, eval_C]
    ring
  simp only [Kpoly, eval_sub, eval_mul, eval_add, eval_pow, hfac, hD,
    zero_pow (by decide : (2 : ℕ) ≠ 0), zero_mul, mul_zero, sub_zero]

theorem Kpoly_eq_zero_of_column_dep
    {B S : ℕ} (h : S < B) (hS : 0 < S) {lam : Fin S → ℝ}
    (_hker : RmatrixFin B S *ᵥ lam = 0)
    (A : ℝ[X]) (hAdeg : A.natDegree ≤ 2 * B - 1)
    (hA : ∀ i ≤ 2 * B + S + 2,
      A.eval (i : ℝ) = Tail.tail (i + 1) * (Dlam B S lam).eval (i : ℝ)) :
    Kpoly A (Dlam B S lam) = 0 := by
  set D := Dlam B S lam
  set K := Kpoly A D
  have hB : 1 ≤ B := by
    have : 0 < B := Nat.pos_of_ne_zero (by omega)
    omega
  have hDdeg : D.natDegree ≤ 2 * B - 1 := natDegree_Dlam_le h lam
  have hKdeg : K.natDegree ≤ 4 * B := natDegree_Kpoly_le hB hAdeg hDdeg
  have hnat : ∀ i ≤ 2 * B + S + 1, K.eval (i : ℝ) = 0 := by
    intro i hi
    have hi0 : i ≤ 2 * B + S + 2 := by omega
    have hi1 : i + 1 ≤ 2 * B + S + 2 := by omega
    exact Kpoly_eval_eq_zero_of_tail (hA i hi0) (hA (i + 1) hi1)
  have hhalf : K.eval (-(3 / 2 : ℝ)) = 0 :=
    Kpoly_eval_neg_three_halves hS lam A
  have hG0dvd : G0 B S ∣ K := G0_dvd_Kpoly h hS lam A
  by_cases hK0 : K = 0
  · exact hK0
  · obtain ⟨Q, hQ⟩ := hG0dvd
    have hQ0 : Q ≠ 0 := fun hQz => hK0 (by simp [hQ, hQz])
    have hG0ne : G0 B S ≠ 0 := G0_ne_zero B S
    have hdegK : K.natDegree = (G0 B S).natDegree + Q.natDegree := by
      rw [hQ, natDegree_mul hG0ne hQ0]
    have hG0deg : (G0 B S).natDegree = 2 * B - S - 2 := natDegree_G0 h
    have hQnat : ∀ i ≤ 2 * B + S + 1, Q.eval (i : ℝ) = 0 := by
      intro i hi
      have hKi : K.eval (i : ℝ) = 0 := hnat i hi
      have hG0i : (G0 B S).eval (i : ℝ) ≠ 0 := G0_eval_nat_ne B S i
      have : (G0 B S).eval (i : ℝ) * Q.eval (i : ℝ) = 0 := by
        simpa [hQ, eval_mul] using hKi
      exact (mul_eq_zero.mp this).resolve_left hG0i
    have hQhalf : Q.eval (-(3 / 2 : ℝ)) = 0 := by
      have : (G0 B S).eval (-(3 / 2 : ℝ)) * Q.eval (-(3 / 2 : ℝ)) = 0 := by
        simpa [hQ, eval_mul] using hhalf
      exact (mul_eq_zero.mp this).resolve_left (G0_eval_neg_three_halves_ne B S)
    let s : Finset ℝ :=
      (Finset.range (2 * B + S + 2)).image (fun i : ℕ => (i : ℝ)) ∪
        {(-(3 / 2 : ℝ))}
    have hs_card : #s = 2 * B + S + 3 := by
      have hdisj :
          Disjoint ((Finset.range (2 * B + S + 2)).image (fun i : ℕ => (i : ℝ)))
            ({(-(3 / 2 : ℝ))} : Finset ℝ) := by
        refine disjoint_left.mpr ?_
        intro x hxN hxH
        obtain ⟨i, _, rfl⟩ := mem_image.mp hxN
        have : (i : ℝ) ≠ -(3 / 2) := by
          have : (0 : ℝ) ≤ (i : ℝ) := Nat.cast_nonneg _
          linarith
        exact this (mem_singleton.mp hxH)
      have hcardN :
          #((Finset.range (2 * B + S + 2)).image (fun i : ℕ => (i : ℝ))) =
            2 * B + S + 2 := by
        rw [Finset.card_image_of_injective _ Nat.cast_injective, card_range]
      rw [card_union_of_disjoint hdisj, hcardN, card_singleton]
    have hQzeros : ∀ x ∈ s, Q.eval x = 0 := by
      intro x hx
      cases mem_union.mp hx with
      | inl hxN =>
        obtain ⟨i, hi, rfl⟩ := mem_image.mp hxN
        exact hQnat i (Nat.lt_succ_iff.mp (mem_range.mp hi))
      | inr hxH =>
        rw [mem_singleton.mp hxH]
        exact hQhalf
    have hQdeg_lt : Q.natDegree < #s := by
      have hle : Q.natDegree ≤ 2 * B + S + 2 := by
        have hEq : K.natDegree = 2 * B - S - 2 + Q.natDegree := by
          rw [hdegK, hG0deg]
        have : 2 * B - S - 2 + Q.natDegree ≤ 4 * B := by
          rw [← hEq]; exact hKdeg
        omega
      rw [hs_card]
      omega
    have hQeq0 :=
      eq_zero_of_natDegree_lt_card_of_eval_eq_zero' Q s hQzeros hQdeg_lt
    exact (hQ0 hQeq0).elim

/-! ## M8: `Kpoly = 0` ⇒ `ClearedEq23`, then Theorem 2.1

`Kpoly` clears with `(C 2 * X + C 3)²`; `ClearedEq23` uses `(2 * X + C 3)²`.
These linear factors agree as polynomials, so vanishing of `Kpoly` is exactly
the cleared equation. Combined with `Dlam ≠ 0` (from nontrivial `lam`) this
contradicts M7. -/

theorem two_mul_X_add_C_three_eq :
    (C (2 : ℝ) * X + C (3 : ℝ) : ℝ[X]) = (2 * X + C (3 : ℝ)) := by
  have h2 : (2 : ℝ[X]) = C (2 : ℝ) := (C_eq_natCast (R := ℝ) 2).symm
  rw [← h2]

theorem clearedEq23_of_Kpoly_eq_zero {A D : ℝ[X]}
    (h : Kpoly A D = 0) : FunctionalEq.ClearedEq23 A D := by
  unfold FunctionalEq.ClearedEq23 Kpoly at *
  rwa [two_mul_X_add_C_three_eq, sub_eq_zero] at h

/-- Theorem 2.1: the residual matrix has full column rank when `B > S > 0`. -/
theorem thm_2_1_full_column_rank {B S : ℕ} (h : S < B) (hS : 0 < S) :
    (RmatrixFin B S).rank = Fintype.card (Fin S) := by
  by_contra hne
  have hle : (RmatrixFin B S).rank ≤ Fintype.card (Fin S) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (RmatrixFin B S).mulVecLin
    have hpi : Module.finrank ℝ (Fin S → ℝ) = Fintype.card (Fin S) :=
      Module.finrank_pi ℝ
    have hsum :
        (RmatrixFin B S).rank +
            Module.finrank ℝ (LinearMap.ker (RmatrixFin B S).mulVecLin) =
          Fintype.card (Fin S) := by
      simpa [Matrix.rank, hpi] using hrn
    omega
  have hlt : (RmatrixFin B S).rank < Fintype.card (Fin S) :=
    lt_of_le_of_ne hle hne
  obtain ⟨lam, hlam0, hker⟩ := exists_nontrivial_column_dependence_of_rank_lt hlt
  obtain ⟨A, hAdeg, _, hA⟩ := exists_Apoly_of_column_dep h hS hker
  have hK : Kpoly A (Dlam B S lam) = 0 :=
    Kpoly_eq_zero_of_column_dep h hS hker A hAdeg hA
  have hCleared : FunctionalEq.ClearedEq23 A (Dlam B S lam) :=
    clearedEq23_of_Kpoly_eq_zero hK
  have hDne : Dlam B S lam ≠ 0 := Dlam_ne_zero_of_lam_ne_zero h hS hlam0
  exact FunctionalEq.no_clearedEq23_solution_real A (Dlam B S lam) hDne hCleared

/-- Absolute Corollary 2.1: a nonvanishing maximal minor exists. -/
theorem cor_2_1 {B S : ℕ} (h : S < B) (hS : 0 < S) :
    ∃ f : Fin S → Fin (S + 3), Function.Injective f ∧
      ((RmatrixFin B S).submatrix f id).det ≠ 0 :=
  cor_2_1_of_thm_2_1 h hS (thm_2_1_full_column_rank h hS)

end CatalanSun.Thm21
