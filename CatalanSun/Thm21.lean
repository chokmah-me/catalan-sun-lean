/-
  CatalanSun/Thm21.lean

  Assembly milestones toward Theorem 2.1 (Sun arXiv:2609.04176v1 §2).

  Status: M3 (column dependence ⇒ vanishing high-order alternating sums of
  `f_i`) is proved. M4 Phase C+D structure identity
    `f_i = - T_{i+1} · D_λ(i) + P_λ(i)`
  is proved (paper's written T_i form corrected). M5–M6 / full
  `thm_2_1_full_column_rank` remain open.
-/

import CatalanSun.Rank
import CatalanSun.NewtonDiff
import CatalanSun.FunctionalEq
import CatalanSun.TwoAdic
import CatalanSun.Tail
import CatalanSun.Structure
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 400000

noncomputable section

namespace CatalanSun.Thm21

open CatalanSun Matrix Finset
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

end CatalanSun.Thm21
