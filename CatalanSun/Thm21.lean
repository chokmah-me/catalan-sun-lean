/-
  CatalanSun/Thm21.lean

  Assembly milestones toward Theorem 2.1 (Sun arXiv:2609.04176v1 §2).
  This file lands the sorry-free prefix that does not yet require the hard
  structure theorem `f_i = T_i · D_λ(i) + P_λ(i)`.

  Status: M3 (column dependence ⇒ vanishing high-order alternating sums of
  `f_i`) is proved. M4–M6 / full `thm_2_1_full_column_rank` remain open.
-/

import CatalanSun.Rank
import CatalanSun.NewtonDiff
import CatalanSun.FunctionalEq
import CatalanSun.TwoAdic
import CatalanSun.Tail
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

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

end CatalanSun.Thm21
