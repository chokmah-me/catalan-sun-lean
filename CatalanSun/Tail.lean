/-
  CatalanSun/Tail.lean

  Sun eq. 1.4: T_m + T_{m+1} = 1/(2m+1)² (arXiv:2609.04176v1 §1).
  Discharges the two sorries from incoming/TailRecurrence.lean.
-/

import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option maxHeartbeats 400000

noncomputable section

/-!
# Catalan tail recurrence (eq. 1.4)
-/

namespace CatalanSun.Tail

open Filter Topology
open scoped Topology

/-- `oddReal n` is `2n + 1` as a real. -/
def oddReal (n : ℕ) : ℝ := 2 * (n : ℝ) + 1

theorem oddReal_pos (n : ℕ) : (0 : ℝ) < oddReal n := by
  unfold oddReal
  positivity

theorem oddReal_ne_zero (n : ℕ) : oddReal n ≠ 0 :=
  ne_of_gt (oddReal_pos n)

theorem oddReal_sq_pos (n : ℕ) : (0 : ℝ) < oddReal n ^ 2 :=
  sq_pos_of_pos (oddReal_pos n)

theorem oddReal_ge_succ (m r : ℕ) : (r + 1 : ℝ) ≤ oddReal (m + r) := by
  unfold oddReal
  rw [Nat.cast_add]
  nlinarith

/-- `r`-th term of the Catalan tail starting at `m`. -/
def tailTerm (m r : ℕ) : ℝ := (-1 : ℝ) ^ r / oddReal (m + r) ^ 2

@[simp]
theorem tailTerm_zero (m : ℕ) : tailTerm m 0 = 1 / oddReal m ^ 2 := by
  simp [tailTerm]

theorem tailTerm_shift (m r : ℕ) :
    tailTerm m (r + 1) = -tailTerm (m + 1) r := by
  simp only [tailTerm]
  have h : m + (r + 1) = m + 1 + r := by abel
  rw [h, pow_succ]
  ring

theorem abs_tailTerm (m r : ℕ) : |tailTerm m r| = 1 / oddReal (m + r) ^ 2 := by
  unfold tailTerm
  rw [abs_div, abs_pow, abs_neg, abs_one]
  simp

theorem abs_tailTerm_le_inv_succ_sq (m r : ℕ) :
    |tailTerm m r| ≤ 1 / (r + 1 : ℝ) ^ 2 := by
  rw [abs_tailTerm]
  have h0 : (0 : ℝ) < r + 1 := by positivity
  have h1 : (0 : ℝ) < oddReal (m + r) := oddReal_pos _
  have hle : (r + 1 : ℝ) ≤ oddReal (m + r) := oddReal_ge_succ m r
  have hsq : (r + 1 : ℝ) ^ 2 ≤ oddReal (m + r) ^ 2 :=
    pow_le_pow_left₀ (le_of_lt h0) hle 2
  exact one_div_le_one_div_of_le (pow_pos h0 2) hsq

theorem summable_inv_succ_sq : Summable fun r : ℕ => 1 / (r + 1 : ℝ) ^ 2 := by
  have h : Summable fun r : ℕ => 1 / |(r : ℝ) + 1| ^ (2 : ℝ) :=
    (Real.summable_one_div_nat_add_rpow 1 2).mpr (by norm_num)
  refine h.congr fun r => ?_
  have hp : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  rw [abs_of_pos hp, Real.rpow_two]

theorem summable_tailTerm (m : ℕ) : Summable (tailTerm m) :=
  Summable.of_norm_bounded summable_inv_succ_sq fun r =>
    (Real.norm_eq_abs _).symm ▸ abs_tailTerm_le_inv_succ_sq m r

/-- Catalan tail `T_m`. -/
def tail (m : ℕ) : ℝ := ∑' r, tailTerm m r

/-- Weighted tail `u_m = T_m / (2m+1)`. -/
def weightedTail (m : ℕ) : ℝ := tail m / oddReal m

theorem tail_add_succ (m : ℕ) :
    tail m + tail (m + 1) = 1 / oddReal m ^ 2 := by
  unfold tail
  rw [(summable_tailTerm m).tsum_eq_zero_add]
  have : ∑' r, tailTerm m (r + 1) = -∑' r, tailTerm (m + 1) r := by
    have hcongr : (fun r => tailTerm m (r + 1)) = fun r => -tailTerm (m + 1) r :=
      funext fun r => tailTerm_shift m r
    rw [hcongr, tsum_neg]
  rw [this, tailTerm_zero]
  ring

theorem tail_eq_inv_sq_sub_succ (m : ℕ) :
    tail m = 1 / oddReal m ^ 2 - tail (m + 1) := by
  linarith [tail_add_succ m]

theorem even_neg_one_pow (k : ℕ) : (-1 : ℝ) ^ (2 * k) = 1 :=
  Even.neg_one_pow ⟨k, two_mul k⟩

theorem odd_neg_one_pow (k : ℕ) : (-1 : ℝ) ^ (2 * k + 1) = -1 := by
  rw [pow_succ, even_neg_one_pow k]
  ring

theorem tailTerm_even (m k : ℕ) :
    tailTerm m (2 * k) = 1 / oddReal (m + 2 * k) ^ 2 := by
  simp [tailTerm, even_neg_one_pow]

theorem tailTerm_odd (m k : ℕ) :
    tailTerm m (2 * k + 1) = -(1 / oddReal (m + 2 * k + 1) ^ 2) := by
  have hidx : m + (2 * k + 1) = m + 2 * k + 1 := by abel
  unfold tailTerm
  rw [hidx, odd_neg_one_pow]
  ring

theorem tailTerm_pair_pos (m k : ℕ) :
    0 < tailTerm m (2 * k) + tailTerm m (2 * k + 1) := by
  rw [tailTerm_even, tailTerm_odd]
  set a := oddReal (m + 2 * k) with ha
  set b := oddReal (m + 2 * k + 1) with hb
  have hapos : 0 < a := oddReal_pos _
  have hbpos : 0 < b := oddReal_pos _
  have hab : a < b := by
    rw [ha, hb]
    unfold oddReal
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    linarith
  have hform : 1 / a ^ 2 + -(1 / b ^ 2) = (b ^ 2 - a ^ 2) / (a ^ 2 * b ^ 2) := by
    field_simp
    ring
  rw [hform]
  refine div_pos ?_ (mul_pos (sq_pos_of_pos hapos) (sq_pos_of_pos hbpos))
  exact sub_pos.mpr (sq_lt_sq' (by linarith [hapos]) hab)

theorem sum_range_two_mul (m N : ℕ) :
    ∑ i ∈ Finset.range (2 * N), tailTerm m i =
      ∑ k ∈ Finset.range N, (tailTerm m (2 * k) + tailTerm m (2 * k + 1)) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hlen : 2 * (N + 1) = 2 * N + 1 + 1 := by ring
    rw [hlen, Finset.sum_range_succ, Finset.sum_range_succ, ih, Finset.sum_range_succ]
    ac_rfl

theorem even_partial_ge_first_pair (m N : ℕ) :
    tailTerm m 0 + tailTerm m 1 ≤
      ∑ i ∈ Finset.range (2 * (N + 1)), tailTerm m i := by
  rw [sum_range_two_mul]
  have h0 : tailTerm m 0 + tailTerm m 1 =
      ∑ k ∈ Finset.range 1, (tailTerm m (2 * k) + tailTerm m (2 * k + 1)) := by
    simp
  have hsub : Finset.range 1 ⊆ Finset.range (N + 1) := by
    intro x hx
    simp at hx ⊢
    omega
  have hnn : ∀ k ∈ Finset.range (N + 1),
      0 ≤ tailTerm m (2 * k) + tailTerm m (2 * k + 1) := fun k _ =>
    (tailTerm_pair_pos m k).le
  calc
    tailTerm m 0 + tailTerm m 1
        = ∑ k ∈ Finset.range 1, (tailTerm m (2 * k) + tailTerm m (2 * k + 1)) := h0
    _ ≤ ∑ k ∈ Finset.range (N + 1), (tailTerm m (2 * k) + tailTerm m (2 * k + 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub fun k hk _ => hnn k hk

/-- `T_m > 0` by grouping consecutive pairs of the alternating series. -/
theorem tail_pos (m : ℕ) : 0 < tail m := by
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, tailTerm m i) atTop (𝓝 (tail m)) :=
    (summable_tailTerm m).hasSum.tendsto_sum_nat
  have hsub :
      Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (2 * (N + 1)), tailTerm m i) atTop (𝓝 (tail m)) := by
    have hmono : Tendsto (fun N : ℕ => 2 * (N + 1)) atTop atTop := by
      exact tendsto_atTop_atTop_of_monotone (fun a b hab => by omega) fun n =>
        ⟨n, by omega⟩
    exact hlim.comp hmono
  have h0 := tailTerm_pair_pos m 0
  have hge : ∀ᶠ N in atTop,
      tailTerm m 0 + tailTerm m 1 ≤ ∑ i ∈ Finset.range (2 * (N + 1)), tailTerm m i :=
    Filter.Eventually.of_forall (even_partial_ge_first_pair m)
  have : tailTerm m 0 + tailTerm m 1 ≤ tail m :=
    ge_of_tendsto hsub hge
  linarith [h0]

theorem tail_lt_inv_sq (m : ℕ) : tail m < 1 / oddReal m ^ 2 := by
  rw [tail_eq_inv_sq_sub_succ]
  linarith [tail_pos (m + 1)]

theorem weightedTail_pos (m : ℕ) : 0 < weightedTail m :=
  div_pos (tail_pos m) (oddReal_pos m)

theorem tail_recurrence_paper_form (m : ℕ) :
    tail m + tail (m + 1) = 1 / (2 * (m : ℝ) + 1) ^ 2 := by
  convert tail_add_succ m using 2
  unfold oddReal
  ring

end CatalanSun.Tail
