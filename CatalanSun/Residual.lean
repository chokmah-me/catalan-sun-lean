/-
  CatalanSun/Residual.lean

  Residual matrix entries R_{α,j} (Sun arXiv:2609.04176v1, eq. (2.1)) built from
  `weightedTail`, and the concrete 2-integrality fact underlying Lemma 5.4:

    If G = a/q ∈ ℚ, then every entry q·R_{α,j} is 2-integral.

  This is the "qT_m has only odd denominators ⇒ qR ⊆ ℤ_(2)" step from the
  paper's proof of Lemma 5.4 (p. 12), instantiated at the concrete definition
  (2.1) of R rather than left as the abstract
  `posPart_sub_eq_zero_of_neg_of_nonneg` shape already in `TwoAdic.lean`.

  Det-level Lemma 5.4 is assembled in `CatalanSun/Lemma54.lean` (avoids an
  import cycle with NewtonCompletion). Theorem 5.1 / Pascal–Cauchy remain open.
-/

import CatalanSun.Tail
import CatalanSun.TwoAdic
import Mathlib.Data.Matrix.Basic

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.style.multiGoal false
set_option maxHeartbeats 400000

noncomputable section

namespace CatalanSun.Residual

open CatalanSun Matrix

/-! ## Rational witness for `q · T_m` when `G = a / q`

Sun's tail recurrence `T_m + T_{m+1} = 1/(2m+1)²` (eq. 1.4, `Tail.tail_add_succ`)
lets us track `q · T_m` as an explicit rational number by induction on `m`,
without ever constructing the finite partial sum `S_{m-1}` from the paper. -/

/-- Rational witness for `q * T_m`, built from the recurrence
`T_{m+1} = 1/(2m+1)² - T_m` and the seed `T_0 = a / q`. -/
def ratWitness (q a : ℕ) : ℕ → ℚ
  | 0 => (a : ℚ)
  | m + 1 => (q : ℚ) / ((2 * m + 1 : ℕ) : ℚ) ^ 2 - ratWitness q a m

theorem ratWitness_eq {q a : ℕ} (hq : 0 < q)
    (hG : Tail.tail 0 = (a : ℝ) / (q : ℝ)) :
    ∀ m, (q : ℝ) * Tail.tail m = (ratWitness q a m : ℝ)
  | 0 => by
      have hq0 : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq.ne'
      simp [ratWitness, hG, mul_div_cancel₀, hq0]
  | m + 1 => by
      have hstep : Tail.tail (m + 1) = 1 / Tail.oddReal m ^ 2 - Tail.tail m := by
        linarith [Tail.tail_add_succ m]
      have hcast : Tail.oddReal m ^ 2 = (((2 * m + 1 : ℕ) : ℝ)) ^ 2 := by
        unfold Tail.oddReal; push_cast; ring
      have hprev := ratWitness_eq hq hG m
      calc (q : ℝ) * Tail.tail (m + 1)
          = (q : ℝ) * (1 / Tail.oddReal m ^ 2 - Tail.tail m) := by rw [hstep]
        _ = (q : ℝ) / Tail.oddReal m ^ 2 - (q : ℝ) * Tail.tail m := by ring
        _ = (q : ℝ) / (((2 * m + 1 : ℕ) : ℝ)) ^ 2 - (ratWitness q a m : ℝ) := by
              rw [hcast, hprev]
        _ = (ratWitness q a (m + 1) : ℝ) := by
              simp only [ratWitness]; push_cast; ring

theorem ratWitness_twoIntegral (q a : ℕ) :
    ∀ m, TwoAdic.IsTwoIntegral (ratWitness q a m)
  | 0 => by simpa [ratWitness] using TwoAdic.isTwoIntegral_nat a
  | m + 1 => by
      have hnum : TwoAdic.IsTwoIntegral ((q : ℚ) / ((2 * m + 1 : ℕ) : ℚ) ^ 2) := by
        have hq2 : TwoAdic.IsTwoIntegral (q : ℚ) := TwoAdic.isTwoIntegral_nat q
        have hodd : Odd ((2 * m + 1) ^ 2) :=
          TwoAdic.odd_sq_of_odd (TwoAdic.odd_two_mul_add_one m)
        have hpos : 0 < (2 * m + 1) ^ 2 := by positivity
        simpa using TwoAdic.isTwoIntegral_div_odd hodd hpos hq2
      simpa [ratWitness] using TwoAdic.isTwoIntegral_sub hnum (ratWitness_twoIntegral q a m)

/-- Rational witness for `q * u_m` (the weighted tail). -/
def uRatWitness (q a m : ℕ) : ℚ := ratWitness q a m / ((2 * m + 1 : ℕ) : ℚ)

theorem uRatWitness_eq {q a : ℕ} (hq : 0 < q)
    (hG : Tail.tail 0 = (a : ℝ) / (q : ℝ)) (m : ℕ) :
    (q : ℝ) * Tail.weightedTail m = (uRatWitness q a m : ℝ) := by
  have hcast : Tail.oddReal m = (((2 * m + 1 : ℕ) : ℝ)) := by
    unfold Tail.oddReal; push_cast; ring
  calc (q : ℝ) * Tail.weightedTail m
      = (q : ℝ) * (Tail.tail m / Tail.oddReal m) := by
        simp only [Tail.weightedTail]
    _ = ((q : ℝ) * Tail.tail m) / Tail.oddReal m := by ring
    _ = (ratWitness q a m : ℝ) / (((2 * m + 1 : ℕ) : ℝ)) := by
        rw [ratWitness_eq hq hG m, hcast]
    _ = (uRatWitness q a m : ℝ) := by
        simp only [uRatWitness]; push_cast; ring

theorem uRatWitness_twoIntegral (q a m : ℕ) : TwoAdic.IsTwoIntegral (uRatWitness q a m) := by
  unfold uRatWitness
  exact TwoAdic.isTwoIntegral_div_odd (TwoAdic.odd_two_mul_add_one m) (by positivity)
    (ratWitness_twoIntegral q a m)

/-! ## Residual matrix entries `R_{α,j}` (paper eq. (2.1))

`Rmatrix B α j := Σ_{i=0}^{α+2B} (-1)^i C(α+2B, i) Πᵢ u_{i+j}`, using the row
index `α` for the paper's `a` (renamed to avoid clashing with the numerator
`a` of `G = a/q`). -/

def Rmatrix (B α j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (α + 2 * B + 1),
    (-1 : ℝ) ^ i * (Nat.choose (α + 2 * B) i : ℝ) * (TwoAdic.PiFactor B i : ℝ) *
      Tail.weightedTail (i + j)

/-- Rational witness for `q * R_{α,j}`. -/
def RmatrixRatWitness (q a B α j : ℕ) : ℚ :=
  ∑ i ∈ Finset.range (α + 2 * B + 1),
    (-1 : ℚ) ^ i * (Nat.choose (α + 2 * B) i : ℚ) * (TwoAdic.PiFactor B i : ℚ) *
      uRatWitness q a (i + j)

theorem RmatrixRatWitness_eq {q a : ℕ} (hq : 0 < q)
    (hG : Tail.tail 0 = (a : ℝ) / (q : ℝ)) (B α j : ℕ) :
    (q : ℝ) * Rmatrix B α j = (RmatrixRatWitness q a B α j : ℝ) := by
  simp only [Rmatrix, RmatrixRatWitness]
  rw [Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  have h := uRatWitness_eq hq hG (i + j)
  calc (q : ℝ) *
        ((-1 : ℝ) ^ i * (Nat.choose (α + 2 * B) i : ℝ) * (TwoAdic.PiFactor B i : ℝ) *
          Tail.weightedTail (i + j))
      = (-1 : ℝ) ^ i * (Nat.choose (α + 2 * B) i : ℝ) * (TwoAdic.PiFactor B i : ℝ) *
          ((q : ℝ) * Tail.weightedTail (i + j)) := by ring
    _ = (-1 : ℝ) ^ i * (Nat.choose (α + 2 * B) i : ℝ) * (TwoAdic.PiFactor B i : ℝ) *
          (uRatWitness q a (i + j) : ℝ) := by rw [h]

/-- **Every residual-matrix entry `q·R_{α,j}` is 2-integral when `G ∈ ℚ`.**
This is the concrete instantiation, at Sun's definition (2.1), of the "qT_m
has only odd denominators ⇒ qR ⊆ ℤ_(2)" step in the proof of Lemma 5.4. -/
theorem RmatrixRatWitness_twoIntegral (q a B α j : ℕ) :
    TwoAdic.IsTwoIntegral (RmatrixRatWitness q a B α j) := by
  unfold RmatrixRatWitness
  apply TwoAdic.isTwoIntegral_sum
  intro i _
  refine TwoAdic.isTwoIntegral_mul' (TwoAdic.isTwoIntegral_mul'
    (TwoAdic.isTwoIntegral_mul' ?_ ?_) ?_) ?_
  · exact_mod_cast TwoAdic.isTwoIntegral_int ((-1 : ℤ) ^ i)
  · exact TwoAdic.isTwoIntegral_nat _
  · exact TwoAdic.isTwoIntegral_nat _
  · exact uRatWitness_twoIntegral q a (i + j)

/-- **Lemma 5.4, entry-level form.** If `G = a/q ∈ ℚ`, every residual entry
`q·R_{α,j}` has nonnegative 2-adic valuation — the fact that, combined with
`A_{2,B} < 0` (`TwoAdic.A2_neg_of_pos_v2`) via
`TwoAdic.posPart_sub_eq_zero_of_neg_of_nonneg`, gives `[A_{2,B} − R_{2,B}]₊ = 0`. -/
theorem lemma_5_4_entry (q a B α j : ℕ) :
    0 ≤ padicValRat 2 (RmatrixRatWitness q a B α j) :=
  RmatrixRatWitness_twoIntegral q a B α j

/-! ## Fin-indexed rational residual matrix

Same indexing as `Rank.RmatrixFin`: rows `Fin (S+3)`, columns `Fin S` with
column `j` corresponding to paper index `j+1`. -/

/-- Rational residual matrix whose entries are `RmatrixRatWitness` (i.e. witnesses
for `q · R_{α,j}`). -/
def RmatrixRatFin (q a B S : ℕ) : Matrix (Fin (S + 3)) (Fin S) ℚ :=
  Matrix.of fun α j => RmatrixRatWitness q a B α.val (j.val + 1)

end CatalanSun.Residual
