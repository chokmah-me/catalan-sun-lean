/-
  CatalanSun/PascalCauchy.lean

  Pascal–Cauchy factorization of residual minors (Sun arXiv:2609.04176v1 §4):
  PC0 structural rewrite / matrix product, PC1 Cauchy–Binet expansion to ∑ Ξ_I
  (paper (4.1) without the `q^S` factor), PC2 Lemma 4.2 odd-Cauchy instance,
  PC3 Lemma 4.1 structural factorization (`paperP` / real `Ψ_A`; integrality open).

  Sign convention follows `Tail.weightedTail_shift_succ` / Thm21 `hwt`:
  paper column `j ≥ 1` has leading coefficient `(-1)^{j-1}` (not the paper's
  written `(-1)^j`, which matches the obsolete `T_i` expansion).
-/

import CatalanSun.Structure
import CatalanSun.NewtonDiff
import CatalanSun.Residual
import CatalanSun.Rank
import CatalanSun.NewtonCompletion
import CatalanSun.Cauchy
import CatalanSun.CauchyBinet
import CatalanSun.Tail
import CatalanSun.TwoAdic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
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

namespace CatalanSun.PascalCauchy

open CatalanSun Matrix Finset Polynomial
open CatalanSun.Structure
open CatalanSun.NewtonCompletion

/-! ## PC0 — matrix factors -/

/-- Pascal (alternating binomial) factor; rows indexed by selected paper rows
`f α`, columns by Newton index `i : Fin (Ndim B S)`. -/
def pascalMatrix (B S : ℕ) (f : Fin S → Fin (S + 3)) :
    Matrix (Fin S) (Fin (Ndim B S)) ℝ :=
  Matrix.of fun α i =>
    (-1 : ℝ) ^ i.val * (((f α).val + 2 * B).choose i.val : ℝ)

/-- Diagonal of `Πᵢ · T_{i+1}`. -/
def diagFactors (B S : ℕ) : Fin (Ndim B S) → ℝ :=
  fun i => (TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1)

/-- Cauchy factor with odd denominators. Column `jj` ↔ paper `j = jj.val + 1`;
sign `(-1)^{jj.val} = (-1)^{j-1}` matches `weightedTail_shift_succ`. -/
def cauchyOddMatrix (B S : ℕ) :
    Matrix (Fin (Ndim B S)) (Fin S) ℝ :=
  Matrix.of fun i jj =>
    (-1 : ℝ) ^ jj.val / Tail.oddReal (i.val + (jj.val + 1))

/-- `Diag(Πᵢ T_{i+1}) · Cauchy`. -/
def diagCauchy (B S : ℕ) : Matrix (Fin (Ndim B S)) (Fin S) ℝ :=
  (Matrix.diagonal (diagFactors B S)) * cauchyOddMatrix B S

/-! ## Per-column remainder polynomial (Plam with a single column, no λ) -/

/-- Remainder after expanding `u_{i+j}` through `T_{i+1}`:
`∑_{m < j-1} (−1)^{j-2-m} · Π(X)/((2X+2j+1)(2X+2(m+1)+1)²)`.
Empty when `j = 1`. -/
def remPoly (B j : ℕ) : ℝ[X] :=
  ∑ m ∈ range (j - 1),
    C ((-1 : ℝ) ^ (j - 2 - m)) * cancelledProd B j (m + 1)

theorem natDegree_remPoly_le {B j : ℕ} (hj : 1 ≤ j) (hjB : j < B) (_hB : 2 ≤ B) :
    (remPoly B j).natDegree ≤ 2 * B - 3 := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro m hm
  refine (natDegree_C_mul_le _ _).trans ?_
  have hm' : m < j - 1 := mem_range.mp hm
  have hjI : j ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hℓ : m + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hne : j ≠ m + 1 := by omega
  exact natDegree_cancelledProd_le hjI hℓ hne

theorem eval_remPoly {B j i : ℕ} (hj : 1 ≤ j) (hjB : j < B) :
    (remPoly B j).eval (i : ℝ) =
      ∑ m ∈ range (j - 1),
        (-1 : ℝ) ^ (j - 2 - m) *
          ((TwoAdic.PiFactor B i : ℝ) /
            (Tail.oddReal (i + j) * Tail.oddReal (i + (m + 1)) ^ 2)) := by
  simp only [remPoly, eval_finsetSum, eval_mul, eval_C]
  refine sum_congr rfl fun m hm => ?_
  have hm' : m < j - 1 := mem_range.mp hm
  have hjI : j ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hℓ : m + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hne : j ≠ m + 1 := by omega
  rw [eval_cancelledProd hjI hℓ hne]

/-- The weighted-tail remainder (without the leading `T_{i+1}` term) equals
`remPoly.eval`. -/
theorem pi_mul_weightedTail_rem_eq_eval_remPoly {B j i : ℕ}
    (hj : 1 ≤ j) (hjB : j < B) :
    (TwoAdic.PiFactor B i : ℝ) *
        ((1 / Tail.oddReal (i + j)) *
          ∑ m ∈ range (j - 1),
            (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) =
      (remPoly B j).eval (i : ℝ) := by
  have hodd : Tail.oddReal (i + j) ≠ 0 := Tail.oddReal_ne_zero _
  rw [eval_remPoly hj hjB]
  -- Pull `Π / odd` through the sum.
  have hpull :
      (TwoAdic.PiFactor B i : ℝ) *
          ((1 / Tail.oddReal (i + j)) *
            ∑ m ∈ range (j - 1),
              (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) =
        ∑ m ∈ range (j - 1),
          (TwoAdic.PiFactor B i : ℝ) * (1 / Tail.oddReal (i + j)) *
            ((-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) := by
    rw [← mul_assoc, Finset.mul_sum]
  rw [hpull]
  refine sum_congr rfl fun m hm => ?_
  have hidx : i + 1 + m = i + (m + 1) := by omega
  rw [hidx]
  have hodd' : Tail.oddReal (i + (m + 1)) ≠ 0 := Tail.oddReal_ne_zero _
  field_simp [hodd, hodd']

/-! ## PC0 — entry rewrite -/

theorem Rmatrix_eq_T_succ_cauchy_sum {B α j : ℕ}
    (hj : 1 ≤ j) (hjB : j < B) (hB : 2 ≤ B) :
    Residual.Rmatrix B α j =
      (-1 : ℝ) ^ (j - 1) *
        ∑ i ∈ Finset.range (α + 2 * B + 1),
          (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j) := by
  -- Expand each weightedTail through T_{i+1}.
  have hwt : ∀ i : ℕ,
      Tail.weightedTail (i + j) =
        (-1 : ℝ) ^ (j - 1) * Tail.tail (i + 1) / Tail.oddReal (i + j) +
          (1 / Tail.oddReal (i + j)) *
            ∑ m ∈ range (j - 1),
              (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2 :=
    fun i => Tail.weightedTail_shift_succ (i := i) (j := j) hj
  -- Split R into main term + remainder.
  have hsplit :
      Residual.Rmatrix B α j =
        ∑ i ∈ range (α + 2 * B + 1),
            (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (TwoAdic.PiFactor B i : ℝ) *
              ((-1 : ℝ) ^ (j - 1) * Tail.tail (i + 1) / Tail.oddReal (i + j)) +
          ∑ i ∈ range (α + 2 * B + 1),
            (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (TwoAdic.PiFactor B i : ℝ) *
              ((1 / Tail.oddReal (i + j)) *
                ∑ m ∈ range (j - 1),
                  (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) := by
    simp only [Residual.Rmatrix]
    rw [← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [hwt i]
    ring
  -- Remainder = alternating binomial sum of remPoly, hence vanishes.
  have hrem :
      ∑ i ∈ range (α + 2 * B + 1),
          (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) *
            ((1 / Tail.oddReal (i + j)) *
              ∑ m ∈ range (j - 1),
                (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) =
        0 := by
    have hdeg := natDegree_remPoly_le hj hjB hB
    have hvanish :=
      NewtonDiff.alternating_binomial_sum_eval_eq_zero_of_deg_le_two_B_sub_three
        (R := ℝ) (p := remPoly B j) (B := B) (a := α) hB hdeg
    -- Identify the summand with remPoly.eval.
    have hident :
        ∑ i ∈ range (α + 2 * B + 1),
            (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (TwoAdic.PiFactor B i : ℝ) *
              ((1 / Tail.oddReal (i + j)) *
                ∑ m ∈ range (j - 1),
                  (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2) =
          ∑ i ∈ range (α + 2 * B + 1),
            (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (remPoly B j).eval (i : ℝ) := by
      refine sum_congr rfl fun i _ => ?_
      have hpi := pi_mul_weightedTail_rem_eq_eval_remPoly (B := B) (j := j) (i := i) hj hjB
      -- Goal: c * Π * rem_inner = c * remPoly.eval; rewrite via hpi.
      calc (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (TwoAdic.PiFactor B i : ℝ) *
              ((1 / Tail.oddReal (i + j)) *
                ∑ m ∈ range (j - 1),
                  (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2)
            = (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
                ((TwoAdic.PiFactor B i : ℝ) *
                  ((1 / Tail.oddReal (i + j)) *
                    ∑ m ∈ range (j - 1),
                      (-1 : ℝ) ^ (j - 2 - m) / Tail.oddReal (i + 1 + m) ^ 2)) := by
                ring
          _ = (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
                (remPoly B j).eval (i : ℝ) := by rw [hpi]
    rw [hident, hvanish]
  -- Factor `(-1)^{j-1}` out of the main sum.
  have hmain :
      ∑ i ∈ range (α + 2 * B + 1),
          (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) *
            ((-1 : ℝ) ^ (j - 1) * Tail.tail (i + 1) / Tail.oddReal (i + j)) =
        (-1 : ℝ) ^ (j - 1) *
          ∑ i ∈ range (α + 2 * B + 1),
            (-1 : ℝ) ^ i * ((α + 2 * B).choose i : ℝ) *
              (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
                Tail.oddReal (i + j) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, hrem, add_zero, hmain]

/-! ## PC0 — matrix product -/

theorem diagCauchy_apply (B S : ℕ) (i : Fin (Ndim B S)) (jj : Fin S) :
    diagCauchy B S i jj =
      (TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) *
        ((-1 : ℝ) ^ jj.val / Tail.oddReal (i.val + (jj.val + 1))) := by
  simp only [diagCauchy, Matrix.mul_apply, Matrix.diagonal, diagFactors, cauchyOddMatrix,
    Matrix.of_apply]
  -- Only the `i = i` diagonal term survives.
  classical
  simp [sum_ite_eq, if_pos rfl]

/-- Extend the alternating binomial sum from `range(a+2B+1)` to `Fin (Ndim B S)`
via `Nat.choose_eq_zero_of_lt`. -/
theorem sum_T_succ_eq_sum_fin {B S a : ℕ} (ha : a + 2 * B + 1 ≤ Ndim B S)
    (j : ℕ) :
    ∑ i ∈ range (a + 2 * B + 1),
        (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
          (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) / Tail.oddReal (i + j) =
      ∑ i : Fin (Ndim B S),
        (-1 : ℝ) ^ i.val * ((a + 2 * B).choose i.val : ℝ) *
          (TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) /
            Tail.oddReal (i.val + j) := by
  -- Rewrite Fin-sum as range(Ndim), then drop zero choose-terms past a+2B.
  have hFin :
      ∑ i : Fin (Ndim B S),
          (-1 : ℝ) ^ i.val * ((a + 2 * B).choose i.val : ℝ) *
            (TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) /
              Tail.oddReal (i.val + j) =
        ∑ i ∈ range (Ndim B S),
          (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j) := by
    simpa using
      (Fin.sum_univ_eq_sum_range
        (fun i =>
          (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j))
        (Ndim B S))
  rw [hFin]
  -- Split `range(Ndim) = range(a+2B+1) + Ico(a+2B+1, Ndim)`.
  have hsplit :=
    sum_range_add_sum_Ico
      (fun i =>
        (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
          (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) / Tail.oddReal (i + j))
      ha
  -- Tail of the split vanishes by choose = 0.
  have htail :
      ∑ i ∈ Ico (a + 2 * B + 1) (Ndim B S),
          (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j) =
        0 := by
    refine sum_eq_zero fun i hi => ?_
    have hi' : a + 2 * B + 1 ≤ i := (mem_Ico.mp hi).1
    have hlt : a + 2 * B < i := by omega
    have hz : (a + 2 * B).choose i = 0 := Nat.choose_eq_zero_of_lt hlt
    simp [hz]
  -- `hsplit` says range(N) = range(k) + Ico; rearrange.
  have : ∑ i ∈ range (Ndim B S),
      (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
        (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) / Tail.oddReal (i + j) =
      ∑ i ∈ range (a + 2 * B + 1),
          (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j) +
        ∑ i ∈ Ico (a + 2 * B + 1) (Ndim B S),
          (-1 : ℝ) ^ i * ((a + 2 * B).choose i : ℝ) *
            (TwoAdic.PiFactor B i : ℝ) * Tail.tail (i + 1) /
              Tail.oddReal (i + j) := hsplit.symm
  rw [this, htail, add_zero]

theorem RmatrixFin_submatrix_eq_mul {B S : ℕ}
    (hS : 0 < S) (h : S < B) (f : Fin S → Fin (S + 3)) :
    (Rank.RmatrixFin B S).submatrix f id =
      pascalMatrix B S f * diagCauchy B S := by
  have hB : 2 ≤ B := by omega
  ext α jj
  -- LHS is a residual entry at paper column jj.val+1.
  have hj : 1 ≤ jj.val + 1 := Nat.succ_pos _
  have hjB : jj.val + 1 < B := by omega
  simp only [submatrix_apply, id_eq, Rank.RmatrixFin, Matrix.of_apply]
  rw [Rmatrix_eq_T_succ_cauchy_sum (B := B) (α := (f α).val) (j := jj.val + 1) hj hjB hB]
  -- RHS is the matrix product entry.
  have hprod :
      (pascalMatrix B S f * diagCauchy B S) α jj =
        ∑ i : Fin (Ndim B S),
          (-1 : ℝ) ^ i.val * (((f α).val + 2 * B).choose i.val : ℝ) *
            ((TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) *
              ((-1 : ℝ) ^ jj.val /
                Tail.oddReal (i.val + (jj.val + 1)))) := by
    simp only [Matrix.mul_apply, pascalMatrix, Matrix.of_apply, diagCauchy_apply]
  rw [hprod]
  -- Factor `(-1)^{jj.val}` and identify with the extended T-sum.
  have hfactor :
      ∑ i : Fin (Ndim B S),
          (-1 : ℝ) ^ i.val * (((f α).val + 2 * B).choose i.val : ℝ) *
            ((TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) *
              ((-1 : ℝ) ^ jj.val /
                Tail.oddReal (i.val + (jj.val + 1)))) =
        (-1 : ℝ) ^ jj.val *
          ∑ i : Fin (Ndim B S),
            (-1 : ℝ) ^ i.val * (((f α).val + 2 * B).choose i.val : ℝ) *
              (TwoAdic.PiFactor B i.val : ℝ) * Tail.tail (i.val + 1) /
                Tail.oddReal (i.val + (jj.val + 1)) := by
    rw [Finset.mul_sum]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hfactor]
  -- `(j-1) = jj.val` for paper j = jj.val+1.
  have hsign : (-1 : ℝ) ^ ((jj.val + 1) - 1) = (-1 : ℝ) ^ jj.val := by
    simp
  rw [hsign]
  -- Extend the finite range sum to Fin Ndim.
  have ha : (f α).val + 2 * B + 1 ≤ Ndim B S := by
    simp only [Ndim]
    have : (f α).val ≤ S + 2 := Nat.lt_succ_iff.mp (f α).isLt
    omega
  have hext :=
    sum_T_succ_eq_sum_fin (B := B) (S := S) (a := (f α).val) ha (jj.val + 1)
  rw [hext]

/-! ## PC1 — Ξ and Cauchy–Binet expansion -/

/-- Paper (4.1) summand (without `q^S`): product of Pascal and DiagCauchy minors. -/
def Xi (B S : ℕ) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) : ℝ :=
  (CauchyBinet.colsSubmatrix (pascalMatrix B S f) I hI).det *
  (CauchyBinet.rowsSubmatrix (diagCauchy B S) I hI).det

theorem det_Rmatrix_submatrix_eq_sum_Xi {B S : ℕ}
    (hS : 0 < S) (h : S < B) (f : Fin S → Fin (S + 3)) :
    ((Rank.RmatrixFin B S).submatrix f id).det =
      ∑ I ∈ (Finset.univ : Finset (Fin (Ndim B S))).powersetCard S,
        if hI : I.card = S then Xi B S f I hI else 0 := by
  rw [RmatrixFin_submatrix_eq_mul hS h f]
  simpa [Xi] using
    CauchyBinet.det_mul_eq_sum_minors (pascalMatrix B S f) (diagCauchy B S)

/-! ## PC2 — Lemma 4.2 odd-Cauchy instance -/

/-- Paper (4.2): `V(I) = ∏_{u<v} (i_v − i_u)` for the increasing enum of `I`. -/
def vandermondeProd {N S : ℕ} (I : Finset (Fin N)) (hI : I.card = S) : ℝ :=
  ∏ u : Fin S, ∏ v ∈ Ioi u,
    (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ))

/-- Paper (4.2): `V(J) = ∏_{0≤u<v<S} (v − u)`. -/
def vandermondeProdFin (S : ℕ) : ℝ :=
  ∏ u : Fin S, ∏ v ∈ Ioi u, ((v.val : ℝ) - (u.val : ℝ))

/-- Unsigned odd Cauchy matrix: entries `1 / (2(i_ν + j) + 1)`. -/
def oddCauchyMatrix {N S : ℕ} (I : Finset (Fin N)) (hI : I.card = S) :
    Matrix (Fin S) (Fin S) ℝ :=
  Matrix.of fun ν jj =>
    (1 : ℝ) / Tail.oddReal ((I.orderEmbOfFin hI ν).val + (jj.val + 1))

/-- `∑_{i : Fin n} #(Ioi i) = n(n-1)/2`, in the doubled form. -/
theorem sum_card_Ioi_mul_two (n : ℕ) :
    (∑ i : Fin n, #(Ioi i)) * 2 = n * (n - 1) := by
  have h : ∑ i : Fin n, #(Ioi i) = ∑ i ∈ range n, (n - 1 - i) := by
    simp_rw [Fin.card_Ioi]
    exact Fin.sum_univ_eq_sum_range (fun i => n - 1 - i) n
  rw [h, sum_range_reflect (fun i => i) n, sum_range_id_mul_two]

theorem prod_Ioi_const (n : ℕ) (c : ℝ) :
    ∏ u : Fin n, ∏ _ ∈ Ioi u, c = c ^ (∑ u : Fin n, #(Ioi u)) := by
  simp_rw [prod_const]
  exact prod_pow_eq_pow_sum univ (fun u : Fin n => #(Ioi u)) c

/-- Remark 4.1 / Lemma 4.2: odd-denominator Cauchy closed form. -/
theorem lemma_4_2_odd_cauchy {N S : ℕ} (_hS : 0 < S)
    (I : Finset (Fin N)) (hI : I.card = S) :
    (oddCauchyMatrix (S := S) I hI).det =
      (2 : ℝ) ^ (S * (S - 1)) * vandermondeProd I hI * vandermondeProdFin S /
        ∏ ν : Fin S, ∏ jj : Fin S,
          Tail.oddReal ((I.orderEmbOfFin hI ν).val + (jj.val + 1)) := by
  let x : Fin S → ℝ := fun ν => 2 * ((I.orderEmbOfFin hI ν).val : ℝ)
  let y : Fin S → ℝ := fun jj => Tail.oddReal (jj.val + 1)
  have hxy : ∀ ν jj, x ν + y jj =
      Tail.oddReal ((I.orderEmbOfFin hI ν).val + (jj.val + 1)) := by
    intro ν jj
    simp only [x, y, Tail.oddReal]
    push_cast
    ring
  have hne : ∀ ν jj, x ν + y jj ≠ 0 := fun ν jj => by
    rw [hxy]
    exact Tail.oddReal_ne_zero _
  have hmat : oddCauchyMatrix (S := S) I hI = Cauchy.cauchyMatrix x y := by
    ext ν jj
    simp only [oddCauchyMatrix, Matrix.of_apply, Cauchy.cauchyMatrix_apply, one_div, hxy]
  rw [hmat, Cauchy.det_cauchyMatrix x y hne]
  have hden : Cauchy.cauchyDetDen x y =
      ∏ ν : Fin S, ∏ jj : Fin S,
        Tail.oddReal ((I.orderEmbOfFin hI ν).val + (jj.val + 1)) := by
    refine prod_congr rfl fun ν _ => prod_congr rfl fun jj _ => hxy ν jj
  have hnum : Cauchy.cauchyDetNum x y =
      (2 : ℝ) ^ (S * (S - 1)) * vandermondeProd I hI * vandermondeProdFin S := by
    simp only [Cauchy.cauchyDetNum, vandermondeProd, vandermondeProdFin]
    have hxdiff : ∀ u v : Fin S,
        x v - x u =
          2 * (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ)) := by
      intro u v
      simp only [x]
      ring
    have hydiff : ∀ u v : Fin S,
        y v - y u = 2 * ((v.val : ℝ) - (u.val : ℝ)) := by
      intro u v
      simp only [y, Tail.oddReal]
      push_cast
      ring
    have hterm : ∀ u v : Fin S,
        (x v - x u) * (y v - y u) =
          (4 : ℝ) *
            (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ)) *
              ((v.val : ℝ) - (u.val : ℝ)) := by
      intro u v
      rw [hxdiff, hydiff]
      ring
    simp_rw [hterm]
    have hsplit :
        (∏ u : Fin S, ∏ v ∈ Ioi u,
            (4 : ℝ) *
              (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ)) *
                ((v.val : ℝ) - (u.val : ℝ))) =
          (∏ u : Fin S, ∏ v ∈ Ioi u, (4 : ℝ)) *
            (∏ u : Fin S, ∏ v ∈ Ioi u,
              (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ))) *
              (∏ u : Fin S, ∏ v ∈ Ioi u, ((v.val : ℝ) - (u.val : ℝ))) := by
      calc
        (∏ u : Fin S, ∏ v ∈ Ioi u,
            (4 : ℝ) *
              (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ)) *
                ((v.val : ℝ) - (u.val : ℝ))) =
            ∏ u : Fin S,
              (∏ v ∈ Ioi u, (4 : ℝ)) *
                (∏ v ∈ Ioi u,
                  (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ))) *
                  (∏ v ∈ Ioi u, ((v.val : ℝ) - (u.val : ℝ))) := by
          refine prod_congr rfl fun u _ => ?_
          simp_rw [mul_assoc]
          rw [prod_mul_distrib, prod_mul_distrib]
        _ = (∏ u : Fin S, ∏ v ∈ Ioi u, (4 : ℝ)) *
              (∏ u : Fin S, ∏ v ∈ Ioi u,
                (((I.orderEmbOfFin hI v).val : ℝ) - ((I.orderEmbOfFin hI u).val : ℝ))) *
                (∏ u : Fin S, ∏ v ∈ Ioi u, ((v.val : ℝ) - (u.val : ℝ))) := by
          simp_rw [← prod_mul_distrib]
    rw [hsplit, prod_Ioi_const]
    have hpow : (4 : ℝ) ^ (∑ u : Fin S, #(Ioi u)) = (2 : ℝ) ^ (S * (S - 1)) := by
      have h4 : (4 : ℝ) = 2 ^ 2 := by norm_num
      rw [h4, ← pow_mul, show 2 * ∑ u : Fin S, #(Ioi u) = S * (S - 1) from
        (mul_comm _ _).trans (sum_card_Ioi_mul_two S)]
    rw [hpow]
  rw [hnum, hden]

/-- Column signs on `cauchyOddMatrix` factor out of the row-minor determinant. -/
theorem det_rowsSubmatrix_cauchyOddMatrix {B S : ℕ} (_hS : 0 < S)
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (CauchyBinet.rowsSubmatrix (cauchyOddMatrix B S) I hI).det =
      (∏ jj : Fin S, (-1 : ℝ) ^ jj.val) *
        (oddCauchyMatrix (N := Ndim B S) (S := S) I hI).det := by
  have hscale :
      CauchyBinet.rowsSubmatrix (cauchyOddMatrix B S) I hI =
        Matrix.of fun ν jj =>
          ((-1 : ℝ) ^ jj.val) *
            oddCauchyMatrix (N := Ndim B S) (S := S) I hI ν jj := by
    ext ν jj
    simp only [CauchyBinet.rowsSubmatrix_apply, cauchyOddMatrix, oddCauchyMatrix,
      Matrix.of_apply, id_eq]
    rw [div_eq_mul_inv, one_div]
  rw [hscale, det_mul_row]

theorem det_rowsSubmatrix_cauchyOddMatrix_closed {B S : ℕ} (hS : 0 < S)
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (CauchyBinet.rowsSubmatrix (cauchyOddMatrix B S) I hI).det =
      (∏ jj : Fin S, (-1 : ℝ) ^ jj.val) *
        ((2 : ℝ) ^ (S * (S - 1)) * vandermondeProd I hI * vandermondeProdFin S /
          ∏ ν : Fin S, ∏ jj : Fin S,
            Tail.oddReal ((I.orderEmbOfFin hI ν).val + (jj.val + 1))) := by
  rw [det_rowsSubmatrix_cauchyOddMatrix hS I hI, lemma_4_2_odd_cauchy hS I hI]

/-! ## PC3 — Lemma 4.1 structural (`paperP` / real `Ψ_A`)

Paper (4.3): residual binomial minor factors through `P_a(i) = ∏_{r=a+1}^{S+2}(2B+r-i)`
and Vandermonde `V(I)`. Integrality of the quotient `Ψ_A = det[P]/V(I)` is left
open (PARTIAL): blocked on a local alternating/`det_polyEval_dvd_vandermonde`
lemma over `ℤ`. -/

/-- Paper `P_a(i) = ∏_{r=a+1}^{S+2} (2B + r - i)` as a real (ℤ differences). -/
def paperP (B S a i : ℕ) : ℝ :=
  ∏ r ∈ Finset.Icc (a + 1) (S + 2), (((2 * B + r : ℤ) - (i : ℤ) : ℝ))

/-- Residual polynomial matrix on selected rows `f` and ordered columns of `I`. -/
def paperPMatrix (B S : ℕ) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    Matrix (Fin S) (Fin S) ℝ :=
  Matrix.of fun α ν =>
    paperP B S (f α).val (I.orderEmbOfFin hI ν).val

/-- Unsigned binomial minor on selected rows/columns. -/
def binomMatrix (B S : ℕ) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    Matrix (Fin S) (Fin S) ℝ :=
  Matrix.of fun α ν =>
    (((f α).val + 2 * B).choose (I.orderEmbOfFin hI ν).val : ℝ)

/-- Under `i ≤ a+2B`, every factor of `paperP` is a nonnegative Nat difference. -/
theorem paperP_eq_nat_prod {B S a i : ℕ} (hle : i ≤ a + 2 * B) (_ha : a ≤ S + 2) :
    paperP B S a i =
      ∏ r ∈ Finset.Icc (a + 1) (S + 2), ((2 * B + r - i : ℕ) : ℝ) := by
  refine prod_congr rfl fun r hr => ?_
  have hr' : a + 1 ≤ r ∧ r ≤ S + 2 := mem_Icc.mp hr
  have hge : i ≤ 2 * B + r := by omega
  -- `↑(2B+r-i) = ↑(2B+r) - ↑i` in ℤ, then cast to ℝ.
  have hz : ((2 * B + r : ℤ) - (i : ℤ)) = ((2 * B + r - i : ℕ) : ℤ) :=
    (Int.natCast_sub hge).symm
  exact_mod_cast hz

/-- `paperP` equals the descending factorial when `i ≤ a+2B`. -/
theorem paperP_eq_descFactorial {B S a i : ℕ}
    (ha : a ≤ S + 2) (hle : i ≤ a + 2 * B) :
    paperP B S a i =
      (((Ndim B S - 1 - i).descFactorial (S + 2 - a) : ℕ) : ℝ) := by
  have hN1 : Ndim B S - 1 = 2 * B + S + 2 := by
    simp only [Ndim]; omega
  rw [paperP_eq_nat_prod hle ha, ← Nat.cast_prod]
  refine congr_arg Nat.cast ?_
  rw [Nat.descFactorial_eq_prod_range, hN1]
  -- `Icc (a+1) (S+2) = Ico (a+1) (S+3)`.
  rw [← Finset.Ico_add_one_right_eq_Icc (a := a + 1) (b := S + 2)]
  rw [Finset.prod_Ico_eq_prod_range]
  have hlen : S + 2 + 1 - (a + 1) = S + 2 - a := by omega
  rw [hlen]
  -- Ascending factors equal reflected descending factors of `descFactorial`.
  have hterm : ∀ j ∈ range (S + 2 - a),
      2 * B + (a + 1 + j) - i =
        (2 * B + S + 2 - i) - ((S + 2 - a) - 1 - j) := by
    intro j hj
    have : j < S + 2 - a := mem_range.mp hj
    omega
  refine Eq.trans (prod_congr rfl hterm) ?_
  exact Finset.prod_range_reflect (fun t => (2 * B + S + 2 - i) - t) (S + 2 - a)

theorem paperP_eq_factorial_div {B S a i : ℕ}
    (ha : a ≤ S + 2) (hle : i ≤ a + 2 * B) :
    paperP B S a i =
      ((Ndim B S - 1 - i).factorial : ℝ) / ((a + 2 * B - i).factorial : ℝ) := by
  have hk : S + 2 - a ≤ Ndim B S - 1 - i := by
    simp only [Ndim]; omega
  have hsub : Ndim B S - 1 - i - (S + 2 - a) = a + 2 * B - i := by
    simp only [Ndim]; omega
  rw [paperP_eq_descFactorial ha hle]
  have hmul := Nat.factorial_mul_descFactorial hk
  rw [hsub] at hmul
  have hne : ((a + 2 * B - i).factorial : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  rw [eq_div_iff hne, ← Nat.cast_mul, Nat.mul_comm, hmul]

/-- `paperP` vanishes when `a+2B < i < Ndim` (zero factor in the product). -/
theorem paperP_eq_zero_of_lt {B S a i : ℕ}
    (_ha : a ≤ S + 2) (hlt : a + 2 * B < i) (hi : i < Ndim B S) :
    paperP B S a i = 0 := by
  have hlo : a + 1 ≤ i - 2 * B := by omega
  have hhi : i - 2 * B ≤ S + 2 := by
    simp only [Ndim] at hi; omega
  have hmem : i - 2 * B ∈ Finset.Icc (a + 1) (S + 2) := mem_Icc.mpr ⟨hlo, hhi⟩
  refine Finset.prod_eq_zero hmem ?_
  -- Factor elaborates as `↑(2*↑B + ↑(i-2B)) - ↑↑i` in ℝ.
  have hge : 2 * B ≤ i := by omega
  have hsub : ((i - 2 * B : ℕ) : ℤ) = (i : ℤ) - ((2 * B : ℕ) : ℤ) :=
    Int.natCast_sub hge
  have htwo : ((2 * B : ℕ) : ℤ) = (2 : ℤ) * (B : ℤ) := by push_cast; ring
  -- Rewrite the Nat-sub term, then cancel in ℤ.
  suffices hZ : ((2 : ℤ) * (B : ℤ) + ((i - 2 * B : ℕ) : ℤ) - (i : ℤ)) = 0 by
    exact_mod_cast hZ
  rw [hsub, htwo]
  ring

theorem choose_eq_factorial_mul_paperP_of_lt_Ndim {B S a i : ℕ}
    (ha : a ≤ S + 2) (hi : i < Ndim B S) :
    ((a + 2 * B).choose i : ℝ) =
      ((a + 2 * B).factorial : ℝ) /
        ((i.factorial : ℝ) * ((Ndim B S - 1 - i).factorial : ℝ)) *
          paperP B S a i := by
  rcases lt_or_ge (a + 2 * B) i with hlt | hle
  · -- Both sides vanish: choose = 0 and paperP = 0.
    have hz : (a + 2 * B).choose i = 0 := Nat.choose_eq_zero_of_lt hlt
    rw [hz, Nat.cast_zero, paperP_eq_zero_of_lt ha hlt hi, mul_zero]
  · have hP := paperP_eq_factorial_div ha hle
    have hch := Nat.cast_choose (K := ℝ) hle
    -- `cast_choose`: `(a+2B).choose i = (a+2B)! / (i! * (a+2B-i)!)`
    rw [hch, hP]
    have hne1 : (i.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hne2 : ((a + 2 * B - i).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    have hne3 : ((Ndim B S - 1 - i).factorial : ℝ) ≠ 0 :=
      Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    field_simp [hne1, hne2, hne3]

theorem det_binomMatrix_eq_factorials_mul_det_paperP
    {B S : ℕ} (_hS : 0 < S) (_h : S < B)
    (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (binomMatrix B S f I hI).det =
      (∏ α : Fin S, (((f α).val + 2 * B).factorial : ℝ)) *
        (∏ ν : Fin S,
          (1 : ℝ) / (((I.orderEmbOfFin hI ν).val.factorial : ℝ) *
            ((Ndim B S - 1 - (I.orderEmbOfFin hI ν).val).factorial : ℝ))) *
        (paperPMatrix B S f I hI).det := by
  let rowScale : Fin S → ℝ := fun α => (((f α).val + 2 * B).factorial : ℝ)
  let colScale : Fin S → ℝ := fun ν =>
    (1 : ℝ) / (((I.orderEmbOfFin hI ν).val.factorial : ℝ) *
      ((Ndim B S - 1 - (I.orderEmbOfFin hI ν).val).factorial : ℝ))
  have hentry : binomMatrix B S f I hI =
      Matrix.of fun α ν => rowScale α * (Matrix.of fun α ν =>
        colScale ν * paperPMatrix B S f I hI α ν) α ν := by
    ext α ν
    simp only [binomMatrix, paperPMatrix, Matrix.of_apply, rowScale, colScale]
    have ha : (f α).val ≤ S + 2 := Nat.lt_succ_iff.mp (f α).isLt
    have hi : (I.orderEmbOfFin hI ν).val < Ndim B S := (I.orderEmbOfFin hI ν).isLt
    have hch := choose_eq_factorial_mul_paperP_of_lt_Ndim (B := B) (S := S)
      (a := (f α).val) (i := (I.orderEmbOfFin hI ν).val) ha hi
    rw [hch]
    ring
  rw [hentry, det_mul_column, det_mul_row]
  ring

theorem det_colsSubmatrix_pascalMatrix
    {B S : ℕ} (_hS : 0 < S) (_h : S < B)
    (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (CauchyBinet.colsSubmatrix (pascalMatrix B S f) I hI).det =
      (∏ ν : Fin S, (-1 : ℝ) ^ (I.orderEmbOfFin hI ν).val) *
        (binomMatrix B S f I hI).det := by
  have hscale :
      CauchyBinet.colsSubmatrix (pascalMatrix B S f) I hI =
        Matrix.of fun α ν =>
          ((-1 : ℝ) ^ (I.orderEmbOfFin hI ν).val) * binomMatrix B S f I hI α ν := by
    ext α ν
    simp only [CauchyBinet.colsSubmatrix_apply, pascalMatrix, binomMatrix, Matrix.of_apply, id_eq]
  rw [hscale, det_mul_row]

/-- `V(I) ≠ 0` because `orderEmbOfFin` is strictly monotone on a set. -/
theorem vandermondeProd_ne_zero {N S : ℕ} (_hS : 0 < S)
    (I : Finset (Fin N)) (hI : I.card = S) :
    vandermondeProd I hI ≠ 0 := by
  simp only [vandermondeProd]
  refine prod_ne_zero_iff.mpr fun u _ => prod_ne_zero_iff.mpr fun v hv => ?_
  have huv : u < v := by simpa using hv
  have hlt : I.orderEmbOfFin hI u < I.orderEmbOfFin hI v :=
    (I.orderEmbOfFin hI).strictMono huv
  exact sub_ne_zero.mpr <|
    Nat.cast_injective.ne (Fin.val_injective.ne (ne_of_lt hlt)).symm

/-- Real stand-in for paper `Ψ_A` (integrality open). -/
noncomputable def PsiA_real (B S : ℕ) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) : ℝ :=
  (paperPMatrix B S f I hI).det / vandermondeProd I hI

theorem lemma_4_1_psi_real
    {B S : ℕ} (hS : 0 < S) (_h : S < B)
    (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (paperPMatrix B S f I hI).det =
      vandermondeProd I hI * PsiA_real B S f I hI := by
  rw [PsiA_real, mul_div_cancel₀ _ (vandermondeProd_ne_zero hS I hI)]

theorem lemma_4_1_real
    {B S : ℕ} (hS : 0 < S) (h : S < B)
    (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    (binomMatrix B S f I hI).det =
      vandermondeProd I hI * PsiA_real B S f I hI *
        (∏ α : Fin S, (((f α).val + 2 * B).factorial : ℝ)) /
        (∏ ν : Fin S,
          ((I.orderEmbOfFin hI ν).val.factorial : ℝ) *
            ((Ndim B S - 1 - (I.orderEmbOfFin hI ν).val).factorial : ℝ)) := by
  rw [det_binomMatrix_eq_factorials_mul_det_paperP hS h f I hI, lemma_4_1_psi_real hS h f I hI]
  -- Rewrite `∏ 1/(a*b)` as `1 / ∏ (a*b)`.
  have hinv :
      (∏ ν : Fin S,
          (1 : ℝ) / (((I.orderEmbOfFin hI ν).val.factorial : ℝ) *
            ((Ndim B S - 1 - (I.orderEmbOfFin hI ν).val).factorial : ℝ))) =
        1 / (∏ ν : Fin S,
          ((I.orderEmbOfFin hI ν).val.factorial : ℝ) *
            ((Ndim B S - 1 - (I.orderEmbOfFin hI ν).val).factorial : ℝ)) := by
    simp_rw [one_div]
    rw [← Finset.prod_inv_distrib]
  rw [hinv]
  ring

end CatalanSun.PascalCauchy
