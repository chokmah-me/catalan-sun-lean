/-
  CatalanSun/NewtonDiff.lean

  Finite-difference / Newton helpers for Sun arXiv:2609.04176v1 §2
  (Theorem 2.1 pipeline, milestones M1–M2).

  Main fact: if `natDegree p < n` then the paper's alternating binomial sum
  `∑_{i=0}^n (-1)^i C(n,i) p(i)` vanishes.
-/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false

noncomputable section

namespace CatalanSun.NewtonDiff

open Polynomial Finset
open scoped fwdDiff

variable {R : Type*} [CommRing R]

/-! ## Sign conversion between Mathlib and paper conventions

Mathlib `fwdDiff_iter_eq_sum_shift` expands
`Δⁿ f(y) = ∑_k ((-1)^{n-k} C(n,k)) • f(y+k)`.
The paper writes `∑_i (-1)^i C(n,i) f(i)`. These differ by the unit `(-1)^n`. -/

theorem neg_one_pow_mul_self (k : ℕ) : (-1 : R) ^ k * (-1 : R) ^ k = 1 := by
  rw [← pow_add, ← two_mul, Even.neg_one_pow (even_two_mul k)]

theorem neg_one_pow_sub_eq {n k : ℕ} (hk : k ≤ n) :
    (-1 : R) ^ (n - k) = (-1 : R) ^ n * (-1 : R) ^ k := by
  calc (-1 : R) ^ (n - k)
      = (-1 : R) ^ (n - k) * 1 := (mul_one _).symm
    _ = (-1 : R) ^ (n - k) * ((-1 : R) ^ k * (-1 : R) ^ k) := by
          rw [neg_one_pow_mul_self]
    _ = ((-1 : R) ^ (n - k) * (-1 : R) ^ k) * (-1 : R) ^ k := by ring
    _ = (-1 : R) ^ ((n - k) + k) * (-1 : R) ^ k := by rw [← pow_add]
    _ = (-1 : R) ^ n * (-1 : R) ^ k := by rw [Nat.sub_add_cancel hk]

private theorem neg_one_pow_n_mul_sub {n k : ℕ} (hk : k ≤ n) :
    (-1 : R) ^ n * (-1 : R) ^ (n - k) = (-1 : R) ^ k := by
  rw [neg_one_pow_sub_eq hk, ← mul_assoc, neg_one_pow_mul_self, one_mul]

private theorem fwdDiff_iter_sum_cast (f : R → R) (n : ℕ) (y : R) :
    (fwdDiff (1 : R))^[n] f y =
      ∑ k ∈ range (n + 1),
        ((-1 : R) ^ (n - k) * (n.choose k : R)) * f (y + (k : R)) := by
  rw [fwdDiff_iter_eq_sum_shift (h := (1 : R))]
  refine sum_congr rfl fun k _ => ?_
  rw [nsmul_one, zsmul_eq_mul]
  push_cast
  ring

/-- Paper alternating sum equals `(-1)^n` times the Mathlib forward difference. -/
theorem alternating_sum_eq_neg_pow_fwdDiff (f : R → R) (n : ℕ) (y : R) :
    ∑ i ∈ range (n + 1), (-1 : R) ^ i * (n.choose i : R) * f (y + (i : R)) =
      (-1 : R) ^ n * (fwdDiff (1 : R))^[n] f y := by
  rw [fwdDiff_iter_sum_cast]
  refine Eq.trans ?_ (mul_sum _ _ _).symm
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsign := neg_one_pow_n_mul_sub (R := R) hk'
  -- (-1)^k * C * f = (-1)^n * ((-1)^{n-k} * C * f)
  calc (-1 : R) ^ k * (n.choose k : R) * f (y + (k : R))
      = ((-1 : R) ^ n * (-1 : R) ^ (n - k)) * (n.choose k : R) *
          f (y + (k : R)) := by rw [← hsign]
    _ = (-1 : R) ^ n * (((-1 : R) ^ (n - k) * (n.choose k : R)) *
          f (y + (k : R))) := by ring

/-- Specialization at `y = 0`. -/
theorem alternating_sum_at_zero_eq_neg_pow_fwdDiff (f : R → R) (n : ℕ) :
    ∑ i ∈ range (n + 1), (-1 : R) ^ i * (n.choose i : R) * f (i : R) =
      (-1 : R) ^ n * (fwdDiff (1 : R))^[n] f 0 := by
  simpa using alternating_sum_eq_neg_pow_fwdDiff f n 0

/-- **M1.** Degree-`< n` polynomials have vanishing paper alternating sums. -/
theorem alternating_binomial_sum_eval_eq_zero {p : R[X]} {n : ℕ}
    (hp : p.natDegree < n) :
    ∑ i ∈ range (n + 1), (-1 : R) ^ i * (n.choose i : R) * p.eval (i : R) = 0 := by
  have hΔ : (fwdDiff (1 : R))^[n] (eval · p) 0 = 0 :=
    congrFun (Polynomial.fwdDiff_iter_eq_zero_of_degree_lt hp) 0
  simpa [hΔ] using alternating_sum_at_zero_eq_neg_pow_fwdDiff (eval · p) n

/-- Variant with degree bound `≤ 2B - 3` and difference order `a + 2B`
(paper §2 finite-diff vanishing when `a + 2B > 2B - 3`). -/
theorem alternating_binomial_sum_eval_eq_zero_of_deg_le_two_B_sub_three
    {p : R[X]} {B a : ℕ} (_hB : 2 ≤ B)
    (hp : p.natDegree ≤ 2 * B - 3) :
    ∑ i ∈ range (a + 2 * B + 1),
      (-1 : R) ^ i * ((a + 2 * B).choose i : R) * p.eval (i : R) = 0 := by
  refine alternating_binomial_sum_eval_eq_zero ?_
  have hlt : 2 * B - 3 < a + 2 * B := by omega
  exact lt_of_le_of_lt hp hlt

/-! ## M2: binomial / Pochhammer helpers -/

/-- `b! · C(a,b) = (descPochhammer R b).eval a` as a ring identity. -/
theorem factorial_mul_choose_eq_descPochhammer_eval (a b : ℕ) :
    (b.factorial : R) * (a.choose b : R) = (descPochhammer R b).eval (a : R) := by
  rw [descPochhammer_eval_eq_descFactorial (R := R) a b,
    Nat.descFactorial_eq_factorial_mul_choose a b]
  push_cast
  ring

/-- Evaluation form used by Newton / binomial-basis bookkeeping. -/
theorem descPochhammer_eval_eq_factorial_mul_choose (k n : ℕ) :
    (descPochhammer R k).eval (n : R) = (k.factorial : R) * (n.choose k : R) := by
  simpa [mul_comm] using (factorial_mul_choose_eq_descPochhammer_eval (R := R) n k).symm

/-- Forward difference of order `n` with paper signs, on a sequence `ℕ → R`. -/
def paperFwdDiff (f : ℕ → R) (n : ℕ) : R :=
  ∑ i ∈ range (n + 1), (-1 : R) ^ i * (n.choose i : R) * f i

theorem paperFwdDiff_eq (f : ℕ → R) (n : ℕ) :
    paperFwdDiff f n =
      (-1 : R) ^ n *
        ∑ k ∈ range (n + 1),
          ((-1 : R) ^ (n - k) * (n.choose k : R)) * f k := by
  unfold paperFwdDiff
  refine Eq.trans ?_ (mul_sum _ _ _).symm
  refine sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (mem_range.mp hk)
  have hsign := neg_one_pow_n_mul_sub (R := R) hk'
  calc (-1 : R) ^ k * (n.choose k : R) * f k
      = ((-1 : R) ^ n * (-1 : R) ^ (n - k)) * (n.choose k : R) * f k := by
          rw [← hsign]
    _ = (-1 : R) ^ n * (((-1 : R) ^ (n - k) * (n.choose k : R)) * f k) := by ring

/-- If a sequence agrees with a degree-`< n` polynomial on `0..n`, its paper
forward difference of order `n` vanishes. -/
theorem paperFwdDiff_eq_zero_of_poly {p : R[X]} {n : ℕ} (hp : p.natDegree < n)
    {f : ℕ → R} (hf : ∀ i ≤ n, f i = p.eval (i : R)) :
    paperFwdDiff f n = 0 := by
  unfold paperFwdDiff
  convert alternating_binomial_sum_eval_eq_zero hp using 2 with i hi
  rw [hf i (Nat.lt_succ_iff.mp (mem_range.mp hi))]

end CatalanSun.NewtonDiff
