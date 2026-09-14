/-
  CatalanSun/NewtonDiff.lean

  Finite-difference / Newton helpers for Sun arXiv:2609.04176v1 §2
  (Theorem 2.1 pipeline, milestones M1–M2).

  Main fact: if `natDegree p < n` then the paper's alternating binomial sum
  `∑_{i=0}^n (-1)^i C(n,i) p(i)` vanishes.
-/

import Mathlib.Algebra.Group.ForwardDiff
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp

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

theorem paperFwdDiff_add (f g : ℕ → R) (n : ℕ) :
    paperFwdDiff (fun i => f i + g i) n = paperFwdDiff f n + paperFwdDiff g n := by
  simp only [paperFwdDiff, mul_add, sum_add_distrib]

theorem paperFwdDiff_const_mul (c : R) (f : ℕ → R) (n : ℕ) :
    paperFwdDiff (fun i => c * f i) n = c * paperFwdDiff f n := by
  simp only [paperFwdDiff, mul_sum, mul_left_comm]

theorem paperFwdDiff_neg (f : ℕ → R) (n : ℕ) :
    paperFwdDiff (fun i => -f i) n = -paperFwdDiff f n := by
  simpa [neg_mul] using paperFwdDiff_const_mul (-1 : R) f n

theorem paperFwdDiff_sub (f g : ℕ → R) (n : ℕ) :
    paperFwdDiff (fun i => f i - g i) n = paperFwdDiff f n - paperFwdDiff g n := by
  simp only [sub_eq_add_neg, paperFwdDiff_add, paperFwdDiff_neg]

theorem paperFwdDiff_poly_eval (p : R[X]) (n : ℕ) :
    paperFwdDiff (fun i => p.eval (i : R)) n =
      (-1 : R) ^ n * (fwdDiff (1 : R))^[n] (eval · p) 0 := by
  simpa [paperFwdDiff] using
    alternating_sum_at_zero_eq_neg_pow_fwdDiff (eval · p) n

/-! ## M5 helpers: binomial polynomials and Newton interpolants

Over a characteristic-zero field, `binomPoly k` is the degree-`k` polynomial
`X(X-1)⋯(X-k+1)/k!`, and `newtonInterpolant f N` is the unique degree-`≤ N`
polynomial agreeing with `f` on `{0,…,N}`, written in the Newton basis.

Forward differences of a sequence `f : ℕ → K` are taken with Mathlib's
`fwdDiff (1 : ℕ)` (step `1` on the domain `ℕ`). -/

variable {K : Type*} [Field K] [CharZero K]

/-- Binomial polynomial `C(X, k) = descPochhammer(k) / k!`. -/
def binomPoly (k : ℕ) : K[X] :=
  C ((k.factorial : K)⁻¹) * descPochhammer K k

theorem natDegree_binomPoly (k : ℕ) : (binomPoly (K := K) k).natDegree = k := by
  have hfac : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hinv : (k.factorial : K)⁻¹ ≠ 0 := inv_ne_zero hfac
  rw [binomPoly, natDegree_C_mul hinv, descPochhammer_natDegree]

theorem binomPoly_ne_zero (k : ℕ) : binomPoly (K := K) k ≠ 0 := by
  have hfac : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hinv : (k.factorial : K)⁻¹ ≠ 0 := inv_ne_zero hfac
  cases k with
  | zero =>
    change C ((0 : ℕ).factorial : K)⁻¹ * 1 ≠ 0
    simpa using hinv
  | succ k =>
    have hdeg : (descPochhammer K (k + 1)).natDegree = k + 1 :=
      descPochhammer_natDegree (R := K) (k + 1)
    exact mul_ne_zero (by simp [hinv])
      (ne_zero_of_natDegree_gt (by rw [hdeg]; exact Nat.succ_pos _))

theorem eval_binomPoly (k n : ℕ) :
    (binomPoly (K := K) k).eval (n : K) = (n.choose k : K) := by
  have hfac : (k.factorial : K) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  simp only [binomPoly, eval_mul, eval_C]
  rw [Nat.cast_choose_eq_descPochhammer_div (K := K) n k]
  field_simp [hfac]

/-- Newton basis coefficient `Δ^k f(0)` (Mathlib forward difference on `ℕ`). -/
def newtonCoeff (f : ℕ → K) (k : ℕ) : K :=
  (fwdDiff (1 : ℕ))^[k] f 0

omit [CharZero K] in
theorem newtonCoeff_eq_paperFwdDiff (f : ℕ → K) (k : ℕ) :
    newtonCoeff f k = (-1 : K) ^ k * paperFwdDiff f k := by
  have hΔ := fwdDiff_iter_eq_sum_shift (h := (1 : ℕ)) f k 0
  have hsum :
      newtonCoeff f k =
        ∑ j ∈ range (k + 1),
          ((-1 : K) ^ (k - j) * (k.choose j : K)) * f j := by
    rw [newtonCoeff, hΔ]
    refine sum_congr rfl fun j hj => ?_
    simp only [nsmul_one, zero_add, zsmul_eq_mul]
    push_cast
    ring
  -- (-1)^{k-j} = (-1)^k * (-1)^j when j ≤ k
  have hpaper :
      ∑ j ∈ range (k + 1),
          ((-1 : K) ^ (k - j) * (k.choose j : K)) * f j =
        (-1 : K) ^ k *
          ∑ j ∈ range (k + 1), (-1 : K) ^ j * (k.choose j : K) * f j := by
    refine Eq.trans ?_ (mul_sum _ _ _).symm
    refine sum_congr rfl fun j hj => ?_
    have hj' : j ≤ k := Nat.lt_succ_iff.mp (mem_range.mp hj)
    rw [neg_one_pow_sub_eq (R := K) hj']
    ring
  simpa [hsum, paperFwdDiff] using hpaper

/-- Newton interpolant of `f` through `{0,…,N}` in the binomial basis. -/
def newtonInterpolant (f : ℕ → K) (N : ℕ) : K[X] :=
  ∑ k ∈ range (N + 1), C (newtonCoeff f k) * binomPoly (K := K) k

theorem natDegree_newtonInterpolant_le (f : ℕ → K) (N : ℕ) :
    (newtonInterpolant f N).natDegree ≤ N := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro k hk
  have hk' : k ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hk)
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_binomPoly]
  exact hk'

/-- If high-order paper differences vanish on `[M, N]`, the interpolant has
degree `≤ M - 1` (for `M ≥ 1`). -/
theorem natDegree_newtonInterpolant_of_high_vanishing {f : ℕ → K} {M N : ℕ}
    (_hM : 1 ≤ M) (hMN : M ≤ N)
    (hvan : ∀ k, M ≤ k → k ≤ N → paperFwdDiff f k = 0) :
    (newtonInterpolant f N).natDegree ≤ M - 1 := by
  have hsum :
      newtonInterpolant f N =
        ∑ k ∈ range M, C (newtonCoeff f k) * binomPoly (K := K) k := by
    rw [newtonInterpolant]
    have hsplit : range (N + 1) = range M ∪ Icc M N := by
      ext x
      simp only [mem_union, mem_range, mem_Icc]
      omega
    have hdisj : Disjoint (range M) (Icc M N) := by
      refine disjoint_left.mpr ?_
      intro x hxM hxI
      simp only [mem_range, mem_Icc] at hxM hxI
      omega
    rw [hsplit, sum_union hdisj, add_eq_left]
    refine sum_eq_zero fun k hk => ?_
    have hkM : M ≤ k := (mem_Icc.mp hk).1
    have hkN : k ≤ N := (mem_Icc.mp hk).2
    have hΔ : newtonCoeff f k = 0 := by
      rw [newtonCoeff_eq_paperFwdDiff, hvan k hkM hkN, mul_zero]
    simp [hΔ]
  rw [hsum]
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro k hk
  have hk' : k < M := mem_range.mp hk
  refine (natDegree_C_mul_le _ _).trans ?_
  rw [natDegree_binomPoly]
  exact Nat.le_sub_one_of_lt hk'

theorem eval_newtonInterpolant {f : ℕ → K} {N n : ℕ} (hn : n ≤ N) :
    (newtonInterpolant f N).eval (n : K) = f n := by
  -- Gregory–Newton on `ℕ` with step `1`.
  have hGN := shift_eq_sum_fwdDiff_iter (h := (1 : ℕ)) f n 0
  have hleft : f (0 + n • 1) = f n := by simp
  have hsum :
      (newtonInterpolant f N).eval (n : K) =
        ∑ k ∈ range (N + 1), newtonCoeff f k * (n.choose k : K) := by
    simp only [newtonInterpolant, eval_finsetSum, eval_mul, eval_C, eval_binomPoly]
  have htrunc :
      ∑ k ∈ range (N + 1), newtonCoeff f k * (n.choose k : K) =
        ∑ k ∈ range (n + 1), newtonCoeff f k * (n.choose k : K) := by
    refine (sum_subset (range_mono (Nat.succ_le_succ hn)) ?_).symm
    intro k hkN hkN'
    have hk : n < k := by
      simp only [mem_range] at hkN' ⊢
      omega
    simp [Nat.choose_eq_zero_of_lt hk]
  have hsmul :
      ∑ k ∈ range (n + 1), newtonCoeff f k * (n.choose k : K) =
        ∑ k ∈ range (n + 1), n.choose k • newtonCoeff f k := by
    refine sum_congr rfl fun k _ => ?_
    rw [nsmul_eq_mul, mul_comm]
  calc (newtonInterpolant f N).eval (n : K)
      = ∑ k ∈ range (N + 1), newtonCoeff f k * (n.choose k : K) := hsum
    _ = ∑ k ∈ range (n + 1), newtonCoeff f k * (n.choose k : K) := htrunc
    _ = ∑ k ∈ range (n + 1), n.choose k • newtonCoeff f k := hsmul
    _ = ∑ k ∈ range (n + 1), n.choose k • (fwdDiff (1 : ℕ))^[k] f 0 := by
          simp only [newtonCoeff]
    _ = f (0 + n • 1) := hGN.symm
    _ = f n := hleft

/-- Convenience: interpolant through `0..N` with vanishing orders `M..N`
has degree `≤ M-1` and matches `f` on `0..N`. -/
theorem exists_newtonInterpolant_of_high_vanishing {f : ℕ → K} {M N : ℕ}
    (hM : 1 ≤ M) (hMN : M ≤ N)
    (hvan : ∀ k, M ≤ k → k ≤ N → paperFwdDiff f k = 0) :
    ∃ p : K[X], p.natDegree ≤ M - 1 ∧ ∀ i ≤ N, p.eval (i : K) = f i := by
  refine ⟨newtonInterpolant f N, natDegree_newtonInterpolant_of_high_vanishing hM hMN hvan, ?_⟩
  intro i hi
  exact eval_newtonInterpolant hi

end CatalanSun.NewtonDiff
