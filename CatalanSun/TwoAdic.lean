/-
  CatalanSun/TwoAdic.lean

  P1 targets from Sun arXiv:2609.04176v1 Lemma 5.4:
  * Positive-part collapse: if `A < 0` and `0 ≤ R` then `[A − R]₊ = 0`
  * Odd natural denominators imply nonnegative 2-adic valuation on `ℚ`
  * Building blocks of the residual matrix are odd (`2m+1`, `Πᵢ`)
  * Closure of 2-integrality under multiplication and division by odd naturals

  Does not yet assemble the full residual-matrix entry formula.
-/

import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option linter.style.header false

/-!
# Lemma 5.4 toolkit (P1)

Arithmetic facts underlying the paper's claim that the prime-2 positive-part
layer vanishes.
-/

namespace CatalanSun.TwoAdic

/-! ## Positive part (paper notation `[x]₊ = max{x, 0}`) -/

/-- Integer positive part. -/
def posPart (x : ℤ) : ℤ := max x 0

/-- **Lemma 5.4 arithmetic core.** If the 2-adic denominator layer `A` is
strictly negative and the residual valuation `R` is nonnegative, then the
positive-part contribution vanishes. -/
theorem posPart_sub_eq_zero_of_neg_of_nonneg (A R : ℤ)
    (hA : A < 0) (hR : 0 ≤ R) : posPart (A - R) = 0 := by
  unfold posPart
  have h : A - R ≤ 0 := by linarith
  exact max_eq_right h

/-- Specialization matching paper notation `[A_{2,B} − R_{2,B}]₊ = 0`. -/
theorem lemma_5_4_positive_part (A₂ R₂ : ℤ)
    (hA : A₂ < 0) (hR : 0 ≤ R₂) : posPart (A₂ - R₂) = 0 :=
  posPart_sub_eq_zero_of_neg_of_nonneg A₂ R₂ hA hR

/-! ## 2-integrality on `ℚ` -/

/-- A rational lies in `ℤ_{(2)}` iff its 2-adic valuation is nonnegative. -/
def IsTwoIntegral (q : ℚ) : Prop := 0 ≤ padicValRat 2 q

theorem isTwoIntegral_int (z : ℤ) : IsTwoIntegral (z : ℚ) := by
  unfold IsTwoIntegral
  simp [padicValRat.of_int, Nat.cast_nonneg]

theorem isTwoIntegral_nat (n : ℕ) : IsTwoIntegral (n : ℚ) :=
  isTwoIntegral_int n

/-- Odd denominator ⇒ nonnegative 2-valuation. -/
theorem isTwoIntegral_of_odd_den (q : ℚ) (hodd : Odd q.den) : IsTwoIntegral q := by
  unfold IsTwoIntegral
  have hden0 : padicValNat 2 q.den = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hdiv
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hdiv)
  have : padicValRat 2 q = (padicValInt 2 q.num : ℤ) := by
    simp [padicValRat, hden0]
  rw [this]
  exact Nat.cast_nonneg _

theorem isTwoIntegral_mul {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (haI : IsTwoIntegral a) (hbI : IsTwoIntegral b) : IsTwoIntegral (a * b) := by
  unfold IsTwoIntegral at *
  rw [padicValRat.mul (p := 2) ha hb]
  linarith

/-- Zero-safe product: no nonvanishing hypotheses needed. -/
theorem isTwoIntegral_mul' {a b : ℚ} (haI : IsTwoIntegral a) (hbI : IsTwoIntegral b) :
    IsTwoIntegral (a * b) := by
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha, IsTwoIntegral, padicValRat.zero]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb, IsTwoIntegral, padicValRat.zero]
  exact isTwoIntegral_mul ha hb haI hbI

theorem isTwoIntegral_zero : IsTwoIntegral 0 := by
  simp [IsTwoIntegral, padicValRat.zero]

theorem isTwoIntegral_neg {a : ℚ} (haI : IsTwoIntegral a) : IsTwoIntegral (-a) := by
  unfold IsTwoIntegral at *
  rwa [padicValRat.neg (p := 2)]

/-- Ultrametric closure: 2-integrality is preserved under addition. -/
theorem isTwoIntegral_add {a b : ℚ} (haI : IsTwoIntegral a) (hbI : IsTwoIntegral b) :
    IsTwoIntegral (a + b) := by
  rcases eq_or_ne (a + b) 0 with hab | hab
  · rw [hab]; exact isTwoIntegral_zero
  unfold IsTwoIntegral at *
  exact le_trans (le_min haI hbI) (padicValRat.min_le_padicValRat_add (p := 2) hab)

theorem isTwoIntegral_sub {a b : ℚ} (haI : IsTwoIntegral a) (hbI : IsTwoIntegral b) :
    IsTwoIntegral (a - b) := by
  rw [sub_eq_add_neg]
  exact isTwoIntegral_add haI (isTwoIntegral_neg hbI)

/-- Finite sums of 2-integral rationals are 2-integral. -/
theorem isTwoIntegral_sum {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, IsTwoIntegral (f i)) : IsTwoIntegral (∑ i ∈ s, f i) := by
  classical
  revert h
  refine s.induction_on (motive := fun t => (∀ i ∈ t, IsTwoIntegral (f i)) →
    IsTwoIntegral (∑ i ∈ t, f i)) ?base ?step
  · intro _; simpa using isTwoIntegral_zero
  · intro a s ha ih h
    rw [Finset.sum_insert ha]
    exact isTwoIntegral_add (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Finite products of 2-integral rationals are 2-integral. -/
theorem isTwoIntegral_prod {ι : Type*} {s : Finset ι} {f : ι → ℚ}
    (h : ∀ i ∈ s, IsTwoIntegral (f i)) : IsTwoIntegral (∏ i ∈ s, f i) := by
  classical
  revert h
  refine s.induction_on (motive := fun t => (∀ i ∈ t, IsTwoIntegral (f i)) →
    IsTwoIntegral (∏ i ∈ t, f i)) ?base ?step
  · intro _
    simpa using isTwoIntegral_nat 1
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact isTwoIntegral_mul' (h a (Finset.mem_insert_self _ _))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Division by an odd positive natural preserves 2-integrality. -/
theorem isTwoIntegral_div_odd {q : ℚ} {d : ℕ} (hd : Odd d) (hdpos : 0 < d)
    (hq : IsTwoIntegral q) : IsTwoIntegral (q / d) := by
  unfold IsTwoIntegral at *
  have hd0 : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hdpos)
  by_cases hq0 : q = 0
  · subst hq0
    simp [padicValRat.zero]
  · have hden : padicValRat 2 (d : ℚ) = 0 := by
      have : padicValNat 2 d = 0 := by
        apply padicValNat.eq_zero_of_not_dvd
        intro hdiv
        exact (Nat.not_even_iff_odd.mpr hd) (even_iff_two_dvd.mpr hdiv)
      simpa [padicValRat.of_nat] using congrArg (fun n : ℕ => (n : ℤ)) this
    rw [div_eq_mul_inv, padicValRat.mul (p := 2) hq0 (inv_ne_zero hd0), padicValRat.inv, hden]
    simpa using hq

/-! ## Odd building blocks from the residual matrix -/

/-- Every weight denominator `2m + 1` is odd. -/
theorem odd_two_mul_add_one (m : ℕ) : Odd (2 * m + 1) :=
  ⟨m, by ring⟩

/-- Squares of odd naturals are odd. -/
theorem odd_sq_of_odd {n : ℕ} (h : Odd n) : Odd (n ^ 2) :=
  Odd.pow h

/-- Finite products of odd naturals are odd. -/
theorem odd_prod {ι : Type*} {s : Finset ι} {f : ι → ℕ}
    (h : ∀ i ∈ s, Odd (f i)) : Odd (∏ i ∈ s, f i) := by
  classical
  revert h
  refine s.induction_on (motive := fun t => (∀ i ∈ t, Odd (f i)) → Odd (∏ i ∈ t, f i)) ?base ?step
  · intro _
    -- empty product = 1 = 2*0+1
    exact ⟨0, by simp⟩
  · intro a s ha ih h
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).mul
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- Paper factor `Πᵢ = ∏_{h=1}^{B} (2(h + i) + 1)²`.
Indexing uses `h ∈ range B` for `h = 0..B-1`, matching `h' = h+1 ∈ {1..B}`. -/
def PiFactor (B i : ℕ) : ℕ :=
  ∏ h ∈ Finset.range B, (2 * (h + 1 + i) + 1) ^ 2

theorem odd_PiFactor (B i : ℕ) : Odd (PiFactor B i) := by
  unfold PiFactor
  apply odd_prod
  intro h _
  exact odd_sq_of_odd (odd_two_mul_add_one (h + 1 + i))

/-- Consequently `Πᵢ` contributes `v₂(Πᵢ) = 0` to the 2-adic layer. -/
theorem padicValNat_two_PiFactor (B i : ℕ) : padicValNat 2 (PiFactor B i) = 0 := by
  apply padicValNat.eq_zero_of_not_dvd
  intro hdiv
  exact (Nat.not_even_iff_odd.mpr (odd_PiFactor B i)) (even_iff_two_dvd.mpr hdiv)

/-- Sign implication used in Lemma 5.4: if `v₂(F_B) > 0` then
`A₂,B = −v₂(F_B) < 0`. -/
theorem A2_neg_of_pos_v2 (v : ℕ) (hv : 0 < v) : (-(v : ℤ) : ℤ) < 0 :=
  neg_neg_of_pos (Int.natCast_pos.mpr hv)

/-- Assemble the paper's Lemma 5.4 conclusion from its two numeric hypotheses. -/
theorem lemma_5_4_from_layers (vF : ℕ) (R₂ : ℤ)
    (hvF : 0 < vF) (hR : 0 ≤ R₂) :
    posPart ((-(vF : ℤ)) - R₂) = 0 :=
  lemma_5_4_positive_part _ R₂ (A2_neg_of_pos_v2 vF hvF) hR

/-! ## Determinant closure of 2-integrality -/

/-- If every entry of a square rational matrix is 2-integral, so is its determinant. -/
theorem isTwoIntegral_det {n : Type*} [Fintype n] [DecidableEq n]
    (M : Matrix n n ℚ) (h : ∀ i j, IsTwoIntegral (M i j)) :
    IsTwoIntegral M.det := by
  classical
  rw [Matrix.det_apply']
  apply isTwoIntegral_sum
  intro σ _
  refine isTwoIntegral_mul' ?sign ?prod
  · exact isTwoIntegral_int (Equiv.Perm.sign σ : ℤ)
  · exact isTwoIntegral_prod fun i _ => h (σ i) i

end CatalanSun.TwoAdic
