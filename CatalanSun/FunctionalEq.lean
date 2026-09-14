/-
  CatalanSun/FunctionalEq.lean

  P3 fragments from Sun arXiv:2609.04176v1 Theorem 2.1:
  polynomial / constant-denominator obstruction for
  `S₀(z) + S₀(z+1) = 1/(4z²)`, extended to the full theorem: no nonzero
  rational function `P/Q` (P, Q ∈ ℚ[X], Q ≠ 0) satisfies the cleared
  functional equation.
-/

import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option linter.style.header false

/-!
# Functional equation impossibility fragments (P3), and the full theorem

The bulk of the file works generically over a characteristic-zero field `K`
(the definitions `shiftPoly`/`ClearedEq` and the base case
`no_constant_denom_solution` are stated for `{K} [Field K] [CharZero K]`, so
the original ℚ-specialized names from earlier passes keep working unchanged
with `K := ℚ` inferred from the argument types). The hard direction
(`no_rational_solution`, no nonzero `Q` works, not just constants) is proved
by specializing to `K := ℂ`, using an extremal-real-part-root argument to
find a common root of `P` and `Q`, canceling it, and inducting on
`Q.natDegree`; the ℂ-result is then transported back to ℚ via
`Polynomial.map (algebraMap ℚ ℂ)`.
-/

namespace CatalanSun.FunctionalEq

open Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Polynomial shift `p(X) ↦ p(X+1)`. -/
noncomputable def shiftPoly (p : K[X]) : K[X] :=
  p.comp (X + C 1)

omit [CharZero K] in
@[simp] theorem shiftPoly_C (a : K) : shiftPoly (C a) = C a := by
  simp [shiftPoly]

omit [CharZero K] in
@[simp] theorem shiftPoly_X : shiftPoly (X : K[X]) = X + C 1 := by
  simp [shiftPoly]

omit [CharZero K] in
theorem shiftPoly_add (p q : K[X]) : shiftPoly (p + q) = shiftPoly p + shiftPoly q := by
  simp [shiftPoly, add_comp]

omit [CharZero K] in
theorem shiftPoly_mul (p q : K[X]) : shiftPoly (p * q) = shiftPoly p * shiftPoly q := by
  simp [shiftPoly, mul_comp]

omit [CharZero K] in
/-- Shifting `X - C a` moves the root: `(X - a)(X+1) = X - (a-1)`. -/
theorem shiftPoly_sub_C (a : K) : shiftPoly (X - C a) = X - C (a - 1) := by
  simp only [shiftPoly, sub_comp, X_comp, C_comp, C_sub]
  ring

/-- Cleared form of `P/Q + P(X+1)/Q(X+1) = 1/(4X²)`. -/
def ClearedEq (P Q : K[X]) : Prop :=
  (C (4 : K) * X ^ 2) * (P * shiftPoly Q + shiftPoly P * Q) = Q * shiftPoly Q

omit [CharZero K] in
/-- A factor of `X²` cannot equal a nonzero constant. -/
theorem X_sq_mul_eq_C_false (p : K[X]) {c : K} (hc : c ≠ 0)
    (h : (C (4 : K) * X ^ 2) * p = C c) : False := by
  have hz := congrArg (eval 0) h
  simp at hz
  exact hc hz.symm

omit [CharZero K] in
/-- Constant-denominator case of `ClearedEq` fails. -/
theorem no_constant_denom_solution (P : K[X]) {c : K} (hc : c ≠ 0) :
    ¬ ClearedEq P (C c) := by
  intro h
  have h' :
      (C (4 : K) * X ^ 2) * (C c * (P + shiftPoly P)) = C (c * c) := by
    unfold ClearedEq at h
    -- expand using shiftPoly_C
    have h1 : shiftPoly (C c) = C c := shiftPoly_C c
    rw [h1] at h
    -- goal algebra
    convert h using 1
    · ring
    · simp
  exact X_sq_mul_eq_C_false _ (mul_ne_zero hc hc) h'

/-- Specialization `Q = 1`. -/
theorem no_polynomial_cleared_solution (P : ℚ[X]) : ¬ ClearedEq P 1 :=
  no_constant_denom_solution P (by norm_num : (1 : ℚ) ≠ 0)

/-- `4 X² (P + P(X+1)) = 1` is impossible. -/
theorem no_polynomial_average_eq_inv_X_sq (P : ℚ[X]) :
    ¬ ((C (4 : ℚ) * X ^ 2) * (P + shiftPoly P) = 1) := by
  intro h
  exact X_sq_mul_eq_C_false (P + shiftPoly P) (by norm_num : (1 : ℚ) ≠ 0)
    (by simpa using h)

/-- Theorem 2.1 polynomial fragment. -/
theorem thm_2_1_polynomial_fragment (P : ℚ[X]) :
    ¬ ((C (4 : ℚ) * X ^ 2) * (P + shiftPoly P) = 1) :=
  no_polynomial_average_eq_inv_X_sq P

/-- If `Q = C c` with `c ≠ 0`, then `ClearedEq` fails (repackaging). -/
theorem clearedEq_of_eq_C {P Q : ℚ[X]} {c : ℚ}
    (hQ : Q = C c) (hc : c ≠ 0) : ¬ ClearedEq P Q := by
  rw [hQ]
  exact no_constant_denom_solution P hc

/-!
## The general theorem: no nonzero `Q` works

We now drop the "constant denominator" restriction entirely.
-/

omit [CharZero K] in
/-- Cancellation of a common linear factor `X - C r` from a `ClearedEq`
instance: if `(X-r)P₁` and `(X-r)Q₁` solve the cleared equation, so do
`P₁` and `Q₁` themselves. Works for any `r`, no case split needed. -/
theorem shiftEq_cancel_common_root (r : K) (P₁ Q₁ : K[X])
    (h : ClearedEq ((X - C r) * P₁) ((X - C r) * Q₁)) : ClearedEq P₁ Q₁ := by
  unfold ClearedEq at h ⊢
  rw [shiftPoly_mul, shiftPoly_mul, shiftPoly_sub_C] at h
  set d : K[X] := (X - C r) * (X - C (r - 1)) with hd_def
  have hd : d ≠ 0 :=
    mul_ne_zero (X_sub_C_ne_zero r) (X_sub_C_ne_zero (r - 1))
  have key : d * ((C (4 : K) * X ^ 2) * (P₁ * shiftPoly Q₁ + shiftPoly P₁ * Q₁))
      = d * (Q₁ * shiftPoly Q₁) := by
    rw [hd_def]
    linear_combination h
  exact mul_left_cancel₀ hd key

/-- Over ℂ, a nonzero polynomial of positive degree has a root of maximal
real part (finitely many roots, extremal-value argument on `Complex.re`). -/
theorem exists_max_re_root {Q : ℂ[X]} (hQ : Q ≠ 0) (hdeg : 1 ≤ Q.natDegree) :
    ∃ a, Q.IsRoot a ∧ ∀ b, Q.IsRoot b → b.re ≤ a.re := by
  have hdegree : Q.degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hdegree
  have hfin : Set.Finite {x : ℂ | Q.IsRoot x} := Polynomial.finite_setOf_isRoot hQ
  obtain ⟨a, ha, hmax⟩ :=
    Set.exists_max_image {x : ℂ | Q.IsRoot x} Complex.re hfin ⟨z, hz⟩
  exact ⟨a, ha, hmax⟩

/-- Dual of `exists_max_re_root`: a root of minimal real part. -/
theorem exists_min_re_root {Q : ℂ[X]} (hQ : Q ≠ 0) (hdeg : 1 ≤ Q.natDegree) :
    ∃ a, Q.IsRoot a ∧ ∀ b, Q.IsRoot b → a.re ≤ b.re := by
  have hdegree : Q.degree ≠ 0 :=
    (Polynomial.natDegree_pos_iff_degree_pos.mp hdeg).ne'
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root Q hdegree
  have hfin : Set.Finite {x : ℂ | Q.IsRoot x} := Polynomial.finite_setOf_isRoot hQ
  obtain ⟨a, ha, hmin⟩ :=
    Set.exists_min_image {x : ℂ | Q.IsRoot x} Complex.re hfin ⟨z, hz⟩
  exact ⟨a, ha, hmin⟩

/-- Evaluating `ClearedEq P Q` at a root `a` of `Q` collapses to
`4 a² · P(a) · Q(a+1) = 0`. -/
theorem clearedEq_eval_root {P Q : ℂ[X]} (h : ClearedEq P Q) {a : ℂ} (haQ : Q.IsRoot a) :
    4 * a ^ 2 * P.eval a * Q.eval (a + 1) = 0 := by
  have he := congrArg (Polynomial.eval a) h
  unfold ClearedEq shiftPoly at he
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_comp] at he
  simp only [haQ.eq_zero, mul_zero, zero_mul, add_zero] at he
  simpa [mul_assoc] using he

/-- Mirror evaluation: evaluating `ClearedEq P Q` at `y`, given that `y+1` is
a root of `Q`, collapses to `4 y² · P(y+1) · Q(y) = 0`. -/
theorem clearedEq_eval_root' {P Q : ℂ[X]} (h : ClearedEq P Q) {y : ℂ}
    (hyQ1 : Q.IsRoot (y + 1)) : 4 * y ^ 2 * P.eval (y + 1) * Q.eval y = 0 := by
  have he := congrArg (Polynomial.eval y) h
  unfold ClearedEq shiftPoly at he
  simp only [eval_mul, eval_add, eval_pow, eval_X, eval_C, eval_comp] at he
  simp only [hyQ1.eq_zero, mul_zero, zero_add] at he
  simpa [mul_assoc] using he

/-- Common-root extraction: if `P/Q` satisfies the cleared equation and `Q`
has positive degree, `P` and `Q` share a root. -/
theorem common_root_exists {P Q : ℂ[X]} (hQ : Q ≠ 0) (hdeg : 1 ≤ Q.natDegree)
    (h : ClearedEq P Q) : ∃ r, P.IsRoot r ∧ Q.IsRoot r := by
  obtain ⟨a, haQ, hmax⟩ := exists_max_re_root hQ hdeg
  by_cases ha0 : a = 0
  · -- `a = 0`: use the *minimal* real-part root `b` instead, and the mirror
    -- evaluation point `y = b - 1` (so `y + 1 = b` is the root of `Q`).
    obtain ⟨b, hbQ, hmin⟩ := exists_min_re_root hQ hdeg
    -- `b ≠ 1`, since `b.re ≤ a.re = 0 < 1 = (1:ℂ).re`.
    have hb_ne_one : b ≠ 1 := by
      intro hb1
      have hle : b.re ≤ a.re := hmin a haQ
      rw [hb1, ha0] at hle
      simp only [Complex.one_re, Complex.zero_re] at hle
      linarith
    have hb1ne : (b - 1) ≠ 0 := sub_ne_zero.mpr hb_ne_one
    have hyb : (b - 1 : ℂ) + 1 = b := by ring
    have hroot' : Q.IsRoot ((b - 1) + 1) := by rw [hyb]; exact hbQ
    have he := clearedEq_eval_root' h hroot'
    rw [hyb] at he
    -- `Q.eval (b-1) ≠ 0`: else `b-1` is a root with strictly smaller real
    -- part than the minimal root `b`, contradicting minimality of `b`.
    have hQb1 : Q.eval (b - 1) ≠ 0 := by
      intro hcontra
      have hroot2 : Q.IsRoot (b - 1) := hcontra
      have hle : b.re ≤ (b - 1).re := hmin (b - 1) hroot2
      simp only [Complex.sub_re, Complex.one_re] at hle
      linarith
    have hsq : (4 : ℂ) * (b - 1) ^ 2 ≠ 0 := by
      have : (b - 1) ^ 2 ≠ 0 := pow_ne_zero 2 hb1ne
      simpa using mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) this
    rcases mul_eq_zero.mp he with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hsq
      · exact ⟨b, by simpa [Polynomial.IsRoot] using h2, hbQ⟩
    · exact absurd h1 hQb1
  · -- `a ≠ 0`: `a + 1` cannot be a root of `Q` since `(a+1).re > a.re`.
    have haQ1 : ¬ Q.IsRoot (a + 1) := by
      intro hcontra
      have hle := hmax (a + 1) hcontra
      simp only [Complex.add_re, Complex.one_re] at hle
      linarith
    have he := clearedEq_eval_root h haQ
    have hsq : (4 : ℂ) * a ^ 2 ≠ 0 := by
      have : a ^ 2 ≠ 0 := pow_ne_zero 2 ha0
      simpa using mul_ne_zero (by norm_num : (4 : ℂ) ≠ 0) this
    rcases mul_eq_zero.mp he with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hsq
      · exact ⟨a, by simpa [Polynomial.IsRoot] using h2, haQ⟩
    · exact absurd h1 haQ1

/-- Main induction over ℂ: no `ClearedEq P Q` solution for any nonzero `Q`. -/
theorem no_rational_solution_complex :
    ∀ n : ℕ, ∀ P Q : ℂ[X], Q.natDegree = n → Q ≠ 0 → ¬ ClearedEq P Q := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro P Q hn hQ h
    rcases Nat.eq_zero_or_pos n with h0 | hpos
    · -- `Q` is a nonzero constant.
      subst h0
      obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hn
      have hc0 : c ≠ 0 := by
        intro hc0
        rw [hc0, map_zero] at hc
        exact hQ hc.symm
      exact no_constant_denom_solution P hc0 (hc ▸ h)
    · -- `Q` has positive degree: find and cancel a common root.
      have hdeg : 1 ≤ Q.natDegree := hn ▸ hpos
      obtain ⟨r, hPr, hQr⟩ := common_root_exists hQ hdeg h
      obtain ⟨P₁, hP⟩ := Polynomial.dvd_iff_isRoot.mpr hPr
      obtain ⟨Q₁, hQeq⟩ := Polynomial.dvd_iff_isRoot.mpr hQr
      have hQ1ne : Q₁ ≠ 0 := by
        intro hc
        apply hQ
        rw [hQeq, hc, mul_zero]
      have hdegQ : Q.natDegree = (X - C r).natDegree + Q₁.natDegree := by
        rw [hQeq, Polynomial.natDegree_mul (X_sub_C_ne_zero r) hQ1ne]
      rw [Polynomial.natDegree_X_sub_C] at hdegQ
      have hQ1deg : Q₁.natDegree = n - 1 := by omega
      have hlt : Q₁.natDegree < n := by omega
      have hClearedEq1 : ClearedEq P₁ Q₁ := by
        apply shiftEq_cancel_common_root r P₁ Q₁
        rw [← hP, ← hQeq]
        exact h
      exact ih Q₁.natDegree hlt P₁ Q₁ rfl hQ1ne hClearedEq1

/-- Corollary form of `no_rational_solution_complex`. -/
theorem no_rational_solution_complex' (P Q : ℂ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q :=
  no_rational_solution_complex Q.natDegree P Q rfl hQ

/-- `shiftPoly` commutes with mapping along a ring homomorphism of fields
(needed to transport `ClearedEq` from ℚ to ℂ). -/
theorem shiftPoly_map (f : ℚ →+* ℂ) (p : ℚ[X]) :
    (shiftPoly p).map f = shiftPoly (p.map f) := by
  unfold shiftPoly
  rw [Polynomial.map_comp]
  congr 1
  simp

/-- **Main theorem.** No nonzero rational function `P/Q` (with `Q ≠ 0`)
satisfies the cleared functional equation
`4X² (P·Q(X+1) + P(X+1)·Q) = Q·Q(X+1)` over ℚ. -/
theorem no_rational_solution (P Q : ℚ[X]) (hQ : Q ≠ 0) : ¬ ClearedEq P Q := by
  intro h
  set f : ℚ →+* ℂ := algebraMap ℚ ℂ with hf_def
  have hfinj : Function.Injective f := FaithfulSMul.algebraMap_injective ℚ ℂ
  have hQmap : Q.map f ≠ 0 := (Polynomial.map_ne_zero_iff hfinj).mpr hQ
  have hClearedEqC : ClearedEq (P.map f) (Q.map f) := by
    unfold ClearedEq at h ⊢
    have hh := congrArg (Polynomial.map f) h
    simpa [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
      Polynomial.map_C, Polynomial.map_X, shiftPoly_map] using hh
  exact no_rational_solution_complex' (P.map f) (Q.map f) hQmap hClearedEqC

end CatalanSun.FunctionalEq
