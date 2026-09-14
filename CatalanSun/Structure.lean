/-
  CatalanSun/Structure.lean

  M4 Phase A–D scaffolding for Sun arXiv:2609.04176v1 §2:
  odd-linear factors, erase-product forms of L_S / E / P*_λ / D_λ,
  cancelled-product P_λ, evaluation lemmas, degree bounds, and the Πᵢ bridge.

  Structure identity (proved in `Thm21.lean`):
    f_i = - T_{i+1} · D_λ(i) + P_λ(i)
  (paper's written T_i form corrected; k=0 remainder is not polynomial).

  Does **not** prove Theorem 2.1 / Corollary 2.1.
-/

import CatalanSun.TwoAdic
import CatalanSun.Tail
import CatalanSun.FunctionalEq
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option maxHeartbeats 400000

noncomputable section

/-!
# D_λ scaffolding (M4 Phase A)

Paper indexing `j ∈ {1..S}` is represented by `Fin S` via `j.val + 1`.
All polynomials live in `ℝ[X]`. Erase-products avoid `divByMonic` on the
non-monic linear factors `2X + 2j + 1`.
-/

namespace CatalanSun.Structure

open Polynomial Finset
open CatalanSun

/-! ## Odd-linear factors -/

/-- Linear factor `2X + 2j + 1 = 2(X + j + 1/2)`. -/
def oddLin (j : ℕ) : ℝ[X] :=
  C (2 : ℝ) * (X + C ((j : ℝ) + (1 : ℝ) / 2))

@[simp]
theorem oddLin_eval (j i : ℕ) :
    (oddLin j).eval (i : ℝ) = 2 * (i : ℝ) + 2 * (j : ℝ) + 1 := by
  simp only [oddLin, eval_mul, eval_C, eval_add, eval_X]
  ring

theorem oddLin_eval_oddReal (j i : ℕ) :
    (oddLin j).eval (i : ℝ) = Tail.oddReal (i + j) := by
  rw [oddLin_eval, Tail.oddReal, Nat.cast_add]
  ring

theorem natDegree_oddLin (j : ℕ) : (oddLin j).natDegree = 1 := by
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  rw [oddLin, natDegree_C_mul h2, natDegree_X_add_C]

/-! ## L_S, E, erase-products, P*_λ, D_λ -/

/-- `L_S(X) = ∏_{j=1}^S (2X + 2j + 1)`. -/
def Lpoly (S : ℕ) : ℝ[X] :=
  ∏ j ∈ Icc 1 S, oddLin j

/-- `E(X) = ∏_{j=S+1}^B (2X + 2j + 1)`. -/
def Epoly (B S : ℕ) : ℝ[X] :=
  ∏ j ∈ Icc (S + 1) B, oddLin j

/-- Erase-product `L_S(X) / (2X + 2j + 1)` as a product (no polynomial division). -/
def LpolyDiv (S j : ℕ) : ℝ[X] :=
  ∏ k ∈ (Icc 1 S).erase j, oddLin k

/--
Paper `P*_λ(X) = ∑_{j=1}^S (−1)^j λ_j ∏_{k≠j} (2X + 2k + 1)`.
Index `j : Fin S` corresponds to paper index `j.val + 1`.
-/
def Pstar (S : ℕ) (lam : Fin S → ℝ) : ℝ[X] :=
  ∑ j : Fin S, C (((-1 : ℝ) ^ (j.val + 1) * lam j)) * LpolyDiv S (j.val + 1)

/-- `D_λ(X) = L_S(X) · E(X)² · P*_λ(X)`. -/
def Dlam (B S : ℕ) (lam : Fin S → ℝ) : ℝ[X] :=
  Lpoly S * (Epoly B S) ^ 2 * Pstar S lam

/-! ## Erase-product recovery of L_S -/

theorem oddLin_mul_LpolyDiv {S j : ℕ} (hj : j ∈ Icc 1 S) :
    oddLin j * LpolyDiv S j = Lpoly S := by
  simpa [Lpoly, LpolyDiv] using mul_prod_erase (Icc 1 S) oddLin hj

/-! ## Nonvanishing of odd-linear factors and products -/

theorem oddLin_ne_zero (j : ℕ) : oddLin j ≠ 0 := by
  intro h
  have := natDegree_oddLin j
  simp [h, natDegree_zero] at this

theorem Lpoly_ne_zero (S : ℕ) : Lpoly S ≠ 0 := by
  rw [Lpoly]
  exact prod_ne_zero_iff.mpr fun j _ => oddLin_ne_zero j

theorem Epoly_ne_zero (B S : ℕ) : Epoly B S ≠ 0 := by
  rw [Epoly]
  exact prod_ne_zero_iff.mpr fun j _ => oddLin_ne_zero j

/-- Root of `oddLin j`: `-(j + 1/2)`. -/
theorem oddLin_eval_neg_half (j : ℕ) :
    (oddLin j).eval (-((j : ℝ) + 1 / 2)) = 0 := by
  simp only [oddLin, eval_mul, eval_C, eval_add, eval_X]
  ring

theorem oddLin_eval_neg_half_of_ne {j k : ℕ} (hne : j ≠ k) :
    (oddLin k).eval (-((j : ℝ) + 1 / 2)) ≠ 0 := by
  have heq : -((j : ℝ) + 1 / 2) + ((k : ℝ) + 1 / 2) = (k : ℝ) - (j : ℝ) := by ring
  simp only [oddLin, eval_mul, eval_C, eval_add, eval_X, heq]
  exact mul_ne_zero (by norm_num)
    (sub_ne_zero.mpr ((Nat.cast_injective (R := ℝ)).ne hne.symm))

theorem eval_LpolyDiv_at_oddLin_root {S j : ℕ} (_hj : j ∈ Icc 1 S) :
    (LpolyDiv S j).eval (-((j : ℝ) + 1 / 2)) ≠ 0 := by
  rw [LpolyDiv, eval_prod]
  refine prod_ne_zero_iff.mpr ?_
  intro k hk
  have hkne : j ≠ k := by
    have : k ≠ j := (mem_erase.mp hk).1
    exact this.symm
  exact oddLin_eval_neg_half_of_ne hkne

/-! ## Evaluation of L and E -/

theorem eval_Lpoly (S i : ℕ) :
    (Lpoly S).eval (i : ℝ) = ∏ j ∈ Icc 1 S, (2 * (i : ℝ) + 2 * (j : ℝ) + 1) := by
  simp only [Lpoly, eval_prod, oddLin_eval]

theorem eval_Epoly (B S i : ℕ) :
    (Epoly B S).eval (i : ℝ) =
      ∏ j ∈ Icc (S + 1) B, (2 * (i : ℝ) + 2 * (j : ℝ) + 1) := by
  simp only [Epoly, eval_prod, oddLin_eval]

private theorem image_succ_range_eq_Icc (n : ℕ) :
    (range n).image Nat.succ = Icc 1 n := by
  ext x
  simp only [mem_image, mem_range, mem_Icc, Nat.succ_eq_add_one]
  constructor
  · rintro ⟨h, hh, rfl⟩
    omega
  · intro hx
    refine ⟨x - 1, ?_, ?_⟩ <;> omega

private theorem prod_Icc_one_eq_prod_range (n : ℕ) (f : ℕ → ℝ) :
    ∏ j ∈ Icc 1 n, f j = ∏ h ∈ range n, f (h + 1) := by
  rw [← image_succ_range_eq_Icc n]
  refine (Finset.prod_image fun a _ b _ h => Nat.succ_injective h).trans ?_
  simp only [Nat.succ_eq_add_one]

private theorem Icc_union_split {S B : ℕ} (h : S ≤ B) :
    Icc 1 S ∪ Icc (S + 1) B = Icc 1 B := by
  ext x
  have := h
  simp only [mem_union, mem_Icc]
  omega

private theorem disjoint_Icc_split (S B : ℕ) :
    Disjoint (Icc 1 S) (Icc (S + 1) B) := by
  refine disjoint_left.mpr ?_
  intro x hxS hxE
  simp only [mem_Icc] at hxS hxE
  omega

theorem eval_Lpoly_mul_Epoly {S B i : ℕ} (h : S ≤ B) :
    (Lpoly S * Epoly B S).eval (i : ℝ) =
      ∏ j ∈ Icc 1 B, (2 * (i : ℝ) + 2 * (j : ℝ) + 1) := by
  rw [eval_mul, eval_Lpoly, eval_Epoly, ← prod_union (disjoint_Icc_split S B),
    Icc_union_split h]

/-- Bridge: `Πᵢ = (L_S(i) · E(i))²` under `S ≤ B`. -/
theorem PiFactor_eq_eval_Lpoly_mul_Epoly_sq {B S i : ℕ} (h : S ≤ B) :
    (TwoAdic.PiFactor B i : ℝ) = ((Lpoly S * Epoly B S).eval (i : ℝ)) ^ 2 := by
  rw [eval_Lpoly_mul_Epoly h, TwoAdic.PiFactor, prod_Icc_one_eq_prod_range]
  -- Both sides become products over `range B` of squared odd integers.
  simp only [Nat.cast_prod, Nat.cast_pow]
  have hpow :=
    Finset.prod_pow (s := range B) (n := 2)
      (f := fun t : ℕ => ((2 * (t + 1 + i) + 1 : ℕ) : ℝ))
  rw [hpow]
  congr 1
  refine prod_congr rfl fun t _ => ?_
  push_cast
  ring

/-! ## Degree bounds -/

private theorem sum_natDegree_oddLin (s : Finset ℕ) :
    (∑ j ∈ s, (oddLin j).natDegree) = #s := by
  rw [sum_congr rfl fun j _ => natDegree_oddLin j]
  simp [sum_const, smul_eq_mul]

theorem natDegree_Lpoly_le (S : ℕ) : (Lpoly S).natDegree ≤ S := by
  refine (natDegree_prod_le (Icc 1 S) oddLin).trans ?_
  rw [sum_natDegree_oddLin]
  have hcard : #(Icc 1 S) = S + 1 - 1 := by simp
  omega

theorem natDegree_Epoly_le {B S : ℕ} (h : S ≤ B) :
    (Epoly B S).natDegree ≤ B - S := by
  refine (natDegree_prod_le (Icc (S + 1) B) oddLin).trans ?_
  rw [sum_natDegree_oddLin]
  have hcard : #(Icc (S + 1) B) = B + 1 - (S + 1) := by simp
  omega

theorem natDegree_LpolyDiv_le {S j : ℕ} (hj : j ∈ Icc 1 S) :
    (LpolyDiv S j).natDegree ≤ S - 1 := by
  refine (natDegree_prod_le ((Icc 1 S).erase j) oddLin).trans ?_
  rw [sum_natDegree_oddLin, card_erase_of_mem hj]
  have hcard : #(Icc 1 S) = S + 1 - 1 := by simp
  omega

theorem natDegree_Pstar_le (S : ℕ) (lam : Fin S → ℝ) :
    (Pstar S lam).natDegree ≤ S - 1 := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  refine (natDegree_C_mul_le _ _).trans ?_
  have hj : j.val + 1 ∈ Icc 1 S := by
    simp only [mem_Icc]
    omega
  exact natDegree_LpolyDiv_le hj

/-- Degree bound from the paper: `deg D_λ ≤ 2B − 1` when `S < B`. -/
theorem natDegree_Dlam_le {B S : ℕ} (h : S < B) (lam : Fin S → ℝ) :
    (Dlam B S lam).natDegree ≤ 2 * B - 1 := by
  cases S with
  | zero =>
    have hP : Pstar 0 lam = 0 := by
      simp [Pstar]
    simp only [Dlam, hP, mul_zero, natDegree_zero]
    have : 0 < B := Nat.pos_of_ne_zero (by omega)
    omega
  | succ S' =>
    have hSB : S' + 1 ≤ B := Nat.le_of_lt h
    have hL : (Lpoly (S' + 1)).natDegree ≤ S' + 1 := natDegree_Lpoly_le _
    have hE : (Epoly B (S' + 1)).natDegree ≤ B - (S' + 1) := natDegree_Epoly_le hSB
    have hE2 : ((Epoly B (S' + 1)) ^ 2).natDegree ≤ 2 * (B - (S' + 1)) :=
      (natDegree_pow_le (p := Epoly B (S' + 1)) (n := 2)).trans (by
        simpa [two_mul] using Nat.mul_le_mul_left 2 hE)
    have hP : (Pstar (S' + 1) lam).natDegree ≤ S' := by
      simpa [Nat.succ_sub_succ_eq_sub, Nat.sub_zero] using natDegree_Pstar_le (S' + 1) lam
    have hLE :
        (Lpoly (S' + 1) * (Epoly B (S' + 1)) ^ 2).natDegree ≤
          (S' + 1) + 2 * (B - (S' + 1)) :=
      natDegree_mul_le.trans (add_le_add hL hE2)
    have hD :
        (Dlam B (S' + 1) lam).natDegree ≤
          (S' + 1) + 2 * (B - (S' + 1)) + S' := by
      simpa [Dlam, mul_assoc] using
        (natDegree_mul_le (p := Lpoly (S' + 1) * (Epoly B (S' + 1)) ^ 2)
          (q := Pstar (S' + 1) lam)).trans (add_le_add hLE hP)
    have harith :
        (S' + 1) + 2 * (B - (S' + 1)) + S' = 2 * B - 1 := by omega
    exact hD.trans (le_of_eq harith)

/-! ## Cancelled products and P_λ (Phase C)

Remainder denominators after expanding through `T_{i+1}` are
`oddReal(i+j)` and `oddReal(i+ℓ)²` with `1 ≤ ℓ < j ≤ S < B`, all factors of
`Π_i`. The cancelled product is therefore a genuine element of `ℝ[X]`. -/

/-- `Π(X) / ((2X+2j+1)(2X+2ℓ+1)²)` as an erase-product polynomial. -/
def cancelledProd (B j ℓ : ℕ) : ℝ[X] :=
  oddLin j * ∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2

/-- Full squared product `∏_{h=1}^B (2X+2h+1)²`. -/
def PiPoly (B : ℕ) : ℝ[X] :=
  ∏ h ∈ Icc 1 B, (oddLin h) ^ 2

theorem eval_PiPoly (B i : ℕ) :
    (PiPoly B).eval (i : ℝ) = (TwoAdic.PiFactor B i : ℝ) := by
  have hbridge :=
    PiFactor_eq_eval_Lpoly_mul_Epoly_sq (B := B) (S := B) (i := i) le_rfl
  -- `Epoly B B` is an empty product (= 1), so `(Lpoly B).eval ^ 2 = Πᵢ`.
  have hE : Epoly B B = 1 := by
    simp [Epoly, Icc_eq_empty_of_lt (Nat.lt_succ_self B)]
  rw [hE, mul_one] at hbridge
  -- `(∏ oddLin).eval ^ 2 = (∏ (oddLin)^2).eval`.
  have hprod :
      ((Lpoly B).eval (i : ℝ)) ^ 2 = (PiPoly B).eval (i : ℝ) := by
    simp only [Lpoly, PiPoly, eval_prod, eval_pow]
    exact (Finset.prod_pow (Icc 1 B) 2 (fun h => (oddLin h).eval (i : ℝ))).symm
  rw [← hprod, hbridge]

theorem cancelledProd_mul {B j ℓ : ℕ}
    (hj : j ∈ Icc 1 B) (hℓ : ℓ ∈ Icc 1 B) (hne : j ≠ ℓ) :
    cancelledProd B j ℓ * oddLin j * (oddLin ℓ) ^ 2 = PiPoly B := by
  have hℓ' : ℓ ∈ (Icc 1 B).erase j := by
    simp only [mem_erase, mem_Icc] at hj hℓ ⊢
    exact ⟨hne.symm, hℓ⟩
  calc
    cancelledProd B j ℓ * oddLin j * (oddLin ℓ) ^ 2
        = oddLin j * (∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2) *
            oddLin j * (oddLin ℓ) ^ 2 := by
          simp only [cancelledProd]
    _ = (oddLin j) ^ 2 *
          ((oddLin ℓ) ^ 2 * ∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2) := by
          ring
    _ = (oddLin j) ^ 2 * ∏ h ∈ (Icc 1 B).erase j, (oddLin h) ^ 2 := by
          rw [mul_prod_erase ((Icc 1 B).erase j) (fun h => (oddLin h) ^ 2) hℓ']
    _ = ∏ h ∈ Icc 1 B, (oddLin h) ^ 2 := by
          rw [mul_prod_erase (Icc 1 B) (fun h => (oddLin h) ^ 2) hj]
    _ = PiPoly B := rfl

theorem eval_cancelledProd {B j ℓ i : ℕ}
    (hj : j ∈ Icc 1 B) (hℓ : ℓ ∈ Icc 1 B) (hne : j ≠ ℓ) :
    (cancelledProd B j ℓ).eval (i : ℝ) =
      (TwoAdic.PiFactor B i : ℝ) /
        (Tail.oddReal (i + j) * Tail.oddReal (i + ℓ) ^ 2) := by
  have hmul := congrArg (fun p : ℝ[X] => p.eval (i : ℝ))
    (cancelledProd_mul hj hℓ hne)
  simp only [eval_mul, eval_pow, oddLin_eval_oddReal, eval_PiPoly] at hmul
  have hden :
      Tail.oddReal (i + j) * Tail.oddReal (i + ℓ) ^ 2 ≠ 0 :=
    mul_ne_zero (Tail.oddReal_ne_zero _) (pow_ne_zero 2 (Tail.oddReal_ne_zero _))
  refine (eq_div_iff hden).mpr ?_
  -- Reassociate `a * b * c` to `a * (b * c)`.
  convert hmul using 1
  ring

theorem natDegree_cancelledProd_le {B j ℓ : ℕ}
    (hj : j ∈ Icc 1 B) (hℓ : ℓ ∈ Icc 1 B) (hne : j ≠ ℓ) :
    (cancelledProd B j ℓ).natDegree ≤ 2 * B - 3 := by
  have hℓ' : ℓ ∈ (Icc 1 B).erase j := by
    simp only [mem_erase, mem_Icc] at hj hℓ ⊢
    exact ⟨hne.symm, hℓ⟩
  -- Distinct elements of `Icc 1 B` force `B ≥ 2`.
  have hB2 : 2 ≤ B := by
    have hj1 : 1 ≤ j := (mem_Icc.mp hj).1
    have hjB : j ≤ B := (mem_Icc.mp hj).2
    have hℓ1 : 1 ≤ ℓ := (mem_Icc.mp hℓ).1
    have hℓB : ℓ ≤ B := (mem_Icc.mp hℓ).2
    omega
  have hcard : #(((Icc 1 B).erase j).erase ℓ) = B - 2 := by
    have hB : #(Icc 1 B) = B := by
      have : #(Icc 1 B) = B + 1 - 1 := by simp
      omega
    rw [card_erase_of_mem hℓ', card_erase_of_mem hj, hB, Nat.sub_sub]
  have hprod :
      (∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2).natDegree ≤ 2 * (B - 2) := by
    refine (natDegree_prod_le _ _).trans ?_
    have hterm : ∀ h ∈ ((Icc 1 B).erase j).erase ℓ,
        ((oddLin h) ^ 2).natDegree ≤ 2 := fun h _ =>
      (natDegree_pow_le (p := oddLin h) (n := 2)).trans (by rw [natDegree_oddLin])
    refine (sum_le_sum hterm).trans ?_
    rw [sum_const, smul_eq_mul, hcard]
    omega
  refine (natDegree_mul_le (p := oddLin j)
      (q := ∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2)).trans ?_
  have : (oddLin j).natDegree +
      (∏ h ∈ ((Icc 1 B).erase j).erase ℓ, (oddLin h) ^ 2).natDegree ≤ 2 * B - 3 := by
    have := natDegree_oddLin j
    omega
  exact this

/--
Paper remainder polynomial after expanding through `T_{i+1}`:
`P_λ(X) = ∑_j λ_j ∑_{0≤m<j-1} (−1)^{j-2-m} · Π(X)/((2X+2j+1)(2X+2(m+1)+1)²)`.
Index `j : Fin S` ↔ paper index `j.val + 1`; inner `m` runs over `range j.val`.
-/
def Plam (B S : ℕ) (lam : Fin S → ℝ) : ℝ[X] :=
  ∑ j : Fin S,
    ∑ m ∈ range j.val,
      C (lam j * (-1 : ℝ) ^ (j.val - 1 - m)) *
        cancelledProd B (j.val + 1) (m + 1)

theorem natDegree_Plam_le {B S : ℕ} (h : S < B) (lam : Fin S → ℝ) :
    (Plam B S lam).natDegree ≤ 2 * B - 3 := by
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro j _
  refine natDegree_sum_le_of_forall_le _ _ ?_
  intro m hm
  refine (natDegree_C_mul_le _ _).trans ?_
  have hj : j.val + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hm' : m < j.val := mem_range.mp hm
  have hℓ : m + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hne : j.val + 1 ≠ m + 1 := by omega
  exact natDegree_cancelledProd_le hj hℓ hne

/-! ## Evaluation bridge: D_λ(i) as the cleared weighted sum -/

theorem eval_Lpoly_mul_Epoly_sq_div_oddLin {B S j i : ℕ}
    (h : S ≤ B) (hj : j ∈ Icc 1 S) :
    (Lpoly S * (Epoly B S) ^ 2 * LpolyDiv S j).eval (i : ℝ) =
      (TwoAdic.PiFactor B i : ℝ) / Tail.oddReal (i + j) := by
  have hrec := oddLin_mul_LpolyDiv hj
  have hodd : Tail.oddReal (i + j) ≠ 0 := Tail.oddReal_ne_zero _
  have hL : (Lpoly S).eval (i : ℝ) =
      Tail.oddReal (i + j) * (LpolyDiv S j).eval (i : ℝ) := by
    have h := congrArg (fun p : ℝ[X] => p.eval (i : ℝ)) hrec
    simp only [eval_mul, oddLin_eval_oddReal] at h
    exact h.symm
  have hPi : (TwoAdic.PiFactor B i : ℝ) =
      ((Lpoly S * Epoly B S).eval (i : ℝ)) ^ 2 :=
    PiFactor_eq_eval_Lpoly_mul_Epoly_sq h (i := i)
  have hPi' : (TwoAdic.PiFactor B i : ℝ) =
      ((Lpoly S).eval (i : ℝ)) ^ 2 * ((Epoly B S).eval (i : ℝ)) ^ 2 := by
    rw [hPi, eval_mul, mul_pow]
  refine (eq_div_iff hodd).mpr ?_
  calc
    (Lpoly S * (Epoly B S) ^ 2 * LpolyDiv S j).eval (i : ℝ) * Tail.oddReal (i + j)
        = (Lpoly S).eval (i : ℝ) * ((Epoly B S).eval (i : ℝ)) ^ 2 *
            (LpolyDiv S j).eval (i : ℝ) * Tail.oddReal (i + j) := by
          simp [eval_mul, eval_pow]
    _ = (Tail.oddReal (i + j) * (LpolyDiv S j).eval (i : ℝ)) *
          ((Epoly B S).eval (i : ℝ)) ^ 2 *
          (LpolyDiv S j).eval (i : ℝ) * Tail.oddReal (i + j) := by
          rw [hL]
    _ = ((Lpoly S).eval (i : ℝ)) ^ 2 * ((Epoly B S).eval (i : ℝ)) ^ 2 := by
          have hL' :
              ((Lpoly S).eval (i : ℝ)) ^ 2 =
                Tail.oddReal (i + j) ^ 2 * ((LpolyDiv S j).eval (i : ℝ)) ^ 2 := by
            rw [hL]; ring
          rw [hL']; ring
    _ = (TwoAdic.PiFactor B i : ℝ) := hPi'.symm

theorem eval_Dlam {B S : ℕ} (h : S ≤ B) (lam : Fin S → ℝ) (i : ℕ) :
    (Dlam B S lam).eval (i : ℝ) =
      ∑ j : Fin S,
        (-1 : ℝ) ^ (j.val + 1) * lam j *
          ((TwoAdic.PiFactor B i : ℝ) / Tail.oddReal (i + (j.val + 1))) := by
  calc
    (Dlam B S lam).eval (i : ℝ)
        = (Lpoly S * (Epoly B S) ^ 2).eval (i : ℝ) * (Pstar S lam).eval (i : ℝ) := by
          simp only [Dlam, eval_mul]
    _ = (Lpoly S * (Epoly B S) ^ 2).eval (i : ℝ) *
          ∑ j : Fin S,
            (C (((-1 : ℝ) ^ (j.val + 1) * lam j)) * LpolyDiv S (j.val + 1)).eval
              (i : ℝ) := by
          congr 1
          simp only [Pstar, eval_finsetSum]
    _ = ∑ j : Fin S,
          (Lpoly S * (Epoly B S) ^ 2).eval (i : ℝ) *
            (C (((-1 : ℝ) ^ (j.val + 1) * lam j)) * LpolyDiv S (j.val + 1)).eval
              (i : ℝ) := by
          rw [Finset.mul_sum]
    _ = ∑ j : Fin S,
          (-1 : ℝ) ^ (j.val + 1) * lam j *
            ((TwoAdic.PiFactor B i : ℝ) / Tail.oddReal (i + (j.val + 1))) := by
          refine Finset.sum_congr rfl fun j _ => ?_
          have hj : j.val + 1 ∈ Icc 1 S := by
            simp only [mem_Icc]
            omega
          have hdiv := eval_Lpoly_mul_Epoly_sq_div_oddLin h hj (i := i)
          simp only [eval_mul, eval_C, eval_pow] at hdiv ⊢
          calc
            (Lpoly S).eval (i : ℝ) * ((Epoly B S).eval (i : ℝ)) ^ 2 *
                (((-1 : ℝ) ^ (j.val + 1) * lam j) *
                  (LpolyDiv S (j.val + 1)).eval (i : ℝ))
                = ((-1 : ℝ) ^ (j.val + 1) * lam j) *
                    ((Lpoly S).eval (i : ℝ) * ((Epoly B S).eval (i : ℝ)) ^ 2 *
                      (LpolyDiv S (j.val + 1)).eval (i : ℝ)) := by ring
            _ = ((-1 : ℝ) ^ (j.val + 1) * lam j) *
                  ((TwoAdic.PiFactor B i : ℝ) /
                    Tail.oddReal (i + (j.val + 1))) := by rw [hdiv]

theorem eval_Plam {B S : ℕ} (h : S < B) (lam : Fin S → ℝ) (i : ℕ) :
    (Plam B S lam).eval (i : ℝ) =
      ∑ j : Fin S,
        ∑ m ∈ range j.val,
          lam j * (-1 : ℝ) ^ (j.val - 1 - m) *
            ((TwoAdic.PiFactor B i : ℝ) /
              (Tail.oddReal (i + (j.val + 1)) *
                Tail.oddReal (i + (m + 1)) ^ 2)) := by
  simp only [Plam, eval_finsetSum, eval_mul, eval_C]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm' : m < j.val := Finset.mem_range.mp hm
  have hj : j.val + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hℓ : m + 1 ∈ Icc 1 B := by
    simp only [mem_Icc]
    omega
  have hne : j.val + 1 ≠ m + 1 := by omega
  rw [eval_cancelledProd hj hℓ hne]

/-! ## G₀ and the half-integer root of D_λ (M6 scaffolding)

Paper (2.14):
`G₀(X) = ∏_{j=1}^S (2X+2j+3) · ∏_{S<j<B} (2X+2j+3)²`.
Each factor `2X+2j+3` equals `oddLin (j+1)`. -/

/-- Linear factor `2X + 2j + 3 = oddLin (j+1)`. -/
def g0Lin (j : ℕ) : ℝ[X] := oddLin (j + 1)

@[simp]
theorem g0Lin_eq_oddLin (j : ℕ) : g0Lin j = oddLin (j + 1) := rfl

theorem natDegree_g0Lin (j : ℕ) : (g0Lin j).natDegree = 1 := natDegree_oddLin _

theorem g0Lin_ne_zero (j : ℕ) : g0Lin j ≠ 0 :=
  ne_zero_of_natDegree_gt (by rw [natDegree_g0Lin]; exact one_pos)

theorem leadingCoeff_oddLin (j : ℕ) : (oddLin j).leadingCoeff = 2 := by
  have hmonic : (X + C ((j : ℝ) + 1 / 2)).Monic := monic_X_add_C _
  simpa [oddLin] using hmonic.leadingCoeff_C_mul (2 : ℝ)

theorem leadingCoeff_g0Lin (j : ℕ) : (g0Lin j).leadingCoeff = 2 := by
  simpa [g0Lin] using leadingCoeff_oddLin (j + 1)

/-- Paper `G₀` from (2.14). -/
def G0 (B S : ℕ) : ℝ[X] :=
  (∏ j ∈ Icc 1 S, g0Lin j) * ∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2

theorem shiftPoly_oddLin (j : ℕ) :
    FunctionalEq.shiftPoly (oddLin j) = oddLin (j + 1) := by
  have hconst : (1 : ℝ) + ((j : ℝ) + 1 / 2) = ((j + 1 : ℕ) : ℝ) + 1 / 2 := by
    push_cast; ring
  simp only [FunctionalEq.shiftPoly, oddLin]
  rw [mul_comp, add_comp, X_comp, C_comp, C_comp]
  congr 1
  rw [add_assoc, ← C_add, hconst]

theorem shiftPoly_g0Lin (j : ℕ) :
    FunctionalEq.shiftPoly (g0Lin j) = g0Lin (j + 1) := by
  simpa [g0Lin] using shiftPoly_oddLin (j + 1)

theorem G0_ne_zero (B S : ℕ) : G0 B S ≠ 0 := by
  refine mul_ne_zero ?_ ?_
  · exact prod_ne_zero_iff.mpr fun _ _ => g0Lin_ne_zero _
  · exact prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero 2 (g0Lin_ne_zero _)

private theorem natDegree_eq_of_degree_eq_nat {p : ℝ[X]} {n : ℕ}
    (hne : p ≠ 0) (h : p.degree = (n : WithBot ℕ)) : p.natDegree = n := by
  rw [degree_eq_natDegree hne] at h
  exact (Nat.cast_injective (R := WithBot ℕ) h)

private theorem natDegree_prod_g0Lin (s : Finset ℕ) :
    (∏ j ∈ s, g0Lin j).natDegree = #s := by
  have hne : ∏ j ∈ s, g0Lin j ≠ 0 := prod_ne_zero_iff.mpr fun _ _ => g0Lin_ne_zero _
  have hdeg : (∏ j ∈ s, g0Lin j).degree = ∑ j ∈ s, (g0Lin j).degree :=
    degree_prod (s := s) g0Lin
  have hsum : ∑ j ∈ s, (g0Lin j).degree = (↑(#s) : WithBot ℕ) := by
    have : ∑ j ∈ s, (g0Lin j).degree = ∑ _j ∈ s, (1 : WithBot ℕ) := by
      refine sum_congr rfl fun j _ => ?_
      rw [degree_eq_natDegree (g0Lin_ne_zero j), natDegree_g0Lin, Nat.cast_one]
    rw [this, sum_const, nsmul_eq_mul, mul_one]
  exact natDegree_eq_of_degree_eq_nat hne (hdeg.trans hsum)

private theorem natDegree_prod_g0Lin_sq (s : Finset ℕ) :
    (∏ j ∈ s, (g0Lin j) ^ 2).natDegree = 2 * #s := by
  have hne : ∏ j ∈ s, (g0Lin j) ^ 2 ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero 2 (g0Lin_ne_zero _)
  have hterm : ∀ j, ((g0Lin j) ^ 2).natDegree = 2 := by
    intro j
    have hlc : (g0Lin j).leadingCoeff ^ 2 ≠ 0 := by
      rw [leadingCoeff_g0Lin]; norm_num
    rw [natDegree_pow' hlc, natDegree_g0Lin, mul_one]
  have hdeg : (∏ j ∈ s, (g0Lin j) ^ 2).degree =
      ∑ j ∈ s, ((g0Lin j) ^ 2).degree :=
    degree_prod (s := s) (fun j => (g0Lin j) ^ 2)
  have hsum : ∑ j ∈ s, ((g0Lin j) ^ 2).degree = (↑(2 * #s) : WithBot ℕ) := by
    have : ∑ j ∈ s, ((g0Lin j) ^ 2).degree = ∑ _j ∈ s, (2 : WithBot ℕ) := by
      refine sum_congr rfl fun j _ => ?_
      rw [degree_eq_natDegree (pow_ne_zero 2 (g0Lin_ne_zero j)), hterm, Nat.cast_two]
    rw [this, sum_const, nsmul_eq_mul]
    norm_cast
    ring
  exact natDegree_eq_of_degree_eq_nat hne (hdeg.trans hsum)

/-- Exact degree: `deg G₀ = 2B − S − 2` under `S < B`. -/
theorem natDegree_G0 {B S : ℕ} (h : S < B) :
    (G0 B S).natDegree = 2 * B - S - 2 := by
  have hcard1 : #(Icc 1 S) = S := by
    have : #(Icc 1 S) = S + 1 - 1 := by simp
    omega
  have hcard2 : #(Icc (S + 1) (B - 1)) = B - S - 1 := by
    have : #(Icc (S + 1) (B - 1)) = (B - 1) + 1 - (S + 1) := by simp
    omega
  have h1 := natDegree_prod_g0Lin (Icc 1 S)
  have h2 := natDegree_prod_g0Lin_sq (Icc (S + 1) (B - 1))
  have hne1 : ∏ j ∈ Icc 1 S, g0Lin j ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => g0Lin_ne_zero _
  have hne2 : ∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2 ≠ 0 :=
    prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero 2 (g0Lin_ne_zero _)
  rw [G0, natDegree_mul hne1 hne2, h1, h2, hcard1, hcard2]
  omega

/-- Reindex: first G₀ product is `∏_{k=2}^{S+1} oddLin k`. -/
theorem G0_first_eq (S : ℕ) :
    (∏ j ∈ Icc 1 S, g0Lin j) = ∏ k ∈ Icc 2 (S + 1), oddLin k := by
  have himg : (Icc 1 S).image (fun j : ℕ => j + 1) = Icc 2 (S + 1) := by
    ext x; simp only [mem_image, mem_Icc]; constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hx; refine ⟨x - 1, ?_, ?_⟩ <;> omega
  have hinj : Set.InjOn (fun j : ℕ => j + 1) (Icc 1 S) :=
    fun a _ b _ h => Nat.succ_injective h
  simp only [g0Lin]
  rw [← himg, Finset.prod_image hinj]

/-- Reindex: second G₀ product is `∏_{k=S+2}^{B} (oddLin k)²`. -/
theorem G0_second_eq (B S : ℕ) :
    (∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2) =
      ∏ k ∈ Icc (S + 2) B, (oddLin k) ^ 2 := by
  have himg :
      (Icc (S + 1) (B - 1)).image (fun j : ℕ => j + 1) = Icc (S + 2) B := by
    ext x; simp only [mem_image, mem_Icc]; constructor
    · rintro ⟨j, hj, rfl⟩; omega
    · intro hx; refine ⟨x - 1, ?_, ?_⟩ <;> omega
  have hinj : Set.InjOn (fun j : ℕ => j + 1) (Icc (S + 1) (B - 1)) :=
    fun a _ b _ h => Nat.succ_injective h
  simp only [g0Lin]
  rw [← himg, Finset.prod_image hinj]

/-- Cofactor identity under `0 < S < B`:
`G₀ · oddLin 1 · oddLin (S+1) = L_S · E²`. -/
theorem G0_mul_oddLin_one_mul_oddLin_succ {B S : ℕ} (h : S < B) (hS : 0 < S) :
    G0 B S * oddLin 1 * oddLin (S + 1) = Lpoly S * (Epoly B S) ^ 2 := by
  have hP := G0_first_eq S
  have hQ := G0_second_eq B S
  have hsplit :
      ∏ k ∈ Icc 2 (S + 1), oddLin k =
        (∏ k ∈ Icc 2 S, oddLin k) * oddLin (S + 1) := by
    have hunion : Icc 2 S ∪ {S + 1} = Icc 2 (S + 1) := by
      ext x; simp only [mem_union, mem_Icc, mem_singleton]; omega
    have hdisj : Disjoint (Icc 2 S) ({S + 1} : Finset ℕ) := by
      refine disjoint_left.mpr ?_
      intro x hxS hx1
      simp only [mem_Icc, mem_singleton] at hxS hx1
      omega
    rw [← hunion, prod_union hdisj, prod_singleton]
  have hL : Lpoly S = oddLin 1 * ∏ k ∈ Icc 2 S, oddLin k := by
    have hmem : (1 : ℕ) ∈ Icc 1 S := by simp only [mem_Icc]; omega
    have herase : (Icc 1 S).erase (1 : ℕ) = Icc 2 S := by
      ext x; simp only [mem_erase, mem_Icc]; omega
    rw [Lpoly, ← mul_prod_erase (Icc 1 S) oddLin hmem, herase]
  have hE :
      (Epoly B S) ^ 2 =
        (oddLin (S + 1)) ^ 2 * ∏ k ∈ Icc (S + 2) B, (oddLin k) ^ 2 := by
    have hmem : S + 1 ∈ Icc (S + 1) B := by simp only [mem_Icc]; omega
    have herase : (Icc (S + 1) B).erase (S + 1) = Icc (S + 2) B := by
      ext x; simp only [mem_erase, mem_Icc]; omega
    rw [Epoly, ← mul_prod_erase (Icc (S + 1) B) oddLin hmem, herase, mul_pow,
      Finset.prod_pow]
  calc
    G0 B S * oddLin 1 * oddLin (S + 1)
        = ((∏ j ∈ Icc 1 S, g0Lin j) *
            ∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2) *
            oddLin 1 * oddLin (S + 1) := rfl
    _ = ((∏ k ∈ Icc 2 (S + 1), oddLin k) *
            ∏ k ∈ Icc (S + 2) B, (oddLin k) ^ 2) *
            oddLin 1 * oddLin (S + 1) := by rw [hP, hQ]
    _ = (((∏ k ∈ Icc 2 S, oddLin k) * oddLin (S + 1)) *
            ∏ k ∈ Icc (S + 2) B, (oddLin k) ^ 2) *
            oddLin 1 * oddLin (S + 1) := by rw [hsplit]
    _ = (oddLin 1 * ∏ k ∈ Icc 2 S, oddLin k) *
          ((oddLin (S + 1)) ^ 2 * ∏ k ∈ Icc (S + 2) B, (oddLin k) ^ 2) := by
            ring
    _ = Lpoly S * (Epoly B S) ^ 2 := by rw [hL, hE]

theorem G0_dvd_Lpoly_mul_Epoly_sq {B S : ℕ} (h : S < B) (hS : 0 < S) :
    G0 B S ∣ Lpoly S * (Epoly B S) ^ 2 :=
  ⟨oddLin 1 * oddLin (S + 1), by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (G0_mul_oddLin_one_mul_oddLin_succ h hS).symm⟩

theorem G0_dvd_Dlam {B S : ℕ} (h : S < B) (hS : 0 < S) (lam : Fin S → ℝ) :
    G0 B S ∣ Dlam B S lam := by
  obtain ⟨q, hq⟩ := G0_dvd_Lpoly_mul_Epoly_sq h hS
  refine ⟨q * Pstar S lam, ?_⟩
  simp only [Dlam, hq]
  ring

/-- Shifted cofactor: `G₀ · g0Lin B = shiftPoly(L) · shiftPoly(E)² / wait —
`G₀ · (g0Lin B)² = shiftPoly L · (shiftPoly E)²`. -/
theorem G0_mul_g0Lin_B_sq {B S : ℕ} (h : S < B) (hS : 0 < S) :
    G0 B S * (g0Lin B) ^ 2 =
      FunctionalEq.shiftPoly (Lpoly S) *
        (FunctionalEq.shiftPoly (Epoly B S)) ^ 2 := by
  have hL :
      FunctionalEq.shiftPoly (Lpoly S) = ∏ j ∈ Icc 1 S, g0Lin j := by
    have : FunctionalEq.shiftPoly (Lpoly S) =
        ∏ j ∈ Icc 1 S, FunctionalEq.shiftPoly (oddLin j) := by
      simp only [Lpoly, FunctionalEq.shiftPoly, Polynomial.prod_comp]
    rw [this]
    refine prod_congr rfl fun j _ => ?_
    rw [shiftPoly_oddLin, g0Lin]
  have hE :
      FunctionalEq.shiftPoly (Epoly B S) = ∏ j ∈ Icc (S + 1) B, g0Lin j := by
    have : FunctionalEq.shiftPoly (Epoly B S) =
        ∏ j ∈ Icc (S + 1) B, FunctionalEq.shiftPoly (oddLin j) := by
      simp only [Epoly, FunctionalEq.shiftPoly, Polynomial.prod_comp]
    rw [this]
    refine prod_congr rfl fun j _ => ?_
    rw [shiftPoly_oddLin, g0Lin]
  have hEsplit :
      ∏ j ∈ Icc (S + 1) B, g0Lin j =
        (∏ j ∈ Icc (S + 1) (B - 1), g0Lin j) * g0Lin B := by
    have hunion : Icc (S + 1) (B - 1) ∪ {B} = Icc (S + 1) B := by
      ext x; simp only [mem_union, mem_Icc, mem_singleton]; omega
    have hdisj : Disjoint (Icc (S + 1) (B - 1)) ({B} : Finset ℕ) := by
      refine disjoint_left.mpr ?_
      intro x hx hxB
      simp only [mem_Icc, mem_singleton] at hx hxB
      omega
    rw [← hunion, prod_union hdisj, prod_singleton]
  have hQpow :
      ∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2 =
        (∏ j ∈ Icc (S + 1) (B - 1), g0Lin j) ^ 2 := by
    rw [Finset.prod_pow]
  calc
    G0 B S * (g0Lin B) ^ 2
        = (∏ j ∈ Icc 1 S, g0Lin j) *
            (∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2) * (g0Lin B) ^ 2 := rfl
    _ = (∏ j ∈ Icc 1 S, g0Lin j) *
          ((∏ j ∈ Icc (S + 1) (B - 1), g0Lin j) ^ 2 * (g0Lin B) ^ 2) := by
            rw [hQpow]; ring
    _ = (∏ j ∈ Icc 1 S, g0Lin j) *
          ((∏ j ∈ Icc (S + 1) (B - 1), g0Lin j) * g0Lin B) ^ 2 := by ring
    _ = FunctionalEq.shiftPoly (Lpoly S) *
          (FunctionalEq.shiftPoly (Epoly B S)) ^ 2 := by
            rw [hL, hE, hEsplit]

theorem G0_dvd_shiftPoly_L_mul_E_sq {B S : ℕ} (h : S < B) (hS : 0 < S) :
    G0 B S ∣
      FunctionalEq.shiftPoly (Lpoly S) *
        (FunctionalEq.shiftPoly (Epoly B S)) ^ 2 :=
  ⟨(g0Lin B) ^ 2, by
    simpa [mul_comm, mul_left_comm, mul_assoc] using
      (G0_mul_g0Lin_B_sq h hS).symm⟩

theorem G0_dvd_shiftPoly_Dlam {B S : ℕ} (h : S < B) (hS : 0 < S) (lam : Fin S → ℝ) :
    G0 B S ∣ FunctionalEq.shiftPoly (Dlam B S lam) := by
  have hpow :
      FunctionalEq.shiftPoly ((Epoly B S) ^ 2) =
        (FunctionalEq.shiftPoly (Epoly B S)) ^ 2 := by
    simp only [FunctionalEq.shiftPoly, pow_two, mul_comp]
  have hD :
      FunctionalEq.shiftPoly (Dlam B S lam) =
        FunctionalEq.shiftPoly (Lpoly S) *
          (FunctionalEq.shiftPoly (Epoly B S)) ^ 2 *
            FunctionalEq.shiftPoly (Pstar S lam) := by
    simp only [Dlam]
    rw [FunctionalEq.shiftPoly_mul, FunctionalEq.shiftPoly_mul, hpow]
  obtain ⟨q, hq⟩ := G0_dvd_shiftPoly_L_mul_E_sq h hS
  refine ⟨q * FunctionalEq.shiftPoly (Pstar S lam), ?_⟩
  rw [hD, hq, mul_assoc]

theorem Dlam_eval_neg_three_halves {B S : ℕ} (hS : 0 < S) (lam : Fin S → ℝ) :
    (Dlam B S lam).eval (-(3 / 2 : ℝ)) = 0 := by
  have hroot : (oddLin 1).eval (-(3 / 2 : ℝ)) = 0 := by
    simp only [oddLin, eval_mul, eval_C, eval_add, eval_X]
    ring
  have h1 : 1 ∈ Icc 1 S := by simp only [mem_Icc]; omega
  have hL : (Lpoly S).eval (-(3 / 2 : ℝ)) = 0 := by
    rw [Lpoly, eval_prod]
    exact prod_eq_zero h1 hroot
  simp only [Dlam, eval_mul, eval_pow, hL, zero_mul]

theorem G0_eval_neg_three_halves_ne (B S : ℕ) :
    (G0 B S).eval (-(3 / 2 : ℝ)) ≠ 0 := by
  have hfac : ∀ j : ℕ, 0 < j → (g0Lin j).eval (-(3 / 2 : ℝ)) ≠ 0 := by
    intro j hj
    have heq : -(3 / 2 : ℝ) + (((j + 1 : ℕ) : ℝ) + 1 / 2) = (j : ℝ) := by
      push_cast; ring
    simp only [g0Lin, oddLin, eval_mul, eval_C, eval_add, eval_X, heq]
    exact mul_ne_zero (by norm_num) (Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hj))
  have h1 : (∏ j ∈ Icc 1 S, g0Lin j).eval (-(3 / 2 : ℝ)) ≠ 0 := by
    rw [eval_prod]
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    have hj0 : 0 < j := by simp only [mem_Icc] at hj; omega
    exact hfac j hj0
  have h2 :
      (∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2).eval (-(3 / 2 : ℝ)) ≠ 0 := by
    rw [eval_prod]
    refine prod_ne_zero_iff.mpr ?_
    intro j hj
    have hj0 : 0 < j := by simp only [mem_Icc] at hj; omega
    simpa [eval_pow] using pow_ne_zero 2 (hfac j hj0)
  simp only [G0, eval_mul]
  exact mul_ne_zero h1 h2

theorem G0_eval_nat_ne (B S n : ℕ) : (G0 B S).eval (n : ℝ) ≠ 0 := by
  have hfac : ∀ j, (g0Lin j).eval (n : ℝ) ≠ 0 := by
    intro j
    have hpos : (0 : ℝ) < 2 * (n : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) + 1 := by positivity
    have heq :
        (2 : ℝ) * ((n : ℝ) + (((j + 1 : ℕ) : ℝ) + 1 / 2)) =
          2 * (n : ℝ) + 2 * ((j + 1 : ℕ) : ℝ) + 1 := by ring
    simp only [g0Lin, oddLin, eval_mul, eval_C, eval_add, eval_X, heq]
    exact ne_of_gt hpos
  have h1 : (∏ j ∈ Icc 1 S, g0Lin j).eval (n : ℝ) ≠ 0 := by
    rw [eval_prod]
    exact prod_ne_zero_iff.mpr fun j _ => hfac j
  have h2 :
      (∏ j ∈ Icc (S + 1) (B - 1), (g0Lin j) ^ 2).eval (n : ℝ) ≠ 0 := by
    rw [eval_prod]
    refine prod_ne_zero_iff.mpr fun j _ => ?_
    simpa [eval_pow] using pow_ne_zero 2 (hfac j)
  simp only [G0, eval_mul]
  exact mul_ne_zero h1 h2

/-! ## M8: `P*_λ ≠ 0` / `D_λ ≠ 0` from nontrivial `lam` -/

/-- Evaluating `P*_λ` at the root of `oddLin (j+1)` isolates the `j`-th summand. -/
theorem eval_Pstar_at_oddLin_root {S : ℕ} (lam : Fin S → ℝ) (j : Fin S) :
    (Pstar S lam).eval (-((j.val + 1 : ℝ) + 1 / 2)) =
      ((-1 : ℝ) ^ (j.val + 1) * lam j) *
        (LpolyDiv S (j.val + 1)).eval (-((j.val + 1 : ℝ) + 1 / 2)) := by
  set x : ℝ := -((j.val + 1 : ℝ) + 1 / 2)
  have hterm : ∀ i : Fin S,
      (C (((-1 : ℝ) ^ (i.val + 1) * lam i) : ℝ) * LpolyDiv S (i.val + 1)).eval x =
        ((-1 : ℝ) ^ (i.val + 1) * lam i) * (LpolyDiv S (i.val + 1)).eval x := by
    intro i
    simp [eval_mul, eval_C]
  -- Off-diagonal erase-products contain `oddLin (j.val+1)`, hence vanish at `x`.
  have hvanish : ∀ i : Fin S, i ≠ j →
      (LpolyDiv S (i.val + 1)).eval x = 0 := by
    intro i hi
    have hjmem : j.val + 1 ∈ (Icc 1 S).erase (i.val + 1) := by
      refine mem_erase.mpr ⟨?_, ?_⟩
      · omega
      · simp only [mem_Icc]; omega
    rw [LpolyDiv, eval_prod]
    exact prod_eq_zero hjmem (by
      simpa [x] using oddLin_eval_neg_half (j.val + 1))
  simp only [Pstar, eval_finsetSum]
  rw [Finset.sum_eq_single j]
  · exact hterm j
  · intro i _ hi
    rw [hterm i, hvanish i hi, mul_zero]
  · intro hj
    exact (hj (mem_univ j)).elim

theorem Pstar_ne_zero_of_lam_ne_zero {S : ℕ} (_hS : 0 < S)
    {lam : Fin S → ℝ} (hlam : lam ≠ 0) : Pstar S lam ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j : Fin S, lam j ≠ 0 := by
    contrapose! hlam
    exact funext hlam
  have hjIcc : j.val + 1 ∈ Icc 1 S := by simp only [mem_Icc]; omega
  set x : ℝ := -((j.val + 1 : ℝ) + 1 / 2)
  intro hP0
  have heval : (Pstar S lam).eval x = 0 := by simp [hP0]
  have hisol := eval_Pstar_at_oddLin_root lam j
  have hLne : (LpolyDiv S (j.val + 1)).eval x ≠ 0 := by
    simpa [x] using eval_LpolyDiv_at_oddLin_root hjIcc
  have hsign : (-1 : ℝ) ^ (j.val + 1) ≠ 0 :=
    pow_ne_zero _ (by norm_num : (-1 : ℝ) ≠ 0)
  have : ((-1 : ℝ) ^ (j.val + 1) * lam j) *
      (LpolyDiv S (j.val + 1)).eval x ≠ 0 :=
    mul_ne_zero (mul_ne_zero hsign hj) hLne
  rw [← hisol] at this
  exact this heval

theorem Dlam_ne_zero_of_lam_ne_zero {B S : ℕ} (_h : S < B) (hS : 0 < S)
    {lam : Fin S → ℝ} (hlam : lam ≠ 0) : Dlam B S lam ≠ 0 := by
  have hP : Pstar S lam ≠ 0 := Pstar_ne_zero_of_lam_ne_zero hS hlam
  have hL : Lpoly S ≠ 0 := Lpoly_ne_zero S
  have hE : Epoly B S ≠ 0 := Epoly_ne_zero B S
  have hE2 : (Epoly B S) ^ 2 ≠ 0 := pow_ne_zero 2 hE
  simpa [Dlam] using mul_ne_zero (mul_ne_zero hL hE2) hP

end CatalanSun.Structure
