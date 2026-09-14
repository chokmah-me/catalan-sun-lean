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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Defs
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

end CatalanSun.Structure
