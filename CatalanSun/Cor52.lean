/-
  CatalanSun/Cor52.lean

  Sun arXiv:2609.04176v1 §5, Corollary 5.2: the odd-prime-power positive-part
  ledger `∑_Q [a_{Q,B} − m^A_{Q,B}]₊ log p` of eq. (5.24).

  **What this file establishes, and what it does not.**

  It defines (5.24)'s right-hand side and proves the structural facts about it
  that Theorem 5.1 and Lemma 5.5 supply: the sum is finite and well defined,
  nonnegative, and loses nothing to the positive part (Theorem 5.1 gives
  `aQB ≥ mAQ`, so `[a−m]₊ = a−m` on every layer).

  It establishes **nothing** about `H_B^min`, integerizers, or `q̂_B`. The
  paper's Cor 5.2 bounds `log H_B^min` by this sum; that bridge needs the §4→§5
  odd-`p` valuation lemma (`v_p(Ξ_I) ≥ ℓ^A_Q(I) − …`), which does not exist in
  this development — `Thm51.lean` and `Lemma55.lean` contain no `padicVal`
  whatsoever, their layer quantities being pure ℕ/ℤ floor-and-collision
  combinatorics. The only valuation↔determinant bridge here is
  `lemma_5_4_det`, and it is `p = 2` only. Accordingly nothing in this file is
  named `logHmin`, and `posPartLedger` is a *definition* of the paper's bound,
  not a theorem about a height.

  **Divergence from the paper (the layer cutoff).** The index set is **not**
  `Lemma55.layerIndex B` (odd prime powers `< 5B`). That cutoff truncates a
  `Θ(B²)` contribution: `[a−m]₊` is nonzero for odd prime powers `Q ≥ 5B`, up
  to the exact threshold `Q ≤ 2(N−1) + 2B + 1 = 6B + 2S + 5`. Above that,
  `NKQ` vanishes identically and with it both `aQB` and `mAQ`. See
  `docs/FORMALIZATION-NOTES.md` (`#cor-52-cutoff`) for the measurements; the
  dropped mass is `≈ 0.627·B²`, about 65× the paper's `δ₀` margin. This file
  therefore sums over `layerIndexFull B S`, which carries the correct
  threshold.
-/

import CatalanSun.Lemma55
import CatalanSun.TwoAdic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false

noncomputable section

namespace CatalanSun.Cor52

open Finset CatalanSun.Thm51 CatalanSun.Lemma55

/-! ## Stage A: the paper's cited-but-undisplayed "Lemma 5.3"

Corollary 5.2's proof invokes a "Lemma 5.3" that is never displayed anywhere in
the arXiv v1 PDF. From its usage (`[x]₊ = x` given `x ≥ 0`) it is the trivial
positive-part identity, recorded here as a named lemma so the citation has a
referent. -/

/-- The paper's "Lemma 5.3": `[x]₊ = x` for `x ≥ 0`. -/
theorem posPart_eq_self_of_nonneg {x : ℤ} (hx : 0 ≤ x) :
    TwoAdic.posPart x = x :=
  max_eq_left hx

theorem posPart_nonneg (x : ℤ) : 0 ≤ TwoAdic.posPart x :=
  le_max_right _ _

/-- The positive part is 1-Lipschitz. This is the workhorse for comparing the
exact and corrected ledgers. -/
theorem abs_posPart_sub_le (x y : ℤ) :
    |TwoAdic.posPart x - TwoAdic.posPart y| ≤ |x - y| := by
  unfold TwoAdic.posPart
  simpa using abs_max_sub_max_le_max x (0 : ℤ) y (0 : ℤ)

/-! ## Stage B: the (5.24) index set and right-hand side

`Lemma55.layerIndex B` cuts off at `p^ν < 5*B`, which is **too small here** —
see the file header and `docs/FORMALIZATION-NOTES.md#cor-52-cutoff`. The
correct threshold is `layerBound B S = 6B + 2S + 5 = 2(N−1) + 2B + 1`, the
largest value the modulus argument `2i+2h+1` attains for `i < Ndim B S` and
`1 ≤ h ≤ B`. Above it `NKQ B Q i = 0` for every `i`, so the layer is empty of
content. -/

/-- The exact cutoff for nonzero layers: `2(N−1) + 2B + 1` with
`N = Ndim B S = 2B+S+3`. -/
def layerBound (B S : ℕ) : ℕ := 6 * B + 2 * S + 5

theorem layerBound_eq (B S : ℕ) :
    layerBound B S = 2 * (CatalanSun.NewtonCompletion.Ndim B S - 1) + 2 * B + 1 := by
  unfold layerBound CatalanSun.NewtonCompletion.Ndim
  omega

/-- `5*B` is strictly below the true cutoff, which is why `layerIndex` truncates. -/
theorem five_mul_lt_layerBound (B S : ℕ) (hB : 0 < B) :
    5 * B < layerBound B S := by
  unfold layerBound; omega

/-- Odd prime powers `p^ν ≤ layerBound B S`, indexed by the pair `(p, ν)`.
Mirrors `Lemma55.layerIndex`'s shape, with the corrected threshold. -/
def layerIndexFull (B S : ℕ) : Finset (ℕ × ℕ) :=
  ((range (layerBound B S + 1)) ×ˢ (range (layerBound B S + 1))).filter
    (fun pv => pv.1.Prime ∧ Odd pv.1 ∧ 1 ≤ pv.2 ∧ pv.1 ^ pv.2 ≤ layerBound B S)

theorem layerFull_mem_iff {B S : ℕ} {pv : ℕ × ℕ} :
    pv ∈ layerIndexFull B S ↔
      (pv.1 < layerBound B S + 1 ∧ pv.2 < layerBound B S + 1) ∧
        (pv.1.Prime ∧ Odd pv.1 ∧ 1 ≤ pv.2 ∧ pv.1 ^ pv.2 ≤ layerBound B S) := by
  unfold layerIndexFull
  rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]

/-- Each layer's `p ^ ν` is an odd prime power — the hypothesis `thm_5_1`
consumes. -/
theorem layerFull_oddPrimePower {B S : ℕ} {pv : ℕ × ℕ} (h : pv ∈ layerIndexFull B S) :
    OddPrimePower (pv.1 ^ pv.2) := by
  obtain ⟨-, hp, hodd, hnu, -⟩ := layerFull_mem_iff.mp h
  exact ⟨⟨pv.1, pv.2, hp.prime, hnu, rfl⟩, hodd.pow⟩

/-- Paper (5.24) summand: `[a_{Q,B} − m^A_{Q,B}]₊ · log p` at `Q = p^ν`.

The layer argument is `pv.1 ^ pv.2` (the prime *power*) and the weight is
`Real.log pv.1` (the *prime*). These two slots are exactly where the (5.3)
transcription bug lived; see `docs/FORMALIZATION-NOTES.md`. -/
def layerLogTerm (B S : ℕ) (f : Fin S → Fin (S + 3)) (pv : ℕ × ℕ) : ℝ :=
  ((TwoAdic.posPart (aQB B S (pv.1 ^ pv.2) - mAQ B S (pv.1 ^ pv.2) f) : ℤ) : ℝ)
    * Real.log pv.1

/-- Paper (5.24)'s right-hand side: the odd-prime-power positive-part ledger.

This is a **definition of the paper's bound**, not of `H_B^min`; see the file
header for what is and is not claimed. -/
def posPartLedger (B S : ℕ) (f : Fin S → Fin (S + 3)) : ℝ :=
  ∑ pv ∈ layerIndexFull B S, layerLogTerm B S f pv

theorem layerLogTerm_nonneg (B S : ℕ) (f : Fin S → Fin (S + 3)) (pv : ℕ × ℕ) :
    0 ≤ layerLogTerm B S f pv := by
  unfold layerLogTerm
  apply mul_nonneg
  · exact_mod_cast posPart_nonneg _
  · exact Real.log_natCast_nonneg _

theorem posPartLedger_nonneg (B S : ℕ) (f : Fin S → Fin (S + 3)) :
    0 ≤ posPartLedger B S f :=
  Finset.sum_nonneg fun pv _ => layerLogTerm_nonneg B S f pv

/-! ## Stage C: consuming Theorem 5.1 — the positive part collapses

This is Corollary 5.2's actual content at this level, and it is exactly where
the paper applies its "Lemma 5.3". Theorem 5.1 gives `aQB ≥ mAQ` on every odd
prime power layer, so `[a − m]₊ = a − m` and the ledger loses nothing to the
positive part. -/

/-- **Theorem 5.1 ⇒ no positive-part loss.** On every layer, at `B ≥ 20`,
`S = B/20` and injective `f`, the positive part is the plain difference. -/
theorem posPart_layer_eq (B : ℕ) (hB : 20 ≤ B)
    (f : Fin (B / 20) → Fin (B / 20 + 3)) (hf : Function.Injective f)
    {pv : ℕ × ℕ} (hpv : pv ∈ layerIndexFull B (B / 20)) :
    TwoAdic.posPart
        (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f)
      = aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f := by
  have hOPP : OddPrimePower (pv.1 ^ pv.2) := layerFull_oddPrimePower hpv
  have hS0 : 0 < B / 20 := Nat.div_pos hB (by norm_num)
  have hSB : B / 20 * 20 ≤ B := Nat.div_mul_le_self B 20
  have h51 := thm_5_1 B hB (pv.1 ^ pv.2) hOPP (B / 20) hS0 hSB f hf
  exact posPart_eq_self_of_nonneg (by omega)

/-- (5.24) with the positive parts discharged — the form §§6–9 integrate. -/
theorem posPartLedger_eq_raw (B : ℕ) (hB : 20 ≤ B)
    (f : Fin (B / 20) → Fin (B / 20 + 3)) (hf : Function.Injective f) :
    posPartLedger B (B / 20) f
      = ∑ pv ∈ layerIndexFull B (B / 20),
          ((aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f : ℤ) : ℝ)
            * Real.log pv.1 := by
  unfold posPartLedger layerLogTerm
  refine Finset.sum_congr rfl fun pv hpv => ?_
  rw [posPart_layer_eq B hB f hf hpv]

/-! ## Stage E: the `p = 2` layer

(5.24) is stated over all primes, with `p = 2` contributing nothing by Lemma
5.4. Here the prime 2 is absent from the index set by construction; this lemma
records that, so the omission is visible rather than silent. The mathematical
justification is `CatalanSun.lemma_5_4_det`. -/

theorem two_not_mem_layerIndexFull (B S ν : ℕ) : (2, ν) ∉ layerIndexFull B S := by
  intro h
  obtain ⟨-, -, hodd, -, -⟩ := layerFull_mem_iff.mp h
  exact (Nat.not_odd_iff_even.mpr even_two) hodd

/-! ## Stage D: the corrected-model ledger, and why Lemma 5.5 does not close it

`posPartLedger0` is (5.24)'s right-hand side in the `(0)` model that §§6–9
actually evaluate asymptotically. Lemma 5.5's (5.3)
(`lemma_5_5_ledger_little_o_holds`) is the statement that the two agree to
`o(B²)` — **but it is indexed over `Lemma55.layerIndex B`, whose cutoff is
`5B`, whereas the ledger here is indexed over `layerIndexFull B S`, whose
cutoff is `layerBound B S = 6B+2S+5`.**

`layerIndex_subset_layerIndexFull` below records that the former is contained
in the latter, so the difference is a sum over the band `[5B, 6B+2S+5]`. That
band is **not** negligible: measured `Θ(B²)` with `drop/B² ≈ 0.627` (stable
across `B = 400…1200` at `S = B/20`), against the paper's `δ₀ ≈ 0.00966`
margin. Consequently `lemma_5_5_ledger_little_o_holds` **cannot** be consumed
directly to compare `posPartLedger` with `posPartLedger0`, and this file does
not claim such a comparison. Closing that gap needs (5.3) re-proved over
`layerIndexFull`; see `docs/FORMALIZATION-NOTES.md#cor-52-cutoff`. -/

/-- The `(0)`-model ledger: (5.24)'s RHS with `a^{(0)}`/`m^{(0)}`. -/
def posPartLedger0 (B S : ℕ) (f : Fin S → Fin (S + 3)) : ℝ :=
  ∑ pv ∈ layerIndexFull B S,
    ((TwoAdic.posPart (a0QB B S (pv.1 ^ pv.2) - m0AQ B S (pv.1 ^ pv.2) f) : ℤ) : ℝ)
      * Real.log pv.1

theorem posPartLedger0_nonneg (B S : ℕ) (f : Fin S → Fin (S + 3)) :
    0 ≤ posPartLedger0 B S f := by
  refine Finset.sum_nonneg fun pv _ => mul_nonneg ?_ (Real.log_natCast_nonneg _)
  exact_mod_cast posPart_nonneg _

/-- Lemma 5.5's index set sits inside this file's: `5B < layerBound B S`. -/
theorem layerIndex_subset_layerIndexFull (B S : ℕ) (hB : 0 < B) :
    Lemma55.layerIndex B ⊆ layerIndexFull B S := by
  intro pv hpv
  obtain ⟨⟨h1, h2⟩, hp, hodd, hnu, hlt⟩ := Lemma55.layer_mem_iff.mp hpv
  have hbd : 5 * B < layerBound B S := five_mul_lt_layerBound B S hB
  exact layerFull_mem_iff.mpr ⟨⟨by omega, by omega⟩, hp, hodd, hnu, by omega⟩

/-- The termwise comparison Stage D would need, available unconditionally from
Stage A: the per-layer ledger discrepancy is controlled by the underlying
`(a−m)` discrepancy. This is the piece that *is* true regardless of the index
set; only the summation over the correct index set is missing. -/
theorem abs_layer_diff_le (B S : ℕ) (f : Fin S → Fin (S + 3)) (pv : ℕ × ℕ) :
    |((TwoAdic.posPart (aQB B S (pv.1 ^ pv.2) - mAQ B S (pv.1 ^ pv.2) f) : ℤ) : ℝ)
        - ((TwoAdic.posPart (a0QB B S (pv.1 ^ pv.2) - m0AQ B S (pv.1 ^ pv.2) f) : ℤ) : ℝ)|
      ≤ (((|(aQB B S (pv.1 ^ pv.2) - mAQ B S (pv.1 ^ pv.2) f)
              - (a0QB B S (pv.1 ^ pv.2) - m0AQ B S (pv.1 ^ pv.2) f)| : ℤ)) : ℝ) := by
  rw [← Int.cast_sub, ← Int.cast_abs, Int.cast_le]
  exact abs_posPart_sub_le _ _

end CatalanSun.Cor52
