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
  threshold, and re-proves Lemma 5.5's (5.3) over that index set (Stage F,
  `ledgerFull_little_o`) so that the exact-model and `(0)`-model ledgers can be
  compared: `posPartLedger_sub_little_o` says they agree to `o(B²)`.
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
directly to compare `posPartLedger` with `posPartLedger0`. Stage F below
re-proves (5.3) over `layerIndexFull` (`ledgerFull_little_o`), and the closing
theorem `posPartLedger_sub_little_o` is proved against that; see
`docs/FORMALIZATION-NOTES.md#cor-52-cutoff`. -/

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

/-! ## Stage F: Lemma 5.5's (5.3), re-proved over the full index set

`Lemma55.lemma_5_5_ledger_little_o_holds` is (5.3) over `layerIndex B`
(cutoff `5B`). The proof there never uses `5B` structurally — only as a
numeric cap on the layer count, the harmonic sum and `log p`. This stage
re-runs that proof over `layerIndexFull B (B/20)` with every cap replaced by
`12 * B` (since `layerBound B (B/20) = 6B + 2(B/20) + 5 ≤ 12B` for `B ≥ 1`),
giving `SUM ≤ 111 · B · log(12B) · (13 + log 12B) = Θ(B log² B) = o(B²)`.
Gated numerically first (`scripts/gates/gate_full53.py`): the bound is at most
~1.9× the `5B` one and decays to `0` as `B → ∞`. -/

theorem layerFull_pow_injOn {B S : ℕ} :
    Set.InjOn (fun pv : ℕ × ℕ => pv.1 ^ pv.2) (layerIndexFull B S) := by
  intro x hx y hy hxy
  simp only [Finset.mem_coe, layerFull_mem_iff] at hx hy
  obtain ⟨-, hpx, -, hnx, -⟩ := hx
  obtain ⟨-, hpy, -, hny, -⟩ := hy
  simp only at hxy
  have hp : x.1 = y.1 := by
    have hdvd : x.1 ∣ y.1 ^ y.2 := by rw [← hxy]; exact dvd_pow_self x.1 (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hpx hpy).mp (hpx.dvd_of_dvd_pow hdvd)
  have hexp : x.2 = y.2 := by
    apply Nat.pow_right_injective hpx.two_le
    change x.1 ^ x.2 = x.1 ^ y.2
    rw [hxy, hp]
  exact Prod.ext hp hexp

/-- Layer count: `(p,ν) ↦ p^ν` injects into `[1, layerBound B S]`. -/
theorem card_layerIndexFull_le (B S : ℕ) :
    (layerIndexFull B S).card ≤ layerBound B S := by
  classical
  have := Finset.card_le_card_of_injOn (f := fun pv : ℕ × ℕ => pv.1 ^ pv.2)
    (s := layerIndexFull B S) (t := Finset.Icc 1 (layerBound B S))
    (fun pv hpv => by
      obtain ⟨-, hp, -, -, hle⟩ := layerFull_mem_iff.mp hpv
      exact Finset.mem_Icc.mpr ⟨Nat.pow_pos hp.pos, hle⟩)
    layerFull_pow_injOn
  simpa using this

/-- At the paper's ratio `S = B/20`, the cutoff is at most `12 B`. -/
theorem layerBound_le_twelve (B : ℕ) (hB : 1 ≤ B) :
    layerBound B (B / 20) ≤ 12 * B := by
  unfold layerBound; omega

theorem sum_inv_layerFull_le (B S : ℕ) :
    ∑ pv ∈ layerIndexFull B S, (1 : ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ)
      ≤ (harmonic (layerBound B S) : ℝ) := by
  classical
  have himg : ∑ pv ∈ layerIndexFull B S, (1 : ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ)
      = ∑ n ∈ (layerIndexFull B S).image (fun pv => pv.1 ^ pv.2),
          (1 : ℝ) / ((n : ℕ) : ℝ) := by
    rw [Finset.sum_image]
    intro a ha b hb h
    exact layerFull_pow_injOn ha hb h
  rw [himg]
  have hharm : (harmonic (layerBound B S) : ℝ)
      = ∑ i ∈ Finset.range (layerBound B S), ((i : ℝ) + 1)⁻¹ := by
    unfold harmonic
    push_cast
    ring_nf
  have hsub : (layerIndexFull B S).image (fun pv => pv.1 ^ pv.2)
      ⊆ (Finset.range (layerBound B S)).image (fun i => i + 1) := by
    intro n hn
    rw [Finset.mem_image] at hn
    obtain ⟨pv, hpv, rfl⟩ := hn
    obtain ⟨-, hp, -, -, hle⟩ := layerFull_mem_iff.mp hpv
    have hpos : 0 < pv.1 ^ pv.2 := Nat.pow_pos hp.pos
    rw [Finset.mem_image]
    exact ⟨pv.1 ^ pv.2 - 1, Finset.mem_range.mpr (by omega), by omega⟩
  have hrhs : ∑ i ∈ Finset.range (layerBound B S), ((i : ℝ) + 1)⁻¹
      = ∑ n ∈ (Finset.range (layerBound B S)).image (fun i => i + 1),
          (1 : ℝ) / ((n : ℕ) : ℝ) := by
    rw [Finset.sum_image (by intro a _ b _ h; simp only [] at h; omega)]
    apply Finset.sum_congr rfl
    intro i _
    push_cast
    rw [one_div]
  rw [hharm, hrhs]
  apply Finset.sum_le_sum_of_subset_of_nonneg hsub
  intro n _ _
  positivity

/-- The per-layer bound, with `log p ≤ log(12B)`. Mirrors
`Lemma55.layer_term_le`; the (5.2) input `layer_int_bound` has no upper
cutoff on `Q`, which is exactly why the widening is mechanical. -/
theorem layerFull_term_le {B : ℕ} (hB0 : 0 < B / 20) {pv : ℕ × ℕ}
    (hpv : pv ∈ layerIndexFull B (B / 20)) (f : Fin (B / 20) → Fin (B / 20 + 3)) :
    (|(((a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) -
        (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)|)
      * Real.log pv.1
      ≤ 111 * ((B : ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ) + 1) * Real.log (12 * B) := by
  set Q := pv.1 ^ pv.2 with hQdef
  obtain ⟨-, hp, hodd, hnu, hQle⟩ := layerFull_mem_iff.mp hpv
  have hOPP : OddPrimePower Q := ⟨⟨pv.1, pv.2, hp.prime, hnu, rfl⟩, hodd.pow⟩
  have hQ : 0 < Q := hOPP.pos
  have hSB : (B / 20) * 20 ≤ B := Nat.div_mul_le_self B 20
  have hB1 : 1 ≤ B := by omega
  have hint := layer_int_bound (B := B) (S := B / 20) (Q := Q) hQ hOPP.odd hB0 hSB f
  have hcast : (|(((a0QB B (B / 20) Q - m0AQ B (B / 20) Q f) -
      (aQB B (B / 20) Q - mAQ B (B / 20) Q f) : ℤ) : ℝ)|)
      ≤ 111 * ((((B / Q : ℕ)) : ℝ) + 1) := by
    have h := (Int.cast_le (R := ℝ)).mpr hint
    rw [Int.cast_abs] at h
    refine h.trans (le_of_eq ?_)
    rw [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast]
    norm_num
  have hdiv : (((B / Q : ℕ)) : ℝ) ≤ (B : ℝ) / (Q : ℝ) := Nat.cast_div_le
  have habs_le : (|(((a0QB B (B / 20) Q - m0AQ B (B / 20) Q f) -
      (aQB B (B / 20) Q - mAQ B (B / 20) Q f) : ℤ) : ℝ)|)
      ≤ 111 * ((B : ℝ) / (Q : ℝ) + 1) := by linarith
  have hp2 : 2 ≤ pv.1 := hp.two_le
  have hple : pv.1 ≤ Q := by rw [hQdef]; exact Nat.le_self_pow (by omega) _
  have hlogp : Real.log pv.1 ≤ Real.log (12 * B) := by
    apply Real.log_le_log (by positivity)
    have h12 := layerBound_le_twelve B hB1
    have : pv.1 ≤ 12 * B := by omega
    exact_mod_cast this
  have hlogp0 : 0 ≤ Real.log pv.1 := Real.log_natCast_nonneg _
  have hrhs0 : (0:ℝ) ≤ 111 * ((B : ℝ) / (Q : ℝ) + 1) := by
    have : (0:ℝ) ≤ (B : ℝ) / (Q : ℝ) := by positivity
    linarith
  calc _ ≤ (111 * ((B : ℝ) / (Q : ℝ) + 1)) * Real.log pv.1 := by
          exact mul_le_mul_of_nonneg_right habs_le hlogp0
    _ ≤ (111 * ((B : ℝ) / (Q : ℝ) + 1)) * Real.log (12 * B) :=
          mul_le_mul_of_nonneg_left hlogp hrhs0
    _ = 111 * ((B : ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ) + 1) * Real.log (12 * B) := by
          rw [← hQdef]

/-- `111 · log(12B) · (13 + log 12B) ≤ ε B` eventually: `log²x / x → 0`. -/
theorem eventually_log_sq_le_twelve {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ B : ℕ in Filter.atTop,
      111 * Real.log (12 * B) * (13 + Real.log (12 * B)) ≤ ε * (B : ℝ) := by
  have h2 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 2 / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have h0 : Filter.Tendsto (fun x : ℝ => Real.log x ^ 0 / (1 * x + 0)) Filter.atTop (nhds 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 0 one_ne_zero
  -- 111·(l12 + lB)·(13 + l12 + lB) = 111 lB² + (222 l12 + 1443) lB + (111 l12² + 1443 l12)
  set c1 : ℝ := 111
  set c2 : ℝ := 222 * Real.log 12 + 1443
  set c3 : ℝ := 111 * Real.log 12 ^ 2 + 1443 * Real.log 12
  have hF : Filter.Tendsto
      (fun x : ℝ => c1 * (Real.log x ^ 2 / (1 * x + 0))
                  + c2 * (Real.log x ^ 1 / (1 * x + 0))
                  + c3 * (Real.log x ^ 0 / (1 * x + 0))) Filter.atTop (nhds 0) := by
    have := ((h2.const_mul c1).add (h1.const_mul c2)).add (h0.const_mul c3)
    simpa using this
  have hFN := hF.comp tendsto_natCast_atTop_atTop
  have hev := hFN.eventually (eventually_lt_nhds hε)
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with B hB hB1
  simp only [Function.comp_apply, one_mul, add_zero, pow_one, pow_zero] at hB
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB1
  have hlogB : Real.log (12 * (B:ℝ)) = Real.log 12 + Real.log B := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hBpos)]
  have hlogBnn : 0 ≤ Real.log B := Real.log_natCast_nonneg _
  have hlog12 : (0:ℝ) ≤ Real.log 12 := Real.log_nonneg (by norm_num)
  have hB' : c1 * Real.log B ^ 2 + c2 * Real.log B + c3 < ε * (B:ℝ) := by
    have hcomb : c1 * (Real.log B ^ 2 / (B:ℝ)) + c2 * (Real.log B / (B:ℝ))
        + c3 * (1 / (B:ℝ))
        = (c1 * Real.log B ^ 2 + c2 * Real.log B + c3) / (B:ℝ) := by
      field_simp
    rw [hcomb] at hB
    exact (div_lt_iff₀ hBpos).mp hB
  rw [hlogB]
  simp only [c1, c2, c3] at hB'
  nlinarith [hB', hlogBnn, hlog12, hBpos]

/-- The assembled full-index ledger bound:
`SUM ≤ 111 · B · log(12B) · (13 + log 12B)`. -/
theorem ledgerFull_sum_le {B : ℕ} (hB0 : 0 < B / 20) (hB1 : 1 ≤ B)
    (f : Fin (B / 20) → Fin (B / 20 + 3)) :
    ∑ pv ∈ layerIndexFull B (B / 20),
      (|(((a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) -
          (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)|)
        * Real.log pv.1
      ≤ 111 * (B : ℝ) * Real.log (12 * B) * (13 + Real.log (12 * B)) := by
  classical
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB1
  have hlog12B : 0 ≤ Real.log (12 * B) := by
    apply Real.log_nonneg
    have h : (1:ℝ) ≤ (B:ℝ) := by exact_mod_cast hB1
    linarith
  have hterm : ∀ pv ∈ layerIndexFull B (B / 20),
      (|(((a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) -
          (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)|)
        * Real.log pv.1
        ≤ (111 * Real.log (12 * B)) * ((B:ℝ) * ((1:ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ)))
          + 111 * Real.log (12 * B) := by
    intro pv hpv
    have h := layerFull_term_le hB0 hpv f
    have hQpos : (0:ℝ) < ((pv.1 ^ pv.2 : ℕ) : ℝ) := by
      have hp := (layerFull_oddPrimePower hpv).pos
      exact_mod_cast hp
    calc _ ≤ 111 * ((B : ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ) + 1) * Real.log (12 * B) := h
      _ = (111 * Real.log (12 * B)) * ((B:ℝ) * ((1:ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ)))
            + 111 * Real.log (12 * B) := by field_simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
  -- the harmonic step, capped at 12B
  have h12 := layerBound_le_twelve B hB1
  have h12R : ((layerBound B (B / 20) : ℕ) : ℝ) ≤ 12 * (B:ℝ) := by
    have h : ((layerBound B (B / 20) : ℕ) : ℝ) ≤ ((12 * B : ℕ) : ℝ) := by
      exact_mod_cast h12
    have h' : ((12 * B : ℕ) : ℝ) = 12 * (B:ℝ) := by push_cast; ring
    rw [h'] at h; exact h
  have hinv : ∑ pv ∈ layerIndexFull B (B / 20),
        (B:ℝ) * ((1:ℝ) / ((pv.1 ^ pv.2 : ℕ) : ℝ))
      ≤ (B:ℝ) * (1 + Real.log (12 * B)) := by
    rw [← Finset.mul_sum]
    have h1 := sum_inv_layerFull_le B (B / 20)
    have h2 : (harmonic (layerBound B (B / 20)) : ℝ)
        ≤ 1 + Real.log ((layerBound B (B / 20) : ℕ) : ℝ) :=
      harmonic_le_one_add_log _
    have hLpos : (0:ℝ) < ((layerBound B (B / 20) : ℕ) : ℝ) := by
      have : 0 < layerBound B (B / 20) := by unfold layerBound; omega
      exact_mod_cast this
    have h3 : Real.log ((layerBound B (B / 20) : ℕ) : ℝ) ≤ Real.log (12 * B) :=
      Real.log_le_log hLpos h12R
    exact mul_le_mul_of_nonneg_left (h1.trans (h2.trans (by linarith))) (le_of_lt hBpos)
  have hcard : ((layerIndexFull B (B / 20)).card : ℝ) ≤ 12 * (B:ℝ) := by
    have hc := card_layerIndexFull_le B (B / 20)
    calc ((layerIndexFull B (B / 20)).card : ℝ)
        ≤ ((layerBound B (B / 20) : ℕ) : ℝ) := by exact_mod_cast hc
      _ ≤ 12 * (B:ℝ) := h12R
  have hc0 : (0:ℝ) ≤ 111 * Real.log (12 * B) := by positivity
  nlinarith [hinv, hcard, hc0, hlog12B, hBpos]

/-- **Paper (5.3) over the full index set** `layerIndexFull B (B/20)`: the
exact statement of `Lemma55.lemma_5_5_ledger_little_o` with `layerIndex B`
replaced by the correctly-cut-off index set. Same `ε`-`B₀` form. -/
theorem ledgerFull_little_o :
    ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (f : Fin (B / 20) → Fin (B / 20 + 3)),
        ∑ pv ∈ layerIndexFull B (B / 20),
          (|(((a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) -
                (aQB B (B / 20) (pv.1 ^ pv.2)
                  - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)| : ℝ)
            * Real.log pv.1 ≤ ε * (B : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨B₁, hB₁⟩ := Filter.eventually_atTop.mp (eventually_log_sq_le_twelve hε)
  refine ⟨max B₁ 20, ?_⟩
  intro B hB f
  have hB1' : B₁ ≤ B := le_trans (le_max_left _ _) hB
  have hB20 : 20 ≤ B := le_trans (le_max_right _ _) hB
  have hB0 : 0 < B / 20 := Nat.div_pos hB20 (by norm_num)
  have hB1 : 1 ≤ B := by omega
  have hBpos : (0:ℝ) < (B:ℝ) := by exact_mod_cast hB1
  have hsum := ledgerFull_sum_le hB0 hB1 f
  have hlim := hB₁ B hB1'
  have hrw : 111 * (B : ℝ) * Real.log (12 * B) * (13 + Real.log (12 * B))
      = (B:ℝ) * (111 * Real.log (12 * B) * (13 + Real.log (12 * B))) := by ring
  rw [hrw] at hsum
  calc _ ≤ (B:ℝ) * (111 * Real.log (12 * B) * (13 + Real.log (12 * B))) := hsum
    _ ≤ (B:ℝ) * (ε * (B:ℝ)) := mul_le_mul_of_nonneg_left hlim (le_of_lt hBpos)
    _ = ε * (B:ℝ) ^ 2 := by ring

/-! ## Stage D, closed: the two ledgers agree to `o(B²)`

With (5.3) available over `layerIndexFull`, the termwise 1-Lipschitz bound
`abs_layer_diff_le` sums to the comparison Stage D was missing. -/

/-- Termwise-to-summed: `|posPartLedger − posPartLedger0|` is at most the
(5.3) ledger sum over the same index set. -/
theorem abs_posPartLedger_sub_le (B : ℕ) (f : Fin (B / 20) → Fin (B / 20 + 3)) :
    |posPartLedger B (B / 20) f - posPartLedger0 B (B / 20) f|
      ≤ ∑ pv ∈ layerIndexFull B (B / 20),
          (|(((a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) -
                (aQB B (B / 20) (pv.1 ^ pv.2)
                  - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)| : ℝ)
            * Real.log pv.1 := by
  unfold posPartLedger posPartLedger0 layerLogTerm
  rw [← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun pv _ => ?_)
  have hlog : 0 ≤ Real.log pv.1 := Real.log_natCast_nonneg _
  have hcomm : (|(aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f)
        - (a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f)| : ℤ)
      = |(a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f)
        - (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f)| :=
    abs_sub_comm _ _
  calc _ = |((TwoAdic.posPart
                (aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)
            - ((TwoAdic.posPart
                (a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f) : ℤ) : ℝ)|
            * Real.log pv.1 := by
          rw [← sub_mul, abs_mul, abs_of_nonneg hlog]
    _ ≤ (((|(aQB B (B / 20) (pv.1 ^ pv.2) - mAQ B (B / 20) (pv.1 ^ pv.2) f)
              - (a0QB B (B / 20) (pv.1 ^ pv.2) - m0AQ B (B / 20) (pv.1 ^ pv.2) f)| : ℤ)) : ℝ)
            * Real.log pv.1 :=
          mul_le_mul_of_nonneg_right (abs_layer_diff_le B (B / 20) f pv) hlog
    _ = _ := by rw [hcomm, Int.cast_abs]

/-- **Stage D closed.** The exact-model and `(0)`-model positive-part ledgers
of (5.24) agree to `o(B²)` at `S = B/20`, for every `f`. This is the statement
§§6–9 need in order to evaluate (5.24) in the `(0)` model. -/
theorem posPartLedger_sub_little_o :
    ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
      ∀ (f : Fin (B / 20) → Fin (B / 20 + 3)),
        |posPartLedger B (B / 20) f - posPartLedger0 B (B / 20) f| ≤ ε * (B : ℝ) ^ 2 := by
  intro ε hε
  obtain ⟨B₀, hB₀⟩ := ledgerFull_little_o ε hε
  exact ⟨B₀, fun B hB f => (abs_posPartLedger_sub_le B f).trans (hB₀ B hB f)⟩

end CatalanSun.Cor52
