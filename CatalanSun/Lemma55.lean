/-
  CatalanSun/Lemma55.lean

  Sun arXiv:2609.04176v1 §5.1 "Corrected full-row stability", Lemma 5.5.

  Scaffold only: definitions for the consecutive-row-set analogue `m^{(0)}_{Q,B}`
  of `mAQ` (using cutoff `U_0 = 2B+S-1` in place of `U = N-1 = 2B+S+2`), and the
  statement of Lemma 5.5's two claims:

    (5.2)  |m^A_{Q,B} - m^{(0)}_{Q,B}| ≤ C * (1 + B/Q)   for an absolute C,
           for every odd prime power Q (and the same bound for the
           corresponding denominator layers a_{Q,B} / a^{(0)}_{Q,B});

    (5.3)  ∑_{p odd, ν≥1} |(a_{p^ν,B} - m^A_{p^ν,B}) - (a^{(0)}_{p^ν,B} - m^{(0)}_{p^ν,B})| log p
             = o(B^2).

  Not proved here. The paper's argument (p.12) is genuinely asymptotic, unlike
  everything else landed in `Thm51.lean`:
    - the two row sets (exact selected rows vs. consecutive `{0,...,S-1}`) have
      symmetric difference at most six;
    - swapping `U = N-1` for `U_0` changes `⌊(U-i)/Q⌋` for at most `O(1+B/Q)`
      indices `i` on the common range, and every residue class mod `Q`
      contains at most `1 + U/Q` admissible indices, so each replacement's
      local cost (both the additive term and the double-Vandermonde/collision
      occupancy) changes by `O(1+B/Q)`;
    - at most three replacements suffice, giving (5.2);
    - nonzero layers satisfy `p^ν < 5B`; summing `O(1+B/Q)` over
      `O(√B log B)` prime powers below `5B` (via the trivial bound on the
      count of prime powers `< 5B`) gives `O(B log B) = o(B²)`, proving (5.3).

  See `docs/WORKPLAN-CONTINUATION.md` for the reduction plan.
-/

import CatalanSun.Thm51

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.Lemma55

open Finset CatalanSun.Thm51
open Function

/-! ## The consecutive-row cutoff `U₀` -/

/-- Paper (5.1): `U₀ := 2B + S - 1`, the cutoff used by the "clean limiting
model" (as opposed to the exact selected-row model's `U = N - 1 = 2B+S+2`
baked into `Ndim`). We track it as `U₀ + 1`, the analogue of `Ndim B S`, so it
plugs directly into `FNQ`/`ellAQ`'s existing `N` parameter. -/
def Ndim0 (B S : ℕ) : ℕ := 2 * B + S

theorem Ndim0_le_Ndim (B S : ℕ) :
    Ndim0 B S ≤ CatalanSun.NewtonCompletion.Ndim B S := by
  unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
  omega

/-- `S ≤ Ndim0 B S` whenever `0 ≤ B` (always true in `ℕ`), matching
`S_le_Ndim`'s unconditional shape. -/
theorem S_le_Ndim0 (B S : ℕ) : S ≤ Ndim0 B S := by
  unfold Ndim0
  omega

/-! ## `ℓ^{(0)}` / `m^{(0)}`: the consecutive-row-set local layer and its min

These reuse `ellAQ`/`mAQ`'s formula verbatim but instantiate the ambient
dimension at `Ndim0 B S` (i.e. `U₀ + 1` in place of `N = U + 1`), and restrict
the minimization to the single consecutive index set `{0,...,S-1}` rather
than minimizing over all card-`S` subsets (paper: "the analogue of (5.8) with
the consecutive row set `{0,...,S-1}`, upper index `U₀`"). -/

/-- `ℓ^{(0)}_Q` (paper §5.1): `ellAQ`'s formula at dimension `Ndim0 B S`,
evaluated at the fixed consecutive row set. -/
def ell0AQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S) : ℤ :=
  ellAQ B S Q f
    ((CatalanSun.Thm51.consecutiveInitial (N := Ndim0 B S) S hS).map
      ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
    (by
      rw [Finset.card_map]
      exact CatalanSun.Thm51.consecutiveInitial_card hS)

/-- `m^{(0)}_{Q,B}` (paper §5.1): since the consecutive row set is fixed (not
minimized over), `m^{(0)}` is just `ell0AQ` at that set. -/
def m0AQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S) : ℤ :=
  ell0AQ B S Q f hS

/-- `a^{(0)}_{Q,B}` (paper §5.1): `aQB`'s formula with the row range cut at
`Ndim0 B S` (i.e. `U₀ + 1`) instead of `Ndim B S`. -/
def a0QB (B S Q : ℕ) : ℤ :=
  2 * ∑ i : Fin (Ndim0 B S), (NKQ B Q i.val : ℤ) -
    (phiQ Q (CatalanSun.NewtonCompletion.Dref B) : ℤ)

/-! ## Lemma 5.5, target statements -/

/-- Paper (5.2): an absolute constant `C` bounding `|m^A - m^{(0)}|` by
`C * (1 + B/Q)`, uniformly over odd prime powers `Q`. Stated with the
`ℚ`-valued ratio `B / Q` to match the paper's real-number bound; `C` is
existentially quantified once, ahead of `B`/`S`/`Q`/`f`, matching "absolute
constant." -/
def lemma_5_5_row_stability : Prop :=
  ∃ C : ℚ, 0 < C ∧
    ∀ (B S Q : ℕ), OddPrimePower Q → 0 < S → S * 20 ≤ B →
      ∀ (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S),
        (|(mAQ B S Q f : ℚ) - (m0AQ B S Q f hS : ℚ)| : ℚ) ≤
          C * (1 + (B : ℚ) / (Q : ℚ))

/-- The finite index set of layers summed in (5.3) and (5.24): odd primes `p`
with some `ν ≥ 1` giving a nonzero layer, restricted (per the proof) to
`p ^ ν < 5 * B`. We range over `(p, ν) ∈ ℕ × ℕ` pairs with `p` odd prime,
`1 ≤ ν`, `p ^ ν < 5 * B`, taking this as a `Finset` via a bounding box on
`p` and `ν` (both are `< 5 * B`). -/
def layerIndex (B : ℕ) : Finset (ℕ × ℕ) :=
  ((range (5 * B)) ×ˢ (range (5 * B))).filter
    (fun pv => pv.1.Prime ∧ Odd pv.1 ∧ 1 ≤ pv.2 ∧ pv.1 ^ pv.2 < 5 * B)

/-- Paper (5.3): fixing `S` at the paper's canonical ratio `S = B / 20`, for
every `ε > 0` there is `B₀` such that for all `B ≥ B₀`, the summed absolute
ledger difference between the exact and consecutive-row models is at most
`ε * B ^ 2` (i.e. `o(B²)` unwound to its `ε`-`B₀` definition). `f`/`hS` are
universally quantified per `B` since the bound must hold along any
`Injective f` witness used in `thm_5_1_statement`. -/
def lemma_5_5_ledger_little_o : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
    ∀ (f : Fin (B / 20) → Fin (B / 20 + 3)) (hS : B / 20 ≤ Ndim0 B (B / 20)),
      ∑ pv ∈ layerIndex B,
        (|(((a0QB B (B / 20) pv.1 - m0AQ B (B / 20) pv.1 f hS) -
              (aQB B (B / 20) pv.1 - mAQ B (B / 20) pv.1 f) : ℤ) : ℝ)| : ℝ) *
          Real.log pv.1 ≤ ε * (B : ℝ) ^ 2

end CatalanSun.Lemma55
