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

open Finset CatalanSun.Thm51 CatalanSun.NewtonCompletion
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

/-- `ℓ^{(0)}_Q` (paper §5.1): `ellAQ`'s formula, but at ambient dimension
`Ndim0 B S` (i.e. with `FNQ (Ndim0 B S) Q i.val` in place of
`FNQ (Ndim B S) Q i.val`), evaluated at the fixed consecutive row set. Uses
`ellAQN` (the `N`-generalized `ellAQ`) directly at `N = Ndim0 B S`, so the
`U₀ = 2B+S-1` cutoff genuinely appears in the value. -/
def ell0AQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S) : ℤ :=
  ellAQN B S Q f (Ndim0 B S)
    (CatalanSun.Thm51.consecutiveInitial (N := Ndim0 B S) S hS)
    (CatalanSun.Thm51.consecutiveInitial_card hS)

/-- `m^{(0)}_{Q,B}` (paper §5.1): since the consecutive row set is fixed (not
minimized over), `m^{(0)}` is just `ell0AQ` at that set. -/
def m0AQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S) : ℤ :=
  ell0AQ B S Q f hS

/-- `a^{(0)}_{Q,B}` (paper §5.1): `aQB`'s formula with the row range cut at
`Ndim0 B S` (i.e. `U₀ + 1`) instead of `Ndim B S`. -/
def a0QB (B S Q : ℕ) : ℤ :=
  2 * ∑ i : Fin (Ndim0 B S), (NKQ B Q i.val : ℤ) -
    (phiQ Q (CatalanSun.NewtonCompletion.Dref B) : ℤ)

/-! ## Div-shift bound: `⌊(x+d)/Q⌋ - ⌊x/Q⌋ ≤ d/Q + 1`

The atomic combinatorial fact behind (5.2): shifting the dividend by a fixed
`d` changes a floor-division value by at most `d/Q + 1`. This drives the
`FNQ` swap between `Ndim B S` and `Ndim0 B S` (which differ by the constant
`3`), and will drive the row-swap replacements too. -/

private theorem lt_div_add_one_mul (n Q : ℕ) (hQ : 0 < Q) : n < (n / Q + 1) * Q := by
  have h := Nat.div_add_mod n Q
  have hm : n % Q < Q := Nat.mod_lt _ hQ
  nlinarith

theorem div_add_le_div_add (x d Q : ℕ) (hQ : 0 < Q) :
    (x + d) / Q ≤ x / Q + d / Q + 1 := by
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hQ]
  have hx : x < (x / Q + 1) * Q := lt_div_add_one_mul x Q hQ
  have hd : d < (d / Q + 1) * Q := lt_div_add_one_mul d Q hQ
  nlinarith

theorem div_le_div_add (x d Q : ℕ) (hQ : 0 < Q) :
    x / Q ≤ (x + d) / Q + d / Q + 1 := by
  have h4 : (x + d) / Q + 1 ≤ ((x + d) / Q + d / Q + 1).succ := by
    have h5 : (x + d) / Q + 1 ≤ (x + d) / Q + d / Q + 1 := by
      have := Nat.le_add_right ((x + d) / Q + 1) (d / Q)
      omega
    exact Nat.le_succ_of_le h5
  rw [← Nat.lt_succ_iff, Nat.div_lt_iff_lt_mul hQ]
  have h1 : x + d < ((x + d) / Q + 1) * Q := lt_div_add_one_mul (x + d) Q hQ
  have h2 : x ≤ x + d := Nat.le_add_right x d
  have h3 : x < ((x + d) / Q + 1) * Q := lt_of_le_of_lt h2 h1
  calc x < ((x + d) / Q + 1) * Q := h3
    _ ≤ ((x + d) / Q + d / Q + 1).succ * Q := by gcongr

/-- The two-sided div-shift bound: `|⌊(x+d)/Q⌋ - ⌊x/Q⌋| ≤ d/Q + 1` (as `ℕ`
subtraction cast to `ℤ`, i.e. genuinely `|·|` since both orders are covered). -/
theorem abs_div_shift_le (x d Q : ℕ) (hQ : 0 < Q) :
    (|(((x + d) / Q : ℕ) : ℤ) - ((x / Q : ℕ) : ℤ)| : ℤ) ≤ ((d / Q : ℕ) : ℤ) + 1 := by
  have h1 : (x + d) / Q ≤ x / Q + d / Q + 1 := div_add_le_div_add x d Q hQ
  have h2 : x / Q ≤ (x + d) / Q + d / Q + 1 := div_le_div_add x d Q hQ
  rw [abs_le]
  constructor
  · have : ((x / Q : ℕ) : ℤ) ≤ (((x + d) / Q : ℕ) : ℤ) + ((d / Q : ℕ) : ℤ) + 1 := by
      exact_mod_cast h2
    linarith
  · have : (((x + d) / Q : ℕ) : ℤ) ≤ ((x / Q : ℕ) : ℤ) + ((d / Q : ℕ) : ℤ) + 1 := by
      exact_mod_cast h1
    linarith

/-! ## Comparing `ellAQ` and `ell0AQ` on the shared consecutive row set

`ellAQN`'s four summands (`CAQ`, the collision sum via `nQr`, the `NKQ`/
`indicatorQle` terms) depend on `I` only through the underlying natural
values `i.val`, not on the ambient `N`; only the `FNQ N Q i.val` term does.
Since `consecutiveInitial (N := Ndim0 B S) S hS`, mapped into
`Fin (Ndim B S)` via `castLE`, has exactly the same underlying values as
`consecutiveInitial (N := Ndim B S) S hS`, the two `ellAQN` evaluations
differ by exactly the sum of `FNQ` differences over `i < S`. -/

/-- The `FNQ` shift for `N = Ndim B S` vs `N' = Ndim0 B S = N - 3`, at an
index `i < S ≤ Ndim0 B S`: bounded by `3/Q + 1` via `abs_div_shift_le`. -/
theorem abs_FNQ_shift_le {B S Q i : ℕ} (hQ : 0 < Q) (hi : i < S)
    (hS0 : S ≤ Ndim0 B S) :
    (|(FNQ (Ndim B S) Q i : ℤ) - (FNQ (Ndim0 B S) Q i : ℤ)| : ℤ) ≤
      ((3 / Q : ℕ) : ℤ) + 1 := by
  have hiN0 : i < Ndim0 B S := lt_of_lt_of_le hi hS0
  have key := abs_div_shift_le (Ndim0 B S - 1 - i) 3 Q hQ
  have heq1 : Ndim0 B S - 1 - i + 3 = Ndim B S - 1 - i := by
    unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
    omega
  rw [heq1] at key
  have hFNQ : FNQ (Ndim B S) Q i = i / Q + (Ndim B S - 1 - i) / Q := rfl
  have hFNQ0 : FNQ (Ndim0 B S) Q i = i / Q + (Ndim0 B S - 1 - i) / Q := rfl
  rw [hFNQ, hFNQ0]
  have heq2 : (((i / Q + (Ndim B S - 1 - i) / Q : ℕ) : ℤ)) -
      (((i / Q + (Ndim0 B S - 1 - i) / Q : ℕ)) : ℤ) =
      (((Ndim B S - 1 - i) / Q : ℕ) : ℤ) - (((Ndim0 B S - 1 - i) / Q : ℕ) : ℤ) := by
    push_cast
    ring
  rw [heq2]
  exact key

/-- `nQr` is invariant under the `castLE` embedding of the consecutive set:
the residue-`r` count among `{0,…,S-1} ⊆ Fin (Ndim0 B S)` equals the same
count after re-embedding into `Fin (Ndim B S)`, since `castLE` preserves
`.val` and hence `% Q`. -/
theorem nQr_consecutiveInitial_castLE {B S Q r : ℕ} (hS : S ≤ Ndim0 B S) :
    nQr Q r
        ((consecutiveInitial (N := Ndim0 B S) S hS).map
          ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩) =
      nQr Q r (consecutiveInitial (N := Ndim0 B S) S hS) := by
  unfold nQr
  rw [Finset.filter_map]
  simp only [Function.Embedding.coeFn_mk, Fin.val_castLE, Function.comp]
  rw [Finset.card_map]

/-- The row-level layer sum (`NKQ`/`indicatorQle`/`FNQ` terms of `ellAQN`) is
invariant under `castLE` except for the `FNQ` piece, since `NKQ`/
`indicatorQle` depend only on `.val`. -/
theorem ellAQN_castLE_sub_eq {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (hS : S ≤ Ndim0 B S) :
    ellAQN B S Q f (Ndim B S)
        ((consecutiveInitial (N := Ndim0 B S) S hS).map
          ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
        (by rw [Finset.card_map]; exact consecutiveInitial_card hS) -
      ellAQN B S Q f (Ndim0 B S) (consecutiveInitial (N := Ndim0 B S) S hS)
        (consecutiveInitial_card hS) =
      ∑ i ∈ consecutiveInitial (N := Ndim0 B S) S hS,
        ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
  unfold ellAQN
  set J := consecutiveInitial (N := Ndim0 B S) S hS
  set e : Fin (Ndim0 B S) ↪ Fin (Ndim B S) :=
    ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩
  have hnQr : ∀ r, nQr Q r (J.map e) = nQr Q r J := fun r =>
    nQr_consecutiveInitial_castLE (B := B) (S := S) (Q := Q) (r := r) hS
  have hsum1 :
      ∑ i ∈ J.map e,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) =
        ∑ i ∈ J,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
    rw [Finset.sum_map]
    rfl
  simp only [hnQr, hsum1]
  have hfinal :
      ∑ i ∈ J,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) -
        ∑ i ∈ J,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) =
      ∑ i ∈ J, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hfinal]

/-- The `castLE`-image of the consecutive set at `Ndim0 B S` is literally the
consecutive set at `Ndim B S` (both are `{i : i.val < S}`). -/
theorem consecutiveInitial_castLE_eq {B S : ℕ} (hS : S ≤ Ndim0 B S) :
    (consecutiveInitial (N := Ndim0 B S) S hS).map
        ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩ =
      consecutiveInitial (N := Ndim B S) S (S_le_Ndim0 B S |>.trans (Ndim0_le_Ndim B S)) := by
  ext i
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, mem_consecutiveInitial_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa [Fin.castLE] using hj
  · intro hi
    exact ⟨⟨i.val, lt_of_lt_of_le hi hS⟩, hi, rfl⟩

/-- The main bridge: `ellAQ` at the full-dimension consecutive set minus
`ell0AQ` is exactly the sum of `FNQ` differences over `{0,…,S-1}`, hence
bounded by `S * (3/Q + 1)` via `abs_FNQ_shift_le`. -/
theorem abs_ellAQ_consecutive_sub_ell0AQ_le {B S Q : ℕ} (hQ : 0 < Q)
    (f : Fin S → Fin (S + 3)) (hS0 : S ≤ Ndim0 B S) :
    (|ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S
          (S_le_Ndim0 B S |>.trans (Ndim0_le_Ndim B S)))
        (consecutiveInitial_card _) -
      ell0AQ B S Q f hS0| : ℤ) ≤ (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
  have hcast := consecutiveInitial_castLE_eq (B := B) (S := S) hS0
  have hbridge := ellAQN_castLE_sub_eq (B := B) (S := S) (Q := Q) f hS0
  have hellAQ_eq :
      ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S
          (S_le_Ndim0 B S |>.trans (Ndim0_le_Ndim B S))) (consecutiveInitial_card _) =
        ellAQN B S Q f (Ndim B S)
          ((consecutiveInitial (N := Ndim0 B S) S hS0).map
            ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
          (by rw [Finset.card_map]; exact consecutiveInitial_card hS0) := by
    unfold ellAQ ellAQN
    rw [hcast]
  rw [hellAQ_eq]
  have hell0 : ell0AQ B S Q f hS0 =
      ellAQN B S Q f (Ndim0 B S) (consecutiveInitial (N := Ndim0 B S) S hS0)
        (consecutiveInitial_card hS0) := rfl
  rw [hell0, hbridge]
  calc
    (|∑ i ∈ consecutiveInitial (N := Ndim0 B S) S hS0,
        ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ))| : ℤ)
        ≤ ∑ i ∈ consecutiveInitial (N := Ndim0 B S) S hS0,
            (|(FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)| : ℤ) :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ consecutiveInitial (N := Ndim0 B S) S hS0,
          (((3 / Q : ℕ) : ℤ) + 1) := by
        refine Finset.sum_le_sum fun i hi => ?_
        rw [abs_sub_comm]
        exact abs_FNQ_shift_le hQ ((mem_consecutiveInitial_iff hS0 i).mp hi) hS0
    _ = (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
        rw [Finset.sum_const, consecutiveInitial_card]
        push_cast
        ring

/-- One direction of (5.2): `m^A_{Q,B} ≤ m^{(0)}_{Q,B} + S * (3/Q + 1)`, via
`mAQ ≤ ellAQ(consecutive)` and the `ellAQ`/`ell0AQ` bridge. -/
theorem mAQ_le_m0AQ_add {B S Q : ℕ} (hQ : 0 < Q) (f : Fin S → Fin (S + 3))
    (hS0 : S ≤ Ndim0 B S) :
    (mAQ B S Q f : ℤ) ≤ m0AQ B S Q f hS0 + (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
  have hSN : S ≤ Ndim B S := S_le_Ndim0 B S |>.trans (Ndim0_le_Ndim B S)
  have h1 := mAQ_le_ellAQ_consecutive (B := B) (S := S) (Q := Q) f hSN
  have h2 := abs_ellAQ_consecutive_sub_ell0AQ_le (B := B) (S := S) (Q := Q) hQ f hS0
  have h2' := (abs_le.mp h2).2
  unfold m0AQ
  have h1' : (mAQ B S Q f : ℤ) ≤
      ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S hSN) (consecutiveInitial_card hSN) := by
    exact_mod_cast h1
  have hconsist :
      ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S
          (S_le_Ndim0 B S |>.trans (Ndim0_le_Ndim B S))) (consecutiveInitial_card _) =
        ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S hSN) (consecutiveInitial_card hSN) :=
    rfl
  rw [hconsist] at h2'
  linarith

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
