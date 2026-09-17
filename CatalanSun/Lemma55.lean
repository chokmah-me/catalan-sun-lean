/-
  CatalanSun/Lemma55.lean

  Sun arXiv:2609.04176v1 §5.1 "Corrected full-row stability", Lemma 5.5.

  Definitions for the `Ndim0 B S`-dimension analogue `m^{(0)}_{Q,B}` of `mAQ`
  (using cutoff `U_0 = 2B+S-1` in place of `U = N-1 = 2B+S+2`), and the
  statement of Lemma 5.5's two claims:

    (5.2)  |m^A_{Q,B} - m^{(0)}_{Q,B}| ≤ C * (1 + B/Q)   for an absolute C,
           for every odd prime power Q (and the same bound for the
           corresponding denominator layers a_{Q,B} / a^{(0)}_{Q,B});

    (5.3)  ∑_{p odd, ν≥1} |(a_{p^ν,B} - m^A_{p^ν,B}) - (a^{(0)}_{p^ν,B} - m^{(0)}_{p^ν,B})| log p
             = o(B^2).

  **Divergence from the paper (`m0AQ`):** `m^{(0)}_{Q,B}` is formalized here as
  a **minimum** of `ellAQN` over all card-`S` subsets of `Fin (Ndim0 B S)`,
  mirroring `mAQ`'s definition — not as the value at the single fixed
  consecutive row set `{0,...,S-1}`. An earlier scaffold used the fixed-set
  reading (`m0AQ := ell0AQ`); that makes (5.2) demonstrably false, since the
  fixed set is far from optimal once `Q` is large relative to `S` (the gap
  grows like `S`, not `1+B/Q` — worst measured ratio 140+, unbounded).
  `docs/catalan-constant-irrational.md`'s reading of the paper — "the
  **minimum** of a certain function over S-element index sets" — supports the
  minimized version, which is numerically solid (worst ratio ≈ 0.34, exactly 0
  for large `Q`). See `docs/WORKPLAN-CONTINUATION.md` for the full numeric
  history, including the earlier sessions' (correct) refutation of the
  fixed-set reading.

  **(5.2) is fully proved** (`lemma_5_5_row_stability_holds`, absolute
  constant `C = 210`, unconditional):
    - easy direction `mAQ_le_m0AQ_add_sharp`: `mAQ ≤ m0AQ + 9*(1+B/Q)`.
    - hard direction `m0AQ_le_mAQ_add`: `m0AQ ≤ mAQ + 105*(1+B/Q)`, by
      swapping the `≤ 3` indices of `mAQ`'s minimizer that lie in `topBlock`
      (the indices of `Fin (Ndim B S)` with no counterpart in
      `Fin (Ndim0 B S)`) for *arbitrary* free indices of the common range.
      No greedy choice or occupancy argument is needed: each swap's cost is
      bounded termwise (`nQr_le`/`FNQ_le`/`NKQ_le` for the additive part,
      `abs_collTerm_swap_le` for the collision part), which the numeric gate
      in `docs/WORKPLAN-CONTINUATION.md` confirms saturates.
    - `abs_a0QB_sub_aQB_le`: `|a0QB - aQB| ≤ 6*(1+B/Q)`, exact and
      self-contained (no minimization).

  **Sign trap:** the `FNQ` shift sum runs opposite ways in the two directions.
  The easy direction gets it free from `FNQ_shift_nonneg`; the hard direction
  needs the genuine counting bound `sum_FNQ_shift_le`.

  Not yet proved: (5.3) itself (`lemma_5_5_ledger_little_o`).

  **Divergence from the paper (layer count):** the paper claims
  `O(√B log B)` odd prime powers below `5B`; this undercounts, since it omits
  the primes themselves (`~5B/log 5B` of them — measured 348,918 layers at
  `B = 10^6`, not the ~15,000 the paper's count would suggest). The `o(B²)`
  conclusion of (5.3) still appears reachable via Chebyshev (`∑_{p<5B} log p
  ≈ 5B`), giving `O(B log B) = o(B²)` for an `O(1+B/Q)`-per-layer bound — but
  Lean should derive it that way rather than reproduce the paper's count.

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

/-- `m^{(0)}_{Q,B}` (paper §5.1): the minimum of `ellAQN` over **all** card-`S`
subsets of `Fin (Ndim0 B S)` — the `Ndim0`-dimension analogue of `mAQ`, not
the value at the fixed consecutive set alone. (An earlier scaffold defined
`m0AQ := ell0AQ`, i.e. the value at the fixed consecutive set with no
minimization; that reading makes (5.2) false — the fixed set is far from
optimal once `Q` is large relative to `S`, so `|mAQ - ell0AQ|` grows like `S`
rather than `1 + B/Q`. `docs/catalan-constant-irrational.md`'s reading of the
paper — "the **minimum** of a certain function over S-element index sets" —
and the numerics in `docs/WORKPLAN-CONTINUATION.md` both support the
minimized reading below. See `m0AQ_le_ell0AQ` for the link to `ell0AQ`.) -/
noncomputable def m0AQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) : ℤ :=
  let s :=
    ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).image fun I =>
      if hI : I.card = S then ellAQN B S Q f (Ndim0 B S) I hI else 0
  if h : s.Nonempty then s.min' h else 0

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

/-- The `FNQ` shift for `N = Ndim B S` vs `N' = Ndim0 B S = N - 3`, at any
index `i < Ndim0 B S`: bounded by `3/Q + 1` via `abs_div_shift_le`. (Holds for
every row in the common range, not just the consecutive block `i < S`.) -/
theorem abs_FNQ_shift_le {B S Q i : ℕ} (hQ : 0 < Q) (hiN0 : i < Ndim0 B S) :
    (|(FNQ (Ndim B S) Q i : ℤ) - (FNQ (Ndim0 B S) Q i : ℤ)| : ℤ) ≤
      ((3 / Q : ℕ) : ℤ) + 1 := by
  have key := abs_div_shift_le (Ndim0 B S - 1 - i) 3 Q hQ
  have heq1 : Ndim0 B S - 1 - i + 3 = Ndim B S - 1 - i := by
    unfold Ndim0 at hiN0
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

/-- `nQr` is invariant under the `castLE` embedding, for **any** row set `I`:
`castLE` preserves `.val` and hence `% Q`, so the residue-`r` count among `I`
equals the same count after re-embedding `I` into `Fin (Ndim B S)`. -/
theorem nQr_castLE {B S Q r : ℕ} (I : Finset (Fin (Ndim0 B S))) :
    nQr Q r (I.map ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩) =
      nQr Q r I := by
  unfold nQr
  rw [Finset.filter_map]
  simp only [Function.Embedding.coeFn_mk, Fin.val_castLE, Function.comp]
  rw [Finset.card_map]

/-- `nQr` is invariant under the `castLE` embedding of the consecutive set:
the residue-`r` count among `{0,…,S-1} ⊆ Fin (Ndim0 B S)` equals the same
count after re-embedding into `Fin (Ndim B S)`, since `castLE` preserves
`.val` and hence `% Q`. Specialization of `nQr_castLE`. -/
theorem nQr_consecutiveInitial_castLE {B S Q r : ℕ} (hS : S ≤ Ndim0 B S) :
    nQr Q r
        ((consecutiveInitial (N := Ndim0 B S) S hS).map
          ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩) =
      nQr Q r (consecutiveInitial (N := Ndim0 B S) S hS) :=
  nQr_castLE _

/-- The row-level layer sum (`NKQ`/`indicatorQle`/`FNQ` terms of `ellAQN`) is
invariant under `castLE` except for the `FNQ` piece, for **any** row set `I`,
since `NKQ`/`indicatorQle` depend only on `.val`. -/
theorem ellAQN_castLE_sub_eq_general {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim0 B S))) (hI : I.card = S) :
    ellAQN B S Q f (Ndim B S)
        (I.map ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
        (by rw [Finset.card_map]; exact hI) -
      ellAQN B S Q f (Ndim0 B S) I hI =
      ∑ i ∈ I, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
  unfold ellAQN
  set e : Fin (Ndim0 B S) ↪ Fin (Ndim B S) :=
    ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩
  have hnQr : ∀ r, nQr Q r (I.map e) = nQr Q r I := fun r => nQr_castLE I
  have hsum1 :
      ∑ i ∈ I.map e,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) =
        ∑ i ∈ I,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
    rw [Finset.sum_map]
    rfl
  simp only [hnQr, hsum1]
  have hfinal :
      ∑ i ∈ I,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) -
        ∑ i ∈ I,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) =
      ∑ i ∈ I, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith [hfinal]

/-- Specialization of `ellAQN_castLE_sub_eq_general` to the consecutive set. -/
theorem ellAQN_castLE_sub_eq {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (hS : S ≤ Ndim0 B S) :
    ellAQN B S Q f (Ndim B S)
        ((consecutiveInitial (N := Ndim0 B S) S hS).map
          ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
        (by rw [Finset.card_map]; exact consecutiveInitial_card hS) -
      ellAQN B S Q f (Ndim0 B S) (consecutiveInitial (N := Ndim0 B S) S hS)
        (consecutiveInitial_card hS) =
      ∑ i ∈ consecutiveInitial (N := Ndim0 B S) S hS,
        ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) :=
  ellAQN_castLE_sub_eq_general f _ (consecutiveInitial_card hS)

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
        refine Finset.sum_le_sum fun i _hi => ?_
        rw [abs_sub_comm]
        exact abs_FNQ_shift_le hQ i.isLt
    _ = (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
        rw [Finset.sum_const, consecutiveInitial_card]
        push_cast
        ring

/-! ## Sharpened `FNQ`-shift bound: the difference is `O(1+B/Q)`, not `O(S)`

`abs_FNQ_shift_le` above bounds each *individual* `FNQ` difference by
`3/Q + 1` (which is `0` or `1` for `Q > 3`, but the sum over a card-`S` set
is then bounded by `S`, not `1 + B/Q` — too weak for (5.2), which demands a
bound uniform in `S`/`B`). This section shows the difference is **nonzero on
at most 3 residue classes mod `Q`**, so the *sum* over any card-`S` subset is
bounded by `min(S, 3 * (Ndim0 B S / Q) + 3)`, which genuinely is `O(1+B/Q)`. -/

/-- The `FNQ` difference vanishes unless `(Ndim0 B S - 1 - i) % Q` lands in
the top three residues `{Q-1, Q-2, Q-3}` (i.e. adding `3` doesn't cross a
multiple of `Q`). -/
theorem FNQ_shift_eq_of_mod {B S Q i : ℕ} (hQ3 : 3 < Q) (hiN0 : i < Ndim0 B S)
    (hmod : (Ndim0 B S - 1 - i) % Q + 3 < Q) :
    FNQ (Ndim B S) Q i = FNQ (Ndim0 B S) Q i := by
  have heq1 : Ndim0 B S - 1 - i + 3 = Ndim B S - 1 - i := by
    unfold Ndim0 at hiN0
    unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
    omega
  have hFNQ : FNQ (Ndim B S) Q i = i / Q + (Ndim B S - 1 - i) / Q := rfl
  have hFNQ0 : FNQ (Ndim0 B S) Q i = i / Q + (Ndim0 B S - 1 - i) / Q := rfl
  rw [hFNQ, hFNQ0, ← heq1]
  congr 1
  set y := Ndim0 B S - 1 - i with hy
  have hdm : y = Q * (y / Q) + y % Q := (Nat.div_add_mod y Q).symm
  have hdiv : (y + 3) / Q = y / Q := by
    have hlt : y + 3 < (y / Q + 1) * Q := by nlinarith
    have h1 : (y + 3) / Q < y / Q + 1 := (Nat.div_lt_iff_lt_mul (by omega)).mpr hlt
    have h2 : y / Q ≤ (y + 3) / Q := Nat.div_le_div_right (by omega)
    omega
  omega

/-- The `FNQ` difference is nonnegative: `Ndim > Ndim0` makes the right
summand of `FNQ` only bigger, for **any** `Q > 0` (no lower bound on `Q`
needed — this direction is plain monotonicity of `/Q`). -/
theorem FNQ_shift_nonneg {B S Q i : ℕ} (_hQ : 0 < Q) (hiN0 : i < Ndim0 B S) :
    FNQ (Ndim0 B S) Q i ≤ FNQ (Ndim B S) Q i := by
  have heq1 : Ndim0 B S - 1 - i + 3 = Ndim B S - 1 - i := by
    unfold Ndim0 at hiN0
    unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
    omega
  have hFNQ : FNQ (Ndim B S) Q i = i / Q + (Ndim B S - 1 - i) / Q := rfl
  have hFNQ0 : FNQ (Ndim0 B S) Q i = i / Q + (Ndim0 B S - 1 - i) / Q := rfl
  rw [hFNQ, hFNQ0, ← heq1]
  have h1 : (Ndim0 B S - 1 - i) / Q ≤ (Ndim0 B S - 1 - i + 3) / Q :=
    Nat.div_le_div_right (by omega)
  omega

/-- The `FNQ` difference is at most `1`, **for `Q > 3`** (false for
`Q ∈ {1,2,3}`: e.g. at `Q = 1`, `FNQ(N,1,i) = N-1`, so the difference is
exactly `3`, matching `abs_FNQ_shift_le`'s looser `3/Q+1` bound instead). -/
theorem FNQ_shift_le_one {B S Q i : ℕ} (hQ3 : 3 < Q) (hiN0 : i < Ndim0 B S) :
    FNQ (Ndim0 B S) Q i ≤ FNQ (Ndim B S) Q i ∧
      FNQ (Ndim B S) Q i ≤ FNQ (Ndim0 B S) Q i + 1 := by
  have hQ : 0 < Q := by omega
  have heq1 : Ndim0 B S - 1 - i + 3 = Ndim B S - 1 - i := by
    unfold Ndim0 at hiN0
    unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
    omega
  have hFNQ : FNQ (Ndim B S) Q i = i / Q + (Ndim B S - 1 - i) / Q := rfl
  have hFNQ0 : FNQ (Ndim0 B S) Q i = i / Q + (Ndim0 B S - 1 - i) / Q := rfl
  rw [hFNQ, hFNQ0, ← heq1]
  set y := Ndim0 B S - 1 - i with hy
  constructor
  · have h1 : y / Q ≤ (y + 3) / Q := Nat.div_le_div_right (by omega)
    omega
  · have h2 : (y + 3) / Q ≤ y / Q + 3 / Q + 1 := div_add_le_div_add y 3 Q hQ
    have h3 : 3 / Q = 0 := Nat.div_eq_of_lt (by omega)
    omega

/-- The set of indices where the `FNQ` difference is nonzero injects (via
`i ↦ Ndim0 B S - 1 - i.val`) into the union of the three residue classes
`{Q-1, Q-2, Q-3}` mod `Q` inside `range (Ndim0 B S)`; each class has size
`≤ Ndim0 B S / Q + 1`, giving the crude bound `3 * (Ndim0 B S / Q) + 3`. -/
theorem card_filter_FNQ_shift_ne {B S Q : ℕ} (hQ3 : 3 < Q)
    (I : Finset (Fin (Ndim0 B S))) :
    (I.filter fun i => FNQ (Ndim B S) Q i.val ≠ FNQ (Ndim0 B S) Q i.val).card
      ≤ 3 * (Ndim0 B S / Q) + 3 := by
  classical
  set T := I.filter fun i => FNQ (Ndim B S) Q i.val ≠ FNQ (Ndim0 B S) Q i.val with hT
  have hsub : T.image (fun i => Ndim0 B S - 1 - i.val) ⊆
      (range (Ndim0 B S)).filter (fun y => y % Q = Q - 1) ∪
        ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 2) ∪
          (range (Ndim0 B S)).filter (fun y => y % Q = Q - 3)) := by
    intro y hy
    simp only [mem_image, hT, mem_filter] at hy
    obtain ⟨i, ⟨_hiI, hine⟩, rfl⟩ := hy
    have hcontra : ¬ ((Ndim0 B S - 1 - i.val) % Q + 3 < Q) :=
      fun h => hine (FNQ_shift_eq_of_mod hQ3 i.isLt h)
    have hcontra' : Q ≤ (Ndim0 B S - 1 - i.val) % Q + 3 := by omega
    have hlt : Ndim0 B S - 1 - i.val < Ndim0 B S := by omega
    have hrange : (Ndim0 B S - 1 - i.val) % Q < Q := Nat.mod_lt _ (by omega)
    simp only [mem_union, mem_filter, mem_range]
    omega
  have hcard_img : T.card ≤
      ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 1) ∪
        ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 2) ∪
          (range (Ndim0 B S)).filter (fun y => y % Q = Q - 3))).card := by
    calc T.card = (T.image (fun i => Ndim0 B S - 1 - i.val)).card := by
          rw [Finset.card_image_of_injOn]
          intro a _ b _ hab
          simp only at hab
          have ha : a.val < Ndim0 B S := a.isLt
          have hb : b.val < Ndim0 B S := b.isLt
          have : a.val = b.val := by omega
          exact Fin.ext this
      _ ≤ _ := Finset.card_le_card hsub
  refine hcard_img.trans ?_
  calc ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 1) ∪
        ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 2) ∪
          (range (Ndim0 B S)).filter (fun y => y % Q = Q - 3))).card
      ≤ ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 1)).card +
          (((range (Ndim0 B S)).filter (fun y => y % Q = Q - 2)).card +
            ((range (Ndim0 B S)).filter (fun y => y % Q = Q - 3)).card) :=
        (Finset.card_union_le _ _).trans (by gcongr; exact Finset.card_union_le _ _)
    _ ≤ 3 * (Ndim0 B S / Q) + 3 := by
        rw [card_range_filter_mod_eq (by omega) (by omega) (Ndim0 B S),
          card_range_filter_mod_eq (by omega) (by omega) (Ndim0 B S),
          card_range_filter_mod_eq (by omega) (by omega) (Ndim0 B S)]
        have e1 : Ndim0 B S + Q - 1 - (Q - 1) = Ndim0 B S := by omega
        have e2 : Ndim0 B S + Q - 1 - (Q - 2) ≤ Ndim0 B S + 1 := by omega
        have e3 : Ndim0 B S + Q - 1 - (Q - 3) ≤ Ndim0 B S + 2 := by omega
        have b1 : (Ndim0 B S + Q - 1 - (Q - 1)) / Q = Ndim0 B S / Q := by rw [e1]
        have b2 : (Ndim0 B S + Q - 1 - (Q - 2)) / Q ≤ (Ndim0 B S + 1) / Q :=
          Nat.div_le_div_right e2
        have b3 : (Ndim0 B S + Q - 1 - (Q - 3)) / Q ≤ (Ndim0 B S + 2) / Q :=
          Nat.div_le_div_right e3
        have hdm : Ndim0 B S = Q * (Ndim0 B S / Q) + Ndim0 B S % Q :=
          (Nat.div_add_mod (Ndim0 B S) Q).symm
        have hmodlt : Ndim0 B S % Q < Q := Nat.mod_lt _ (by omega)
        have c2 : (Ndim0 B S + 1) / Q ≤ Ndim0 B S / Q + 1 := by
          have hbound2 : Ndim0 B S + 1 < (Ndim0 B S / Q + 1 + 1) * Q := by nlinarith
          have := (Nat.div_lt_iff_lt_mul (by omega)).mpr hbound2
          omega
        have c3 : (Ndim0 B S + 2) / Q ≤ Ndim0 B S / Q + 1 := by
          have hbound3 : Ndim0 B S + 2 < (Ndim0 B S / Q + 1 + 1) * Q := by nlinarith
          have := (Nat.div_lt_iff_lt_mul (by omega)).mpr hbound3
          omega
        rw [b1]
        omega

/-- Extract `m0AQ`'s minimizing row set: `m0AQ` equals `ellAQN` at `Ndim0 B S`
for some particular card-`S` subset `I₀`. -/
theorem m0AQ_eq_ellAQN_min {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (hne : ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).Nonempty) :
    ∃ (I₀ : Finset (Fin (Ndim0 B S))) (hI₀ : I₀.card = S),
      m0AQ B S Q f = ellAQN B S Q f (Ndim0 B S) I₀ hI₀ := by
  classical
  unfold m0AQ
  set s :=
    ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).image fun I =>
      if hI : I.card = S then ellAQN B S Q f (Ndim0 B S) I hI else 0
  have hsne : s.Nonempty := hne.image _
  simp only [hsne, ↓reduceDIte]
  obtain ⟨I₀, hI₀mem, hI₀eq⟩ := mem_image.mp (Finset.min'_mem s hsne)
  refine ⟨I₀, ?_, ?_⟩
  · exact (mem_powersetCard.mp hI₀mem).2
  · rw [← hI₀eq]
    simp [(mem_powersetCard.mp hI₀mem).2]

/-- `m0AQ` is at most `ellAQN` at any card-`S` subset of `Fin (Ndim0 B S)`. -/
theorem m0AQ_le_ellAQN {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim0 B S))) (hI : I.card = S) :
    m0AQ B S Q f ≤ ellAQN B S Q f (Ndim0 B S) I hI := by
  classical
  unfold m0AQ
  set s :=
    ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).image fun J =>
      if hJ : J.card = S then ellAQN B S Q f (Ndim0 B S) J hJ else 0
  have hmem : ellAQN B S Q f (Ndim0 B S) I hI ∈ s := by
    refine mem_image.mpr ⟨I, ?_, ?_⟩
    · rw [mem_powersetCard]; exact ⟨subset_univ _, hI⟩
    · simp [hI]
  have hne : s.Nonempty := ⟨_, hmem⟩
  simp only [hne, ↓reduceDIte]
  exact min'_le _ _ hmem

/-- `m0AQ` is at most `ell0AQ` (the fixed consecutive set is one candidate
among the card-`S` subsets `m0AQ` minimizes over). -/
theorem m0AQ_le_ell0AQ {B S Q : ℕ} (f : Fin S → Fin (S + 3)) (hS : S ≤ Ndim0 B S) :
    m0AQ B S Q f ≤ ell0AQ B S Q f hS :=
  m0AQ_le_ellAQN f _ (consecutiveInitial_card hS)

/-- One direction of (5.2): `m^A_{Q,B} ≤ m^{(0)}_{Q,B} + S * (3/Q + 1)`. Takes
`m0AQ`'s minimizing set `I₀`, casts it into `Fin (Ndim B S)` as a candidate
for `mAQ`'s minimization, and bounds the resulting `FNQ` shift exactly as in
`abs_ellAQ_consecutive_sub_ell0AQ_le`, but for the arbitrary set `I₀` instead
of the fixed consecutive block (via the generalized `abs_FNQ_shift_le`). -/
theorem mAQ_le_m0AQ_add {B S Q : ℕ} (hQ : 0 < Q) (f : Fin S → Fin (S + 3))
    (hS0 : S ≤ Ndim0 B S) :
    (mAQ B S Q f : ℤ) ≤ m0AQ B S Q f + (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
  have hne : ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).Nonempty := by
    refine ⟨consecutiveInitial (N := Ndim0 B S) S hS0, ?_⟩
    rw [mem_powersetCard]
    exact ⟨subset_univ _, consecutiveInitial_card hS0⟩
  obtain ⟨I₀, hI₀, hI₀eq⟩ := m0AQ_eq_ellAQN_min (B := B) (S := S) (Q := Q) f hne
  set e : Fin (Ndim0 B S) ↪ Fin (Ndim B S) :=
    ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩
  have hI₀mapcard : (I₀.map e).card = S := by rw [Finset.card_map]; exact hI₀
  have h1 : (mAQ B S Q f : ℤ) ≤ ellAQN B S Q f (Ndim B S) (I₀.map e) hI₀mapcard :=
    mAQ_le_ellAQ f (I₀.map e) hI₀mapcard
  have hbridge := ellAQN_castLE_sub_eq_general (B := B) (S := S) (Q := Q) f I₀ hI₀
  have hbound :
      (|∑ i ∈ I₀, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ))| : ℤ) ≤
        (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
    calc
      (|∑ i ∈ I₀, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ))| : ℤ)
          ≤ ∑ i ∈ I₀, (|(FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)| : ℤ) :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i ∈ I₀, (((3 / Q : ℕ) : ℤ) + 1) := by
          refine Finset.sum_le_sum fun i _hi => ?_
          rw [abs_sub_comm]
          exact abs_FNQ_shift_le hQ i.isLt
      _ = (S : ℤ) * (((3 / Q : ℕ) : ℤ) + 1) := by
          rw [Finset.sum_const, hI₀]; push_cast; ring
  have h2 := (abs_le.mp hbound).2
  rw [hI₀eq]
  linarith [hbridge]


/-- The sharpened `FNQ`-shift sum bound: `O(1+B/Q)`, not `O(S)`. Splits `I`
into the (small) set where the difference is nonzero, bounded via
`card_filter_FNQ_shift_ne`, and its complement, which contributes `0`. -/
theorem sum_FNQ_shift_le {B S Q : ℕ} (hQ : 0 < Q) (hSB : S * 20 ≤ B)
    (I : Finset (Fin (Ndim0 B S))) (hI : I.card = S) :
    ∑ i ∈ I, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) ≤
      15 * (((B / Q : ℕ) : ℤ) + 1) := by
  classical
  rcases lt_or_ge 3 Q with hQ3 | hQ3
  · -- Q > 3: use the sharp counting bound.
    set T := I.filter fun i => FNQ (Ndim B S) Q i.val ≠ FNQ (Ndim0 B S) Q i.val with hTdef
    have hsplit :
        ∑ i ∈ I, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) =
          ∑ i ∈ T, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) +
            ∑ i ∈ I.filter fun i => ¬ (FNQ (Ndim B S) Q i.val ≠ FNQ (Ndim0 B S) Q i.val),
              ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) :=
      (Finset.sum_filter_add_sum_filter_not I _ _).symm
    have hzero :
        ∑ i ∈ I.filter fun i => ¬ (FNQ (Ndim B S) Q i.val ≠ FNQ (Ndim0 B S) Q i.val),
          ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      simp only [mem_filter, not_not] at hi
      rw [hi.2]; ring
    have htop : ∑ i ∈ T, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) ≤
        (T.card : ℤ) := by
      calc ∑ i ∈ T, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ))
          ≤ ∑ _i ∈ T, (1 : ℤ) := by
            refine Finset.sum_le_sum fun i _hi => ?_
            have h := FNQ_shift_le_one (B := B) (S := S) (Q := Q) hQ3 i.isLt
            have : (FNQ (Ndim B S) Q i.val : ℤ) ≤ (FNQ (Ndim0 B S) Q i.val : ℤ) + 1 := by
              exact_mod_cast h.2
            linarith
        _ = (T.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have hcardT : (T.card : ℤ) ≤ 3 * ((Ndim0 B S / Q : ℕ) : ℤ) + 3 := by
      have := card_filter_FNQ_shift_ne (B := B) (S := S) (Q := Q) hQ3 I
      exact_mod_cast this
    have hNdim0 : (Ndim0 B S : ℤ) ≤ 3 * (B : ℤ) := by
      have : Ndim0 B S ≤ 3 * B := by
        unfold Ndim0
        omega
      exact_mod_cast this
    have hdivbound : ((Ndim0 B S / Q : ℕ) : ℤ) ≤ 3 * ((B / Q : ℕ) : ℤ) + 4 := by
      have hle : Ndim0 B S / Q ≤ (3 * B) / Q := by
        apply Nat.div_le_div_right
        unfold Ndim0; omega
      have hmul : (3 * B) / Q ≤ 3 * (B / Q) + 4 := by
        rcases Nat.eq_zero_or_pos Q with hQ0 | hQpos
        · omega
        -- `B = Q*(B/Q) + B%Q` with `B%Q < Q` gives `3*B < Q*(3*(B/Q)+3) + Q`,
        -- i.e. `3*B < Q*(3*(B/Q)+4)`, hence `(3*B)/Q < 3*(B/Q)+4` via
        -- `Nat.div_lt_iff_lt_mul`.
        have hdm : B = Q * (B / Q) + B % Q := (Nat.div_add_mod B Q).symm
        have hmodlt : B % Q < Q := Nat.mod_lt _ hQpos
        have hbound : 3 * B < (3 * (B / Q) + 4) * Q := by nlinarith
        have := (Nat.div_lt_iff_lt_mul hQpos).mpr hbound
        omega
      calc (Ndim0 B S / Q : ℤ) ≤ ((3 * B) / Q : ℕ) := by exact_mod_cast hle
        _ ≤ 3 * (B / Q) + 4 := by exact_mod_cast hmul
    rw [hsplit, hzero, add_zero]
    calc ∑ i ∈ T, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ))
        ≤ (T.card : ℤ) := htop
      _ ≤ 3 * ((Ndim0 B S / Q : ℕ) : ℤ) + 3 := hcardT
      _ ≤ 3 * (3 * ((B / Q : ℕ) : ℤ) + 4) + 3 := by linarith
      _ ≤ 15 * (((B / Q : ℕ) : ℤ) + 1) := by linarith
  · -- Q ≤ 3: crude bound `≤ S ≤ B/20 ≤ B/Q` beats `15*(B/Q+1)`.
    have hSQ : (S : ℤ) ≤ ((B / Q : ℕ) : ℤ) := by
      have h1 : S ≤ B / Q := by
        have hBQ : B / 3 ≤ B / Q := Nat.div_le_div_left hQ3 hQ
        have hS3 : S ≤ B / 3 := by omega
        omega
      exact_mod_cast h1
    -- `FNQ_shift_le_one` needs `Q > 3` (false at `Q ≤ 3`); use the looser but
    -- unconditional `abs_FNQ_shift_le` (`≤ 3/Q+1 ≤ 4` here) instead.
    have htop : ∑ i ∈ I, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) ≤
        4 * (I.card : ℤ) := by
      calc ∑ i ∈ I, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ))
          ≤ ∑ _i ∈ I, (4 : ℤ) := by
            refine Finset.sum_le_sum fun i _hi => ?_
            have h := abs_FNQ_shift_le (B := B) (S := S) (Q := Q) hQ i.isLt
            have h4 : ((3 / Q : ℕ) : ℤ) + 1 ≤ 4 := by
              have : 3 / Q ≤ 3 := Nat.div_le_self 3 Q
              have : ((3 / Q : ℕ) : ℤ) ≤ 3 := by exact_mod_cast this
              linarith
            have := (abs_le.mp h).2
            linarith
        _ = 4 * (I.card : ℤ) := by rw [Finset.sum_const, nsmul_eq_mul]; ring
    rw [hI] at htop
    linarith

/-- One direction of (5.2), sharpened: `m^A_{Q,B} ≤ m^{(0)}_{Q,B} + 9*(1+B/Q)`
— an `O(1+B/Q)` constant, unlike `mAQ_le_m0AQ_add`'s `O(S)` constant, which is
too weak to establish `lemma_5_5_row_stability`. Same proof spine as
`mAQ_le_m0AQ_add`, but using `FNQ_shift_nonneg` (`FNQ(Ndim0) ≤ FNQ(Ndim)`
pointwise, for **any** `Q > 0`) to see the `FNQ`-difference sum in
`ellAQN_castLE_sub_eq_general` is `≤ 0`, hence trivially `≤ 9*(1+B/Q)`; the
crude per-index bound summed over `I₀` (`sum_FNQ_shift_le`, which needs the
`Q > 3` vs `Q ≤ 3` split) is not even needed for *this* direction, only for
the hard direction later. (`hSB` is unused by this particular proof — kept in
the signature to match the paper's stated hypotheses and for parity with
`mAQ_le_m0AQ_add`.) -/
theorem mAQ_le_m0AQ_add_sharp {B S Q : ℕ} (hQ : 0 < Q) (_hSB : S * 20 ≤ B)
    (f : Fin S → Fin (S + 3)) (hS0 : S ≤ Ndim0 B S) :
    (mAQ B S Q f : ℤ) ≤ m0AQ B S Q f + 9 * (((B / Q : ℕ) : ℤ) + 1) := by
  have hne : ((univ : Finset (Fin (Ndim0 B S))).powersetCard S).Nonempty := by
    refine ⟨consecutiveInitial (N := Ndim0 B S) S hS0, ?_⟩
    rw [mem_powersetCard]
    exact ⟨subset_univ _, consecutiveInitial_card hS0⟩
  obtain ⟨I₀, hI₀, hI₀eq⟩ := m0AQ_eq_ellAQN_min (B := B) (S := S) (Q := Q) f hne
  set e : Fin (Ndim0 B S) ↪ Fin (Ndim B S) :=
    ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩
  have hI₀mapcard : (I₀.map e).card = S := by rw [Finset.card_map]; exact hI₀
  have h1 : (mAQ B S Q f : ℤ) ≤ ellAQN B S Q f (Ndim B S) (I₀.map e) hI₀mapcard :=
    mAQ_le_ellAQ f (I₀.map e) hI₀mapcard
  have hbridge := ellAQN_castLE_sub_eq_general (B := B) (S := S) (Q := Q) f I₀ hI₀
  have hnonpos : ∑ i ∈ I₀, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) ≤ 0 := by
    have : ∑ i ∈ I₀, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) ≤
        ∑ _i ∈ I₀, (0 : ℤ) := by
      refine Finset.sum_le_sum fun i _hi => ?_
      have h := FNQ_shift_nonneg (B := B) (S := S) (Q := Q) hQ i.isLt
      have : (FNQ (Ndim0 B S) Q i.val : ℤ) ≤ (FNQ (Ndim B S) Q i.val : ℤ) := by
        exact_mod_cast h
      linarith
    simpa using this
  have hnonneg : (0 : ℤ) ≤ 9 * (((B / Q : ℕ) : ℤ) + 1) := by positivity
  rw [hI₀eq]
  linarith [hbridge, hnonpos, hnonneg]

/-! ## `a0QB` vs `aQB`: an exact, self-contained bound

`a0QB`/`aQB` differ only in how many rows `NKQ B Q i.val` is summed over
(`Ndim0 B S = 2B+S` vs `Ndim B S = 2B+S+3`, i.e. exactly three extra terms);
the `phiQ Q (Dref B)` term is identical in both and cancels. Each `NKQ` term
is itself bounded by an elementary arithmetic-progression count, giving a
clean, unconditional `O(1+B/Q)` bound with no minimization involved. -/

/-- `NKQ K Q i ≤ K/Q + 1`: the solutions `h ∈ [1,K]` to `Q ∣ 2i+2h+1` form (at
most) an arithmetic progression with common difference `Q` — any two
solutions `a,b` satisfy `Q ∣ 2(a-b)`, hence `Q ∣ (a-b)` since `Q` is odd — so
there are at most `K/Q + 1` of them. -/
theorem NKQ_le {Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (K i : ℕ) :
    NKQ K Q i ≤ K / Q + 1 := by
  unfold NKQ
  set T := (Icc 1 K).filter (fun h => Q ∣ 2 * i + 2 * h + 1) with hTdef
  rcases T.eq_empty_or_nonempty with hemp | hne
  · simp [hemp]
  obtain ⟨h0, h0mem, h0min⟩ := T.exists_min_image id hne
  have hcop : Nat.gcd Q 2 = 1 := Nat.coprime_two_right.mpr hodd
  -- Any solution `h` satisfies `2*h ≡ 2*h0 [MOD Q]` (both `2i+2h+1` and
  -- `2i+2h0+1` are `≡ 0`), hence `h ≡ h0 [MOD Q]` after cancelling `2`.
  have hmod : ∀ h ∈ T, h ≡ h0 [MOD Q] := by
    intro h hmem
    have hh' := mem_filter.mp hmem
    have h0' := mem_filter.mp h0mem
    have hcong2 : 2 * h ≡ 2 * h0 [MOD Q] := by
      have e1 : (2 * i + 2 * h + 1) ≡ 0 [MOD Q] := (Nat.modEq_zero_iff_dvd).mpr hh'.2
      have e2 : (2 * i + 2 * h0 + 1) ≡ 0 [MOD Q] := (Nat.modEq_zero_iff_dvd).mpr h0'.2
      have e3 := e1.trans e2.symm
      have hcomm1 : 2 * i + 2 * h + 1 = 2 * h + (2 * i + 1) := by ring
      have hcomm2 : 2 * i + 2 * h0 + 1 = 2 * h0 + (2 * i + 1) := by ring
      rw [hcomm1, hcomm2] at e3
      exact (Nat.ModEq.add_right_cancel' (2 * i + 1) e3)
    exact hcong2.cancel_left_of_coprime hcop
  have hinj : Set.InjOn (fun h => (h - h0) / Q) T := by
    intro a ha b hb hab
    simp only at hab
    have hage : h0 ≤ a := h0min a ha
    have hbge : h0 ≤ b := h0min b hb
    have hda : Q ∣ (a - h0) := (Nat.modEq_iff_dvd' hage).mp (hmod a ha).symm
    have hdb : Q ∣ (b - h0) := (Nat.modEq_iff_dvd' hbge).mp (hmod b hb).symm
    obtain ⟨qa, hqa⟩ := hda
    obtain ⟨qb, hqb⟩ := hdb
    rw [hqa, hqb, Nat.mul_div_cancel_left _ hQ, Nat.mul_div_cancel_left _ hQ] at hab
    subst hab
    omega
  have hmaps : ∀ h ∈ T, (h - h0) / Q ∈ range (K / Q + 1) := by
    intro h hmem
    have hK : h ≤ K := (mem_Icc.mp (mem_filter.mp hmem).1).2
    have hh0K : h0 ≤ K := (mem_Icc.mp (mem_filter.mp h0mem).1).2
    have hle : h - h0 ≤ K := by omega
    have hdiv : (h - h0) / Q ≤ K / Q := Nat.div_le_div_right hle
    rw [mem_range]
    omega
  calc T.card ≤ (range (K / Q + 1)).card :=
        Finset.card_le_card_of_injOn _ hmaps hinj
    _ = K / Q + 1 := card_range _

/-- `a0QB` restricted to `Fin (Ndim0 B S)` plus the three extra top rows
recovers `aQB` on `Fin (Ndim B S)`: `Ndim B S = Ndim0 B S + 3`, and both share
the same `phiQ Q (Dref B)` correction term. -/
theorem aQB_sub_a0QB_eq {B S Q : ℕ} :
    aQB B S Q - a0QB B S Q =
      2 * ((NKQ B Q (Ndim0 B S) : ℤ) + (NKQ B Q (Ndim0 B S + 1) : ℤ) +
        (NKQ B Q (Ndim0 B S + 2) : ℤ)) := by
  unfold aQB a0QB
  have hNdim : Ndim B S = Ndim0 B S + 3 := by
    unfold Ndim0 CatalanSun.NewtonCompletion.Ndim
    ring
  have hsplit :
      ∑ i : Fin (Ndim B S), (NKQ B Q i.val : ℤ) =
        ∑ i : Fin (Ndim0 B S), (NKQ B Q i.val : ℤ) +
          ((NKQ B Q (Ndim0 B S) : ℤ) + (NKQ B Q (Ndim0 B S + 1) : ℤ) +
            (NKQ B Q (Ndim0 B S + 2) : ℤ)) := by
    rw [hNdim]
    rw [show Ndim0 B S + 3 = Ndim0 B S + 1 + 1 + 1 from by ring]
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    ring
  rw [hsplit]
  ring

/-- `|a0QB - aQB| ≤ 6 * (1 + B/Q)`, an exact, self-contained, unconditional
bound (no minimization): exactly three extra `NKQ B Q` terms separate the two
models, each bounded via `NKQ_le`. -/
theorem abs_a0QB_sub_aQB_le {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) :
    (|a0QB B S Q - aQB B S Q| : ℤ) ≤ 6 * ((B / Q : ℕ) : ℤ) + 6 := by
  have hkey := aQB_sub_a0QB_eq (B := B) (S := S) (Q := Q)
  have hb1 : NKQ B Q (Ndim0 B S) ≤ B / Q + 1 := NKQ_le hQ hodd B (Ndim0 B S)
  have hb2 : NKQ B Q (Ndim0 B S + 1) ≤ B / Q + 1 := NKQ_le hQ hodd B (Ndim0 B S + 1)
  have hb3 : NKQ B Q (Ndim0 B S + 2) ≤ B / Q + 1 := NKQ_le hQ hodd B (Ndim0 B S + 2)
  have hb1' : (NKQ B Q (Ndim0 B S) : ℤ) ≤ ((B / Q : ℕ) : ℤ) + 1 := by exact_mod_cast hb1
  have hb2' : (NKQ B Q (Ndim0 B S + 1) : ℤ) ≤ ((B / Q : ℕ) : ℤ) + 1 := by exact_mod_cast hb2
  have hb3' : (NKQ B Q (Ndim0 B S + 2) : ℤ) ≤ ((B / Q : ℕ) : ℤ) + 1 := by exact_mod_cast hb3
  have hnn1 : (0 : ℤ) ≤ (NKQ B Q (Ndim0 B S) : ℤ) := Int.natCast_nonneg _
  have hnn2 : (0 : ℤ) ≤ (NKQ B Q (Ndim0 B S + 1) : ℤ) := Int.natCast_nonneg _
  have hnn3 : (0 : ℤ) ≤ (NKQ B Q (Ndim0 B S + 2) : ℤ) := Int.natCast_nonneg _
  rw [abs_le]
  constructor <;> [skip; nlinarith [hkey]]
  nlinarith [hkey]

/-! ## Stage A–C toward (5.2)'s hard direction: termwise bounds and the
single-swap collision cost

The hard direction replaces the `≤ 3` row indices of `mAQ`'s minimizer that lie
in the top block `{Ndim0, Ndim0+1, Ndim0+2}` (which has no counterpart in
`Fin (Ndim0 B S)`) by arbitrary free indices in the common range. The numeric
gate (see `docs/WORKPLAN-CONTINUATION.md`) shows the cost of the *adversarially
worst* such replacement still saturates at `≈ 10 * (1 + B/Q)`, so no greedy
choice, occupancy pigeonhole, or minimizer characterization is needed — every
per-swap cost is bounded termwise.

Note `collTerm` is `ellAQN`'s collision term in its literal shape (a `range Q`
sum in `ℤ`), deliberately *not* `Thm51.collisionSum` (a `Fin Q` sum in `ℕ`).
`Thm51.collisionSum_move` is unusable here: its hypothesis `c b + 2 ≤ c a` only
covers balance-*improving* moves, whereas an arbitrary swap can go either way. -/

/-- `indicatorQle Q i ≤ 1`. -/
theorem indicatorQle_le_one (Q i : ℕ) : indicatorQle Q i ≤ 1 := by
  unfold indicatorQle; split_ifs <;> omega

/-- `nQr Q r I ≤ (N-1)/Q + 1`: each residue class mod `Q` meets `range N` in
at most `(N-1)/Q + 1` points. -/
theorem nQr_le {N Q : ℕ} (hQ : 0 < Q) (r : ℕ) (I : Finset (Fin N)) :
    nQr Q r I ≤ (N - 1) / Q + 1 := by
  classical
  unfold nQr
  -- map into `range N` filtered by the same residue condition
  have hsub : (I.filter (fun i => i.val % Q = r % Q)).image (fun i : Fin N => i.val)
      ⊆ (range N).filter (fun y => y % Q = r % Q) := by
    intro y hy
    simp only [mem_image, mem_filter] at hy
    obtain ⟨i, ⟨_hiI, hmod⟩, rfl⟩ := hy
    simp only [mem_filter, mem_range]
    exact ⟨i.isLt, hmod⟩
  have hcard : (I.filter (fun i => i.val % Q = r % Q)).card
      ≤ ((range N).filter (fun y => y % Q = r % Q)).card := by
    calc (I.filter (fun i => i.val % Q = r % Q)).card
        = ((I.filter (fun i => i.val % Q = r % Q)).image (fun i : Fin N => i.val)).card := by
          rw [Finset.card_image_of_injOn]
          intro a _ b _ hab
          exact Fin.ext hab
      _ ≤ _ := Finset.card_le_card hsub
  refine hcard.trans ?_
  rw [card_range_filter_mod_eq hQ (Nat.mod_lt _ hQ) N]
  -- `(N + Q - 1 - r%Q)/Q ≤ (N-1)/Q + 1`
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst hN
    have hlt : 0 + Q - 1 - r % Q < Q := by omega
    have h1 := Nat.div_eq_of_lt hlt
    have h2 : (0 - 1) / Q = 0 := by norm_num
    omega
  have hle : N + Q - 1 - r % Q ≤ (N - 1) + Q := by omega
  calc (N + Q - 1 - r % Q) / Q ≤ ((N - 1) + Q) / Q := Nat.div_le_div_right hle
    _ = (N - 1) / Q + 1 := by rw [Nat.add_div_right _ hQ]

/-- `FNQ N Q i = i/Q + (N-1-i)/Q ≤ (N-1)/Q + 1` for `i < N`. -/
theorem FNQ_le {N Q i : ℕ} (hQ : 0 < Q) (hi : i < N) :
    FNQ N Q i ≤ (N - 1) / Q + 1 := by
  unfold FNQ
  -- `⌊a/Q⌋ + ⌊b/Q⌋ ≤ ⌊(a+b)/Q⌋` with `a + b = N - 1`.
  have hsum : i + (N - 1 - i) = N - 1 := by omega
  have key : i / Q + (N - 1 - i) / Q ≤ (i + (N - 1 - i)) / Q + 1 := by
    have h1 := Nat.div_add_mod i Q
    have h2 := Nat.div_add_mod (N - 1 - i) Q
    have h3 := Nat.div_add_mod (i + (N - 1 - i)) Q
    have m1 : i % Q < Q := Nat.mod_lt _ hQ
    have m2 : (N - 1 - i) % Q < Q := Nat.mod_lt _ hQ
    have m3 : (i + (N - 1 - i)) % Q < Q := Nat.mod_lt _ hQ
    -- Q*(a/Q) + Q*(b/Q) ≤ Q*((a+b)/Q) + Q
    have hmul : Q * (i / Q) + Q * ((N - 1 - i) / Q)
        ≤ Q * ((i + (N - 1 - i)) / Q) + Q := by omega
    have := Nat.le_of_mul_le_mul_left
      (by linarith [hmul] : Q * (i / Q + (N - 1 - i) / Q) ≤ Q * ((i + (N - 1 - i)) / Q + 1)) hQ
    exact this
  rw [hsum] at key
  exact key

/-! ## Stage B -/

/-- `(3*B)/Q ≤ 3*(B/Q) + 4`. -/
theorem three_mul_div_le {B Q : ℕ} (hQ : 0 < Q) : (3 * B) / Q ≤ 3 * (B / Q) + 4 := by
  have hdm := Nat.div_add_mod B Q
  have hmod : B % Q < Q := Nat.mod_lt _ hQ
  have hbound : 3 * B < (3 * (B / Q) + 4) * Q := by nlinarith
  have := (Nat.div_lt_iff_lt_mul hQ).mpr hbound
  omega

/-- The per-index additive term of `ellAQN`, named for reuse. -/
def gTerm (B S Q N i : ℕ) : ℤ :=
  (2 * NKQ B Q i : ℤ) - (NKQ S Q i : ℤ) - (2 * indicatorQle Q i : ℤ) - (FNQ N Q i : ℤ)

/-- Every `g`-term is `O(1+B/Q)` in absolute value, given `N ≤ 3*B` and `S ≤ B`. -/
theorem abs_gTerm_le {B S Q N i : ℕ} (hQ : 0 < Q) (hodd : Odd Q)
    (hN : N ≤ 3 * B) (hSB : S ≤ B) (hi : i < N) :
    |gTerm B S Q N i| ≤ 7 * ((B / Q : ℕ) : ℤ) + 9 := by
  have hb := NKQ_le hQ hodd B i
  have hs := NKQ_le hQ hodd S i
  have hind := indicatorQle_le_one Q i
  have hf := FNQ_le (N := N) (Q := Q) (i := i) hQ hi
  -- `(N-1)/Q ≤ (3B)/Q ≤ 3*(B/Q)+4`
  have hN1 : (N - 1) / Q ≤ (3 * B) / Q := Nat.div_le_div_right (by omega)
  have h3 := three_mul_div_le (B := B) (Q := Q) hQ
  have hSQ : S / Q ≤ B / Q := Nat.div_le_div_right hSB
  have hfN : FNQ N Q i ≤ 3 * (B / Q) + 5 := by omega
  unfold gTerm
  have cb : (NKQ B Q i : ℤ) ≤ ((B / Q : ℕ) : ℤ) + 1 := by exact_mod_cast hb
  have cs : (NKQ S Q i : ℤ) ≤ ((B / Q : ℕ) : ℤ) + 1 := by
    exact_mod_cast le_trans hs (by omega : S / Q + 1 ≤ B / Q + 1)
  have ci : (indicatorQle Q i : ℤ) ≤ 1 := by exact_mod_cast hind
  have cf : (FNQ N Q i : ℤ) ≤ 3 * ((B / Q : ℕ) : ℤ) + 5 := by exact_mod_cast hfN
  have c0b : (0 : ℤ) ≤ (NKQ B Q i : ℤ) := by positivity
  have c0s : (0 : ℤ) ≤ (NKQ S Q i : ℤ) := by positivity
  have c0i : (0 : ℤ) ≤ (indicatorQle Q i : ℤ) := by positivity
  have c0f : (0 : ℤ) ≤ (FNQ N Q i : ℤ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-! ## Stage C: the collision term and its single-swap cost -/

private theorem choose_two_succ' (n : ℕ) : (n + 1).choose 2 = n.choose 2 + n := by
  simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ n 1

/-- `ellAQN`'s collision term, isolated (a `range Q` sum in `ℤ`). -/
def collTerm {N : ℕ} (Q : ℕ) (I : Finset (Fin N)) : ℤ :=
  2 * ∑ r ∈ range Q, (((nQr Q r I).choose 2 : ℕ) : ℤ)

/-- Inserting `b ∉ I` raises each `nQr` at `b`'s residue by one, others unchanged. -/
theorem nQr_insert {N Q : ℕ} (I : Finset (Fin N)) {b : Fin N} (hb : b ∉ I) (r : ℕ) :
    nQr Q r (insert b I) = nQr Q r I + (if b.val % Q = r % Q then 1 else 0) := by
  classical
  unfold nQr
  rw [Finset.filter_insert]
  by_cases h : b.val % Q = r % Q
  · rw [if_pos h, if_pos h, Finset.card_insert_of_notMem (by
      simp only [Finset.mem_filter]; tauto)]
  · rw [if_neg h, if_neg h, Nat.add_zero]

/-- Inserting one index raises the collision term by exactly `2 * nQr Q b.val I`. -/
theorem collTerm_insert {N Q : ℕ} (hQ : 0 < Q) (I : Finset (Fin N)) {b : Fin N}
    (hb : b ∉ I) :
    collTerm Q (insert b I) = collTerm Q I + 2 * (nQr Q b.val I : ℤ) := by
  classical
  unfold collTerm
  have hmem : b.val % Q ∈ range Q := mem_range.mpr (Nat.mod_lt _ hQ)
  have hsplit : ∀ (g : ℕ → ℤ), ∑ r ∈ range Q, g r
      = g (b.val % Q) + ∑ r ∈ (range Q).erase (b.val % Q), g r :=
    fun g => (Finset.add_sum_erase _ g hmem).symm
  rw [hsplit (fun r => (((nQr Q r (insert b I)).choose 2 : ℕ) : ℤ)),
      hsplit (fun r => (((nQr Q r I).choose 2 : ℕ) : ℤ))]
  have hrest : ∑ r ∈ (range Q).erase (b.val % Q),
        (((nQr Q r (insert b I)).choose 2 : ℕ) : ℤ)
      = ∑ r ∈ (range Q).erase (b.val % Q), (((nQr Q r I).choose 2 : ℕ) : ℤ) := by
    refine Finset.sum_congr rfl fun r hr => ?_
    have hrQ : r < Q := mem_range.mp (Finset.mem_of_mem_erase hr)
    have hne : b.val % Q ≠ r := Ne.symm (Finset.mem_erase.mp hr).1
    have : ¬ (b.val % Q = r % Q) := by rwa [Nat.mod_eq_of_lt hrQ]
    rw [nQr_insert I hb r, if_neg this, Nat.add_zero]
  rw [hrest]
  have hat : nQr Q (b.val % Q) (insert b I) = nQr Q (b.val % Q) I + 1 := by
    rw [nQr_insert I hb, if_pos (by rw [Nat.mod_mod])]
  rw [hat, choose_two_succ']
  have hnq : nQr Q (b.val % Q) I = nQr Q b.val I := by
    unfold nQr; congr 1; ext x; simp
  rw [hnq]
  push_cast
  ring

/-- Removing one index drops the collision term by exactly `2*(nQr - 1)`. -/
theorem collTerm_erase {N Q : ℕ} (hQ : 0 < Q) (I : Finset (Fin N)) {a : Fin N}
    (ha : a ∈ I) :
    collTerm Q I = collTerm Q (I.erase a) + 2 * ((nQr Q a.val I : ℤ) - 1) := by
  classical
  have hnotmem : a ∉ I.erase a := Finset.notMem_erase a I
  have hins : insert a (I.erase a) = I := Finset.insert_erase ha
  have h := collTerm_insert (Q := Q) hQ (I.erase a) hnotmem
  rw [hins] at h
  have hcount : nQr Q a.val I = nQr Q a.val (I.erase a) + 1 := by
    conv_lhs => rw [← hins]
    rw [nQr_insert (I.erase a) hnotmem, if_pos rfl]
  rw [h, hcount]
  push_cast
  ring

/-- The two-sided single-swap bound on the collision term. -/
theorem abs_collTerm_swap_le {N Q : ℕ} (hQ : 0 < Q) (I : Finset (Fin N))
    {a b : Fin N} (ha : a ∈ I) (hb : b ∉ I) :
    |collTerm Q (insert b (I.erase a)) - collTerm Q I|
      ≤ 2 * (((N - 1) / Q : ℕ) : ℤ) + 2 := by
  classical
  have hbe : b ∉ I.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  have h1 := collTerm_insert (Q := Q) hQ (I.erase a) hbe
  have h2 := collTerm_erase (Q := Q) hQ I ha
  -- bounds on the two `nQr` values
  have hlo1 : (0 : ℤ) ≤ (nQr Q b.val (I.erase a) : ℤ) := by positivity
  have hhi1 : (nQr Q b.val (I.erase a) : ℤ) ≤ ((N - 1) / Q : ℕ) + 1 := by
    exact_mod_cast nQr_le hQ b.val (I.erase a)
  have hlo2 : (1 : ℤ) ≤ (nQr Q a.val I : ℤ) := by
    have : 1 ≤ nQr Q a.val I := by
      unfold nQr
      refine Finset.card_pos.mpr ⟨a, ?_⟩
      simp only [Finset.mem_filter]
      exact ⟨ha, by simp⟩
    exact_mod_cast this
  have hhi2 : (nQr Q a.val I : ℤ) ≤ ((N - 1) / Q : ℕ) + 1 := by
    exact_mod_cast nQr_le hQ a.val I
  rw [abs_le]
  constructor <;> [linarith; linarith]

/-! ## Stage D: the full single-swap `ellAQN` cost

`CAQ` depends only on `B,S,Q,f`, so it cancels across a swap; the collision
half is Stage C and the additive half is two applications of `abs_gTerm_le`.
The constants are deliberately slack — only the *existence* of an absolute `C`
matters for (5.2). -/

theorem card_insert_erase_eq {N : ℕ} {I : Finset (Fin N)} {a b : Fin N}
    (ha : a ∈ I) (hb : b ∉ I) : (insert b (I.erase a)).card = I.card := by
  classical
  have hbe : b ∉ I.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [Finset.card_insert_of_notMem hbe, Finset.card_erase_of_mem ha]
  have : 1 ≤ I.card := Finset.card_pos.mpr ⟨a, ha⟩
  omega

/-- `ellAQN` rewritten as `CAQ + collTerm + ∑ gTerm`. -/
theorem ellAQN_eq_collTerm_add {B S Q N : ℕ} (f : Fin S → Fin (S + 3))
    (I : Finset (Fin N)) (hI : I.card = S) :
    ellAQN B S Q f N I hI
      = (CAQ B S Q f : ℤ) + collTerm Q I + ∑ i ∈ I, gTerm B S Q N i.val := by
  unfold ellAQN collTerm gTerm
  ring

/-- A single row swap changes `ellAQN` by `O(1+B/Q)`. -/
theorem abs_ellAQN_swap_le {B S Q N : ℕ} (hQ : 0 < Q) (hodd : Odd Q)
    (hN : N ≤ 3 * B) (hSB : S ≤ B) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin N)) (hI : I.card = S) {a b : Fin N}
    (ha : a ∈ I) (hb : b ∉ I) (hcard : (insert b (I.erase a)).card = S) :
    |ellAQN B S Q f N (insert b (I.erase a)) hcard - ellAQN B S Q f N I hI|
      ≤ 30 * ((B / Q : ℕ) : ℤ) + 30 := by
  classical
  have hbe : b ∉ I.erase a := fun h => hb (Finset.mem_of_mem_erase h)
  rw [ellAQN_eq_collTerm_add f _ hcard, ellAQN_eq_collTerm_add f I hI]
  -- the `g`-sum over the swapped set
  have hgsum : ∑ i ∈ insert b (I.erase a), gTerm B S Q N i.val
      = ∑ i ∈ I, gTerm B S Q N i.val + gTerm B S Q N b.val - gTerm B S Q N a.val := by
    rw [Finset.sum_insert hbe]
    have : ∑ i ∈ I.erase a, gTerm B S Q N i.val
        = ∑ i ∈ I, gTerm B S Q N i.val - gTerm B S Q N a.val := by
      have := Finset.sum_erase_add I (fun i : Fin N => gTerm B S Q N i.val) ha
      linarith [this]
    rw [this]; ring
  rw [hgsum]
  have hcoll := abs_collTerm_swap_le (Q := Q) hQ I ha hb
  have hga := abs_gTerm_le (B := B) (S := S) (Q := Q) (N := N) (i := a.val) hQ hodd hN hSB a.isLt
  have hgb := abs_gTerm_le (B := B) (S := S) (Q := Q) (N := N) (i := b.val) hQ hodd hN hSB b.isLt
  -- `(N-1)/Q ≤ 3*(B/Q) + 4`
  have hN1 : (N - 1) / Q ≤ (3 * B) / Q := Nat.div_le_div_right (by omega)
  have h3 := three_mul_div_le (B := B) (Q := Q) hQ
  have hNcast : (((N - 1) / Q : ℕ) : ℤ) ≤ 3 * ((B / Q : ℕ) : ℤ) + 4 := by
    exact_mod_cast le_trans hN1 h3
  rw [abs_le] at hcoll hga hgb ⊢
  constructor <;> linarith [hcoll.1, hcoll.2, hga.1, hga.2, hgb.1, hgb.2]

/-! ## Stage E: the `≤ 3`-step descent into the common range

`mAQ`'s minimizer may use up to three indices of `topBlock B S` — the indices
`{Ndim0, Ndim0+1, Ndim0+2}` of `Fin (Ndim B S)` with no counterpart in
`Fin (Ndim0 B S)`. Each is swapped for an *arbitrary* free index of the common
range; `abs_ellAQN_swap_le` pays `30*(B/Q)+30` per swap, and the top-block
intersection strictly shrinks, so at most `card_topBlock = 3` swaps run. -/

/-- Extract `mAQ`'s minimizing row set (mirror of `m0AQ_eq_ellAQN_min`). -/
theorem mAQ_eq_ellAQ_min {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (hne : ((univ : Finset (Fin (Ndim B S))).powersetCard S).Nonempty) :
    ∃ (I : Finset (Fin (Ndim B S))) (hI : I.card = S),
      mAQ B S Q f = ellAQ B S Q f I hI := by
  classical
  unfold mAQ
  set s :=
    ((univ : Finset (Fin (Ndim B S))).powersetCard S).image fun I =>
      if hI : I.card = S then ellAQ B S Q f I hI else 0
  have hsne : s.Nonempty := hne.image _
  simp only [hsne, ↓reduceDIte]
  obtain ⟨I, hImem, hIeq⟩ := mem_image.mp (Finset.min'_mem s hsne)
  refine ⟨I, ?_, ?_⟩
  · exact (mem_powersetCard.mp hImem).2
  · rw [← hIeq]
    simp [(mem_powersetCard.mp hImem).2]

/-- The top block of `Fin (Ndim B S)`: the three indices with no counterpart in
`Fin (Ndim0 B S)`. -/
def topBlock (B S : ℕ) : Finset (Fin (Ndim B S)) :=
  univ.filter (fun i => Ndim0 B S ≤ i.val)

theorem mem_topBlock_iff {B S : ℕ} (i : Fin (Ndim B S)) :
    i ∈ topBlock B S ↔ Ndim0 B S ≤ i.val := by
  simp [topBlock]

theorem card_topBlock {B S : ℕ} : (topBlock B S).card = 3 := by
  classical
  have : topBlock B S = {⟨Ndim0 B S, by unfold Ndim Ndim0; omega⟩,
      ⟨Ndim0 B S + 1, by unfold Ndim Ndim0; omega⟩,
      ⟨Ndim0 B S + 2, by unfold Ndim Ndim0; omega⟩} := by
    ext i
    rw [mem_topBlock_iff]
    simp only [Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]
    have := i.isLt
    unfold Ndim at this
    unfold Ndim0
    omega
  rw [this]
  rw [Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_insert_of_notMem (by simp [Fin.ext_iff]),
      Finset.card_singleton]

/-- A free index in the common range exists whenever `I` still meets the top
block: `I` has card `S`, the common range has `Ndim0 B S = 2B+S` slots, and
`S * 20 ≤ B` leaves plenty spare. -/
theorem exists_free_common {B S : ℕ} (hS0 : 0 < S) (hSB : S * 20 ≤ B)
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    ∃ b : Fin (Ndim B S), b ∉ I ∧ b.val < Ndim0 B S := by
  classical
  set C : Finset (Fin (Ndim B S)) := univ.filter (fun i => i.val < Ndim0 B S) with hC
  have hCcard : C.card = Ndim0 B S := by
    rw [hC]
    have : (univ.filter (fun i : Fin (Ndim B S) => i.val < Ndim0 B S)).card
        = ((range (Ndim B S)).filter (fun y => y < Ndim0 B S)).card := by
      rw [← Finset.card_map ⟨Fin.val, Fin.val_injective⟩]
      congr 1
      ext y
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk, Finset.mem_range]
      constructor
      · rintro ⟨i, hi, rfl⟩; exact ⟨i.isLt, hi⟩
      · rintro ⟨hy1, hy2⟩; exact ⟨⟨y, hy1⟩, hy2, rfl⟩
    rw [this]
    have hsub : (range (Ndim B S)).filter (fun y => y < Ndim0 B S) = range (Ndim0 B S) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · tauto
      · intro hy; exact ⟨by unfold Ndim Ndim0 at *; omega, hy⟩
    rw [hsub, Finset.card_range]
  have hlt : I.card < C.card := by
    rw [hI, hCcard]; unfold Ndim0; omega
  obtain ⟨b, hbC, hbI⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨b, hbI, by rw [hC] at hbC; simpa using hbC⟩

/-- Swapping a top-block index for a free common-range index strictly shrinks
the top-block intersection. -/
theorem card_inter_topBlock_swap {B S : ℕ} (I : Finset (Fin (Ndim B S)))
    {a b : Fin (Ndim B S)} (ha : a ∈ I ∩ topBlock B S) (hb : b ∉ I)
    (hblt : b.val < Ndim0 B S) :
    ((insert b (I.erase a)) ∩ topBlock B S).card < (I ∩ topBlock B S).card := by
  classical
  have haI : a ∈ I := (Finset.mem_inter.mp ha).1
  have haT : a ∈ topBlock B S := (Finset.mem_inter.mp ha).2
  have hbT : b ∉ topBlock B S := by rw [mem_topBlock_iff]; omega
  have hsub : (insert b (I.erase a)) ∩ topBlock B S ⊆ (I ∩ topBlock B S).erase a := by
    intro x hx
    rw [Finset.mem_inter] at hx
    obtain ⟨hx1, hx2⟩ := hx
    rcases Finset.mem_insert.mp hx1 with rfl | hx1'
    · exact absurd hx2 hbT
    · rw [Finset.mem_erase] at hx1' ⊢
      exact ⟨hx1'.1, Finset.mem_inter.mpr ⟨hx1'.2, hx2⟩⟩
  calc ((insert b (I.erase a)) ∩ topBlock B S).card
      ≤ ((I ∩ topBlock B S).erase a).card := Finset.card_le_card hsub
    _ < (I ∩ topBlock B S).card := Finset.card_erase_lt_of_mem ha

/-- The `≤3`-step descent: any card-`S` row set can be moved into the common
range at a cost of `k * (30*(B/Q)+30)`, where `k` bounds its top-block usage. -/
theorem swap_descent_aux {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (hS0 : 0 < S)
    (hSB : S * 20 ≤ B) (f : Fin S → Fin (S + 3)) :
    ∀ (k : ℕ) (I : Finset (Fin (Ndim B S))) (hI : I.card = S),
      (I ∩ topBlock B S).card ≤ k →
      ∃ (I' : Finset (Fin (Ndim B S))) (hI' : I'.card = S),
        (I' ∩ topBlock B S) = ∅ ∧
        ellAQN B S Q f (Ndim B S) I' hI'
          ≤ ellAQN B S Q f (Ndim B S) I hI + (k : ℤ) * (30 * ((B / Q : ℕ) : ℤ) + 30) := by
  classical
  have hNle : Ndim B S ≤ 3 * B := by unfold Ndim; omega
  have hSle : S ≤ B := by omega
  intro k
  induction k with
  | zero =>
    intro I hI hk
    refine ⟨I, hI, ?_, by simp⟩
    exact Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
  | succ k ih =>
    intro I hI hk
    rcases Finset.eq_empty_or_nonempty (I ∩ topBlock B S) with hempty | ⟨a, ha⟩
    · refine ⟨I, hI, hempty, ?_⟩
      have hk0 : (0 : ℤ) ≤ ((k + 1 : ℕ) : ℤ) * (30 * ((B / Q : ℕ) : ℤ) + 30) := by positivity
      linarith
    · obtain ⟨b, hbI, hblt⟩ := exists_free_common hS0 hSB I hI
      have haI : a ∈ I := (Finset.mem_inter.mp ha).1
      have hcard : (insert b (I.erase a)).card = S := by
        rw [card_insert_erase_eq haI hbI, hI]
      have hshrink := card_inter_topBlock_swap I ha hbI hblt
      have hk' : ((insert b (I.erase a)) ∩ topBlock B S).card ≤ k := by omega
      obtain ⟨I', hI', hI'empty, hI'le⟩ := ih (insert b (I.erase a)) hcard hk'
      refine ⟨I', hI', hI'empty, ?_⟩
      have hswap := abs_ellAQN_swap_le (B := B) (S := S) (Q := Q) (N := Ndim B S)
        hQ hodd hNle hSle f I hI haI hbI hcard
      rw [abs_le] at hswap
      have hcast : ((k + 1 : ℕ) : ℤ) = (k : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      linarith [hswap.2, hI'le]

/-- A card-`S` set avoiding the top block is the `castLE`-image of a card-`S`
set in `Fin (Ndim0 B S)`. -/
theorem exists_preimage_of_disjoint_topBlock {B S : ℕ}
    (I : Finset (Fin (Ndim B S))) (hdisj : I ∩ topBlock B S = ∅) :
    ∃ J : Finset (Fin (Ndim0 B S)),
      J.map ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩ = I ∧ J.card = I.card := by
  classical
  have hlt : ∀ i ∈ I, i.val < Ndim0 B S := by
    intro i hi
    by_contra h
    have : i ∈ I ∩ topBlock B S :=
      Finset.mem_inter.mpr ⟨hi, (mem_topBlock_iff i).mpr (by omega)⟩
    rw [hdisj] at this
    exact absurd this (Finset.notMem_empty i)
  refine ⟨I.attach.image (fun i => ⟨i.val.val, hlt i.val i.property⟩), ?_, ?_⟩
  · ext x
    simp only [Finset.mem_map, Finset.mem_image, Finset.mem_attach, true_and,
      Function.Embedding.coeFn_mk, Subtype.exists]
    constructor
    · rintro ⟨y, ⟨i, hi, rfl⟩, rfl⟩
      simpa [Fin.ext_iff] using hi
    · intro hx
      exact ⟨⟨x.val, hlt x hx⟩, ⟨x, hx, rfl⟩, by simp⟩
  · rw [Finset.card_image_of_injOn, Finset.card_attach]
    intro p _ q _ hpq
    simp only [Fin.ext_iff] at hpq
    exact Subtype.ext (Fin.ext hpq)

/-! ## Lemma 5.5, target statements -/

/-- Paper (5.2): an absolute constant `C` bounding `|m^A - m^{(0)}|` by
`C * (1 + B/Q)`, uniformly over odd prime powers `Q`. Stated with the
`ℚ`-valued ratio `B / Q` to match the paper's real-number bound; `C` is
existentially quantified once, ahead of `B`/`S`/`Q`/`f`, matching "absolute
constant." -/
def lemma_5_5_row_stability : Prop :=
  ∃ C : ℚ, 0 < C ∧
    ∀ (B S Q : ℕ), OddPrimePower Q → 0 < S → S * 20 ≤ B →
      ∀ (f : Fin S → Fin (S + 3)),
        (|(mAQ B S Q f : ℚ) - (m0AQ B S Q f : ℚ)| : ℚ) ≤
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
`ε * B ^ 2` (i.e. `o(B²)` unwound to its `ε`-`B₀` definition). `f` is
universally quantified per `B` since the bound must hold along any
`Injective f` witness used in `thm_5_1_statement`. -/
def lemma_5_5_ledger_little_o : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ B₀ : ℕ, ∀ B : ℕ, B₀ ≤ B →
    ∀ (f : Fin (B / 20) → Fin (B / 20 + 3)),
      ∑ pv ∈ layerIndex B,
        (|(((a0QB B (B / 20) pv.1 - m0AQ B (B / 20) pv.1 f) -
              (aQB B (B / 20) pv.1 - mAQ B (B / 20) pv.1 f) : ℤ) : ℝ)| : ℝ) *
          Real.log pv.1 ≤ ε * (B : ℝ) ^ 2

/-! ## Stage F: assembly — (5.2) in full

The hard direction chains `mAQ`'s minimizer through the `≤ 3`-step descent
(Stage E) and the `castLE` transport, then pays the `FNQ` shift. Note the shift
sum runs the *opposite* way from the easy direction, where `FNQ_shift_nonneg`
made it automatically `≤ 0`; here it needs the genuine `O(1+B/Q)` counting
bound `sum_FNQ_shift_le`, which was landed earlier for exactly this purpose. -/

/-- The hard direction of (5.2): `m^{(0)}_{Q,B} ≤ m^A_{Q,B} + C*(1+B/Q)`. -/
theorem m0AQ_le_mAQ_add {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (hS0 : 0 < S)
    (hSB : S * 20 ≤ B) (f : Fin S → Fin (S + 3)) :
    m0AQ B S Q f ≤ mAQ B S Q f + 105 * (((B / Q : ℕ) : ℤ) + 1) := by
  classical
  -- `mAQ`'s minimizer exists
  have hSN : S ≤ Ndim B S := by unfold Ndim; omega
  have hne : ((univ : Finset (Fin (Ndim B S))).powersetCard S).Nonempty := by
    refine ⟨consecutiveInitial S hSN, ?_⟩
    rw [mem_powersetCard]
    exact ⟨subset_univ _, consecutiveInitial_card hSN⟩
  obtain ⟨I, hI, hIeq⟩ := mAQ_eq_ellAQ_min (Q := Q) f hne
  -- descend into the common range
  have hk : (I ∩ topBlock B S).card ≤ 3 := by
    calc (I ∩ topBlock B S).card ≤ (topBlock B S).card :=
          Finset.card_le_card Finset.inter_subset_right
      _ = 3 := card_topBlock
  obtain ⟨I', hI', hI'empty, hI'le⟩ :=
    swap_descent_aux (Q := Q) hQ hodd hS0 hSB f 3 I hI hk
  -- transport `I'` back to `Fin (Ndim0 B S)`
  obtain ⟨J, hJmap, hJcard⟩ := exists_preimage_of_disjoint_topBlock I' hI'empty
  have hJS : J.card = S := by rw [hJcard, hI']
  -- the `FNQ` bridge: the shift is ≤ 0 in this direction
  have hbridge := ellAQN_castLE_sub_eq_general (Q := Q) f J hJS
  -- The shift sum runs the *other* way here, so `FNQ_shift_nonneg` is not
  -- enough: we need the genuine `O(1+B/Q)` counting bound.
  have hshift := sum_FNQ_shift_le (Q := Q) hQ hSB J hJS
  have hnonpos : -(∑ i ∈ J, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)))
      ≤ 15 * (((B / Q : ℕ) : ℤ) + 1) := by
    have hneg : -(∑ i ∈ J, ((FNQ (Ndim0 B S) Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)))
        = ∑ i ∈ J, ((FNQ (Ndim B S) Q i.val : ℤ) - (FNQ (Ndim0 B S) Q i.val : ℤ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hneg]
    exact hshift
  -- `m0AQ ≤ ellAQN at J`
  have hm0 := m0AQ_le_ellAQN (Q := Q) f J hJS
  -- chain: ellAQN(Ndim0, J) ≤ ellAQN(Ndim, J.map e) = ellAQN(Ndim, I')
  have hmapeq : ellAQN B S Q f (Ndim B S)
      (J.map ⟨Fin.castLE (Ndim0_le_Ndim B S), Fin.castLE_injective _⟩)
      (by rw [Finset.card_map]; exact hJS) = ellAQN B S Q f (Ndim B S) I' hI' := by
    congr 1
  rw [hmapeq] at hbridge
  rw [hIeq, ellAQ_eq_ellAQN]
  have h3 : ((3 : ℕ) : ℤ) = 3 := by norm_num
  rw [h3] at hI'le
  have hexp : (3 : ℤ) * (30 * ((B / Q : ℕ) : ℤ) + 30) = 90 * (((B / Q : ℕ) : ℤ) + 1) := by ring
  rw [hexp] at hI'le
  set X := ellAQN B S Q f (Ndim0 B S) J hJS with hX
  set Y := ellAQN B S Q f (Ndim B S) I' hI' with hY
  set Z := ellAQN B S Q f (Ndim B S) I hI with hZ
  linarith [hbridge, hnonpos, hm0, hI'le]

/-- (5.2) with an explicit `ℕ`-division constant, both directions. -/
theorem abs_mAQ_sub_m0AQ_le {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (hS0 : 0 < S)
    (hSB : S * 20 ≤ B) (f : Fin S → Fin (S + 3)) :
    |(mAQ B S Q f : ℤ) - m0AQ B S Q f| ≤ 105 * (((B / Q : ℕ) : ℤ) + 1) := by
  have hS0' : S ≤ Ndim0 B S := S_le_Ndim0 B S
  have heasy := mAQ_le_m0AQ_add_sharp (Q := Q) hQ hSB f hS0'
  have hhard := m0AQ_le_mAQ_add (Q := Q) hQ hodd hS0 hSB f
  have hpos : (0 : ℤ) ≤ ((B / Q : ℕ) : ℤ) := by positivity
  rw [abs_le]
  constructor <;> linarith

/-- **Paper (5.2)**: `lemma_5_5_row_stability` holds, with `C = 210`. -/
theorem lemma_5_5_row_stability_holds : lemma_5_5_row_stability := by
  refine ⟨210, by norm_num, ?_⟩
  intro B S Q hQpp hS0 hSB f
  have hQ : 0 < Q := hQpp.pos
  have hodd : Odd Q := hQpp.odd
  have hint := abs_mAQ_sub_m0AQ_le (Q := Q) hQ hodd hS0 hSB f
  -- move to `ℚ`
  have hcast : |(mAQ B S Q f : ℚ) - (m0AQ B S Q f : ℚ)|
      = (((|(mAQ B S Q f : ℤ) - m0AQ B S Q f| : ℤ)) : ℚ) := by
    push_cast [abs_sub_comm]
    rw [abs_sub_comm]
  rw [hcast]
  have h1 : (((|(mAQ B S Q f : ℤ) - m0AQ B S Q f| : ℤ)) : ℚ)
      ≤ ((105 * (((B / Q : ℕ) : ℤ) + 1) : ℤ) : ℚ) := by exact_mod_cast hint
  refine h1.trans ?_
  -- `((B/Q : ℕ) : ℚ) ≤ (B:ℚ)/(Q:ℚ)`
  have hdiv : (((B / Q : ℕ) : ℚ)) ≤ (B : ℚ) / (Q : ℚ) := Nat.cast_div_le
  have hQpos : (0 : ℚ) < (Q : ℚ) := by exact_mod_cast hQ
  have hrw : ((105 * (((B / Q : ℕ) : ℤ) + 1) : ℤ) : ℚ)
      = 105 * ((((B / Q : ℕ)) : ℚ) + 1) := by
    rw [Int.cast_mul, Int.cast_add, Int.cast_one, Int.cast_natCast]
    norm_num
  rw [hrw]
  linarith [hdiv]

end CatalanSun.Lemma55
