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

  Landed this session (unconditional, `m0AQ` under the corrected definition):
    - `abs_a0QB_sub_aQB_le`: `|a0QB - aQB| ≤ 6*(1+B/Q)`, exact and
      self-contained (no minimization) — the two models differ by exactly
      three rows, each `NKQ` term bounded via `NKQ_le`.
    - `mAQ_le_m0AQ_add`: the easy direction of (5.2),
      `mAQ ≤ m0AQ + S*(3/Q+1)`.

  Not yet proved: the hard direction of (5.2) (`m0AQ ≤ mAQ + O(1+B/Q)`, the
  paper's genuine row-swap/replacement argument), and (5.3) itself.

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

end CatalanSun.Lemma55
