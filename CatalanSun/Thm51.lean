/-
  CatalanSun/Thm51.lean

  Sun arXiv:2609.04176v1 §5 Theorem 5.1 scaffolding and combinatorial core:
  layer vocabulary (5.1)–(5.8)/(5.12); Φ_Q remainder (5.3); consecutive
  collision (5.15); balanced occupancy; (5.16) expansion; (5.17) row-factorial
  comparison. Does **not** yet prove Theorem 5.1 or Lemma 5.3.
-/

import CatalanSun.PascalCauchy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Cast.Field
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.Thm51

open Finset CatalanSun.PascalCauchy CatalanSun.NewtonCompletion
open Function

/-! ## Paper (5.1)–(5.8), (5.12) layer definitions -/

/-- Paper (5.1): `Φ_Q(n) = ∑_{r=0}^{n-1} ⌊r/Q⌋`. -/
def phiQ (Q n : ℕ) : ℕ :=
  ∑ r ∈ range n, r / Q

/-- Paper (5.4): `N_{K,Q}(i) = #{1 ≤ h ≤ K : Q ∣ 2i+2h+1}`. -/
def NKQ (K Q i : ℕ) : ℕ :=
  ((Icc 1 K).filter (fun h => Q ∣ 2 * i + 2 * h + 1)).card

/-- Paper (5.5): `n_{Q,r}(I) = #{i ∈ I : i ≡ r (mod Q)}`. -/
def nQr {N : ℕ} (Q r : ℕ) (I : Finset (Fin N)) : ℕ :=
  (I.filter (fun i => i.val % Q = r % Q)).card

/-- Paper (5.6): `C^A_Q = ∑_{a∈A} ⌊(a+2B)/Q⌋`. -/
def CAQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) : ℕ :=
  ∑ α : Fin S, ((f α).val + 2 * B) / Q

/-- Paper (5.6): `F_{N,Q}(i) = ⌊i/Q⌋ + ⌊(N-1-i)/Q⌋`. -/
def FNQ (N Q i : ℕ) : ℕ :=
  i / Q + (N - 1 - i) / Q

/-- Indicator `1_{Q ≤ 2i+1}` as `ℕ`. -/
def indicatorQle (Q i : ℕ) : ℕ :=
  if Q ≤ 2 * i + 1 then 1 else 0

/-- Paper (5.7): complete local layer `ℓ^A_Q(I)` (written `λ^A_Q` in the paper). -/
def ellAQ (B S Q : ℕ) (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (_hI : I.card = S) : ℤ :=
  (CAQ B S Q f : ℤ) +
    2 * ∑ r ∈ range Q, (((nQr Q r I).choose 2) : ℤ) +
    ∑ i ∈ I,
      ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
        (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ))

/-- Paper (5.8): `m^A_{Q,B} = min_{|I|=S} ℓ^A_Q(I)`. -/
noncomputable def mAQ (B S Q : ℕ) (f : Fin S → Fin (S + 3)) : ℤ :=
  let s :=
    ((univ : Finset (Fin (Ndim B S))).powersetCard S).image fun I =>
      if hI : I.card = S then ellAQ B S Q f I hI else 0
  if h : s.Nonempty then s.min' h else 0

/-- Paper (5.12): `a_{Q,B} = 2 ∑_{i=0}^{N-1} N_{B,Q}(i) − Φ_Q(D)` with `D = 2B`. -/
def aQB (B S Q : ℕ) : ℤ :=
  2 * ∑ i : Fin (Ndim B S), (NKQ B Q i.val : ℤ) - (phiQ Q (Dref B) : ℤ)

/-! ## Cheap identities -/

/-- Residue counts partition `I` when `Q > 0`. -/
theorem sum_nQr_eq_card {N Q : ℕ} (hQ : 0 < Q) (I : Finset (Fin N)) :
    ∑ r ∈ range Q, nQr Q r I = I.card := by
  classical
  have hfiber :
      ∑ r ∈ range Q, (I.filter (fun i : Fin N => i.val % Q = r)).card = I.card :=
    (card_eq_sum_card_fiberwise (s := I) (f := fun i : Fin N => i.val % Q)
      (t := range Q) fun _ _ => mem_range.mpr (Nat.mod_lt _ hQ)).symm
  refine Eq.trans ?_ hfiber
  refine sum_congr rfl fun r hr => ?_
  have hr' : r < Q := mem_range.mp hr
  simp only [nQr, Nat.mod_eq_of_lt hr']

/-- `Φ_Q(0) = 0`. -/
@[simp] theorem phiQ_zero (Q : ℕ) : phiQ Q 0 = 0 := by
  simp [phiQ]

/-- One full block of length `Q`: `∑_{k < Q} ⌊k/Q⌋ = 0`. -/
theorem phiQ_of_lt {Q n : ℕ} (hn : n ≤ Q) : phiQ Q n = 0 := by
  unfold phiQ
  refine sum_eq_zero fun k hk => Nat.div_eq_of_lt ?_
  exact lt_of_lt_of_le (mem_range.mp hk) hn

private theorem sum_const_nat_range (n a : ℕ) :
    ∑ _k ∈ range n, a = n * a := by
  rw [sum_const, card_range, nsmul_eq_mul, Nat.cast_id]

/-- `n*(n-1)/2 + n = n*(n+1)/2`. -/
private theorem triangular_succ (n : ℕ) :
    n * (n - 1) / 2 + n = n * (n + 1) / 2 := by
  refine Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 2) ?_
  have hL : 2 * (n * (n - 1) / 2 + n) = n * (n - 1) + 2 * n := by
    have heven : Even (n * (n - 1)) := Nat.even_mul_pred_self n
    rw [Nat.mul_add, Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)]
  have hR : 2 * (n * (n + 1) / 2) = n * (n + 1) := by
    have heven : Even (n * (n + 1)) := Nat.even_mul_succ_self n
    exact Nat.mul_div_cancel' (even_iff_two_dvd.mp heven)
  rw [hL, hR]
  cases n with
  | zero => simp
  | succ n =>
    simp [Nat.succ_sub_one, Nat.mul_succ, Nat.succ_mul]
    ring

/-- Paper (5.2) special case `r = 0`: `Φ_Q(qQ) = Q · q · (q-1)/2`. -/
theorem phiQ_mul {Q q : ℕ} (hQ : 0 < Q) :
    phiQ Q (q * Q) = Q * (q * (q - 1) / 2) := by
  induction q with
  | zero => simp [phiQ]
  | succ q ih =>
    unfold phiQ at ih ⊢
    rw [Nat.succ_mul, sum_range_add, ih]
    have hblock : ∑ k ∈ range Q, (q * Q + k) / Q = Q * q := by
      have hterm : ∀ k ∈ range Q, (q * Q + k) / Q = q := by
        intro k hk
        have hk' : k < Q := mem_range.mp hk
        rw [add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hk', zero_add]
      rw [sum_congr rfl hterm, sum_const_nat_range]
    rw [hblock, ← Nat.mul_add]
    congr 1
    trans q * (q + 1) / 2
    · exact triangular_succ q
    · simp [Nat.add_sub_cancel, mul_comm]

/-- Paper (5.2): if `n = qQ + r` with `r < Q`, then
`Φ_Q(n) = Q·q·(q-1)/2 + r·q`. -/
theorem phiQ_formula {Q n q r : ℕ} (hQ : 0 < Q) (hr : r < Q) (hn : n = q * Q + r) :
    phiQ Q n = Q * (q * (q - 1) / 2) + r * q := by
  unfold phiQ
  rw [hn, sum_range_add]
  have hmain : ∑ k ∈ range (q * Q), k / Q = Q * (q * (q - 1) / 2) := by
    simpa [phiQ] using phiQ_mul (Q := Q) (q := q) hQ
  have hrem : ∑ k ∈ range r, (q * Q + k) / Q = r * q := by
    have hterm : ∀ k ∈ range r, (q * Q + k) / Q = q := by
      intro k hk
      have hk' : k < r := mem_range.mp hk
      have hkQ : k < Q := lt_trans hk' hr
      rw [add_comm, Nat.add_mul_div_right _ _ hQ, Nat.div_eq_of_lt hkQ, zero_add]
    rw [sum_congr rfl hterm, sum_const_nat_range]
  rw [hmain, hrem]


/-! ## COMB-A: paper (5.3) Φ_Q remainder bounds -/

/-- Helper: `Φ_Q(n) − (n²/(2Q) − n/2) = r(Q−r)/(2Q)` for `n = qQ + r`. -/
theorem phiQ_sub_quadratic_eq {Q n q r : ℕ} (hQ : 0 < Q) (hr : r < Q)
    (hn : n = q * Q + r) :
    (phiQ Q n : ℚ) - ((n * n : ℚ) / (2 * Q) - (n : ℚ) / 2) =
      ((r : ℚ) * ((Q : ℚ) - (r : ℚ))) / (2 * Q) := by
  have hφ := phiQ_formula (Q := Q) (n := n) (q := q) (r := r) hQ hr hn
  have heven : Even (q * (q - 1)) := Nat.even_mul_pred_self q
  have hQ0 : (Q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hQ)
  have h20 : (2 : ℚ) ≠ 0 := by norm_num
  -- Rewrite Φ in rationals, using evenness of `q(q-1)`.
  have hdiv : (↑(q * (q - 1) / 2) : ℚ) = (↑q * (↑q - 1)) / 2 := by
    have h1 : (↑(q * (q - 1) / 2) : ℚ) = ↑(q * (q - 1)) / 2 :=
      Nat.cast_div (even_iff_two_dvd.mp heven) h20
    rw [h1, Nat.cast_mul]
    cases q with
    | zero => simp
    | succ q => simp [Nat.cast_succ, Nat.succ_sub_one]
  have hφQ :
      (phiQ Q n : ℚ) =
        (Q : ℚ) * ((q : ℚ) * ((q : ℚ) - 1) / 2) + (r : ℚ) * (q : ℚ) := by
    calc (phiQ Q n : ℚ)
        = ↑(Q * (q * (q - 1) / 2) + r * q) := by rw [hφ]
      _ = ↑Q * ↑(q * (q - 1) / 2) + ↑r * ↑q := by push_cast; ring
      _ = ↑Q * ((↑q * (↑q - 1)) / 2) + ↑r * ↑q := by rw [hdiv]
      _ = ↑Q * (↑q * (↑q - 1) / 2) + ↑r * ↑q := by ring
  have hnQ : (n : ℚ) = (q : ℚ) * (Q : ℚ) + (r : ℚ) := by
    rw [hn]; push_cast; ring
  rw [hφQ, hnQ]
  field_simp [hQ0, h20]
  ring

/-- Paper (5.3) lower half: `n²/(2Q) − n/2 ≤ Φ_Q(n)`. -/
theorem phiQ_sub_quadratic_nonneg {Q n : ℕ} (hQ : 0 < Q) :
    (n * n : ℚ) / (2 * Q) - (n : ℚ) / 2 ≤ (phiQ Q n : ℚ) := by
  have hn : n = (n / Q) * Q + n % Q := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hr : n % Q < Q := Nat.mod_lt n hQ
  have heq :=
    phiQ_sub_quadratic_eq (Q := Q) (n := n) (q := n / Q) (r := n % Q) hQ hr hn
  set r := n % Q
  have hnonneg : (0 : ℚ) ≤ (r : ℚ) * ((Q : ℚ) - (r : ℚ)) / (2 * Q) := by
    refine div_nonneg ?_ (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
    exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast (le_of_lt hr)))
  linarith [heq, hnonneg]

/-- Paper (5.3) upper half: `Φ_Q(n) − (n²/(2Q) − n/2) ≤ Q/8`. -/
theorem phiQ_sub_quadratic_le {Q n : ℕ} (hQ : 0 < Q) :
    (phiQ Q n : ℚ) - ((n * n : ℚ) / (2 * Q) - (n : ℚ) / 2) ≤ (Q : ℚ) / 8 := by
  have hn : n = (n / Q) * Q + n % Q := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hr : n % Q < Q := Nat.mod_lt n hQ
  have heq :=
    phiQ_sub_quadratic_eq (Q := Q) (n := n) (q := n / Q) (r := n % Q) hQ hr hn
  set r := n % Q
  rw [heq]
  have hAM : (4 : ℤ) * (r : ℤ) * ((Q : ℤ) - (r : ℤ)) ≤ (Q : ℤ) ^ 2 := by
    have hs : (0 : ℤ) ≤ (2 * (r : ℤ) - (Q : ℤ)) ^ 2 := sq_nonneg _
    have hexpand :
        (2 * (r : ℤ) - (Q : ℤ)) ^ 2 =
          (Q : ℤ) ^ 2 - 4 * (r : ℤ) * ((Q : ℤ) - (r : ℤ)) := by ring
    linarith
  have hAMQ : (4 : ℚ) * (r : ℚ) * ((Q : ℚ) - (r : ℚ)) ≤ (Q : ℚ) ^ 2 := by
    exact_mod_cast hAM
  have hQ0 : (0 : ℚ) < (Q : ℚ) := Nat.cast_pos.mpr hQ
  have hden : (0 : ℚ) < 2 * (Q : ℚ) := mul_pos (by norm_num) hQ0
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℚ) < 8)]
  nlinarith [hAMQ]

/-! ## COMB-B: paper (5.15) consecutive collision identity -/

/-- `{0, …, S−1}` as a `Finset (Fin N)` when `S ≤ N`. -/
def consecutiveInitial {N : ℕ} (S : ℕ) (hS : S ≤ N) : Finset (Fin N) :=
  (univ : Finset (Fin S)).map
    ⟨fun i : Fin S => ⟨(i : ℕ), Nat.lt_of_lt_of_le i.isLt hS⟩,
      fun _ _ h => Fin.ext (Fin.mk.inj h)⟩

@[simp] theorem consecutiveInitial_card {N S : ℕ} (hS : S ≤ N) :
    (consecutiveInitial (N := N) S hS).card = S := by
  simp [consecutiveInitial, card_map, card_univ, Fintype.card_fin]

theorem mem_consecutiveInitial_iff {N S : ℕ} (hS : S ≤ N) (i : Fin N) :
    i ∈ consecutiveInitial (N := N) S hS ↔ i.val < S := by
  constructor
  · intro hi
    rcases mem_map.mp hi with ⟨j, _, rfl⟩
    exact j.isLt
  · intro hi
    refine mem_map.mpr ⟨⟨i.val, hi⟩, mem_univ _, ?_⟩
    ext; rfl

private theorem consecutiveInitial_succ {N S : ℕ} (hS : S + 1 ≤ N) :
    consecutiveInitial (N := N) (S + 1) hS =
      insert ⟨S, hS⟩ (consecutiveInitial (N := N) S (Nat.le_of_succ_le hS)) := by
  ext i
  simp only [mem_insert, mem_consecutiveInitial_iff]
  constructor
  · intro hi
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | h
    · exact Or.inr h
    · exact Or.inl (Fin.ext h)
  · intro h
    rcases h with h | h
    · simpa [h] using Nat.lt_succ_self S
    · exact Nat.lt_succ_of_lt h

private theorem not_mem_consecutiveInitial_boundary {N S : ℕ} (hS : S + 1 ≤ N) :
    (⟨S, hS⟩ : Fin N) ∉ consecutiveInitial (N := N) S (Nat.le_of_succ_le hS) := by
  simp [mem_consecutiveInitial_iff]

private theorem choose_two_succ (n : ℕ) :
    (n + 1).choose 2 = n.choose 2 + n := by
  -- `(n+1).choose 2 = n.choose 1 + n.choose 2 = n + n.choose 2`
  simpa [Nat.choose_one_right, add_comm] using Nat.choose_succ_succ n 1

private theorem phiQ_succ (Q S : ℕ) :
    phiQ Q (S + 1) = phiQ Q S + S / Q := by
  simp [phiQ, sum_range_succ]

/-- Residue `S % Q` appears exactly `S / Q` times in `{0,…,S−1}`. -/
theorem nQr_consecutiveInitial_mod {N Q S : ℕ} (hQ : 0 < Q) (hS : S ≤ N) :
    nQr Q (S % Q) (consecutiveInitial (N := N) S hS) = S / Q := by
  classical
  set rem := S % Q
  set q := S / Q
  have hSdecomp : S = q * Q + rem := by
    simp [q, rem, Nat.div_add_mod']
  have hrQ : rem < Q := Nat.mod_lt S hQ
  let g : Fin q ↪ Fin N :=
    ⟨fun k => ⟨k.val * Q + rem, by
        have hlt : k.val * Q + rem < S := by
          have : k.val * Q + rem < q * Q + rem :=
            Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right k.isLt hQ) rem
          rwa [← hSdecomp] at this
        exact lt_of_lt_of_le hlt hS⟩,
      fun a b h =>
        Fin.ext (Nat.eq_of_mul_eq_mul_right hQ
          (Nat.add_right_cancel (congrArg Fin.val h)))⟩
  have himg :
      (consecutiveInitial (N := N) S hS).filter
          (fun i : Fin N => i.val % Q = rem) =
        (univ : Finset (Fin q)).map g := by
    ext i
    simp only [mem_filter, mem_map, mem_univ, true_and, mem_consecutiveInitial_iff]
    constructor
    · intro ⟨hiS, hmod⟩
      refine ⟨⟨i.val / Q, ?bound⟩, ?eq⟩
      case bound =>
        by_contra hge
        have hqle : q ≤ i.val / Q := Nat.le_of_not_lt hge
        have hge2 : q * Q ≤ i.val := by
          have h1 : q * Q ≤ (i.val / Q) * Q := Nat.mul_le_mul_right Q hqle
          have h2 : (i.val / Q) * Q ≤ i.val := by
            simpa [Nat.mul_comm] using Nat.mul_div_le i.val Q
          exact le_trans h1 h2
        have hiS' : i.val < q * Q + rem := by
          rw [← hSdecomp]; exact hiS
        have hsub_lt : i.val - q * Q < rem :=
          Nat.sub_lt_left_of_lt_add hge2 hiS'
        have hmod' : i.val % Q = i.val - q * Q := by
          set z := i.val - q * Q
          have hrep : i.val = Q * q + z := by
            calc i.val
                = q * Q + z := (Nat.add_sub_of_le hge2).symm
              _ = Q * q + z := by rw [Nat.mul_comm]
          have hz : z < Q := lt_trans hsub_lt hrQ
          calc i.val % Q
              = (Q * q + z) % Q := by rw [hrep]
            _ = z % Q := Nat.mul_add_mod_self_left _ _ _
            _ = z := Nat.mod_eq_of_lt hz
        have hlt : i.val % Q < rem := by rwa [hmod']
        exact lt_irrefl rem (hmod ▸ hlt)
      case eq =>
        -- Goal: `g ⟨i.val / Q, _⟩ = i`.
        refine Fin.ext ?_
        change (i.val / Q) * Q + rem = i.val
        rw [← hmod, Nat.div_add_mod' i.val Q]
    · intro ⟨k, hk⟩
      -- `hk : g k = i`
      constructor
      · have hlt : k.val * Q + rem < S := by
          have : k.val * Q + rem < q * Q + rem :=
            Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_right k.isLt hQ) rem
          rwa [← hSdecomp] at this
        have hi_val : i.val = k.val * Q + rem := by
          simpa [g] using (congrArg Fin.val hk).symm
        rwa [hi_val]
      · have hi_val : i.val = k.val * Q + rem := by
          simpa [g] using (congrArg Fin.val hk).symm
        have : (k.val * Q + rem) % Q = rem := by
          rw [Nat.mul_comm k.val Q, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hrQ]
        rwa [hi_val]
  -- `nQr` uses `r % Q`; here `rem % Q = rem`.
  simp only [nQr, Nat.mod_eq_of_lt hrQ, himg, card_map, card_univ, Fintype.card_fin]

/-- Paper (5.15): consecutive block collision sum equals `Φ_Q(S)`. -/
theorem sum_choose_nQr_consecutive {N Q S : ℕ} (hQ : 0 < Q) (hS : S ≤ N) :
    ∑ r ∈ range Q, ((nQr Q r (consecutiveInitial (N := N) S hS)).choose 2) =
      phiQ Q S := by
  classical
  induction S generalizing N with
  | zero =>
    simp [phiQ, nQr, consecutiveInitial]
  | succ S ih =>
    have hS0 : S ≤ N := Nat.le_of_succ_le hS
    have ihS := ih (N := N) hS0
    rw [consecutiveInitial_succ hS, phiQ_succ]
    set I := consecutiveInitial (N := N) S hS0
    set i : Fin N := ⟨S, hS⟩
    have hnotin : i ∉ I := not_mem_consecutiveInitial_boundary hS
    have hrem : i.val % Q ∈ range Q := mem_range.mpr (Nat.mod_lt _ hQ)
    have hsame : ∀ r ∈ (range Q).erase (i.val % Q),
        nQr Q r (insert i I) = nQr Q r I := by
      intro r hr
      have hrQ : r < Q := mem_range.mp (erase_subset _ _ hr)
      have hne : i.val % Q ≠ r % Q := by
        have : r ≠ i.val % Q := (mem_erase.mp hr).1
        simpa [Nat.mod_eq_of_lt hrQ] using this.symm
      simp only [nQr]
      rw [filter_insert]
      simp [hnotin, hne]
    have hinc : nQr Q (i.val % Q) (insert i I) = nQr Q (i.val % Q) I + 1 := by
      simp only [nQr]
      rw [filter_insert]
      simp [hnotin, Nat.mod_mod]
    have hsum_step :
        ∑ r ∈ range Q, ((nQr Q r (insert i I)).choose 2) =
          ∑ r ∈ range Q, ((nQr Q r I).choose 2) + nQr Q (i.val % Q) I := by
      have hsplit :
          ∑ r ∈ range Q, ((nQr Q r (insert i I)).choose 2) =
            ∑ r ∈ (range Q).erase (i.val % Q), ((nQr Q r (insert i I)).choose 2) +
              (nQr Q (i.val % Q) (insert i I)).choose 2 :=
        (sum_erase_add (range Q) (fun r => ((nQr Q r (insert i I)).choose 2)) hrem).symm
      have hsplit_old :
          ∑ r ∈ range Q, ((nQr Q r I).choose 2) =
            ∑ r ∈ (range Q).erase (i.val % Q), ((nQr Q r I).choose 2) +
              (nQr Q (i.val % Q) I).choose 2 :=
        (sum_erase_add (range Q) (fun r => ((nQr Q r I).choose 2)) hrem).symm
      calc
        ∑ r ∈ range Q, ((nQr Q r (insert i I)).choose 2)
            = ∑ r ∈ (range Q).erase (i.val % Q), ((nQr Q r (insert i I)).choose 2) +
                (nQr Q (i.val % Q) (insert i I)).choose 2 := hsplit
        _ = ∑ r ∈ (range Q).erase (i.val % Q), ((nQr Q r I).choose 2) +
                (nQr Q (i.val % Q) I + 1).choose 2 := by
              rw [hinc, sum_congr rfl fun r hr => by rw [hsame r hr]]
        _ = ∑ r ∈ (range Q).erase (i.val % Q), ((nQr Q r I).choose 2) +
                ((nQr Q (i.val % Q) I).choose 2 + nQr Q (i.val % Q) I) := by
              rw [choose_two_succ]
        _ = ∑ r ∈ range Q, ((nQr Q r I).choose 2) + nQr Q (i.val % Q) I := by
              linarith [hsplit_old]
    have hold_occ : nQr Q (i.val % Q) I = S / Q := by
      simpa [I, i] using nQr_consecutiveInitial_mod (N := N) (Q := Q) (S := S) hQ hS0
    -- `ihS` needs `hQ`; pass it explicitly via the induction hypothesis shape.
    have ihS' : ∑ r ∈ range Q, ((nQr Q r I).choose 2) = phiQ Q S := by
      simpa [I] using ih (N := N) hS0
    rw [hsum_step, ihS', hold_occ]


/-! ## COMB-C: balanced occupancy minimizes collisions -/

/-- Collision number of a `Q`-tuple. -/
def collisionSum {Q : ℕ} (c : Fin Q → ℕ) : ℕ :=
  ∑ r : Fin Q, (c r).choose 2

/-- Transfer map: move one unit from `a` to `b`. -/
def collisionMove {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q) : Fin Q → ℕ :=
  update (update c a (c a - 1)) b (c b + 1)

private theorem two_mul_choose_two (n : ℕ) :
    2 * n.choose 2 = n * (n - 1) := by
  rw [Nat.choose_two_right, Nat.mul_div_cancel' (even_iff_two_dvd.mp (Nat.even_mul_pred_self n))]

private theorem collisionSum_pair (c : Fin Q → ℕ) (a b : Fin Q) (hne : a ≠ b) :
    collisionSum c =
      (c a).choose 2 + (c b).choose 2 +
        ∑ x ∈ (univ.erase a).erase b, (c x).choose 2 := by
  classical
  have ha : a ∈ (univ : Finset (Fin Q)) := mem_univ a
  have hb : b ∈ univ.erase a := mem_erase.mpr ⟨hne.symm, mem_univ b⟩
  unfold collisionSum
  have h1 := (sum_erase_add univ (fun x => (c x).choose 2) ha).symm
  have h2 := (sum_erase_add (univ.erase a) (fun x => (c x).choose 2) hb).symm
  linarith

private theorem collisionMove_val_a {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q) (hne : a ≠ b) :
    collisionMove c a b a = c a - 1 := by
  simp only [collisionMove]
  rw [update_of_ne hne, update_self]

private theorem collisionMove_val_b {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q) :
    collisionMove c a b b = c b + 1 := by
  simp only [collisionMove, update_self]

private theorem collisionMove_val_other {Q : ℕ} (c : Fin Q → ℕ) (a b x : Fin Q)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    collisionMove c a b x = c x := by
  simp only [collisionMove]
  rw [update_of_ne hxb, update_of_ne hxa]

private theorem nat_mul_move_lt (ca cb : ℕ) (hab : cb + 2 ≤ ca) :
    (ca - 1) * (ca - 1) + (cb + 1) * (cb + 1) < ca * ca + cb * cb := by
  have hca : 1 ≤ ca := by omega
  let x := ca - 1
  have hx : ca = x + 1 := (Nat.sub_add_cancel hca).symm
  have hxb : cb + 1 ≤ x := by omega
  have hcbx : cb ≤ x := Nat.le_of_succ_le hxb
  -- Difference is `2*(x - cb) ≥ 2`.
  have hdiff :
      (x + 1) * (x + 1) + cb * cb =
        x * x + (cb + 1) * (cb + 1) + 2 * (x - cb) := by
    have : x = cb + (x - cb) := (Nat.add_sub_of_le hcbx).symm
    calc (x + 1) * (x + 1) + cb * cb
        = x * x + 2 * x + 1 + cb * cb := by ring
      _ = x * x + (cb * cb + 2 * cb + 1) + 2 * (x - cb) := by
            rw [this]; ring_nf; omega
      _ = x * x + (cb + 1) * (cb + 1) + 2 * (x - cb) := by ring
  have hpos : 0 < 2 * (x - cb) := by
    have : 0 < x - cb := Nat.sub_pos_of_lt (lt_of_lt_of_le (Nat.lt_succ_self cb) hxb)
    omega
  rw [hx]
  change x * x + (cb + 1) * (cb + 1) < (x + 1) * (x + 1) + cb * cb
  linarith [hdiff, hpos]

private theorem nat_choose_move (ca cb : ℕ) (ha : 1 ≤ ca) (hab : cb + 2 ≤ ca) :
    (ca - 1).choose 2 + (cb + 1).choose 2 + (ca - cb - 1) =
      ca.choose 2 + cb.choose 2 := by
  have hA : ca.choose 2 = (ca - 1).choose 2 + (ca - 1) := by
    calc ca.choose 2
        = ((ca - 1) + 1).choose 2 := by rw [Nat.sub_add_cancel ha]
      _ = (ca - 1).choose 2 + (ca - 1) := choose_two_succ _
  have hB : (cb + 1).choose 2 = cb.choose 2 + cb := choose_two_succ cb
  rw [hA, hB]
  omega

/-- Moving mass from a larger part to a smaller decreases the collision sum by `c a - c b - 1`. -/
theorem collisionSum_move {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q)
    (hne : a ≠ b) (hab : c b + 2 ≤ c a) :
    collisionSum (collisionMove c a b) + (c a - c b - 1) = collisionSum c := by
  classical
  have ha : 1 ≤ c a := by omega
  have hpair := collisionSum_pair c a b hne
  have hpair' := collisionSum_pair (collisionMove c a b) a b hne
  have hrest :
      ∑ x ∈ (univ.erase a).erase b, (collisionMove c a b x).choose 2 =
        ∑ x ∈ (univ.erase a).erase b, (c x).choose 2 := by
    refine sum_congr rfl fun x hx => ?_
    have hxb : x ≠ b := (mem_erase.mp hx).1
    have hxa : x ≠ a := (mem_erase.mp (erase_subset b _ hx)).1
    rw [collisionMove_val_other c a b x hxa hxb]
  rw [hpair', collisionMove_val_a c a b hne, collisionMove_val_b c a b, hrest, hpair]
  have := nat_choose_move (c a) (c b) ha hab
  linarith

private theorem collisionMove_sum {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q)
    (hne : a ≠ b) (hab : c b + 2 ≤ c a) :
    ∑ r, collisionMove c a b r = ∑ r, c r := by
  classical
  have ha_mem : a ∈ (univ : Finset (Fin Q)) := mem_univ a
  have hb_mem : b ∈ univ.erase a := mem_erase.mpr ⟨hne.symm, mem_univ b⟩
  have hpair (d : Fin Q → ℕ) :
      ∑ r, d r = d a + d b + ∑ x ∈ (univ.erase a).erase b, d x := by
    have h1 := (sum_erase_add univ d ha_mem).symm
    have h2 := (sum_erase_add (univ.erase a) d hb_mem).symm
    linarith
  have hrest :
      ∑ x ∈ (univ.erase a).erase b, collisionMove c a b x =
        ∑ x ∈ (univ.erase a).erase b, c x := by
    refine sum_congr rfl fun x hx => ?_
    have hxb : x ≠ b := (mem_erase.mp hx).1
    have hxa : x ≠ a := (mem_erase.mp (erase_subset b _ hx)).1
    exact collisionMove_val_other c a b x hxa hxb
  have ha : 1 ≤ c a := by omega
  rw [hpair (collisionMove c a b), hpair c, collisionMove_val_a c a b hne,
    collisionMove_val_b c a b, hrest]
  omega

private theorem collisionMove_sum_sq_lt {Q : ℕ} (c : Fin Q → ℕ) (a b : Fin Q)
    (hne : a ≠ b) (hab : c b + 2 ≤ c a) :
    ∑ r, collisionMove c a b r * collisionMove c a b r < ∑ r, c r * c r := by
  classical
  have ha_mem : a ∈ (univ : Finset (Fin Q)) := mem_univ a
  have hb_mem : b ∈ univ.erase a := mem_erase.mpr ⟨hne.symm, mem_univ b⟩
  have hpair (d : Fin Q → ℕ) :
      ∑ r, d r * d r = d a * d a + d b * d b + ∑ x ∈ (univ.erase a).erase b, d x * d x := by
    have h1 := (sum_erase_add univ (fun r => d r * d r) ha_mem).symm
    have h2 := (sum_erase_add (univ.erase a) (fun r => d r * d r) hb_mem).symm
    linarith
  have hrest :
      ∑ x ∈ (univ.erase a).erase b, collisionMove c a b x * collisionMove c a b x =
        ∑ x ∈ (univ.erase a).erase b, c x * c x := by
    refine sum_congr rfl fun x hx => ?_
    have hxb : x ≠ b := (mem_erase.mp hx).1
    have hxa : x ≠ a := (mem_erase.mp (erase_subset b _ hx)).1
    rw [collisionMove_val_other c a b x hxa hxb]
  have hva := collisionMove_val_a c a b hne
  have hvb := collisionMove_val_b c a b
  have hnat := nat_mul_move_lt (c a) (c b) hab
  rw [hpair (collisionMove c a b), hpair c, hva, hvb, hrest]
  linarith

private theorem le_add_one_of_int_sub_le {m n : ℕ}
    (h : (m : ℤ) - (n : ℤ) ≤ 1) : m ≤ n + 1 := by
  exact_mod_cast (sub_le_iff_le_add'.mp h)

/-- Balanced `Q`-tuple with sum `n` has collision sum `Φ_Q(n)`. -/
theorem collisionSum_eq_phiQ_of_balanced {Q n : ℕ} (hQ : 0 < Q)
    (c : Fin Q → ℕ) (hsum : ∑ r, c r = n)
    (hbal : ∀ r s, (c r : ℤ) - c s ≤ 1) :
    collisionSum c = phiQ Q n := by
  classical
  set q := n / Q
  set r := n % Q
  have hr : r < Q := Nat.mod_lt n hQ
  have hn : n = q * Q + r := by simp [q, r, Nat.div_add_mod']
  have hdiff (u v : Fin Q) : c u ≤ c v + 1 :=
    le_add_one_of_int_sub_le (hbal u v)
  -- Pick a minimizing index.
  have hNonempty : (univ : Finset (Fin Q)).Nonempty := ⟨⟨0, hQ⟩, mem_univ _⟩
  obtain ⟨i0, -, hi0⟩ := (univ : Finset (Fin Q)).exists_min_image c hNonempty
  have hmin : ∀ j, c i0 ≤ c j := fun j => hi0 j (mem_univ j)
  have hparts : ∀ j, c j = c i0 ∨ c j = c i0 + 1 := by
    intro j
    have hlo := hmin j
    have hhi := hdiff j i0
    omega
  set m := c i0
  set k := (univ.filter (fun i : Fin Q => c i = m + 1)).card
  have hk_le : k ≤ Q := by
    simpa [k, card_univ, Fintype.card_fin] using
      card_filter_le (univ : Finset (Fin Q)) (fun i => c i = m + 1)
  have h2card : (univ.filter (fun i : Fin Q => ¬c i = m + 1)).card = Q - k := by
    have h := card_filter_add_card_filter_not
      (s := univ) (p := fun i : Fin Q => c i = m + 1)
    simp only [card_univ, Fintype.card_fin, k] at h ⊢
    omega
  have hk_lt : k < Q := by
    by_contra hge
    have hkQ : k = Q := le_antisymm hk_le (le_of_not_gt hge)
    -- Then every index equals `m+1`, contradicting minimality of `i0`.
    have hall : ∀ i, c i = m + 1 := by
      intro i
      have hmem : i ∈ univ.filter (fun j => c j = m + 1) := by
        have : (univ.filter (fun j => c j = m + 1)).card = Q := hkQ
        have hcard : (univ.filter (fun j => c j = m + 1)) = univ := by
          refine eq_of_subset_of_card_le (filter_subset _ _) ?_
          simp [this, card_univ, Fintype.card_fin]
        simpa [hcard] using mem_univ i
      exact (mem_filter.mp hmem).2
    have : c i0 = m + 1 := hall i0
    simp [m] at this
  have hsum_form : n = Q * m + k := by
    have hsplit :=
      (sum_filter_add_sum_filter_not (s := univ)
        (p := fun i : Fin Q => c i = m + 1) (f := c)).symm
    have h1 : ∑ i ∈ univ.filter (fun i : Fin Q => c i = m + 1), c i = k * (m + 1) := by
      refine Eq.trans (sum_congr rfl fun i hi => (mem_filter.mp hi).2) ?_
      simp [k, sum_const, nsmul_eq_mul]
    have h2 :
        ∑ i ∈ univ.filter (fun i : Fin Q => ¬c i = m + 1), c i = (Q - k) * m := by
      have hterm : ∀ i ∈ univ.filter (fun i : Fin Q => ¬c i = m + 1), c i = m := by
        intro i hi
        have hne : c i ≠ m + 1 := (mem_filter.mp hi).2
        have : c i = m ∨ c i = m + 1 := by simpa [m] using hparts i
        exact this.resolve_right hne
      rw [sum_congr rfl hterm, sum_const, h2card, nsmul_eq_mul, Nat.cast_id]
    have : n = k * (m + 1) + (Q - k) * m := by rw [← hsum, hsplit, h1, h2]
    have hkk : k * m ≤ Q * m := Nat.mul_le_mul_right m hk_le
    calc n = k * (m + 1) + (Q - k) * m := this
      _ = k * m + k + (Q * m - k * m) := by rw [Nat.mul_add, Nat.sub_mul]; ring
      _ = Q * m + k := by omega
  -- Division algorithm uniqueness: `m = q`, `k = r`.
  have hm : m = q := by
    have : n = Q * m + k := hsum_form
    have hdiv : n / Q = m := by
      rw [this, Nat.mul_add_div hQ, Nat.div_eq_of_lt hk_lt, add_zero]
    simpa [q] using hdiv.symm
  have hk : k = r := by
    have : n = Q * m + k := hsum_form
    have hmod : n % Q = k := by
      rw [this, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hk_lt]
    simpa [r] using hmod.symm
  -- Evaluate collision sum.
  have hcoll : collisionSum c = k * ((m + 1).choose 2) + (Q - k) * m.choose 2 := by
    unfold collisionSum
    have hsplit :=
      (sum_filter_add_sum_filter_not (s := univ)
        (p := fun i : Fin Q => c i = m + 1) (f := fun i => (c i).choose 2)).symm
    have h1 :
        ∑ i ∈ univ.filter (fun i : Fin Q => c i = m + 1), (c i).choose 2 =
          k * ((m + 1).choose 2) := by
      refine Eq.trans (sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]) ?_
      simp [k, sum_const, nsmul_eq_mul]
    have h2 :
        ∑ i ∈ univ.filter (fun i : Fin Q => ¬c i = m + 1), (c i).choose 2 =
          (Q - k) * m.choose 2 := by
      have hterm :
          ∀ i ∈ univ.filter (fun i : Fin Q => ¬c i = m + 1),
            (c i).choose 2 = m.choose 2 := by
        intro i hi
        have hne : c i ≠ m + 1 := (mem_filter.mp hi).2
        have : c i = m ∨ c i = m + 1 := by simpa [m] using hparts i
        rw [this.resolve_right hne]
      rw [sum_congr rfl hterm, sum_const, h2card, nsmul_eq_mul, Nat.cast_id]
    rw [hsplit, h1, h2]
  have hφ := phiQ_formula (Q := Q) (n := n) (q := q) (r := r) hQ hr hn
  rw [hcoll, hm, hk, hφ]
  -- Clear the factor `2`.
  refine Nat.eq_of_mul_eq_mul_left (by decide : (0 : ℕ) < 2) ?_
  have he0 : Even (q * (q - 1)) := Nat.even_mul_pred_self q
  have hL :
      2 * (r * ((q + 1).choose 2) + (Q - r) * q.choose 2) =
        r * ((q + 1) * q) + (Q - r) * (q * (q - 1)) := by
    calc 2 * (r * ((q + 1).choose 2) + (Q - r) * q.choose 2)
        = 2 * (r * ((q + 1).choose 2)) + 2 * ((Q - r) * q.choose 2) := by ring
      _ = r * (2 * ((q + 1).choose 2)) + (Q - r) * (2 * q.choose 2) := by ring
      _ = r * ((q + 1) * q) + (Q - r) * (q * (q - 1)) := by
            rw [two_mul_choose_two (q + 1), two_mul_choose_two q]
            simp
  have hR :
      2 * (Q * (q * (q - 1) / 2) + r * q) =
        Q * (q * (q - 1)) + 2 * (r * q) := by
    have : 2 * (Q * (q * (q - 1) / 2)) = Q * (q * (q - 1)) := by
      calc 2 * (Q * (q * (q - 1) / 2))
          = Q * (2 * (q * (q - 1) / 2)) := by ring
        _ = Q * (q * (q - 1)) := by rw [Nat.mul_div_cancel' (even_iff_two_dvd.mp he0)]
    rw [Nat.mul_add, this]
  rw [hL, hR]
  -- `r(q+1)q + (Q-r)q(q-1) = Qq(q-1) + 2rq`.
  have hrQ : r ≤ Q := le_of_lt hr
  cases q with
  | zero => simp
  | succ q =>
    simp only [Nat.succ_sub_one]
    -- Goal: `r*(q+2)*(q+1) + (Q-r)*(q+1)*q = Q*(q+1)*q + 2*r*(q+1)`.
    have hcancel :
        r * ((q + 1 + 1) * (q + 1)) + (Q - r) * ((q + 1) * q) =
          Q * ((q + 1) * q) + 2 * (r * (q + 1)) := by
      have hsub : (Q - r) * ((q + 1) * q) + r * ((q + 1) * q) = Q * ((q + 1) * q) := by
        rw [← Nat.add_mul, Nat.sub_add_cancel hrQ]
      -- Expand left first factor:
      -- r*(q+2)*(q+1) = r*((q+1)*q + 2*(q+1)) = r*(q+1)*q + 2*r*(q+1)
      have hexp : (q + 1 + 1) * (q + 1) = (q + 1) * q + 2 * (q + 1) := by ring
      calc r * ((q + 1 + 1) * (q + 1)) + (Q - r) * ((q + 1) * q)
          = r * ((q + 1) * q + 2 * (q + 1)) + (Q - r) * ((q + 1) * q) := by rw [hexp]
        _ = r * ((q + 1) * q) + 2 * (r * (q + 1)) + (Q - r) * ((q + 1) * q) := by ring
        _ = (Q - r) * ((q + 1) * q) + r * ((q + 1) * q) + 2 * (r * (q + 1)) := by ring
        _ = Q * ((q + 1) * q) + 2 * (r * (q + 1)) := by rw [hsub]
    exact hcancel

/-- Among fixed-sum `Q`-tuples, the collision sum is at least `Φ_Q(n)`. -/
theorem collisionSum_ge_phiQ {Q n : ℕ} (hQ : 0 < Q)
    (c : Fin Q → ℕ) (hsum : ∑ r, c r = n) :
    collisionSum c ≥ phiQ Q n := by
  classical
  let motive : ℕ → Prop := fun s =>
    ∀ (c : Fin Q → ℕ), ∑ r, c r * c r = s → ∑ r, c r = n →
      collisionSum c ≥ phiQ Q n
  have : motive (∑ r, c r * c r) := by
    refine Nat.strong_induction_on (∑ r, c r * c r) fun s ih => ?_
    intro c hs hsum'
    by_cases hbal : ∀ u v, (c u : ℤ) - c v ≤ 1
    · exact ge_of_eq (collisionSum_eq_phiQ_of_balanced hQ c hsum' hbal)
    · push Not at hbal
      rcases hbal with ⟨a, b, habZ⟩
      have hab : c b + 2 ≤ c a := by
        have hZ : (2 : ℤ) ≤ (c a : ℤ) - (c b : ℤ) := by omega
        have : (c b + 2 : ℤ) ≤ (c a : ℤ) := by linarith
        exact_mod_cast this
      have hne : a ≠ b := by intro h; subst h; omega
      have hsum_move : ∑ r, collisionMove c a b r = n := by
        simpa [hsum'] using collisionMove_sum c a b hne hab
      have hsq_lt : ∑ r, collisionMove c a b r * collisionMove c a b r < s := by
        simpa [hs] using collisionMove_sum_sq_lt c a b hne hab
      have ih_apply : collisionSum (collisionMove c a b) ≥ phiQ Q n :=
        ih _ hsq_lt (collisionMove c a b) rfl hsum_move
      have hmove := collisionSum_move c a b hne hab
      have hdec : collisionSum (collisionMove c a b) ≤ collisionSum c := by
        have : 0 ≤ c a - c b - 1 := by omega
        omega
      exact le_trans ih_apply hdec
  exact this c rfl hsum

/-! ## Odd prime power + Theorem 5.1 helpers -/

/-- Odd prime power: `Q = p^k` for an odd prime `p` and `k > 0`. -/
def OddPrimePower (Q : ℕ) : Prop :=
  IsPrimePow Q ∧ Odd Q

theorem OddPrimePower.pos {Q : ℕ} (h : OddPrimePower Q) : 0 < Q :=
  h.1.pos

theorem OddPrimePower.odd {Q : ℕ} (h : OddPrimePower Q) : Odd Q :=
  h.2

theorem OddPrimePower.neZero {Q : ℕ} (h : OddPrimePower Q) : NeZero Q :=
  ⟨Nat.pos_iff_ne_zero.mp h.pos⟩

/-- Paper uses `S ≤ B/20`; with `0 < S` this forces `S < B`. -/
theorem S_lt_B_of_ratio {B S : ℕ} (_hB : 20 ≤ B) (hS0 : 0 < S) (hS : S * 20 ≤ B) :
    S < B := by
  have hmul : S < S * 20 := by
    cases S with
    | zero => cases hS0
    | succ S =>
      have : (S + 1) * 1 < (S + 1) * 20 :=
        Nat.mul_lt_mul_of_pos_left (by decide : 1 < 20) (Nat.succ_pos _)
      simpa using this
  exact lt_of_lt_of_le hmul hS

theorem S_le_Ndim (B S : ℕ) : S ≤ Ndim B S := by
  simp only [Ndim]; omega

theorem consecutiveInitial_mem_powersetCard {B S : ℕ}
    (hS : S ≤ Ndim B S) :
    consecutiveInitial (N := Ndim B S) S hS ∈
      (univ : Finset (Fin (Ndim B S))).powersetCard S := by
  rw [mem_powersetCard]
  exact ⟨subset_univ _, consecutiveInitial_card hS⟩

/-- `m^A_{Q,B}` is ≤ any card-`S` local layer. -/
theorem mAQ_le_ellAQ {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (I : Finset (Fin (Ndim B S))) (hI : I.card = S) :
    mAQ B S Q f ≤ ellAQ B S Q f I hI := by
  classical
  unfold mAQ
  set s :=
    ((univ : Finset (Fin (Ndim B S))).powersetCard S).image fun J =>
      if hJ : J.card = S then ellAQ B S Q f J hJ else 0
  have hmem : ellAQ B S Q f I hI ∈ s := by
    refine mem_image.mpr ⟨I, ?_, ?_⟩
    · rw [mem_powersetCard]; exact ⟨subset_univ _, hI⟩
    · simp [hI]
  have hne : s.Nonempty := ⟨_, hmem⟩
  simp only [hne, ↓reduceDIte]
  exact min'_le _ _ hmem

theorem mAQ_le_ellAQ_consecutive {B S Q : ℕ} (f : Fin S → Fin (S + 3))
    (hS : S ≤ Ndim B S) :
    mAQ B S Q f ≤
      ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S hS)
        (consecutiveInitial_card hS) :=
  mAQ_le_ellAQ f _ (consecutiveInitial_card hS)

/-! ## PROOF-B: expansion (5.16) -/

/-- Tail index set `{S,…,N−1}` as `Fin`s. -/
def tailFin (B S : ℕ) (hS : S ≤ Ndim B S) : Finset (Fin (Ndim B S)) :=
  (univ : Finset (Fin (Ndim B S))) \ consecutiveInitial (N := Ndim B S) S hS

theorem mem_tailFin_iff {B S : ℕ} (hS : S ≤ Ndim B S) (i : Fin (Ndim B S)) :
    i ∈ tailFin B S hS ↔ S ≤ i.val := by
  simp [tailFin, mem_sdiff, mem_consecutiveInitial_iff, not_lt]

theorem sum_univ_split_tail {B S : ℕ} (hS : S ≤ Ndim B S) (f : Fin (Ndim B S) → ℤ) :
    ∑ i : Fin (Ndim B S), f i =
      ∑ i ∈ consecutiveInitial (N := Ndim B S) S hS, f i +
        ∑ i ∈ tailFin B S hS, f i := by
  classical
  simp only [tailFin]
  have hJ : consecutiveInitial (N := Ndim B S) S hS ⊆ (univ : Finset (Fin (Ndim B S))) :=
    subset_univ _
  rw [← sum_sdiff hJ, add_comm]

/-- Paper (5.16). -/
theorem aQB_sub_ellAQ_consecutive {B S Q : ℕ} (hQ : 0 < Q)
    (hS : S ≤ Ndim B S) (f : Fin S → Fin (S + 3)) :
    aQB B S Q -
        ellAQ B S Q f (consecutiveInitial (N := Ndim B S) S hS)
          (consecutiveInitial_card hS) =
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) -
        (phiQ Q (2 * B) : ℤ) - (CAQ B S Q f : ℤ) - 2 * (phiQ Q S : ℤ) +
        ∑ i ∈ consecutiveInitial (N := Ndim B S) S hS,
          ((NKQ S Q i.val : ℤ) + (2 * indicatorQle Q i.val : ℤ) +
            (FNQ (Ndim B S) Q i.val : ℤ)) := by
  classical
  let J := consecutiveInitial (N := Ndim B S) S hS
  have hΦ : (∑ r ∈ range Q, (((nQr Q r J).choose 2) : ℤ)) = (phiQ Q S : ℤ) := by
    exact_mod_cast sum_choose_nQr_consecutive (N := Ndim B S) hQ hS
  have hsplit :=
    sum_univ_split_tail (B := B) (S := S) hS fun i => (NKQ B Q i.val : ℤ)
  set sumAll := ∑ i : Fin (Ndim B S), (NKQ B Q i.val : ℤ)
  set sumJ := ∑ i ∈ J, (NKQ B Q i.val : ℤ)
  set sumT := ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ)
  set sum2 := ∑ i ∈ J,
      ((NKQ S Q i.val : ℤ) + (2 * indicatorQle Q i.val : ℤ) +
        (FNQ (Ndim B S) Q i.val : ℤ))
  have hsplit' : sumAll = sumJ + sumT := hsplit
  have hlayer :
      ∑ i ∈ J,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ)) =
        2 * sumJ - sum2 := by
    have hterm : ∀ i ∈ J,
        (2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ) =
          (2 * NKQ B Q i.val : ℤ) -
            ((NKQ S Q i.val : ℤ) + (2 * indicatorQle Q i.val : ℤ) +
              (FNQ (Ndim B S) Q i.val : ℤ)) := fun _ _ => by ring
    simp only [sumJ, sum2, sum_congr rfl hterm, sum_sub_distrib, two_mul, mul_sum,
      sum_add_distrib]
    ring
  unfold aQB ellAQ
  simp only [Dref]
  change 2 * sumAll - (phiQ Q (2 * B) : ℤ) -
      ((CAQ B S Q f : ℤ) + 2 * ∑ r ∈ range Q, (((nQr Q r J).choose 2) : ℤ) +
        ∑ i ∈ J,
          ((2 * NKQ B Q i.val : ℤ) - (NKQ S Q i.val : ℤ) -
            (2 * indicatorQle Q i.val : ℤ) - (FNQ (Ndim B S) Q i.val : ℤ))) =
      2 * sumT - (phiQ Q (2 * B) : ℤ) - (CAQ B S Q f : ℤ) - 2 * (phiQ Q S : ℤ) + sum2
  rw [hsplit', hΦ, hlayer]
  ring

theorem second_line_nonneg {B S Q : ℕ} (hS : S ≤ Ndim B S) :
    (0 : ℤ) ≤
      ∑ i ∈ consecutiveInitial (N := Ndim B S) S hS,
        ((NKQ S Q i.val : ℤ) + (2 * indicatorQle Q i.val : ℤ) +
          (FNQ (Ndim B S) Q i.val : ℤ)) := by
  refine sum_nonneg fun _ _ => by positivity

/-! ## PROOF-C: (5.17) -/

theorem phiQ_mono {Q m n : ℕ} (h : m ≤ n) : phiQ Q m ≤ phiQ Q n := by
  have h' : m + (n - m) = n := Nat.add_sub_of_le h
  simp only [phiQ]
  rw [← h', sum_range_add]
  exact Nat.le_add_right _ _

theorem phiQ_sum_Ico {Q a b : ℕ} (h : a ≤ b) :
    phiQ Q b = phiQ Q a + ∑ k ∈ Ico a b, k / Q := by
  simp only [phiQ]
  have hdisj : Disjoint (range a) (Ico a b) :=
    disjoint_left.mpr fun x hx hx' => by
      have : x < a := mem_range.mp hx
      have : a ≤ x := (mem_Ico.mp hx').1
      omega
  have hunion : range b = range a ∪ Ico a b := by
    ext x
    simp only [mem_union, mem_range, mem_Ico]
    constructor
    · intro hx
      by_cases hxa : x < a
      · exact Or.inl hxa
      · exact Or.inr ⟨le_of_not_gt hxa, hx⟩
    · rintro (hxa | ⟨_, hxb⟩) <;> omega
  rw [hunion, sum_union hdisj]

theorem phiQ_sub_eq_sum_Ico {Q a b : ℕ} (h : a ≤ b) :
    phiQ Q b - phiQ Q a = ∑ k ∈ Ico a b, k / Q := by
  have := phiQ_sum_Ico (Q := Q) h
  omega

theorem injective_f_add {B S : ℕ} {f : Fin S → Fin (S + 3)} (hf : Injective f) :
    Injective fun α : Fin S => (f α).val + 2 * B :=
  fun _ _ h => hf (Fin.ext (Nat.add_right_cancel h))

/-- Paper (5.17): needs injective `f`. -/
theorem phiQ_add_CAQ_le_phiQ_N {B S Q : ℕ}
    (f : Fin S → Fin (S + 3)) (hf : Injective f) :
    (phiQ Q (2 * B) : ℤ) + (CAQ B S Q f : ℤ) ≤ phiQ Q (Ndim B S) := by
  classical
  have h2B : 2 * B ≤ Ndim B S := by simp [Ndim]; omega
  let s : Finset ℕ := (univ : Finset (Fin S)).image fun α => (f α).val + 2 * B
  have hinj := injective_f_add (B := B) hf
  have hsub : s ⊆ Ico (2 * B) (Ndim B S) := by
    intro x hx
    rcases mem_image.mp hx with ⟨α, _, rfl⟩
    refine mem_Ico.mpr ⟨Nat.le_add_left _ _, ?_⟩
    have : (f α).val < S + 3 := (f α).isLt
    simp only [Ndim]; omega
  have hCAQ : CAQ B S Q f = ∑ k ∈ s, k / Q := by
    unfold CAQ
    rw [sum_image (g := fun α => (f α).val + 2 * B)]
    intro α _ β _ h; exact hinj h
  have hle : ∑ k ∈ s, k / Q ≤ ∑ k ∈ Ico (2 * B) (Ndim B S), k / Q :=
    sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _
  have hΦ : phiQ Q (Ndim B S) - phiQ Q (2 * B) =
      ∑ k ∈ Ico (2 * B) (Ndim B S), k / Q :=
    phiQ_sub_eq_sum_Ico (Q := Q) h2B
  have hle' : CAQ B S Q f ≤ phiQ Q (Ndim B S) - phiQ Q (2 * B) := by
    rwa [← hCAQ, ← hΦ] at hle
  have : (CAQ B S Q f : ℤ) ≤
      (phiQ Q (Ndim B S) : ℤ) - (phiQ Q (2 * B) : ℤ) := by
    rw [← Nat.cast_sub (phiQ_mono h2B)]
    exact_mod_cast hle'
  linarith

theorem phiQ_superadditive (Q a b : ℕ) :
    phiQ Q a + phiQ Q b ≤ phiQ Q (a + b) := by
  simp only [phiQ]
  have hsplit := sum_range_add (fun k => k / Q) a b
  have hsum : ∑ k ∈ range b, k / Q ≤ ∑ k ∈ range b, (a + k) / Q :=
    sum_le_sum fun k _ => Nat.div_le_div_right (Nat.le_add_left _ _)
  linarith [hsplit, hsum]

/-! ## PROOF-D: exact `NKQ`/`sumT` reduction to `phiQ` (toward (KI)) -/

private theorem block_div {Q : ℕ} (hQ : 0 < Q) (q c : ℕ) (hc : c < Q) :
    (q * Q + c) / Q = q := by
  rw [Nat.mul_comm, Nat.mul_add_div hQ, Nat.div_eq_of_lt hc, add_zero]

/-- Exactly one representative `k*Q+r` (`k < q`) per full block. -/
private theorem card_range_mul_filter_mod {Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) (q : ℕ) :
    ((range (q * Q)).filter (fun j => j % Q = r)).card = q := by
  classical
  have hinj : Function.Injective (fun k : Fin q => k.val * Q + r) := by
    intro a b h
    simp only at h
    have hval : a.val * Q = b.val * Q := by omega
    exact Fin.ext (Nat.eq_of_mul_eq_mul_right hQ hval)
  let g : Fin q ↪ ℕ := ⟨fun k => k.val * Q + r, hinj⟩
  have himg : (range (q * Q)).filter (fun j => j % Q = r) = (univ : Finset (Fin q)).map g := by
    ext j
    simp only [mem_filter, mem_range, mem_map, mem_univ, true_and, g,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨hjlt, hjmod⟩
      refine ⟨⟨j / Q, ?_⟩, ?_⟩
      · by_contra hge
        have hle : q ≤ j / Q := Nat.le_of_not_lt hge
        have hqQ : q * Q ≤ (j / Q) * Q := Nat.mul_le_mul_right Q hle
        have hdm : (j / Q) * Q ≤ j := Nat.div_mul_le_self j Q
        omega
      · change (j / Q) * Q + r = j
        rw [← hjmod, Nat.div_add_mod' j Q]
    · rintro ⟨k, rfl⟩
      refine ⟨?_, ?_⟩
      · have hklt : k.val < q := k.isLt
        calc k.val * Q + r < k.val * Q + Q := by omega
          _ = (k.val + 1) * Q := by ring
          _ ≤ q * Q := Nat.mul_le_mul_right Q hklt
      · show (k.val * Q + r) % Q = r
        rw [Nat.mul_comm, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hr]
  rw [himg, card_map, card_univ, Fintype.card_fin]

private theorem card_range_filter_mod_lt {Q r ρ : ℕ} (hr : r < Q) (hρ : ρ < Q) :
    ((range ρ).filter (fun j => j % Q = r)).card = (if r < ρ then 1 else 0) := by
  classical
  have heq : (range ρ).filter (fun j => j % Q = r) = if r < ρ then {r} else ∅ := by
    split_ifs with h
    · ext j
      simp only [mem_filter, mem_range, mem_singleton]
      constructor
      · rintro ⟨hjρ, hjmod⟩
        have hjQ : j < Q := lt_trans hjρ hρ
        rwa [Nat.mod_eq_of_lt hjQ] at hjmod
      · rintro rfl
        exact ⟨h, Nat.mod_eq_of_lt hr⟩
    · ext j
      simp only [mem_filter, mem_range, not_lt] at *
      constructor
      · rintro ⟨hjρ, hjmod⟩
        have hjQ : j < Q := lt_trans hjρ hρ
        rw [Nat.mod_eq_of_lt hjQ] at hjmod
        omega
      · simp
  rw [heq]
  split_ifs <;> simp

/-- Exact closed form: number of `j < n` with `j % Q = r` equals `(n + Q - 1 - r) / Q`. -/
private theorem card_range_filter_mod_eq {Q r : ℕ} (hQ : 0 < Q) (hr : r < Q) (n : ℕ) :
    ((range n).filter (fun j => j % Q = r)).card = (n + Q - 1 - r) / Q := by
  classical
  set q := n / Q with hqdef
  set ρ := n % Q with hρdef
  have hn : n = q * Q + ρ := (Nat.div_add_mod' n Q).symm
  have hρQ : ρ < Q := Nat.mod_lt n hQ
  have hle1 : (0 : ℕ) ≤ q * Q := Nat.zero_le _
  have hle2 : q * Q ≤ n := by rw [hn]; omega
  have hsplit : range n = range (q * Q) ∪ Ico (q * Q) n := by
    rw [range_eq_Ico, range_eq_Ico, Finset.Ico_union_Ico_eq_Ico hle1 hle2]
  have hdisj : Disjoint (range (q * Q)) (Ico (q * Q) n) := by
    rw [range_eq_Ico]
    exact Finset.Ico_disjoint_Ico_consecutive 0 (q * Q) n
  have hcardsplit :
      ((range n).filter (fun j => j % Q = r)).card =
        ((range (q * Q)).filter (fun j => j % Q = r)).card +
          ((Ico (q * Q) n).filter (fun j => j % Q = r)).card := by
    rw [hsplit, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
  have hinj2 : Function.Injective (fun k : ℕ => q * Q + k) := by
    intro a b h
    simpa using h
  let g2 : ℕ ↪ ℕ := ⟨fun k => q * Q + k, hinj2⟩
  have hshift :
      (Ico (q * Q) n).filter (fun j => j % Q = r) =
        ((range ρ).filter (fun j => j % Q = r)).map g2 := by
    ext j
    simp only [mem_filter, mem_Ico, mem_map, mem_range, g2, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨h1, h2⟩, hmod⟩
      refine ⟨j - q * Q, ⟨by omega, ?_⟩, by omega⟩
      have hcomm : q * Q + (j - q * Q) = Q * q + (j - q * Q) := by ring
      have hj : j = q * Q + (j - q * Q) := by omega
      rw [hj, hcomm, Nat.mul_add_mod_self_left] at hmod
      exact hmod
    · rintro ⟨k, ⟨hk, hkmod⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have hcomm : q * Q + k = Q * q + k := by ring
      rw [hcomm, Nat.mul_add_mod_self_left]
      exact hkmod
  have hcard2 : ((Ico (q * Q) n).filter (fun j => j % Q = r)).card =
      ((range ρ).filter (fun j => j % Q = r)).card := by
    rw [hshift, card_map]
  rw [hcardsplit, card_range_mul_filter_mod hQ hr, hcard2, card_range_filter_mod_lt hr hρQ]
  rcases lt_or_ge r ρ with h | h
  · simp only [h, if_true]
    have hrw : n + Q - 1 - r = (q + 1) * Q + (ρ - 1 - r) := by rw [hn]; ring_nf; omega
    rw [hrw, block_div hQ (q + 1) (ρ - 1 - r) (by omega)]
  · simp only [not_lt.mpr h, if_false]
    have hrw : n + Q - 1 - r = q * Q + (ρ + Q - 1 - r) := by rw [hn]; omega
    rw [hrw, block_div hQ q (ρ + Q - 1 - r) (by omega)]
    omega

/-- The "center" residue: for `Q` odd, `2j+1 ≡ 0 (mod Q) ↔ j ≡ r0Q Q (mod Q)`. -/
def r0Q (Q : ℕ) : ℕ := (Q - 1) / 2

theorem two_mul_r0Q {Q : ℕ} (hodd : Odd Q) : 2 * r0Q Q + 1 = Q := by
  obtain ⟨k, hk⟩ := hodd
  simp [r0Q, hk]

theorem r0Q_lt {Q : ℕ} (hQ : 0 < Q) : r0Q Q < Q := by
  unfold r0Q; omega

theorem dvd_two_add_one_iff {Q j : ℕ} (hQ : 0 < Q) (hodd : Odd Q) :
    Q ∣ 2 * j + 1 ↔ j % Q = r0Q Q := by
  have hqr := two_mul_r0Q (Q := Q) hodd
  have hcop : Nat.gcd Q 2 = 1 := (Nat.coprime_two_left.mpr hodd).symm
  constructor
  · intro hdvd
    have h1 : (2 * j + 1) ≡ 0 [MOD Q] := (Nat.modEq_zero_iff_dvd).mpr hdvd
    have h2 : (2 * j + 1) ≡ (2 * r0Q Q + 1) [MOD Q] := by
      rw [hqr]; exact h1.trans (Nat.modEq_zero_iff_dvd.mpr ⟨1, by omega⟩).symm
    have h3 : 2 * j ≡ 2 * r0Q Q [MOD Q] := h2.add_right_cancel' 1
    have h4 : j ≡ r0Q Q [MOD Q] := h3.cancel_left_of_coprime hcop
    unfold Nat.ModEq at h4
    rw [h4, Nat.mod_eq_of_lt (r0Q_lt hQ)]
  · intro hmod
    have h4 : j ≡ r0Q Q [MOD Q] := by
      unfold Nat.ModEq
      rw [hmod, Nat.mod_eq_of_lt (r0Q_lt hQ)]
    have h3 : 2 * j ≡ 2 * r0Q Q [MOD Q] := h4.mul_left 2
    have h2 : (2 * j + 1) ≡ (2 * r0Q Q + 1) [MOD Q] := h3.add_right 1
    rw [hqr] at h2
    exact Nat.modEq_zero_iff_dvd.mp (h2.trans (Nat.modEq_zero_iff_dvd.mpr dvd_rfl))

/-- `Ψ_Q(n) := #{j < n : j % Q = r0Q Q}` (count of `j < n` on the "center" residue). -/
def PsiQ (Q n : ℕ) : ℕ := ((range n).filter (fun j => j % Q = r0Q Q)).card

theorem PsiQ_eq {Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (n : ℕ) :
    PsiQ Q n = (n + r0Q Q) / Q := by
  unfold PsiQ
  rw [card_range_filter_mod_eq hQ (r0Q_lt hQ) n]
  have hqr := two_mul_r0Q (Q := Q) hodd
  congr 1
  omega

theorem PsiQ_mono {Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) {m n : ℕ} (h : m ≤ n) :
    PsiQ Q m ≤ PsiQ Q n := by
  rw [PsiQ_eq hQ hodd, PsiQ_eq hQ hodd]
  exact Nat.div_le_div_right (by omega)

theorem PsiQ_sub_eq_card_Ico {Q a b : ℕ} (hab : a ≤ b) :
    PsiQ Q b - PsiQ Q a = ((Ico a b).filter (fun j => j % Q = r0Q Q)).card := by
  classical
  unfold PsiQ
  have hsplit : range b = range a ∪ Ico a b := by
    rw [range_eq_Ico, range_eq_Ico, Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) hab]
  have hdisj : Disjoint (range a) (Ico a b) := by
    rw [range_eq_Ico]; exact Finset.Ico_disjoint_Ico_consecutive 0 a b
  have : ((range b).filter (fun j => j % Q = r0Q Q)).card =
      ((range a).filter (fun j => j % Q = r0Q Q)).card +
        ((Ico a b).filter (fun j => j % Q = r0Q Q)).card := by
    rw [hsplit, filter_union, card_union_of_disjoint (disjoint_filter_filter hdisj)]
  omega

/-- Exact formula for `NKQ` in terms of `PsiQ` shifted evaluations. This is the paper's
"residue engine" identity: `NKQ K Q i` counts `h ∈ [1,K]` on the center residue, which is
exactly a window-difference of `PsiQ`. -/
theorem NKQ_eq_PsiQ_sub {Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (K i : ℕ) :
    NKQ K Q i = PsiQ Q (i + K + 1) - PsiQ Q (i + 1) := by
  classical
  have hbij : Function.Injective (fun h : ℕ => i + h) := fun a b h => by
    simpa using h
  have himg : ((Icc 1 K).filter (fun h => Q ∣ 2 * i + 2 * h + 1)).image (fun h => i + h) =
      (Ico (i + 1) (i + K + 1)).filter (fun j => j % Q = r0Q Q) := by
    ext j
    simp only [mem_image, mem_filter, mem_Icc, mem_Ico]
    constructor
    · rintro ⟨h, ⟨⟨h1, h2⟩, hdvd⟩, rfl⟩
      refine ⟨⟨by omega, by omega⟩, ?_⟩
      have heq : 2 * i + 2 * h + 1 = 2 * (i + h) + 1 := by ring
      rw [heq] at hdvd
      exact (dvd_two_add_one_iff hQ hodd).mp hdvd
    · rintro ⟨⟨hj1, hj2⟩, hjmod⟩
      refine ⟨j - i, ⟨⟨by omega, by omega⟩, ?_⟩, by omega⟩
      have heq2 : 2 * i + 2 * (j - i) + 1 = 2 * j + 1 := by omega
      rw [heq2, dvd_two_add_one_iff hQ hodd]
      exact hjmod
  have hcard : NKQ K Q i =
      ((Ico (i + 1) (i + K + 1)).filter (fun j => j % Q = r0Q Q)).card := by
    unfold NKQ
    rw [← himg, card_image_of_injective _ hbij]
  rw [hcard, PsiQ_sub_eq_card_Ico (by omega)]

theorem PsiQ_shift_sum {Q c a b : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (hab : a ≤ b) :
    ∑ i ∈ Ico a b, PsiQ Q (i + c) = phiQ Q (b + c + r0Q Q) - phiQ Q (a + c + r0Q Q) := by
  classical
  have hpt : ∀ i, PsiQ Q (i + c) = (i + (c + r0Q Q)) / Q := by
    intro i
    rw [PsiQ_eq hQ hodd]
    congr 1; omega
  simp_rw [hpt]
  rw [Finset.sum_Ico_add' (fun k => k / Q) a b (c + r0Q Q)]
  have heq := phiQ_sub_eq_sum_Ico (Q := Q) (a := a + (c + r0Q Q)) (b := b + (c + r0Q Q))
    (by omega)
  rw [← heq]
  congr 2 <;> omega

/-- Exact formula for `sumT` (the paper's `∑ NKQ` over the tail block) in terms of `phiQ`
alone: this replaces the "convolution/trapezoid" identity anticipated in
`docs/THM51-REDUCTION-NOTES.md` with a closed form built entirely from `phiQ`. -/
theorem sum_NKQ_tail_eq {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q) (hS : S ≤ Ndim B S) :
    (∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ)) =
      (phiQ Q (Ndim B S + (B + 1) + r0Q Q) : ℤ)
        - (phiQ Q (S + (B + 1) + r0Q Q) : ℤ)
        - (phiQ Q (Ndim B S + 1 + r0Q Q) : ℤ)
        + (phiQ Q (S + 1 + r0Q Q) : ℤ) := by
  classical
  have himg : (tailFin B S hS).image Fin.val = Ico S (Ndim B S) := by
    ext j
    simp only [mem_image, mem_Ico]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have := (mem_tailFin_iff (B := B) (S := S) hS i).mp hi
      exact ⟨this, i.isLt⟩
    · rintro ⟨hj1, hj2⟩
      exact ⟨⟨j, hj2⟩, (mem_tailFin_iff (B := B) (S := S) hS ⟨j, hj2⟩).mpr hj1, rfl⟩
  have hreindex : ∀ (g : ℕ → ℤ), ∑ i ∈ tailFin B S hS, g i.val = ∑ j ∈ Ico S (Ndim B S), g j := by
    intro g
    rw [← himg, sum_image]
    intro a _ b _ h
    exact Fin.ext h
  have hNKQeq : ∀ i : ℕ, (NKQ B Q i : ℤ) =
      (PsiQ Q (i + B + 1) : ℤ) - (PsiQ Q (i + 1) : ℤ) := by
    intro i
    have hnkq := NKQ_eq_PsiQ_sub hQ hodd B i
    have hmono : PsiQ Q (i + 1) ≤ PsiQ Q (i + B + 1) :=
      PsiQ_mono hQ hodd (by omega)
    rw [hnkq]
    push_cast [Nat.cast_sub hmono]
    ring
  rw [hreindex (fun i => (NKQ B Q i : ℤ))]
  simp_rw [hNKQeq]
  rw [sum_sub_distrib]
  have h1 : ∑ i ∈ Ico S (Ndim B S), (PsiQ Q (i + B + 1) : ℤ) =
      ((phiQ Q (Ndim B S + (B + 1) + r0Q Q) - phiQ Q (S + (B + 1) + r0Q Q) : ℕ) : ℤ) := by
    have hshift := PsiQ_shift_sum (Q := Q) (c := B + 1) (a := S) (b := Ndim B S) hQ hodd
      (S_le_Ndim B S)
    rw [← hshift]
    push_cast
    rfl
  have h2 : ∑ i ∈ Ico S (Ndim B S), (PsiQ Q (i + 1) : ℤ) =
      ((phiQ Q (Ndim B S + 1 + r0Q Q) - phiQ Q (S + 1 + r0Q Q) : ℕ) : ℤ) := by
    have hshift := PsiQ_shift_sum (Q := Q) (c := 1) (a := S) (b := Ndim B S) hQ hodd
      (S_le_Ndim B S)
    rw [← hshift]
    push_cast
    apply Finset.sum_congr rfl
    intro i _
    norm_num
  rw [h1, h2]
  have hmono1 : phiQ Q (S + (B + 1) + r0Q Q) ≤ phiQ Q (Ndim B S + (B + 1) + r0Q Q) :=
    phiQ_mono (by simp only [Ndim]; omega)
  have hmono2 : phiQ Q (S + 1 + r0Q Q) ≤ phiQ Q (Ndim B S + 1 + r0Q Q) :=
    phiQ_mono (by simp only [Ndim]; omega)
  push_cast [Nat.cast_sub hmono1, Nat.cast_sub hmono2]
  ring

/-! ## PROOF-E: partial progress toward (KI) — two concrete `Q` regimes

`sum_NKQ_tail_ge` (KI) is not proved for all `Q`. The two lemmas below cover
disjoint concrete regimes (`Q` large enough that everything is trivially `0`,
and `Q ≤ B`), each fully proved; the gap `B < Q < 2 * Ndim B S + 2 * B` is
open. See `docs/THM51-REDUCTION-NOTES.md` for the analysis. -/

/-- Case A: `Q` large enough that no `2i+2h+1` in the relevant range can be a
multiple of `Q`, so `NKQ` vanishes identically. -/
theorem NKQ_eq_zero_of_Q_large {K Q i : ℕ} (h : 2 * i + 2 * K + 1 < Q) :
    NKQ K Q i = 0 := by
  unfold NKQ
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro hh hhmem hdvd
  have h2 : hh ≤ K := (mem_Icc.mp hhmem).2
  have hbound : 2 * i + 2 * hh + 1 < Q := by omega
  have hpos : 0 < 2 * i + 2 * hh + 1 := by omega
  have := Nat.le_of_dvd hpos hdvd
  omega

/-- (KI), regime A: `Q` large enough that both sides are trivially `0`. -/
theorem sum_NKQ_tail_ge_of_Q_large {B S Q : ℕ} (hS : S ≤ Ndim B S)
    (hQ : 2 * Ndim B S + 2 * B ≤ Q) :
    (phiQ Q (Ndim B S) : ℤ) + 2 * (phiQ Q S : ℤ) ≤
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) := by
  have hzero : ∀ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) = 0 := by
    intro i _
    have hilt : i.val < Ndim B S := i.isLt
    have : NKQ B Q i.val = 0 := NKQ_eq_zero_of_Q_large (by omega)
    exact_mod_cast this
  have hsum0 : ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) = 0 :=
    Finset.sum_eq_zero hzero
  have hN0 : phiQ Q (Ndim B S) = 0 := phiQ_of_lt (by omega)
  have hS0 : phiQ Q S = 0 := phiQ_of_lt (by omega)
  rw [hsum0, hN0, hS0]
  norm_num

/-- `phiQ_sub_quadratic_le`, cleared of the `Q`-denominator: `8Q·φ ≤ 4n²-4nQ+Q²`. -/
theorem phiQ_poly_le {Q n : ℕ} (hQ : 0 < Q) :
    8 * (Q : ℚ) * phiQ Q n ≤ 4 * (n : ℚ) * n - 4 * n * Q + Q * Q := by
  have hn : n = (n / Q) * Q + n % Q := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hr : n % Q < Q := Nat.mod_lt n hQ
  have heq := phiQ_sub_quadratic_eq (Q := Q) (n := n) (q := n / Q) (r := n % Q) hQ hr hn
  set r := n % Q
  have hQQ : (0 : ℚ) < Q := Nat.cast_pos.mpr hQ
  have hAM : (4 : ℤ) * (r : ℤ) * ((Q : ℤ) - (r : ℤ)) ≤ (Q : ℤ) ^ 2 := by
    nlinarith [sq_nonneg (2 * (r : ℤ) - (Q : ℤ))]
  have hAMQ : (4 : ℚ) * (r : ℚ) * ((Q : ℚ) - (r : ℚ)) ≤ (Q : ℚ) ^ 2 := by exact_mod_cast hAM
  have hQne : (Q : ℚ) ≠ 0 := ne_of_gt hQQ
  field_simp at heq
  nlinarith [heq, hAMQ]

/-- `phiQ_sub_quadratic_nonneg`, cleared of the `Q`-denominator: `4n²-4nQ ≤ 8Q·φ`. -/
theorem phiQ_poly_ge {Q n : ℕ} (hQ : 0 < Q) :
    4 * (n : ℚ) * n - 4 * n * Q ≤ 8 * (Q : ℚ) * phiQ Q n := by
  have hn : n = (n / Q) * Q + n % Q := by rw [Nat.mul_comm, Nat.div_add_mod]
  have hr : n % Q < Q := Nat.mod_lt n hQ
  have heq := phiQ_sub_quadratic_eq (Q := Q) (n := n) (q := n / Q) (r := n % Q) hQ hr hn
  set r := n % Q
  have hQQ : (0 : ℚ) < Q := Nat.cast_pos.mpr hQ
  have hrnn : (0 : ℚ) ≤ (r : ℚ) := Nat.cast_nonneg r
  have hrQ : (r : ℚ) ≤ (Q : ℚ) := by exact_mod_cast le_of_lt hr
  have hQne : (Q : ℚ) ≠ 0 := ne_of_gt hQQ
  field_simp at heq
  nlinarith [heq, mul_nonneg hrnn (sub_nonneg.mpr hrQ)]

set_option maxHeartbeats 4000000 in
-- The 6-term phiQ-polynomial combination below has large enough symbolic
-- expressions (before `ring_nf` normalizes them) to exceed the default budget.
/-- (KI), regime B: `Q ≤ B` (a conservative sub-case of the paper's "small `Q`"
range). Uses the exact `sum_NKQ_tail_eq` formula plus the crude `Corr(n) ≤ Q/8`
bound (`phiQ_sub_quadratic_le`), which is only sufficient once `Q` is capped
this tightly relative to `B`; see the reduction notes for why the naive bound
is NOT sufficient for `Q` up to the paper's full range. -/
theorem sum_NKQ_tail_ge_of_Q_small {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q)
    (hB : 20 ≤ B) (hSB : S * 20 ≤ B)
    (hS : S ≤ Ndim B S)
    (hbracket : Q ≤ B) :
    (phiQ Q (Ndim B S) : ℤ) + 2 * (phiQ Q S : ℤ) ≤
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) := by
  rw [sum_NKQ_tail_eq hQ hodd hS]
  have hNv : (Ndim B S : ℚ) = 2 * (B : ℚ) + S + 3 := by
    simp only [Ndim]; push_cast; ring
  have hQQ : (0 : ℚ) < Q := Nat.cast_pos.mpr hQ
  have hN_le := phiQ_poly_le (Q := Q) (n := Ndim B S) hQ
  have hS_le := phiQ_poly_le (Q := Q) (n := S) hQ
  have hA1_ge := phiQ_poly_ge (Q := Q) (n := Ndim B S + (B + 1) + r0Q Q) hQ
  have hA2_le := phiQ_poly_le (Q := Q) (n := S + (B + 1) + r0Q Q) hQ
  have hA3_le := phiQ_poly_le (Q := Q) (n := Ndim B S + 1 + r0Q Q) hQ
  have hA4_ge := phiQ_poly_ge (Q := Q) (n := S + 1 + r0Q Q) hQ
  have hqr := two_mul_r0Q (Q := Q) hodd
  have hqrQ : (2 : ℚ) * (r0Q Q : ℚ) + 1 = Q := by exact_mod_cast hqr
  have key : (phiQ Q (Ndim B S) : ℚ) + 2 * (phiQ Q S : ℚ) ≤
      2 * ((phiQ Q (Ndim B S + (B + 1) + r0Q Q) : ℚ)
        - (phiQ Q (S + (B + 1) + r0Q Q) : ℚ)
        - (phiQ Q (Ndim B S + 1 + r0Q Q) : ℚ)
        + (phiQ Q (S + 1 + r0Q Q) : ℚ)) := by
    have hA1v : ((Ndim B S + (B + 1) + r0Q Q : ℕ) : ℚ) =
        (Ndim B S : ℚ) + B + 1 + r0Q Q := by push_cast; ring
    have hA2v : ((S + (B + 1) + r0Q Q : ℕ) : ℚ) = (S : ℚ) + B + 1 + r0Q Q := by
      push_cast; ring
    have hA3v : ((Ndim B S + 1 + r0Q Q : ℕ) : ℚ) = (Ndim B S : ℚ) + 1 + r0Q Q := by
      push_cast; ring
    have hA4v : ((S + 1 + r0Q Q : ℕ) : ℚ) = (S : ℚ) + 1 + r0Q Q := by push_cast; ring
    rw [hA1v] at hA1_ge
    rw [hA2v] at hA2_le
    rw [hA3v] at hA3_le
    rw [hA4v] at hA4_ge
    rw [hNv] at hN_le hA1_ge hA3_le
    -- Step 1: combine the two "upper" bounds (N, S) into a single Q*phiQ bound.
    have hLHS : 8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S ≤
        (4 * (2 * (B:ℚ) + S + 3) * (2 * (B:ℚ) + S + 3) - 4 * (2 * (B:ℚ) + S + 3) * Q + Q * Q)
          + 2 * (4 * (S:ℚ) * S - 4 * S * Q + Q * Q) := by
      linarith [hN_le, hS_le]
    -- Step 2: combine the four "tail" bounds (A1..A4) into a single Q*phiQ bound.
    have hRHS :
        2 * (4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * Q)
          - 2 * (4 * ((S:ℚ) + B + 1 + r0Q Q) * ((S:ℚ) + B + 1 + r0Q Q)
              - 4 * ((S:ℚ) + B + 1 + r0Q Q) * Q + Q * Q)
          - 2 * (4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * Q + Q * Q)
          + 2 * (4 * ((S:ℚ) + 1 + r0Q Q) * ((S:ℚ) + 1 + r0Q Q) - 4 * ((S:ℚ) + 1 + r0Q Q) * Q)
        ≤ 16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
          - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
          - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
          + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) := by
      linarith [hA1_ge, hA2_le, hA3_le, hA4_ge]
    -- Step 3: the pure polynomial inequality (no phiQ), where the ratio hypothesis bites.
    have hPure :
        (4 * (2 * (B:ℚ) + S + 3) * (2 * (B:ℚ) + S + 3) - 4 * (2 * (B:ℚ) + S + 3) * Q + Q * Q)
          + 2 * (4 * (S:ℚ) * S - 4 * S * Q + Q * Q) ≤
        2 * (4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * Q)
          - 2 * (4 * ((S:ℚ) + B + 1 + r0Q Q) * ((S:ℚ) + B + 1 + r0Q Q)
              - 4 * ((S:ℚ) + B + 1 + r0Q Q) * Q + Q * Q)
          - 2 * (4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * Q + Q * Q)
          + 2 * (4 * ((S:ℚ) + 1 + r0Q Q) * ((S:ℚ) + 1 + r0Q Q) - 4 * ((S:ℚ) + 1 + r0Q Q) * Q) := by
      have hBQ : (20 : ℚ) ≤ B := by exact_mod_cast hB
      have hSBQ : (S : ℚ) * 20 ≤ B := by exact_mod_cast hSB
      have hbracketQ : (Q : ℚ) ≤ B := by exact_mod_cast hbracket
      have hrnn : (0 : ℚ) ≤ r0Q Q := Nat.cast_nonneg _
      have hQnn : (0 : ℚ) ≤ Q := Nat.cast_nonneg _
      have hQB2 : (Q : ℚ) * Q ≤ (B : ℚ) * B := by nlinarith [hbracketQ, hQnn]
      have hstep : (0:ℚ) ≤ 7 * ((B:ℚ)*B - (Q:ℚ)*Q) := by nlinarith [hQB2]
      have hrterm : (0:ℚ) ≤ (16*(B:ℚ)+24*S+24) * r0Q Q := by positivity
      have hBnn : (0:ℚ) ≤ B := by positivity
      have hSnn : (0:ℚ) ≤ S := by positivity
      have hd : (0:ℚ) ≤ B - 20 * S := by linarith [hSBQ]
      have h1 : (0:ℚ) ≤ B * B - 20 * (B * S) := by nlinarith [mul_nonneg hBnn hd]
      have h2 : (0:ℚ) ≤ B * B - 400 * (S * S) := by
        nlinarith [mul_nonneg hd (by linarith [hSBQ] : (0:ℚ) ≤ B + 20 * S)]
      have hrem : 16 * (B:ℚ) * S - 9 * B * B + 12 * S + 12 * S * S - 8 * B + 24 ≤ 0 := by
        nlinarith [h1, h2, hBQ, hSBQ]
      rw [← hqrQ] at hstep ⊢
      ring_nf
      ring_nf at hstep hrterm hrem
      linarith [hstep, hrterm, hrem]
    have hchain :
        8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S ≤
          16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
            + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) :=
      le_trans hLHS (le_trans hPure hRHS)
    have h8Q : (0 : ℚ) < 8 * Q := by positivity
    have heqL : 8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S =
        8 * (Q : ℚ) * ((phiQ Q (Ndim B S) : ℚ) + 2 * (phiQ Q S : ℚ)) := by ring
    have heqR :
        16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
            + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) =
        8 * (Q : ℚ) * (2 * ((phiQ Q (Ndim B S + (B + 1) + r0Q Q) : ℚ)
          - (phiQ Q (S + (B + 1) + r0Q Q) : ℚ)
          - (phiQ Q (Ndim B S + 1 + r0Q Q) : ℚ)
          + (phiQ Q (S + 1 + r0Q Q) : ℚ))) := by ring
    rw [heqL, heqR] at hchain
    exact le_of_mul_le_mul_left hchain h8Q
  exact_mod_cast key

set_option maxHeartbeats 4000000 in
-- Same symbolic-size concern as `sum_NKQ_tail_ge_of_Q_small` above.
/-- (KI), regime B extended: `Q ≤ 2 * B` (a wider "small `Q`" range than
`sum_NKQ_tail_ge_of_Q_small`). Same proof skeleton (`sum_NKQ_tail_eq` plus the
crude `Corr(n) ≤ Q/8` bound), but the pure-polynomial step now needs the sharper
fact that the four `A1..A2..A3..A4` quadratic terms combine to a value
independent of `r0Q Q`, reducing the target to a quadratic-in-`Q` inequality on
`[0, 2*B]` which is checked via its (concave) endpoint values at `Q = 0` and
`Q = 2 * B`. -/
theorem sum_NKQ_tail_ge_of_Q_le_2B {B S Q : ℕ} (hQ : 0 < Q) (hodd : Odd Q)
    (hB : 20 ≤ B) (hSB : S * 20 ≤ B)
    (hS : S ≤ Ndim B S)
    (hbracket : Q ≤ 2 * B) :
    (phiQ Q (Ndim B S) : ℤ) + 2 * (phiQ Q S : ℤ) ≤
      2 * ∑ i ∈ tailFin B S hS, (NKQ B Q i.val : ℤ) := by
  rw [sum_NKQ_tail_eq hQ hodd hS]
  have hNv : (Ndim B S : ℚ) = 2 * (B : ℚ) + S + 3 := by
    simp only [Ndim]; push_cast; ring
  have hQQ : (0 : ℚ) < Q := Nat.cast_pos.mpr hQ
  have hN_le := phiQ_poly_le (Q := Q) (n := Ndim B S) hQ
  have hS_le := phiQ_poly_le (Q := Q) (n := S) hQ
  have hA1_ge := phiQ_poly_ge (Q := Q) (n := Ndim B S + (B + 1) + r0Q Q) hQ
  have hA2_le := phiQ_poly_le (Q := Q) (n := S + (B + 1) + r0Q Q) hQ
  have hA3_le := phiQ_poly_le (Q := Q) (n := Ndim B S + 1 + r0Q Q) hQ
  have hA4_ge := phiQ_poly_ge (Q := Q) (n := S + 1 + r0Q Q) hQ
  have hqr := two_mul_r0Q (Q := Q) hodd
  have hqrQ : (2 : ℚ) * (r0Q Q : ℚ) + 1 = Q := by exact_mod_cast hqr
  have key : (phiQ Q (Ndim B S) : ℚ) + 2 * (phiQ Q S : ℚ) ≤
      2 * ((phiQ Q (Ndim B S + (B + 1) + r0Q Q) : ℚ)
        - (phiQ Q (S + (B + 1) + r0Q Q) : ℚ)
        - (phiQ Q (Ndim B S + 1 + r0Q Q) : ℚ)
        + (phiQ Q (S + 1 + r0Q Q) : ℚ)) := by
    have hA1v : ((Ndim B S + (B + 1) + r0Q Q : ℕ) : ℚ) =
        (Ndim B S : ℚ) + B + 1 + r0Q Q := by push_cast; ring
    have hA2v : ((S + (B + 1) + r0Q Q : ℕ) : ℚ) = (S : ℚ) + B + 1 + r0Q Q := by
      push_cast; ring
    have hA3v : ((Ndim B S + 1 + r0Q Q : ℕ) : ℚ) = (Ndim B S : ℚ) + 1 + r0Q Q := by
      push_cast; ring
    have hA4v : ((S + 1 + r0Q Q : ℕ) : ℚ) = (S : ℚ) + 1 + r0Q Q := by push_cast; ring
    rw [hA1v] at hA1_ge
    rw [hA2v] at hA2_le
    rw [hA3v] at hA3_le
    rw [hA4v] at hA4_ge
    rw [hNv] at hN_le hA1_ge hA3_le
    -- Step 1: combine the two "upper" bounds (N, S) into a single Q*phiQ bound.
    have hLHS : 8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S ≤
        (4 * (2 * (B:ℚ) + S + 3) * (2 * (B:ℚ) + S + 3) - 4 * (2 * (B:ℚ) + S + 3) * Q + Q * Q)
          + 2 * (4 * (S:ℚ) * S - 4 * S * Q + Q * Q) := by
      linarith [hN_le, hS_le]
    -- Step 2: combine the four "tail" bounds (A1..A4) into a single Q*phiQ bound.
    have hRHS :
        2 * (4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * Q)
          - 2 * (4 * ((S:ℚ) + B + 1 + r0Q Q) * ((S:ℚ) + B + 1 + r0Q Q)
              - 4 * ((S:ℚ) + B + 1 + r0Q Q) * Q + Q * Q)
          - 2 * (4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * Q + Q * Q)
          + 2 * (4 * ((S:ℚ) + 1 + r0Q Q) * ((S:ℚ) + 1 + r0Q Q) - 4 * ((S:ℚ) + 1 + r0Q Q) * Q)
        ≤ 16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
          - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
          - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
          + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) := by
      linarith [hA1_ge, hA2_le, hA3_le, hA4_ge]
    -- Step 3: the pure polynomial inequality (no phiQ), where the ratio hypothesis bites.
    -- Unlike `sum_NKQ_tail_ge_of_Q_small`, the four tail-quadratic terms combine
    -- (via difference-of-squares) to a value with *no* `r0Q Q` dependence at all,
    -- so the whole inequality reduces to a quadratic-in-`Q` fact `g Q ≥ 0` on
    -- `[0, 2*B]`; since `g` is concave (its `Q^2` coefficient is `-7`), it suffices
    -- to check the endpoints `Q = 0` and `Q = 2*B`, which is the `hg0`/`hg2B` split
    -- below, combined via `2*B*g(Q) = (2*B-Q)*g(0) + Q*g(2*B) + 14*B*Q*(2*B-Q)`.
    have hPure :
        (4 * (2 * (B:ℚ) + S + 3) * (2 * (B:ℚ) + S + 3) - 4 * (2 * (B:ℚ) + S + 3) * Q + Q * Q)
          + 2 * (4 * (S:ℚ) * S - 4 * S * Q + Q * Q) ≤
        2 * (4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * Q)
          - 2 * (4 * ((S:ℚ) + B + 1 + r0Q Q) * ((S:ℚ) + B + 1 + r0Q Q)
              - 4 * ((S:ℚ) + B + 1 + r0Q Q) * Q + Q * Q)
          - 2 * (4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + 1 + r0Q Q)
              - 4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * Q + Q * Q)
          + 2 * (4 * ((S:ℚ) + 1 + r0Q Q) * ((S:ℚ) + 1 + r0Q Q) - 4 * ((S:ℚ) + 1 + r0Q Q) * Q) := by
      have hBQ : (20 : ℚ) ≤ B := by exact_mod_cast hB
      have hSBQ : (S : ℚ) * 20 ≤ B := by exact_mod_cast hSB
      have hbracketQ : (Q : ℚ) ≤ 2 * B := by exact_mod_cast hbracket
      have hQnn : (0 : ℚ) ≤ Q := Nat.cast_nonneg _
      have hBnn : (0 : ℚ) ≤ B := Nat.cast_nonneg _
      have hSnn : (0 : ℚ) ≤ S := Nat.cast_nonneg _
      have hd : (0 : ℚ) ≤ B - 20 * S := by linarith
      have h2BQ : (0 : ℚ) ≤ 2 * B - Q := by linarith
      have hBd : (0 : ℚ) ≤ (B : ℚ) * (B - 20 * S) := mul_nonneg hBnn hd
      have hSd : (0 : ℚ) ≤ (S : ℚ) * (B - 20 * S) := mul_nonneg hSnn hd
      have hSBsq : 400 * (S : ℚ) * S ≤ (B : ℚ) * B := by nlinarith [hBd, hSd]
      have hB20 : 20 * (B : ℚ) ≤ (B : ℚ) * B := by nlinarith [hBQ, hBnn]
      have hBSnn : (0 : ℚ) ≤ (B : ℚ) * S := mul_nonneg hBnn hSnn
      -- `g 0`: the polynomial at `Q = 0`.
      have hg0 : (0 : ℚ) ≤ 16 * (B : ℚ) * B - 16 * B * S - 12 * S * S - 24 * S - 36 := by
        nlinarith [hBd, hSBsq, hSBQ, hB20, hBQ]
      -- `g (2*B)`: the polynomial at `Q = 2*B`.
      have hg2B : (0 : ℚ) ≤
          4 * (B : ℚ) * B + 8 * B * S + 24 * B - 12 * S * S - 24 * S - 36 := by
        nlinarith [hBSnn, hSBsq, hSBQ, hB20, hBQ]
      have hterm1 : (0 : ℚ) ≤
          (2 * (B : ℚ) - Q) * (16 * B * B - 16 * B * S - 12 * S * S - 24 * S - 36) :=
        mul_nonneg h2BQ hg0
      have hterm2 : (0 : ℚ) ≤
          (Q : ℚ) * (4 * B * B + 8 * B * S + 24 * B - 12 * S * S - 24 * S - 36) :=
        mul_nonneg hQnn hg2B
      have hterm3 : (0 : ℚ) ≤ 14 * (B : ℚ) * Q * (2 * B - Q) := by
        have h14BQ : (0 : ℚ) ≤ 14 * (B : ℚ) * Q := by positivity
        nlinarith [mul_nonneg h14BQ h2BQ]
      have hBpos : (0 : ℚ) < 2 * B := by linarith
      have hgQ2B : (2 * (B : ℚ)) * 0 ≤ (2 * (B : ℚ)) *
          (16 * B * B - 16 * B * S - 12 * S * S - 24 * S - 36
            + 8 * B * Q + 12 * S * Q + 12 * Q - 7 * Q * Q) := by
        nlinarith [hterm1, hterm2, hterm3]
      have hgQ : (0 : ℚ) ≤
          16 * (B : ℚ) * B - 16 * B * S - 12 * S * S - 24 * S - 36
            + 8 * B * Q + 12 * S * Q + 12 * Q - 7 * Q * Q :=
        le_of_mul_le_mul_left hgQ2B hBpos
      have hident :
          (2 * (4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q)
                - 4 * ((2*(B:ℚ)+S+3) + B + 1 + r0Q Q) * Q)
            - 2 * (4 * ((S:ℚ) + B + 1 + r0Q Q) * ((S:ℚ) + B + 1 + r0Q Q)
                - 4 * ((S:ℚ) + B + 1 + r0Q Q) * Q + Q * Q)
            - 2 * (4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * ((2*(B:ℚ)+S+3) + 1 + r0Q Q)
                - 4 * ((2*(B:ℚ)+S+3) + 1 + r0Q Q) * Q + Q * Q)
            + 2 * (4 * ((S:ℚ) + 1 + r0Q Q) * ((S:ℚ) + 1 + r0Q Q) - 4 * ((S:ℚ) + 1 + r0Q Q) * Q))
          -
          ((4 * (2 * (B:ℚ) + S + 3) * (2 * (B:ℚ) + S + 3) - 4 * (2 * (B:ℚ) + S + 3) * Q + Q * Q)
            + 2 * (4 * (S:ℚ) * S - 4 * S * Q + Q * Q))
        = 16 * (B : ℚ) * B - 16 * B * S - 12 * S * S - 24 * S - 36
            + 8 * B * Q + 12 * S * Q + 12 * Q - 7 * Q * Q := by ring
      linarith [hgQ, hident]
    have hchain :
        8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S ≤
          16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
            + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) :=
      le_trans hLHS (le_trans hPure hRHS)
    have h8Q : (0 : ℚ) < 8 * Q := by positivity
    have heqL : 8 * (Q : ℚ) * phiQ Q (Ndim B S) + 16 * (Q : ℚ) * phiQ Q S =
        8 * (Q : ℚ) * ((phiQ Q (Ndim B S) : ℚ) + 2 * (phiQ Q S : ℚ)) := by ring
    have heqR :
        16 * (Q : ℚ) * phiQ Q (Ndim B S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (S + (B + 1) + r0Q Q)
            - 16 * (Q : ℚ) * phiQ Q (Ndim B S + 1 + r0Q Q)
            + 16 * (Q : ℚ) * phiQ Q (S + 1 + r0Q Q) =
        8 * (Q : ℚ) * (2 * ((phiQ Q (Ndim B S + (B + 1) + r0Q Q) : ℚ)
          - (phiQ Q (S + (B + 1) + r0Q Q) : ℚ)
          - (phiQ Q (Ndim B S + 1 + r0Q Q) : ℚ)
          + (phiQ Q (S + 1 + r0Q Q) : ℚ))) := by ring
    rw [heqL, heqR] at hchain
    exact le_of_mul_le_mul_left hchain h8Q
  exact_mod_cast key

/-- Paper Theorem 5.1 as a proposition. -/
def thm_5_1_statement : Prop :=
  ∀ (B : ℕ), 20 ≤ B →
    ∀ (Q : ℕ), OddPrimePower Q →
      ∀ (S : ℕ), 0 < S → S * 20 ≤ B →
        ∀ (f : Fin S → Fin (S + 3)), Function.Injective f →
          aQB B S Q ≥ mAQ B S Q f

end CatalanSun.Thm51
