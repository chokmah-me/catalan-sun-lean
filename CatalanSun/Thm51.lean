/-
  CatalanSun/Thm51.lean

  Scaffolding for Sun arXiv:2609.04176v1 §5 Theorem 5.1:
  layer vocabulary (5.1)–(5.8)/(5.12) and a Prop encoding the statement.
  Does **not** prove Theorem 5.1 or Lemma 5.3.
-/

import CatalanSun.PascalCauchy
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.IsPrimePow
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Prime.Defs

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.Thm51

open Finset CatalanSun.PascalCauchy CatalanSun.NewtonCompletion

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

/-! ## Theorem 5.1 statement scaffolding (unproved)

Paper Theorem 5.1: for every odd prime power `Q` and every `B ≥ 20`,
`a_{Q,B} ≥ m^A_{Q,B}`.

Encoded as a `Prop` only — no proof, no `sorry`/`admit`/`axiom`.
Ambient `S`/`f` are quantified over the same hypotheses used elsewhere
(`0 < S < B`); the paper treats them as fixed construction parameters. -/

/-- Odd prime power: `Q = p^k` for an odd prime `p` and `k > 0`. -/
def OddPrimePower (Q : ℕ) : Prop :=
  IsPrimePow Q ∧ Odd Q

/-- Paper Theorem 5.1 as a proposition (not proved here). -/
def thm_5_1_statement : Prop :=
  ∀ (B : ℕ), 20 ≤ B →
    ∀ (Q : ℕ), OddPrimePower Q →
      ∀ (S : ℕ), 0 < S → S < B →
        ∀ (f : Fin S → Fin (S + 3)),
          aQB B S Q ≥ mAQ B S Q f

end CatalanSun.Thm51
