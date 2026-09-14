/-
  CatalanSun/Qhat.lean

  Optional stretch after Prop 3.1: some Newton-completed matrix `Ahat` has
  nonzero determinant (`qhat_ne_zero`), via Cor 2.1 + Prop 3.1 + `F_B ≠ 0` +
  `∏ Πᵢ ≠ 0`.
-/

import CatalanSun.NewtonCompletion
import CatalanSun.Thm21
import Mathlib.Algebra.Ring.Int.Units
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false

noncomputable section

namespace CatalanSun.NewtonCompletion

open Matrix Finset
open CatalanSun

/-! ## Complement of a Cor 2.1 row selection -/

/-- Complement of an injective `S`-row selection inside `Fin (S+3)`. -/
def omittedOfSelected {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    Finset (Fin (S + 3)) :=
  univ \ univ.map ⟨f, hf⟩

theorem omittedOfSelected_card {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    (omittedOfSelected f hf).card = 3 := by
  simp only [omittedOfSelected]
  rw [card_sdiff_of_subset (subset_univ _)]
  simp [card_map, Fintype.card_fin]

/-- Enumerate the three omitted residual indices complementary to `f`. -/
def oOfSelected {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    Fin 3 → Fin (S + 3) :=
  (omittedOfSelected f hf).orderEmbOfFin (omittedOfSelected_card f hf)

theorem oOfSelected_injective {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    Function.Injective (oOfSelected f hf) :=
  ((omittedOfSelected f hf).orderEmbOfFin (omittedOfSelected_card f hf)).injective

theorem omittedFinset_oOfSelected {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    omittedFinset (oOfSelected f hf) (oOfSelected_injective f hf) =
      omittedOfSelected f hf := by
  ext x
  simp only [omittedFinset, oOfSelected, mem_map, mem_univ, true_and]
  constructor
  · rintro ⟨t, ht⟩
    have hx : oOfSelected f hf t ∈ omittedOfSelected f hf :=
      (omittedOfSelected f hf).orderEmbOfFin_mem (omittedOfSelected_card f hf) t
    rwa [← ht]
  · intro hx
    have : x ∈ Set.range (oOfSelected f hf) := by
      change x ∈ Set.range ((omittedOfSelected f hf).orderEmbOfFin (omittedOfSelected_card f hf))
      rw [range_orderEmbOfFin]
      exact hx
    obtain ⟨t, ht⟩ := this
    exact ⟨t, ht⟩

theorem selectedFinset_oOfSelected {S : ℕ} (f : Fin S → Fin (S + 3)) (hf : Function.Injective f) :
    selectedFinset (oOfSelected f hf) (oOfSelected_injective f hf) =
      univ.map ⟨f, hf⟩ := by
  simp only [selectedFinset, omittedFinset_oOfSelected, omittedOfSelected]
  rw [sdiff_sdiff_right_self, inf_eq_inter, univ_inter]

theorem range_selectedRows_oOfSelected {S : ℕ} (f : Fin S → Fin (S + 3))
    (hf : Function.Injective f) :
    Set.range (selectedRows (oOfSelected f hf) (oOfSelected_injective f hf)) =
      Set.range f := by
  rw [selectedRows, range_orderEmbOfFin, selectedFinset_oOfSelected]
  ext x
  simp [mem_map]

/-- Two injective row maps with the same image give square minors equal up to `±1`. -/
theorem det_submatrix_eq_sign_of_same_range {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq n] {K : Type*} [CommRing K]
    (A : Matrix m n K) (f g : n → m)
    (hf : Function.Injective f) (hg : Function.Injective g)
    (hrange : Set.range f = Set.range g) :
    ∃ ε : K, (ε = 1 ∨ ε = -1) ∧
      (A.submatrix g id).det = ε * (A.submatrix f id).det := by
  classical
  -- `e` sends `j` to the unique index with `f (e j) = g j`.
  let e : n ≃ n :=
    (Equiv.ofInjective g hg).trans
      ((Equiv.setCongr hrange.symm).trans (Equiv.ofInjective f hf).symm)
  have hfg : ∀ j, f (e j) = g j := by
    intro j
    simp only [e, Equiv.trans_apply]
    exact Equiv.apply_ofInjective_symm hf _
  have hsub :
      A.submatrix g id = (A.submatrix f id).submatrix e id := by
    ext i j
    simp [hfg]
  have hsign := Int.units_eq_one_or (Equiv.Perm.sign e)
  refine ⟨(Equiv.Perm.sign e : K), ?_, ?_⟩
  · rcases hsign with h | h <;> simp [h]
  · rw [hsub, det_permute]

theorem prod_PiFactor_ne_zero (B S : ℕ) :
    (∏ i : Fin (Ndim B S), (TwoAdic.PiFactor B i.val : ℝ)) ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => PiFactor_cast_ne_zero B i.val

/-- Some omitted-row choice makes `det Ahat ≠ 0` (paper scalar `q̂`). -/
theorem qhat_ne_zero {B S : ℕ} (h : S < B) (hS : 0 < S) :
    ∃ o : Fin 3 → Fin (S + 3), Function.Injective o ∧
      (Ahat B S o).det ≠ 0 := by
  obtain ⟨f, hf, hdet⟩ := Thm21.cor_2_1 h hS
  set o := oOfSelected f hf
  set ho := oOfSelected_injective f hf
  have hrange := range_selectedRows_oOfSelected f hf
  obtain ⟨εr, hεr, hR⟩ :=
    det_submatrix_eq_sign_of_same_range (Rank.RmatrixFin B S) f (selectedRows o ho)
      hf (selectedRows_injective o ho) hrange.symm
  have hRne :
      ((Rank.RmatrixFin B S).submatrix (selectedRows o ho) id).det ≠ 0 := by
    rw [hR]
    exact mul_ne_zero (by rcases hεr with r | r <;> simp [r]) hdet
  obtain ⟨ε, hε, hAt⟩ := prop_3_1_det_Atilde h hS o ho
  have hAtne : (Atilde B S o).det ≠ 0 := by
    rw [hAt]
    exact mul_ne_zero
      (mul_ne_zero (by rcases hε with r | r <;> simp [r]) (F_B_ne_zero B)) hRne
  refine ⟨o, ho, ?_⟩
  intro h0
  have : (Atilde B S o).det = 0 := by
    rw [det_Atilde_eq_Pi_mul_det_Ahat, h0, mul_zero]
  exact hAtne this

end CatalanSun.NewtonCompletion
