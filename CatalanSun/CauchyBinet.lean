/-
  CatalanSun/CauchyBinet.lean

  Cauchy–Binet formula over a commutative ring (Sun arXiv:2609.04176v1 §4).
  Mathlib v4.32.2 has no Cauchy–Binet; proved from `det_apply'` / `det_mul`-style
  Leibniz expansion, vanishing on non-injective column maps, and partitioning
  injectives by image via `Finset.orderEmbOfFin`.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Logic.Equiv.Set

set_option linter.style.header false
set_option linter.unusedSimpArgs false
set_option linter.style.setOption false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

noncomputable section

namespace CatalanSun.CauchyBinet

open Matrix Finset Equiv
open scoped Matrix BigOperators

variable {R : Type*} [CommRing R]

local notation "ε " σ:arg => ((Equiv.Perm.sign σ : ℤ) : R)

/-! ## Column / row minors via `orderEmbOfFin` -/

/-- Square column minor of an `m × n` matrix on an `m`-element column set. -/
def colsSubmatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  A.submatrix id (s.orderEmbOfFin hs)

/-- Square row minor of an `n × m` matrix on an `m`-element row set. -/
def rowsSubmatrix {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) : Matrix (Fin m) (Fin m) R :=
  B.submatrix (s.orderEmbOfFin hs) id

@[simp] theorem colsSubmatrix_apply {m n : ℕ} (A : Matrix (Fin m) (Fin n) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    colsSubmatrix A s hs i j = A i (s.orderEmbOfFin hs j) :=
  rfl

@[simp] theorem rowsSubmatrix_apply {m n : ℕ} (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) (i j : Fin m) :
    rowsSubmatrix B s hs i j = B (s.orderEmbOfFin hs i) j :=
  rfl

/-! ## CB0: `m = 0` and `m = 1` -/

theorem det_mul_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det = 1 :=
  det_fin_zero

theorem det_mul_eq_sum_minors_fin_zero {n : ℕ}
    (A : Matrix (Fin 0) (Fin n) R) (B : Matrix (Fin n) (Fin 0) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 0,
        if hs : s.card = 0 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  simp [det_fin_zero, colsSubmatrix, rowsSubmatrix, powersetCard_zero]

theorem det_mul_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det = ∑ k : Fin n, A 0 k * B k 0 := by
  rw [det_fin_one, Matrix.mul_apply]

theorem det_mul_eq_sum_minors_fin_one {n : ℕ}
    (A : Matrix (Fin 1) (Fin n) R) (B : Matrix (Fin n) (Fin 1) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard 1,
        if hs : s.card = 1 then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [det_mul_fin_one]
  have hmap :
      (univ : Finset (Fin n)).powersetCard 1 =
        (univ : Finset (Fin n)).map ⟨fun k => {k}, singleton_injective⟩ :=
    powersetCard_one _
  rw [hmap, sum_map]
  refine Fintype.sum_congr _ _ fun k => ?_
  have hs : ({k} : Finset (Fin n)).card = 1 := card_singleton k
  simp only [Function.Embedding.coeFn_mk, dif_pos hs, det_fin_one,
    colsSubmatrix_apply, rowsSubmatrix_apply, orderEmbOfFin_singleton]

/-! ## Helpers: expansion, vanishing, permutations of a column image -/

/-- Leibniz expansion of `det(A * B)` as a sum over column-selection maps. -/
theorem det_mul_eq_sum_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i : Fin m, B (p i) i := by
  calc
    (A * B).det
        = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i) * B (p i) i := by
          simp only [det_apply', Matrix.mul_apply, prod_univ_sum, mul_sum,
            Fintype.piFinset_univ]
          rw [sum_comm]
    _ = ∑ p : Fin m → Fin n,
            ∑ σ : Perm (Fin m),
              (ε σ * ∏ i, A (σ i) (p i)) * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => sum_congr rfl fun σ _ => ?_
          rw [prod_mul_distrib, mul_assoc]
    _ = ∑ p : Fin m → Fin n,
            (∑ σ : Perm (Fin m), ε σ * ∏ i, A (σ i) (p i)) *
              ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          exact (Finset.sum_mul _ _ _).symm
    _ = ∑ p : Fin m → Fin n, (A.submatrix id p).det * ∏ i, B (p i) i := by
          refine sum_congr rfl fun p _ => ?_
          congr 1
          simpa [submatrix_apply] using (det_apply' (A.submatrix id p)).symm

/-- Non-injective column selection forces a repeated column, hence determinant zero. -/
theorem det_submatrix_eq_zero_of_not_injective {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) {p : Fin m → Fin n}
    (hp : ¬ Function.Injective p) :
    (A.submatrix id p).det = 0 := by
  simp only [Function.Injective] at hp
  push Not at hp
  obtain ⟨i, j, hpij, hij⟩ := hp
  exact det_zero_of_column_eq hij fun k => by simp [hpij]

/-- Only injective column maps contribute to the expansion. -/
theorem det_mul_eq_sum_injective_colMap {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ p : Fin m → Fin n,
        if Function.Injective p then
          (A.submatrix id p).det * ∏ i : Fin m, B (p i) i
        else 0 := by
  rw [det_mul_eq_sum_colMap]
  refine sum_congr rfl fun p _ => ?_
  split_ifs with hp
  · rfl
  · rw [det_submatrix_eq_zero_of_not_injective A hp, zero_mul]

/-- The unique permutation realizing an injective map as `orderEmbOfFin ∘ τ`. -/
def permOfImage {m n : ℕ} (p : Fin m → Fin n) (hp : Function.Injective p)
    (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) : Perm (Fin m) :=
  let emb : Fin m → Fin n := s.orderEmbOfFin hs
  have hrangep : Set.range p = (s : Set (Fin n)) := by
    rw [← him, coe_image, coe_univ, Set.image_univ]
  have hrangee : Set.range emb = (s : Set (Fin n)) := range_orderEmbOfFin s hs
  (Equiv.ofInjective p hp).trans <|
    (Equiv.setCongr (hrangep.trans hrangee.symm)).trans
      (Equiv.ofInjective emb (s.orderEmbOfFin hs).injective).symm

theorem apply_orderEmb_permOfImage {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) (i : Fin m) :
    s.orderEmbOfFin hs (permOfImage p hp s hs him i) = p i := by
  dsimp [permOfImage]
  exact Equiv.apply_ofInjective_symm (s.orderEmbOfFin hs).injective _

theorem permOfImage_comp {m n : ℕ} (p : Fin m → Fin n)
    (hp : Function.Injective p) (s : Finset (Fin n)) (hs : s.card = m)
    (him : image p univ = s) :
    (s.orderEmbOfFin hs : Fin m → Fin n) ∘ permOfImage p hp s hs him = p :=
  funext fun i => apply_orderEmb_permOfImage p hp s hs him i

/-- Image of an injective `Fin m → Fin n` is an `m`-element subset of `univ`. -/
theorem image_mem_powersetCard {m n : ℕ} {p : Fin m → Fin n}
    (hp : Function.Injective p) :
    image p univ ∈ (univ : Finset (Fin n)).powersetCard m := by
  refine mem_powersetCard.mpr ⟨subset_univ _, ?_⟩
  rw [card_image_of_injective _ hp, card_univ, Fintype.card_fin]

/-- `orderEmbOfFin` of the full universe is the identity map. -/
theorem orderEmbOfFin_univ_eq_id (m : ℕ) :
    ((univ : Finset (Fin m)).orderEmbOfFin (by simp [card_univ, Fintype.card_fin]) :
      Fin m → Fin m) =
      id := by
  have h :
      (id : Fin m → Fin m) =
        (univ : Finset (Fin m)).orderEmbOfFin
          (by simp [card_univ, Fintype.card_fin]) :=
    orderEmbOfFin_unique (s := (univ : Finset (Fin m)))
      (by simp [card_univ, Fintype.card_fin]) (fun _ => mem_univ _)
      (strictMono_id : StrictMono (id : Fin m → Fin m))
  exact h.symm

/-! ## CB1: square case `m = n` -/

theorem powersetCard_univ_self (m : ℕ) :
    (univ : Finset (Fin m)).powersetCard m = {univ} := by
  ext s
  simp only [mem_powersetCard, mem_singleton, subset_univ, true_and]
  exact ⟨fun hs => eq_univ_of_card _ (hs.trans (by simp [card_univ, Fintype.card_fin])),
    fun hs => hs ▸ by simp [card_univ, Fintype.card_fin]⟩

theorem colsSubmatrix_univ {m : ℕ} (A : Matrix (Fin m) (Fin m) R) :
    colsSubmatrix A univ (by simp [card_univ, Fintype.card_fin]) = A := by
  ext i j
  simp [colsSubmatrix, orderEmbOfFin_univ_eq_id]

theorem rowsSubmatrix_univ {m : ℕ} (B : Matrix (Fin m) (Fin m) R) :
    rowsSubmatrix B univ (by simp [card_univ, Fintype.card_fin]) = B := by
  ext i j
  simp [rowsSubmatrix, orderEmbOfFin_univ_eq_id]

/-- Square Cauchy–Binet collapses to `Matrix.det_mul`. -/
theorem det_mul_eq_sum_minors_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin m)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  rw [powersetCard_univ_self, sum_singleton]
  have hs : (univ : Finset (Fin m)).card = m := by simp [card_univ, Fintype.card_fin]
  simp only [dif_pos hs, colsSubmatrix_univ, rowsSubmatrix_univ, Matrix.det_mul]

/-! ## Fiber of a fixed image: sum over permutations -/

theorem det_submatrix_comp_perm {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (emb : Fin m → Fin n) (τ : Perm (Fin m)) :
    (A.submatrix id (emb ∘ τ)).det = ε τ * (A.submatrix id emb).det := by
  have h : A.submatrix id (emb ∘ τ) = (A.submatrix id emb).submatrix id τ := by
    ext; simp [Function.comp_apply]
  rw [h, det_permute']

theorem sum_fiber_eq_det_mul_det {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R)
    (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ τ : Perm (Fin m),
        (A.submatrix id ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ)).det *
          (∏ i : Fin m, B (((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) i) i)) =
      (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det := by
  let emb : Fin m → Fin n := fun i => s.orderEmbOfFin hs i
  change ∑ τ : Perm (Fin m),
      (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
    (A.submatrix id emb).det * (B.submatrix emb id).det
  have hsum :
      ∑ τ : Perm (Fin m),
          (A.submatrix id (emb ∘ τ)).det * (∏ i : Fin m, B (emb (τ i)) i) =
        ∑ τ : Perm (Fin m),
          (A.submatrix id emb).det * (ε τ * (∏ i : Fin m, B (emb (τ i)) i)) := by
    refine sum_congr rfl fun τ _ => ?_
    rw [det_submatrix_comp_perm A emb τ]
    ring
  rw [hsum, ← Finset.mul_sum]
  congr 1
  exact (det_apply' (B.submatrix emb id)).symm

/-- Enumerate injective maps with a fixed image by permutations of `orderEmbOfFin`. -/
theorem sum_injective_with_image {m n : ℕ}
    (f : (Fin m → Fin n) → R) (s : Finset (Fin n)) (hs : s.card = m) :
    (∑ p : Fin m → Fin n,
        if Function.Injective p ∧ image p univ = s then f p else 0) =
      ∑ τ : Perm (Fin m), f ((s.orderEmbOfFin hs : Fin m → Fin n) ∘ τ) := by
  classical
  let emb : Fin m → Fin n := (s.orderEmbOfFin hs : Fin m → Fin n)
  have hembinj : Function.Injective emb := (s.orderEmbOfFin hs).injective
  have himemb : image emb univ = s := image_orderEmbOfFin_univ s hs
  have hfilter :
      ∑ τ : Perm (Fin m), f (emb ∘ τ) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f := by
    refine sum_bij (fun τ _ => emb ∘ (τ : Fin m → Fin m)) ?mem ?inj ?surj ?eq
    · intro τ _
      refine mem_filter.mpr ⟨mem_univ _, hembinj.comp τ.injective, ?_⟩
      have himτ : image (τ : Fin m → Fin m) univ = univ := by
        rw [← coe_inj, coe_image, coe_univ, Set.image_univ, τ.surjective.range_eq]
      rw [image_comp, himτ, himemb]
    · intro τ₁ _ τ₂ _ h
      exact Equiv.Perm.ext fun i => hembinj (congrFun h i)
    · intro p hp
      obtain ⟨_, hpinj, him⟩ := mem_filter.mp hp
      refine ⟨permOfImage p hpinj s hs him, mem_univ _, ?_⟩
      -- `emb ∘ permOfImage = p`
      simpa [emb] using permOfImage_comp p hpinj s hs him
    · intro τ _; rfl
  have hsplit :
      (∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0) =
        (filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
          univ).sum f :=
    (sum_filter (fun p : Fin m → Fin n => Function.Injective p ∧ image p univ = s)
      (f := f)).symm
  exact hsplit.trans hfilter.symm

/-! ## CB2: general Cauchy–Binet -/

/-- Group injective column maps by their image in `powersetCard m`. -/
theorem sum_injective_eq_sum_powerset {m n : ℕ} (f : (Fin m → Fin n) → R) :
    (∑ p : Fin m → Fin n, if Function.Injective p then f p else 0) =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        ∑ p : Fin m → Fin n,
          if Function.Injective p ∧ image p univ = s then f p else 0 := by
  classical
  have hswap :
      (∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
          ∑ p : Fin m → Fin n,
            if Function.Injective p ∧ image p univ = s then f p else 0) =
        ∑ p : Fin m → Fin n,
          ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
            if Function.Injective p ∧ image p univ = s then f p else 0 :=
    sum_comm
  rw [hswap]
  refine sum_congr rfl fun p _ => ?_
  by_cases hp : Function.Injective p
  · have him : image p univ ∈ (univ : Finset (Fin n)).powersetCard m :=
      image_mem_powersetCard hp
    rw [sum_eq_single (image p univ)]
    · simp [hp]
    · intro s hs hne
      simp only [hp, true_and]
      split_ifs with h
      · exact (hne h.symm).elim
      · rfl
    · intro hnot
      exact (hnot him).elim
  · simp only [hp, false_and, ite_false, sum_const_zero]

/-- **Cauchy–Binet.** For `A : m × n` and `B : n × m` over a commutative ring,
`det(A * B)` equals the sum of products of complementary minors over all
`m`-element subsets of `Fin n`. -/
theorem det_mul_eq_sum_minors {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det =
      ∑ s ∈ (univ : Finset (Fin n)).powersetCard m,
        if hs : s.card = m then
          (colsSubmatrix A s hs).det * (rowsSubmatrix B s hs).det
        else 0 := by
  classical
  rw [det_mul_eq_sum_injective_colMap]
  have hgroup :=
    sum_injective_eq_sum_powerset
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
  rw [hgroup]
  refine sum_congr rfl fun s hs => ?_
  have hcard : s.card = m := (mem_powersetCard.mp hs).2
  simp only [dif_pos hcard]
  have hfiber :=
    sum_injective_with_image
      (fun p : Fin m → Fin n => (A.submatrix id p).det * ∏ i : Fin m, B (p i) i)
      s hcard
  rw [hfiber, sum_fiber_eq_det_mul_det A B s hcard]

/-! ## CB3: corollaries -/

/-- If `m > n`, there are no `m`-column subsets, so `det(A * B) = 0`. -/
theorem det_mul_eq_zero_of_card_lt {m n : ℕ} (hmn : n < m)
    (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
    (A * B).det = 0 := by
  rw [det_mul_eq_sum_minors]
  have hempty : (univ : Finset (Fin n)).powersetCard m = ∅ := by
    rw [powersetCard_eq_empty]
    simpa [card_univ, Fintype.card_fin] using hmn
  simp [hempty]

/-- Square re-export of `Matrix.det_mul` through the Cauchy–Binet packaging. -/
theorem det_mul_square {m : ℕ}
    (A : Matrix (Fin m) (Fin m) R) (B : Matrix (Fin m) (Fin m) R) :
    (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

end CatalanSun.CauchyBinet
