/-
  CatalanSun.lean

  Lean-first slice of Zhi-Wei Sun, "Catalan's constant is irrational"
  (arXiv:2609.04176v1). This library formalizes high-ROI structural lemmas
  from §§2–5 and the exact rational ledger identities — it does **not** claim
  Theorem 1.1 (G irrational).

  Scope of this pass:
  * P4 — exact identities Δ_{>B} = 83/2400 and 4ρ − 2ρ² = 39/200 at ρ = 1/20
  * P1 — Lemma 5.4–style 2-adic positive-part collapse + 2-integrality toolkit

  Deferred: Props 6.3 / 7.4 interval arithmetic; Mertens/PNT; full Thm 1.1.
-/

import CatalanSun.Ledger
import CatalanSun.TwoAdic
import CatalanSun.Cauchy
import CatalanSun.FunctionalEq
import CatalanSun.Tail
import CatalanSun.Residual
import CatalanSun.Rank
import CatalanSun.NewtonDiff
import CatalanSun.Thm21

/-! ## Axiom audit (picked up by lean-proof-forge from the build log) -/

#print axioms CatalanSun.Ledger.rawQuadratic_at_one_twentieth
#print axioms CatalanSun.Ledger.deltaLarge_at_one_twentieth
#print axioms CatalanSun.TwoAdic.lemma_5_4_positive_part
#print axioms CatalanSun.TwoAdic.isTwoIntegral_of_odd_den
#print axioms CatalanSun.TwoAdic.odd_PiFactor
#print axioms CatalanSun.Cauchy.det_cauchy_fin_one
#print axioms CatalanSun.Cauchy.det_cauchy_fin_two
#print axioms CatalanSun.Cauchy.oddDenom_cast_ne_zero
#print axioms CatalanSun.FunctionalEq.thm_2_1_polynomial_fragment
#print axioms CatalanSun.FunctionalEq.no_constant_denom_solution
#print axioms CatalanSun.FunctionalEq.no_polynomial_cleared_solution
#print axioms CatalanSun.FunctionalEq.no_rational_solution
#print axioms CatalanSun.FunctionalEq.no_clearedEq23_solution
#print axioms CatalanSun.FunctionalEq.no_clearedEq23_solution_real
#print axioms CatalanSun.Cauchy.lemma_4_2_S_one
#print axioms CatalanSun.Tail.summable_tailTerm
#print axioms CatalanSun.Tail.tail_pos
#print axioms CatalanSun.Tail.tail_add_succ
#print axioms CatalanSun.Tail.tail_lt_inv_sq
#print axioms CatalanSun.Residual.ratWitness_eq
#print axioms CatalanSun.Residual.ratWitness_twoIntegral
#print axioms CatalanSun.Residual.RmatrixRatWitness_eq
#print axioms CatalanSun.Residual.RmatrixRatWitness_twoIntegral
#print axioms CatalanSun.Residual.lemma_5_4_entry
#print axioms CatalanSun.Rank.exists_nonvanishing_minor_of_full_column_rank
#print axioms CatalanSun.Rank.cor_2_1_of_thm_2_1
#print axioms CatalanSun.Rank.rank_eq_card_iff_mulVec_injective
#print axioms CatalanSun.Rank.exists_nontrivial_column_dependence_of_rank_lt
#print axioms CatalanSun.NewtonDiff.alternating_binomial_sum_eval_eq_zero
#print axioms CatalanSun.NewtonDiff.paperFwdDiff_eq_zero_of_poly
#print axioms CatalanSun.Thm21.column_dep_high_fwdDiff_eq_zero
#print axioms CatalanSun.Thm21.exists_column_dep_with_vanishing_fwdDiff
