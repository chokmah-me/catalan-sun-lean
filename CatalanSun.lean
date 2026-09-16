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
import CatalanSun.CauchyBinet
import CatalanSun.FunctionalEq
import CatalanSun.Tail
import CatalanSun.Residual
import CatalanSun.Rank
import CatalanSun.NewtonDiff
import CatalanSun.NewtonCompletion
import CatalanSun.Thm21
import CatalanSun.Qhat
import CatalanSun.Structure
import CatalanSun.Lemma54
import CatalanSun.PascalCauchy
import CatalanSun.Thm51
import CatalanSun.Lemma55

/-! ## Axiom audit (picked up by lean-proof-forge from the build log) -/

#print axioms CatalanSun.Ledger.rawQuadratic_at_one_twentieth
#print axioms CatalanSun.Ledger.deltaLarge_at_one_twentieth
#print axioms CatalanSun.TwoAdic.lemma_5_4_positive_part
#print axioms CatalanSun.TwoAdic.isTwoIntegral_of_odd_den
#print axioms CatalanSun.TwoAdic.odd_PiFactor
#print axioms CatalanSun.Cauchy.det_cauchy_fin_one
#print axioms CatalanSun.Cauchy.det_cauchy_fin_two
#print axioms CatalanSun.Cauchy.det_cauchyMatrix
#print axioms CatalanSun.Cauchy.oddDenom_cast_ne_zero
#print axioms CatalanSun.CauchyBinet.det_mul_eq_sum_minors
#print axioms CatalanSun.CauchyBinet.det_mul_eq_zero_of_card_lt
#print axioms CatalanSun.CauchyBinet.det_mul_eq_sum_minors_square
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
#print axioms CatalanSun.Tail.tail_shift
#print axioms CatalanSun.Tail.weightedTail_shift
#print axioms CatalanSun.Tail.tail_shift_succ
#print axioms CatalanSun.Tail.weightedTail_shift_succ
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
#print axioms CatalanSun.Structure.natDegree_Dlam_le
#print axioms CatalanSun.Structure.PiFactor_eq_eval_Lpoly_mul_Epoly_sq
#print axioms CatalanSun.Structure.natDegree_Plam_le
#print axioms CatalanSun.Structure.eval_Plam
#print axioms CatalanSun.Structure.eval_Dlam
#print axioms CatalanSun.Thm21.fSeq_eq_neg_tail_succ_mul_Dlam_add_Plam
#print axioms CatalanSun.NewtonDiff.newtonInterpolant
#print axioms CatalanSun.NewtonDiff.eval_newtonInterpolant
#print axioms CatalanSun.NewtonDiff.natDegree_newtonInterpolant_of_high_vanishing
#print axioms CatalanSun.Structure.natDegree_G0
#print axioms CatalanSun.Structure.G0_dvd_Dlam
#print axioms CatalanSun.Structure.G0_dvd_shiftPoly_Dlam
#print axioms CatalanSun.Structure.Dlam_eval_neg_three_halves
#print axioms CatalanSun.Thm21.exists_poly_natDegree_le_two_B_sub_one_of_column_dep
#print axioms CatalanSun.Thm21.exists_Apoly_of_column_dep
#print axioms CatalanSun.Thm21.Kpoly_eq_zero_of_column_dep
#print axioms CatalanSun.Structure.oddLin_ne_zero
#print axioms CatalanSun.Structure.Lpoly_ne_zero
#print axioms CatalanSun.Structure.Epoly_ne_zero
#print axioms CatalanSun.Structure.eval_Pstar_at_oddLin_root
#print axioms CatalanSun.Structure.Pstar_ne_zero_of_lam_ne_zero
#print axioms CatalanSun.Structure.Dlam_ne_zero_of_lam_ne_zero
#print axioms CatalanSun.Thm21.clearedEq23_of_Kpoly_eq_zero
#print axioms CatalanSun.Thm21.thm_2_1_full_column_rank
#print axioms CatalanSun.Thm21.cor_2_1
#print axioms CatalanSun.NewtonCompletion.det_DiffMat
#print axioms CatalanSun.NewtonCompletion.isUnit_det_DiffMat
#print axioms CatalanSun.NewtonCompletion.det_powerDiffBlock_Dref
#print axioms CatalanSun.NewtonCompletion.alternating_sum_choose
#print axioms CatalanSun.NewtonCompletion.DiffMat_mulVec_binomCol
#print axioms CatalanSun.NewtonCompletion.det_Atilde_eq_Pi_mul_det_Ahat
#print axioms CatalanSun.NewtonCompletion.DiffMat_mulVec_Pi_u_eq_Rmatrix
#print axioms CatalanSun.NewtonCompletion.F_B_ne_zero
#print axioms CatalanSun.NewtonCompletion.selectedFinset_card
#print axioms CatalanSun.NewtonCompletion.AtildeDiff_pow_ref
#print axioms CatalanSun.NewtonCompletion.AtildeDiff_aux_at_omitted
#print axioms CatalanSun.NewtonCompletion.AtildeDiff_target_selected
#print axioms CatalanSun.NewtonCompletion.AtildeDiff_submatrix_eq_outerBlock
#print axioms CatalanSun.NewtonCompletion.det_AtildeDiff_eq_signed_F_B_det_R
#print axioms CatalanSun.NewtonCompletion.prop_3_1_det_Atilde
#print axioms CatalanSun.NewtonCompletion.qhat_ne_zero
#print axioms CatalanSun.TwoAdic.isTwoIntegral_det
#print axioms CatalanSun.NewtonCompletion.padicValNat_two_F_B_pos
#print axioms CatalanSun.lemma_5_4_det
#print axioms CatalanSun.PascalCauchy.Rmatrix_eq_T_succ_cauchy_sum
#print axioms CatalanSun.PascalCauchy.RmatrixFin_submatrix_eq_mul
#print axioms CatalanSun.PascalCauchy.det_Rmatrix_submatrix_eq_sum_Xi
#print axioms CatalanSun.PascalCauchy.lemma_4_2_odd_cauchy
#print axioms CatalanSun.PascalCauchy.det_rowsSubmatrix_cauchyOddMatrix
#print axioms CatalanSun.PascalCauchy.det_rowsSubmatrix_cauchyOddMatrix_closed
#print axioms CatalanSun.PascalCauchy.choose_eq_factorial_mul_paperP_of_lt_Ndim
#print axioms CatalanSun.PascalCauchy.det_binomMatrix_eq_factorials_mul_det_paperP
#print axioms CatalanSun.PascalCauchy.det_colsSubmatrix_pascalMatrix
#print axioms CatalanSun.PascalCauchy.lemma_4_1_psi_real
#print axioms CatalanSun.PascalCauchy.lemma_4_1_real
#print axioms CatalanSun.PascalCauchy.det_polyEval_dvd_vandermonde
#print axioms CatalanSun.PascalCauchy.vandermondeProdZ_dvd_det_paperPMatrixZ
#print axioms CatalanSun.PascalCauchy.lemma_4_1_psi
#print axioms CatalanSun.PascalCauchy.lemma_4_1
#print axioms CatalanSun.PascalCauchy.det_rowsSubmatrix_diagCauchy
#print axioms CatalanSun.PascalCauchy.Xi_pascal_factor
#print axioms CatalanSun.PascalCauchy.Xi_cauchy_factor
#print axioms CatalanSun.PascalCauchy.Xi_closed_form
#print axioms CatalanSun.Thm51.sum_nQr_eq_card
#print axioms CatalanSun.Thm51.phiQ_formula
#print axioms CatalanSun.Thm51.phiQ_sub_quadratic_nonneg
#print axioms CatalanSun.Thm51.phiQ_sub_quadratic_le
#print axioms CatalanSun.Thm51.sum_choose_nQr_consecutive
#print axioms CatalanSun.Thm51.collisionSum_eq_phiQ_of_balanced
#print axioms CatalanSun.Thm51.collisionSum_ge_phiQ
#print axioms CatalanSun.Thm51.sum_NKQ_tail_ge
#print axioms CatalanSun.Thm51.thm_5_1
