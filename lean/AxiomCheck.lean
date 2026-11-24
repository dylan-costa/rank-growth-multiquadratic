import RankGrowth

/-! Axiom audit: each result should depend only on `propext`, `Classical.choice`, `Quot.sound`.
Run with `lake env lean AxiomCheck.lean`. -/

#print axioms RankGrowth.TwistFamily.part1
#print axioms RankGrowth.TwistFamily.part2
#print axioms RankGrowth.TwistFamily.part3_rootNumber
#print axioms RankGrowth.TwistFamily.part3a
#print axioms RankGrowth.TwistFamily.part3b
#print axioms RankGrowth.TwistFamily.part3b_bsd
#print axioms RankGrowth.TwistFamily.part4a
#print axioms RankGrowth.TwistFamily.part4b
#print axioms RankGrowth.TwistFamily.part4c
#print axioms RankGrowth.TwistFamily.signPattern_plus
#print axioms RankGrowth.TwistFamily.signPattern_minus
#print axioms RankGrowth.incEven_attained
#print axioms RankGrowth.incOdd_attained
#print axioms RankGrowth.rootNumber_product
#print axioms RankGrowth.rootNumber_full_product
#print axioms RankGrowth.legendreSym_F_eq_one
#print axioms RankGrowth.legendreSym_F_eq_neg_one
#print axioms RankGrowth.numF_modEq_one_eight
#print axioms RankGrowth.numF_pos
#print axioms RankGrowth.numF_neg
#print axioms RankGrowth.prod_not_isSquare
#print axioms RankGrowth.f_eval_eq

-- Added for v9: Remark 1.1, Theorem 1.2, Remarks 5.7-5.9, Lemma 5.4 for d₀
#print axioms RankGrowth.RkInf_downward
#print axioms RankGrowth.sSup_mem_RkInfExact
#print axioms RankGrowth.sSup_RkInfExact
#print axioms RankGrowth.RkInf_unbounded_transfer
#print axioms RankGrowth.Rk1_unbounded_transfer
#print axioms RankGrowth.exists_family_ge
#print axioms RankGrowth.thm_main1_inf
#print axioms RankGrowth.thm_main1_one
#print axioms RankGrowth.infinite_fiber_or_unbounded
#print axioms RankGrowth.exact_dichotomy
#print axioms RankGrowth.cor_highrank_arith
#print axioms RankGrowth.legendreSym_d0_eq_one
#print axioms RankGrowth.legendreSym_d0_eq_neg_one
#print axioms RankGrowth.d0_modEq_one_eight
#print axioms RankGrowth.d0_pos
#print axioms RankGrowth.d0_neg
#print axioms RankGrowth.sqfree_part_prod
#print axioms RankGrowth.TwistFamily.rootNumber_eq_neg_one_iff_plus
#print axioms RankGrowth.TwistFamily.rootNumber_eq_neg_one_iff_minus
#print axioms RankGrowth.bound4a_le_bound4c
#print axioms RankGrowth.bound4b_lt_bound4c
