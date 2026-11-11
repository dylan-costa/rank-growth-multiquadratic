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
