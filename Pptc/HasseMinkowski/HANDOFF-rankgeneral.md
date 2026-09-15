# HANDOFF: RankCriteriaGeneral.lean

Goal: new file `Pptc/HasseMinkowski/RankCriteriaGeneral.lean`, namespace `Pptc.HasseMinkowski`.
- `represents_iff_of_rank_two`
- `represents_zero_iff_of_rank_three`
No `sorry`. Iterate with lean_diagnostic_messages; lake_check once at end.

## Log

- Read RankCriteria, HasseInvariantWellDef, HasseInvariant, Basic, Prod, RankTwo, RankThree, Targets. Available: hasseMinkowskiInv_eq_aux_of_equiv, hasseMinkowskiInvAux_two/_three, weightedSumSquares_isotropic_iff_hilbertSym_eq_one, epresents_zero_iff_of_rank_three_diag, wssCongr, hasseMinkowskiInvAux_finCongr, epresents_of_isotropic_nondegenerate. Plan: diagonal rank-2 criterion via ternary criterion; then general theorems with hconn.
- DONE: weightedSumSquares_two_represents_iff_ternary + weightedSumSquares_represents_iff_of_rank_two (diagonal rank-2) compile clean (only an unused-section-variable warning).
- DONE: added hilbertSym_neg_discr_eq_neg_prod, separatingLeft_of_nondegenerate, equivalent_represents_iff, weightedSumSquares_isotropic_iff_of_rank_three, and the general theorems epresents_iff_of_rank_two, epresents_zero_iff_of_rank_three. diagnostics clean, no sorry, axioms propext/Classical.choice/Quot.sound only. Next: final lake_check.
- FINAL: lake_check Pptc/HasseMinkowski/RankCriteriaGeneral.lean -> OK - no errors or warnings. Deliverable complete.
