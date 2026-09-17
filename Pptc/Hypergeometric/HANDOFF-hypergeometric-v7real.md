# HANDOFF: V7Real.lean (Goursat quartic transformation, real)

Target file: `pptc/Pptc/Hypergeometric/V7Real.lean`
Declarations: `hasSum_rSeries`, `goursat_small`, `goursat_unit`, `hyp_quarter_three_quarter`.

Plan: (1) hasSum_rSeries via rSeries = sqrtInvSeries*mSeries + HasSum.mul + fibrewise
reindex; (2) goursat_small via coeff phiSeries = coeff rSeries + HasSum.unique;
(3) goursat_unit analytic continuation on Ioo 0 1; (4) hyp_quarter_three_quarter
z=0 / sqrt substitution.

## Log
- created log; reading existing files.
- confirmed lemma signatures via `#check`: `hasSum_sum_range_mul_of_summable_norm`,
  `Finset.Nat.sum_antidiagonal_eq_sum_range_succ`, `AnalyticOnNhd.div/inv/pow`, etc.
- full draft written to `pptc/Pptc/Hypergeometric/V7Real.lean`; tests clean
  (`lean_diagnostic_messages` → no items).
- final `lake_check Pptc/Hypergeometric/V7Real.lean` → `OK - no errors or warnings.`
- all four theorems sorry-free; `lean_verify Pconstructible.hyp_quarter_three_quarter`
  → axioms exactly `propext, Classical.choice, Quot.sound`.
