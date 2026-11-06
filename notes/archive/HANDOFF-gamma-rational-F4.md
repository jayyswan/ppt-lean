# HANDOFF gamma-rational F4 (BetaSplit.lean)

Goal: fill proofs of
- `Pconstructible.betaIntegral_ofReal_eq_halfBeta`
- `Pconstructible.Gamma_mul_Gamma_half_sub`
in `pptc/Pptc/GammaRational/BetaSplit.lean`.

Plan: (i) real<->complex via ofReal_cpow; (ii) integrability on halves;
(iii) split Ioo 0 1 at 1/2, reflect right half; (iv) Gamma_mul_Gamma_eq_betaIntegral.

## Log
- [start] created log; reading target file + neighbours.
- [step] Both proofs filled; diagnostics clean (no errors/warnings). Next: lean_verify + lake build.
- [done] lean_verify both: [propext, Classical.choice, Quot.sound].
- [done] lake build Pptc.GammaRational.BetaSplit -> Build completed successfully.
- [notes] No helper lemmas needed. Approach thm1: unfold Complex.betaIntegral, push ofReal_cpow
  pointwise on Icc 0 1; split interval at 1/2 via integral_add_adjacent_intervals
  (IntervalIntegrable by intervalIntegrable_rpow' * ContinuousOn.rpow_const); left half is
  halfBeta alpha beta, right half reflected by integral_comp_sub_left 1 is halfBeta beta alpha.
  Thm2: Complex.Gamma_mul_Gamma_eq_betaIntegral at s=rho, t=1/2-rho, rewrite Gamma_ofReal,
  Gamma_one_half_eq, and thm1, then exact_mod_cast.
