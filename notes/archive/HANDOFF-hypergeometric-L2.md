# HANDOFF hypergeometric L2 (H2): complete elliptic integrals as ₂F₁

Goal (Lean):
```
theorem ellipticF_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticF c (π / 2) = π / 2 * hyp (1 / 2) (1 / 2) 1 c
theorem ellipticE_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticE c (π / 2) = π / 2 * hyp (-1 / 2) (1 / 2) 1 c
```
plus corollaries
```
@[pconstructible_cond] theorem hyp_half_half_one_Pconstructible {c : ℝ} (hcP : PConstructible c)
    (hc : |c| < 1) : PConstructible (hyp (1 / 2) (1 / 2) 1 c)
@[pconstructible_cond] theorem hyp_neg_half_half_one_Pconstructible {c : ℝ} (hcP : PConstructible c)
    (hc : |c| < 1) : PConstructible (hyp (-1 / 2) (1 / 2) 1 c)
```
Target file: `pptc/Pptc/Hypergeometric/Elliptic.lean`
Plan: binomial series + termwise integral 0..π/2 + `integral_sin_pow_even` + match `hypCoeff`.

## Log
- read plan overview (§2 V1/V2, §4 H2), Hypergeometric/Basic.lean (L1 API + `hasSum_arcsin` style).
- read Pptc/Basic.lean: `ellipticEIntegrand = sqrt(1-c sin²)`, `ellipticE = ∫`, `ellipticFIntegrand = (ellipticEIntegrand)⁻¹`, `ellipticF = ∫`; `ellipticF_pi_div_two_Pconstructible` needs `c < 1`; `ellipticE_Pconstructible` needs `c < 1`.
- confirmed `integral_sin_pow_even` is over `0..π` (not π/2): `π * ∏ (2i+1)/(2i+2)`; need a halving lemma.
- confirmed `Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero a` and `intervalIntegral.hasSum_integral_of_dominated_convergence` signatures; `ascPochhammer_eval_one`, `ascPochhammer_succ_eval`, `Real.sin_pi_sub`, `HasSum.mul_left`, `Summable.congr` exist.
- plan: shared DCT lemma for `∫₀^{π/2} 1/(1-c sin²x)^a`; F uses a=1/2 (integrand = (1-u)^(-1/2)), E uses a=-1/2 (integrand = (1-u)^(1/2)); term = Ring.choose(a+n-1,n) c^n ∫ sin^{2n}; half-integral = (π/2)(1/2)_n/n!; coeff match to hypCoeff.
- wrote Elliptic.lean skeleton, diagnostics OK.
- full proof written; `lean_diagnostic_messages` now returns EMPTY (success). Key gotchas resolved:
  `-1/2` parses as `(-1)/2` (NOT `-(1/2)`), so `Real.rpow_neg` needed an explicit exponent rewrite;
  `Ring.choose (1/2 + n - 1) n` defaults to ℕ without a type ascription; `field_simp` closed some
  goals so the trailing `ring` had to go.
- declarations: `ellipticF_pi_div_two_eq_hyp`, `ellipticE_pi_div_two_eq_hyp`,
  `hyp_half_half_one_Pconstructible`, `hyp_neg_half_half_one_Pconstructible` all present.
- FINAL: `lake_check Pptc/Hypergeometric/Elliptic.lean` -> "OK - no errors or warnings".
  `lean_verify` on the F identity and the E corollary -> axioms `[propext, Classical.choice, Quot.sound]`.
  No `sorry`. No `.olean` built (did not run `lake build`, per instructions). DONE.
