# HANDOFF gamma-rational F2

Target: `Pptc/GammaRational/Conversion.lean`, theorem `Pconstructible.integral_inv_sqrt_one_add_rpow`.

Goal:
```lean
theorem integral_inv_sqrt_one_add_rpow {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹
      = (1 + 2 / σ) * (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ)) - 2 * Real.sqrt 2 / σ
```

Plan: F x = x * sqrt(1 + x^σ); FTC on [0,1] differentiable on (0,1); F' = sqrt + (σ/2)(x^σ/sqrt(1+x^σ)) = (1+σ/2) sqrt - (σ/2)/sqrt; split integral; solve linear relation.

Log:
- (start) read file; 7 errors reported by prior worker.
- (fix) added import Mathlib.Analysis.SpecialFunctions.Sqrt (Real.hasDerivAt_sqrt lives there).
- (fix) hcomp: Real.hasDerivAt_sqrt needs `x ≠ 0` for the *argument* `1 + x^σ` (not its sqrt);
  used harg : (1+x^σ) ≠ 0. hb built with `.const_add 1` (avoids `.add`/`simpa` mismatch).
- (fix) sqrt-ne & positivity only on Icc 0 1; `ContinuousOn G (Icc 0 1)` (G is not Continuous
  on all of ℝ since 1+x^σ can vanish for x<0).
- (fix) hF' derived via h0 = (hasDerivAt_id x).mul hcomp then rw [one_mul-type ring] + exact.
- (fix) FTC lemma: intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le.
- (fix) hLint/hAint use MeasureTheory.volume explicitly.
- (fix) hlin: `rw [show G = f - g from rfl]; simp only [Pi.sub_apply]` before integral_sub.
- (fix) final: field_simp [hσ.ne']; simp only [one_div]; linear_combination (-2) * hkey.
- (done) lean_diagnostic_messages: success, NO errors/warnings.
- (verified) lean_verify Pconstructible.integral_inv_sqrt_one_add_rpow -> axioms:
  propext, Classical.choice, Quot.sound only.
- (verified) `lake build Pptc.GammaRational.Conversion` succeeded (2688 jobs, 11s), no sorry.
FINAL: complete. FTC lemma = intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le;
sqrt-derivative lemma = Real.hasDerivAt_sqrt (from Mathlib.Analysis.SpecialFunctions.Sqrt,
  condition is on the argument `1 + x^σ`, composed with Real.hasDerivAt_rpow_const via
  HasDerivAt.const_add / HasDerivAt.comp).
