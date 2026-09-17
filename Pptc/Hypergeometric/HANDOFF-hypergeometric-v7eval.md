# HANDOFF: V7Eval

Target file: `Pptc/Hypergeometric/V7Eval.lean` (new)
Namespace `Pconstructible`, `noncomputable section`.

Goals (exact):
```lean
theorem hasSum_phiSeries {w : ℝ} (hw : |w| < 1) :
    HasSum (fun k : ℕ => PowerSeries.coeff k phiSeries * w ^ k)
      (hyp (1 / 4) (3 / 4) 1 (w ^ 2))

theorem hasSum_sqrtInvSeries {w : ℝ} (hw : |w| < 1) :
    HasSum (fun n : ℕ => sqrtInvCoeff n * w ^ n) ((1 + w) ^ (-(1 / 2 : ℝ)))
```

Plan:
1. Orient in V7.lean / Heun.lean / HeunMobius.lean / SqrtSeries.lean.
2. hasSum_sqrtInvSeries via `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` + `Ring.choose (-(1/2)) n = sqrtInvCoeff n`.
3. hasSum_phiSeries via `hasSum_hyp` at `w^2` + parity reindex.

## Log
- [start] created log.
- Oriented: V7.lean (phiSeries_eq_rSeries), Heun.lean (phiSeries, coeff_zero_phiSeries), SqrtSeries.lean (sqrtInvCoeff, sqrtInvCoeff_succ), Basic.lean (hyp, hypCoeff, hasSum_hyp), Goursat/Quadratic (hypSeries).
- Key finds: `PowerSeries.coeff_subst_X_pow` (exact even/odd coefficient rule), `Function.Injective.hasSum_iff` (reindex with zero off range), `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` + `HasFPowerSeriesOnBall.hasSum`, `Ring.choose_smul_choose` + `Ring.choose_one_right` for the recurrence.
- Wrote full draft of Pptc/Hypergeometric/V7Eval.lean (4 decls). Now checking diagnostics.
- Diagnostics clean via lean-lsp (success=true, no items). Fixed: `Metric.eball`/`mem_eball_zero_iff` (EMetric.ball deprecated), `open scoped ENNReal`, `mul_left_cancel₀` for injectivity of `·*2`, `HasSum.congr_fun` to convert the binomial series term via `binomialSeries_apply`, and `hasSum_sqrtInvSeries` term conversion through `ring_choose_neg_half`.
- Line-length fix (docstring line was 101 -> reworded). No sorry/axiom/admit.
- Running final `lake_check Pptc/Hypergeometric/V7Eval.lean`.
- DONE. `lake_check Pptc/Hypergeometric/V7Eval.lean` -> `OK - no errors or warnings.`
  `lean_verify` on both theorems: axioms exactly `propext, Classical.choice, Quot.sound`.
  Max line length 98. No sorry/axiom/admit. No scratch files.
- Exact final signatures:
  `Pconstructible.hasSum_phiSeries {w : ℝ} (hw : |w| < 1) :
      HasSum (fun k : ℕ => PowerSeries.coeff k phiSeries * w ^ k) (hyp (1/4) (3/4) 1 (w^2))`
  `Pconstructible.hasSum_sqrtInvSeries {w : ℝ} (hw : |w| < 1) :
      HasSum (fun n : ℕ => sqrtInvCoeff n * w ^ n) ((1 + w) ^ (-(1/2 : ℝ)))`
- Auxiliary lemmas added (same file): `ring_choose_neg_half`, `coeff_phiSeries`.
