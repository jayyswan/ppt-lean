# HANDOFF: V7MobiusEval

Goal: `Pptc/Hypergeometric/V7MobiusEval.lean`, namespace `Pconstructible`:

```lean
theorem hasSum_mSeries {w : ℝ} (hw : |w| < 1 / 3) :
    HasSum (fun k : ℕ => PowerSeries.coeff k mSeries * w ^ k)
      (hyp (1 / 2) (1 / 2) 1 (2 * w / (1 + w)))
```

## Log
- start: created log.
- Wrote full first draft of V7MobiusEval.lean (~430 lines): recipP/invOneSubPow coefficient
  formula, mobius_pow_eq, coeff_mobius_pow_of_pos, negative-binomial HasSum via
  Real.one_div_one_sub_rpow_hasFPowerSeriesOnBall_zero, abs/signed row HasSums using
  hasSum_nat_add_iff, coeff_mSeries via coeff_subst', summability + final HasSum mirroring
  Quadratic. About to run diagnostics.
- First diagnostics: many errors. Fixed: open scoped ENNReal; C(-1) proof; pow_ne_zero ->
  constantCoeff argument; coeff_mobius_pow_of_pos show/coeff_X_pow_mul; HasSum.congr ->
  HasSum.congr_fun in 3 places; hval one_mul; norm_ofNat -> abs_of_nonneg; hcol stray ring.
  Re-running diagnostics.
- 2nd diagnostics: fewer errors. Fixed: inv_mul_cancel ordering; hasSum_negBinom zero_add;
  hval via simp only; hnorm via concrete hC; coeff_mobius_pow_of_pos n-rewrite corruption
  (moved into hcoeff); explicit f in hasSum_nat_add_iff. Re-running.
- 3rd diagnostics: 2 errors (hcast ring had no goal; hsym congr/omega). Fixed.
- 4th diagnostics: CLEAN. lake_check: OK - no errors or warnings.
- Final: theorem `Pconstructible.hasSum_mSeries` proved sorry-free, exactly as specified
  (|w| < 1/3). No deviation from the statement.
