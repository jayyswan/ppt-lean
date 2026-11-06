# HANDOFF gamma-rational F1 (ArcLength.lean)

Target: C:\dev\Powerpoint\lean\pptc\Pptc\GammaRational\ArcLength.lean
Namespace: Pconstructible
Goal: prove the 5 remaining declarations (speed_powerLawParam already done).
Plan: read file + template arcLengthOf_parabolaParam (Basic.lean ~1830), then prove each.

## Log
- created log; reading target file
- all 5 proofs written; diagnostics clean (0 errors, 0 warnings)
- confirmed via scratch `example` that the RHS set literal is defeq to
  `PConstructibleCurve.power_law ((1+σ/2)⁻¹) (1+σ/2)`; scratch removed
- next: lean_verify x5, then lake build Pptc.GammaRational.ArcLength
- lean_verify x5: all show [propext, Classical.choice, Quot.sound], no warnings
- running: lake build Pptc.GammaRational.ArcLength
- DONE: lake build succeeded (Built Pptc.GammaRational.ArcLength, 2681 jobs, 15s)
- final file has 0 errors / 0 warnings; only speed_powerLawParam's original proof untouched.

### Final proof sketches
- arcLengthOf_powerLawParam: rw [arcLengthOf]; integral_congr on uIcc; speed_powerLawParam hσ hx.1.
- powerLawParam_image_subset: rintro; constructor; split `0<t` vs `t=0` via eq_or_lt_of_le ht.1
  (Or.inr ⟨h.symm, by linarith⟩ / Or.inl); second conj: simp only [powerLawParam]; push_cast; ring.
- powerLawParam_injOn: simpa [powerLawParam] using congrArg Prod.fst h.
- powerLawParam_differentiableAt: differentiableAt_id; and
  (DifferentiableAt.rpow_const differentiableAt_id (Or.inr hb)).const_mul _ with hb : 1 ≤ 1+σ/2.
  `ht` referenced (ht.1) only to silence unused-variable warning.
- powerLawParam_intervalIntegrable: continuous √(1+t^σ); IntervalIntegrable.congr with
  EqOn on uIoc 0 1 via Set.uIoc_of_le + speed_powerLawParam.
