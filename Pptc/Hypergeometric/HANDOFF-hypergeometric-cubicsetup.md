# HANDOFF: cubic signature transformation setup

## Goal
Create `Pptc/Hypergeometric/CubicSetup.lean` (imports SqrtSeries + Substitution),
`namespace Pconstructible`, `noncomputable section`, proving sorry-free:

- defs: `gSeries`, `gammaSeries`, `alphaSeries`, `betaSeries`
- `constantCoeff_gSeries : constantCoeff gSeries = 1`
- `gSeries_mul_self : gSeries * gSeries * (1 + 2*X) = 1`
- `one_add_two_X_mul_derivative_gSeries : (1 + 2*X) * D gSeries = -gSeries`
- `gammaSeries_mul_self : gammaSeries*gammaSeries*(1+2X) = (1+X+X²)²`
- `alphaSeries_mul : alphaSeries*(1+2X) = X³*(2+X)`
- `betaSeries_mul : betaSeries*(4*(1+X+X²)³) = 27*X²*(1+X)²`
- `hasSubst_alphaSeries`, `hasSubst_betaSeries`

## Plan
gSeries = subst (2X) sqrtInvSeries; use substAlgHom, derivative_subst,
HasSubst.of_constantCoeff_zero'; units via constantCoeff ≠ 0; HasSubst via const coeff 0.

## Log
- [start] read SqrtSeries.lean; file does not exist yet; Hypergeometric dir listed.
- Wrote v1 of CubicSetup.lean. First diagnostics: (a) need type ascription
  `(2*X : PowerSeries ℝ)` in HasSubst statements; (b) need import
  `Mathlib.RingTheory.PowerSeries.Inverse` for `PowerSeries.inv_mul_cancel`;
  (c) constantCoeff_gSeries proof revamped via `rescale` + `coeff_rescale`.
- Wrote v2 with fixes.
- v3: ascriptions `(... : PowerSeries ℝ)` on `2*X` and `1+X` args of `subst`, explicit
  element for `inv_mul_cancel`, `hden` helper for the `4(1+X+X²)³` constant coefficient,
  `← coeff_zero_eq_constantCoeff_apply` in `constantCoeff_gSeries`.
- lean_diagnostic_messages => success: true, items: [] (file compiles, no warnings).
- Next: lake_check final confirmation.
- DONE: `lake_check Pptc/Hypergeometric/CubicSetup.lean` => "lake env lean ...OK - no errors
  or warnings." No sorry/axiom. lean_verify on betaSeries_mul & gSeries_mul_self =>
  axioms {propext, Classical.choice, Quot.sound}. All required names present.
