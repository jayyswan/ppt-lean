# HANDOFF gamma-rational F3: halfBeta_inv_eq

Target file: `pptc/Pptc/GammaRational/Substitution.lean`
Declaration: `Pconstructible.halfBeta_inv_eq`

Goal (fixed):
```lean
theorem halfBeta_inv_eq {σ : ℝ} (hσ : 0 < σ) :
    halfBeta σ⁻¹ (1 / 2 - σ⁻¹) = σ * ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹
```
with `halfBeta α β = ∫ t in Set.Ioo (0:ℝ) (1/2), t ^ (α - 1) * (1 - t) ^ (β - 1)`
(sibling file `Pptc/GammaRational/HalfBeta.lean`, namespace `Pconstructible`).

Plan: substitution `φ x = x^σ/(1+x^σ)` mapping `Ioo 0 1` onto `Ioo 0 (1/2)` via
`integral_image_eq_integral_abs_deriv_smul`; pointwise collapse of the integrand;
finish with `integral_const_mul`, `integral_of_le`, `integral_Ioc_eq_integral_Ioo`.

## Log
- [start] read target file, wrote log.
- [diag] file has errors: (1) phi_hasDerivAt `convert`/`ext` fails; (2) phi_pos unused hσ
  warning; (3) phi_injOn `convex_Ioo` needs args `(0:ℝ) 1`; (4) div_rpow_mul_inv_rpow final
  goal has `b+a` vs `a+b`; (5) phi_integrand_eq line 156 `ring` -> `ring_nf`.
- [fix] applied all five; `simpa only [phi]` did not unfold phi -> used defeq `exact`
  with an explicit lambda form. Diag now: success, only unused-hσ warning in phi_hasDerivAt.
- [fix] renamed binder to `_hσ`; re-diagnosing.
- [diag] success, zero errors, zero warnings.
- [verify] `lean_verify Pconstructible.halfBeta_inv_eq` -> propext, Classical.choice, Quot.sound.
- [next] final `lake build Pptc.GammaRational.Substitution`.
- [done] `lake build Pptc.GammaRational.Substitution` -> success (2695 jobs, 13s).
  No sorry, no errors, no warnings. DONE.
