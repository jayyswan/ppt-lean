# HANDOFF: ModulusZero

Goal:
```lean
theorem ellipticPiInc_zero_modulus_Pconstructible {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 0 n Φ)
```
File: `Pptc/ThirdKindAll/ModulusZero.lean` (new file, header import `Pptc.ThirdKindAll.Standard`).

Plan: substitution `integral_comp_tan` -> `∫ u in 0..tan Φ, 1/(1+(1-n)u²)`; case split on `n` vs `1`;
use arctan (n<1) / artanh (n>1) antiderivatives; `ellipticPiInc_Pconstructible_of_base'` for n<1.

## Log
- (start) created log
- Surveyed: `ellipticPiIntegrand 0 n θ = 1/(1-n sin²θ)`; `ellipticPi` unfolds to `∫0..π/2`;
  `ellipticPiInc_Pconstructible_of_base'` needs `hK : PConstructible (ellipticPi 0 n)`.
- KEY REALIZATION: the prompt's suggested half-interval symmetry f(π/2-θ)=f(θ) is FALSE for
  sin². Instead split ∫0..π/2 = ∫0..π/4 (t=tan θ) + ∫π/4..π/2 (θ↦π/2-θ, t=tan θ), which gives
  `Π(0,n) = ∫0..1 1/(1+(1-n)u²) + ∫0..1 1/((1-n)+u²)`, both elementary.
- Plan: 3 antiderivative lemmas (arctan, arctan/√b, artanh) via FTC, then substitution identity,
  then complete integral, then main by cases n<1 / 1≤n.
- Next: write chunk 1 (three integral lemmas) and compile.
- DONE: 3 generic integral lemmas (`integral_one_div_one_add_mul_sq`, `_add_sq`,
  `_one_sub_mul_sq`) compile.
- REVISED PLAN: instead of `integral_comp_tan` for the main case (g not globally continuous
  when n>1), use direct FTC in θ. Closed forms proved and compiling:
  `ellipticPiIntegrand_zero_eq_tan`, `ellipticPiInc_zero_eq_arctan` (n<1, |Φ|<π/2),
  `ellipticPiInc_zero_one_eq` (n=1: = tan Φ), `ellipticPiInc_zero_eq_artanh`
  (n>1, 0≤Φ, no-pole hypothesis).
- Next: cos² antiderivative lemma + complete integral `ellipticPi 0 n` via halving at π/4,
  then PConstructible's and main theorem.
- DONE (all): `integral_one_div_one_sub_mul_cos_sq`, `ellipticPi_zero_modulus_eq`,
  `ellipticPi_zero_modulus_Pconstructible`, `ellipticPiInc_zero_Pconstructible_of_le_half_pi`,
  and the headline `ellipticPiInc_zero_modulus_Pconstructible` all compile.
- `lake build Pptc.ThirdKindAll.ModulusZero` succeeded (2797 jobs). Diagnostics empty.
- Axiom check (lean_verify) on `Pconstructible.ellipticPiInc_zero_modulus_Pconstructible`:
  `propext`, `Classical.choice`, `Quot.sound` only — no `sorryAx`.
- Handoff note written to `notes/third-kind/HANDOFF-modulus-zero.md`. No other files touched.

