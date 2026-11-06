# Phase 2: general Goursat quadratic transformation

Goal (Lean): for a, b : ℝ with `∀ n, a + b + 1/2 ≠ -(n:ℝ)`, and 0 <= z < 1/2,
  hyp (2*a) (2*b) (a + b + 1/2) z = hyp a b (a + b + 1/2) (4*z*(1-z))

Target file: pptc/Pptc/Hypergeometric/GoursatGeneral.lean (new, only file created).
Reference: Pptc/Hypergeometric/Quadratic.lean (a = b = 1/4 case), SubstODE.lean, Goursat.lean.

- [start] reading plan and reference files.
- Sympy check: with w = 4X(1-X), E = w(1-w)w'F'' + (-w(1-w)w'' + (c-(a+b+1)w)w'^2)F'
  - ab w'^3 F equals 16(1-2X)^3 * [X(1-X)F'' + c(1-2X)F' - 4abF] EXACTLY iff c = a+b+1/2.
  And that bracket is the (2a,2b;c) hypergeometric operator. Verified = 0 differences.
- Read Quadratic.lean fully (1003 lines): formal part, recurrence, analytic transfer.
- DONE `two_mul_C_half : 2 * C(1/2) = 1` in ℝ⟦X⟧ (needed because ring sees C(1/2) as atom;
  residual of the factorisation is 32 F' X(1-X)(1-2X)^2 (2 C(1/2) - 1)).
- DONE `quadSubst_operator_factor`: pulled-back (a,b;c) operator = 16(1-2X)^3 * (2a,2b;c) op.
- DONE `hypSeriesQuadG_ode`: X(1-X)F'' + c(1-2X)F' - 4ab F = 0; used IsUnit cancellation
  (needs Mathlib.RingTheory.PowerSeries.Inverse import for PowerSeries.isUnit_iff_constantCoeff).
- DONE `hypSeriesQuadG_ode_expand` (2c form) and `coeff_hypSeriesQuadG_rec`:
  (n+1)(n+c) b_{n+1} = (n+2a)(n+2b) b_n, 3-case coefficient extraction (0, 1, k+2).
- DONE `hypSeriesQuadG_eq`: subst quadSubst (hypSeries a b c) = hypSeries (2a) (2b) c.
  constant term via coeff_subst' + finsum_eq_single; ratio + induction with hypCoeff_succ.
- DONE analytic: `quadFamilyG`, `summable_quadFamilyG`, `tsum_hypCoeff_mul_coeff_quadSubstG`,
  `hasSum_quadFamilyG`, `hyp_goursat_small`.
- DONE `hyp_goursat` (final): analytic continuation on Ioo ((1-√2)/2, 1/2).
- ALL diagnostics clean (lean_diagnostic_messages success, no warnings).
- styles: fixed the only >100 char line (module docstring).
- FINAL CHECK: `lake env lean Pptc/Hypergeometric/GoursatGeneral.lean` from pptc/ → EXIT=0,
  no output (no errors, no warnings).
- AXIOM CHECK: lean_verify on Pconstructible.hyp_goursat → axioms = [propext,
  Classical.choice, Quot.sound], trust = standard, no warnings, no sorryAx.
- DELIVERABLE COMPLETE: `Pconstructible.hyp_goursat` proved.
  Signature: {a b : ℝ} (hc : ∀ n, a + b + 1/2 ≠ -(n:ℝ)) {z : ℝ} (hz0 : 0 ≤ z)
    (hz : z < 1/2) → hyp (2*a) (2*b) (a+b+1/2) z = hyp a b (a+b+1/2) (4*z*(1-z)).
- Only one new file created; no existing file edited; no scratch files left in the repo.

## Note on the sympy vs Lean factor constant
The raw sympy factorisation gives `E - 16(1-2X)^3 D = 64 F' X (1-X)(1-2X)^2 (c - a - b - 1/2)`.
After `rw [h]` and pushing `C` through `+,-,*`, `C(1/2)` is an independent atom H, and the
residual is `32 F' X (1-X)(1-2X)^2 (2H - 1)`; `two_mul_C_half` gives `2H = 1`, so the
`linear_combination` coefficient is 32 (not 64).

