# HANDOFF: Heun.lean (V7 w = sqrt(z) reduction)

Target file: `Pptc/Hypergeometric/Heun.lean`
Deliverables: `phiSeries`, `coeff_zero_phiSeries`, `phiSeries_heun`, `heun_uniqueness`.

Plan:
1. Read Goursat.lean + Quadratic.lean template proof `hypSeries_quarter_subst_ode`.
2. Write phiSeries + coeff_zero.
3. Pull ODE back via subst template for phiSeries_heun.
4. Coefficient recurrence for heun_uniqueness.
5. Final lake_check.

## Log
- [start] Created log. Goal exactly as specified by caller.
- [note] Caller statement `(3 / 4 : ℝ) * PowerSeries.X * ...` does NOT elaborate: no
  `HMul ℝ (PowerSeries ℝ) (PowerSeries ℝ)`. Replaced by `PowerSeries.C (3 / 4) * ...`
  (mathematically identical) in the 3 statements. Everything else kept verbatim.
- [ok] hasSubst_X_sq, derivative_X_sq, derivative_derivative_X_sq compile.
- [ok] coeff_zero_phiSeries compiles.
- [ok] phiSeries_heun compiles (needed explicit constant certificates
  C 1 = 1, C 2 = 2, 4*C(3/16) = C(3/4) for the final linear_combination).
- [ok] heun_ode_expand, heun_coeff_one, heun_coeff_rec, heun_uniqueness all compile;
  `lean_diagnostic_messages` returns zero items (no errors, warnings, or sorry).
- [next] run final `lake_check Pptc/Hypergeometric/Heun.lean`.
- [DONE] lake_check -> "OK - no errors or warnings." Max line length 99. No sorry/axiom.
  Declarations: hasSubst_X_sq, derivative_X_sq, derivative_derivative_X_sq, phiSeries,
  coeff_zero_phiSeries, phiSeries_heun, heun_ode_expand, heun_coeff_one, heun_coeff_rec,
  heun_uniqueness. Only deviation from the spec: `(3/4 : ℝ) * X` in the three statements
  became `PowerSeries.C (3 / 4) * X` (the former does not elaborate).
- [verify] lean_verify phiSeries_heun / coeff_zero_phiSeries / heun_uniqueness:
  axioms = [propext, Classical.choice, Quot.sound], warnings [].
