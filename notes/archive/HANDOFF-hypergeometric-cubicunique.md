# HANDOFF: cubicOp_unique

Target file: `Pptc/Hypergeometric/CubicUnique.lean`
Goal:
```lean
theorem cubicOp_unique {F G : PowerSeries ℝ} (hF : cubicOp F = 0) (hG : cubicOp G = 0)
    (h0 : PowerSeries.coeff 0 F = PowerSeries.coeff 0 G) : F = G
```
Plan: apply to D = F - G; get coeff 1 D = 0 (m=2), coeff 2 D = 0 (m=3),
then strong induction n>=3. Need low-order coeffs of betaSeries and P2/P1/P0.

## Log
- start: created log; exploring Cubic.lean / Heun.lean templates.
- explored templates: Clausen.lean uses explicit-polynomial coeff extraction; our P2/P1/P0 are infinite series so plan uses factorization P2=X^3*U, P1=X^2*Vp, P0=X^3*W + general coeff recurrence via coeff_X_pow_mul. betaSeries = X^2*R with R=betaUnit=27(1+X)^2/(4(1+X+X^2)^3).
- [DONE] Pptc/Hypergeometric/CubicUnique.lean compiled clean. Key constants: coeff 0 betaU = coeff 0 betaVp = 729/8. Main lemmas: cubicOp_eq (factorization), cubicOp_coeff_two, cubicOp_coeff_rec (n>=2), cubicOp_unique. lake_check -> "OK - no errors or warnings." lean_verify cubicOp_unique -> axioms [propext, Classical.choice, Quot.sound]. No sorry/axiom. All lines <= 100.
- draft compiles except: (a) numeral-vs-C issue for constantCoeff of numerals, (b) ring vs C-form. Reverted defs to plain numerals. Testing map_ofNat for constantCoeff (2 : PowerSeries R) = 2.
