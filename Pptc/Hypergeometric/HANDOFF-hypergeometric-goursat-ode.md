# HANDOFF: hypergeometric Goursat ODE

Goal: prove `Pconstructible.hypSeries_ode` in `Pptc/Hypergeometric/Goursat.lean`.

```lean
theorem hypSeries_ode (a b c : ℝ) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c))
      + (PowerSeries.C c - PowerSeries.C (a + b + 1) * PowerSeries.X)
        * PowerSeries.derivative ℝ (hypSeries a b c)
      - PowerSeries.C (a * b) * hypSeries a b c = 0
```

Plan: read draft, expand LHS into 5 monomial products via `ring`, then per `m` cases
coeff via simp lemmas, close with `hypCoeff_succ` + field_simp/ring.

## Log
- init: task started.
- Accidentally collapsed Goursat.lean to 1 line with a `Set-Content -NoNewline` replace.
  File was untracked so no git restore. Rewrote whole file from context; added `add_mul` to
  simp sets and fixed `hc1`/`hc2` proofs. Must use `edit` tool only from now on.
- Diagnose run 2 (full file rewrite with add_mul): coefficient extraction now correct. Only
  arithmetic left. Case 0: `field_simp` alone left `c⁻¹`; `field_simp [hc0]` fixes it.
  Case 1: `field_simp [hc0, hc1]` works. Case 2: `field_simp` would not clear
  `(2 + ↑k + c)⁻¹` (hypothesis-form mismatch), and without `set` it unfolded `hypCoeff`
  into `ascPochhammer`. Solution: prove the cross-multiplied recurrence
  `hrec : (c+(k+2))*(k+3)*h_{k+3} = (a+(k+2))*(b+(k+2))*h_{k+2}` via
  `hypCoeff_succ; push_cast; div_mul_cancel₀` and close the goal with `linear_combination hrec`.
- Applied all three fixes to the file; running diagnostics.
- DONE. `lake_check Pptc/Hypergeometric/Goursat.lean` -> "OK - no errors or warnings."
  `lean_diagnostic_messages` -> success, no items. `lean_verify Pconstructible.hypSeries_ode`
  -> axioms only `propext, Classical.choice, Quot.sound`. No sorry/admit/axiom in the file.
  Declarations in file: `Pconstructible.hypSeries_ode` (namespace `Pconstructible`).
  Proof shape: `h0`, `hc0`, `hc1`, `e1`, `e2`; `ext m; rcases m with _|_|k`;
  each case: `rw [map_zero, e1, e2, show X^2 = X*X by ring]`, then
  `simp only [map_add, map_sub, add_mul, PowerSeries.coeff_C_mul, mul_assoc,
   (PowerSeries.coeff_succ_X_mul,) PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]`
  (case 2 omits `coeff_zero_X_mul`), `repeat rw [coeff_hypSeries]`, substitute
  `hypCoeff_succ` and `h0`; case 0: `field_simp [hc0]; ring`; case 1:
  `field_simp [hc0, hc1]; ring`; case 2: cross-multiplied `hrec` via
  `div_mul_cancel₀` + `linear_combination hrec`.
