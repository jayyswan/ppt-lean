# HANDOFF: hypSeries_subst_ode

Goal (Lean syntax):
```lean
theorem hypSeries_subst_ode {a b c : ℝ} (hc : ∀ n : ℕ, c ≠ -(n : ℝ))
    {φ : PowerSeries ℝ} (hφ : PowerSeries.HasSubst φ) :
    φ * (1 - φ) * PowerSeries.derivative ℝ φ
        * PowerSeries.derivative ℝ
            (PowerSeries.derivative ℝ (PowerSeries.subst φ (hypSeries a b c)))
      + (-(φ * (1 - φ) * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ φ))
          + (PowerSeries.C c - PowerSeries.C (a + b + 1) * φ)
            * (PowerSeries.derivative ℝ φ) ^ 2)
        * PowerSeries.derivative ℝ (PowerSeries.subst φ (hypSeries a b c))
      - PowerSeries.C (a * b) * (PowerSeries.derivative ℝ φ) ^ 3
        * PowerSeries.subst φ (hypSeries a b c) = 0
```
Target file: pptc/Pptc/Hypergeometric/SubstODE.lean, decl name `Pconstructible.hypSeries_subst_ode`.
Plan: pull back hypSeries_ode via PowerSeries.subst/derivative_subst chain rule; linear_combination.

## Log
- Created log. Next: read Goursat.lean, Quadratic.lean, Heun.lean templates.
- Wrote first draft of SubstODE.lean (full proof). Next: diagnostics.
- diagnostics: EMPTY (no errors/warnings) on first draft. Next: lean_verify + lake_check.
- lean_verify: axioms = propext, Classical.choice, Quot.sound (clean). lake_check: OK - no errors or warnings. DONE.
