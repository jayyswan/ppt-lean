/- Copyright (c) 2024 Lean Community. All rights reserved.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

This file is part of the Pptc (PowerPoint Constructibility) project.
-/

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
-- `Pptc.Hypergeometric.Quadratic` supplies `hypSeries`, its coefficient lemma
-- `coeff_hypSeries`, the substitution and chain-rule API of `PowerSeries`, and the
-- worked `(1/4, 1/4; 1)` ODE `hypSeries_quarter_ode` whose proof is the template here.
import Pptc.Hypergeometric.Quadratic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Pptc.Hypergeometric.Goursat

The quadratic transformation of Goursat (V7 of `PLAN-hypergeometric-00-overview.md`),

`₂F₁(1/4, 3/4; 1; z) = (1 + √z)^(−1/2) · ₂F₁(1/2, 1/2; 1; 2√z / (1 + √z))`   for `0 ≤ z < 1`,

proved at the level of formal power series and then transferred to the real interval.

## Why the general hypergeometric equation

`Pptc.Hypergeometric.Quadratic` proves V6 by reading the coefficient recurrence of the
hypergeometric equation off the substituted series `H(4X(1-X))`, where `H = ₂F₁(1/4,1/4;1;·)`.
The same route reaches V7 once the *general* equation

`X(1−X) H'' + (c − (a+b+1) X) H' − ab H = 0`,   `H = ∑ₙ hypCoeff a b c n Xⁿ`,

is available for the two series that meet in V7 — `(1/4, 3/4; 1)` and `(1/2, 1/2; 1)`. The first
section below lands it; it is the formal-power-series form of the classical hypergeometric
differential equation, and its proof is a one-step coefficient computation with `hypCoeff_succ`.
-/

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! ### The general hypergeometric equation

The residual `X(1−X) H'' + (c − (a+b+1) X) H' − ab H` vanishes coefficient by coefficient: at
`Xᵐ` with `m ≥ 2` it is `(m+1)(m+c) h_{m+1} − (m+a)(m+b) h_m`, which is exactly `hypCoeff_succ`;
the coefficients `m = 0, 1` are the same identity at `n = 0, 1`, where the `X²` term is absent.
The hypothesis `c ∉ −ℕ` is needed: at `c = 0` the recurrence degenerates and Mathlib's junk
value `hypCoeff a b 0 n = 0 (n ≥ 1)` does not solve the equation. -/

/-- The general hypergeometric equation satisfied by the formal hypergeometric series
`hypSeries a b c`: `X(1−X) H'' + (c − (a+b+1)X) H' − ab H = 0`. -/
-- Theorem: the hypergeometric series `hypSeries a b c` satisfies the hypergeometric ODE.
theorem hypSeries_ode (a b c : ℝ) (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
    PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c))
      + (PowerSeries.C c - PowerSeries.C (a + b + 1) * PowerSeries.X)
        * PowerSeries.derivative ℝ (hypSeries a b c)
      - PowerSeries.C (a * b) * hypSeries a b c = 0 := by
  have h0 : hypCoeff a b c 0 = 1 := by
    norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  have hc0 : c ≠ 0 := by simpa using hc 0
  have hc1 : c + 1 ≠ 0 := by
    intro h
    exact hc 1 (by rw [show ((1 : ℕ) : ℝ) = 1 by norm_num]; linarith)
  -- Peel the product `X (1 - X)` and the linear factor off the highest derivatives, so that
  -- every leftover factor of `X` sits on the *left* of a power series and the coefficient
  -- rules `coeff_zero_X_mul` / `coeff_succ_X_mul` can fire.
  have e1 : PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c))
      = PowerSeries.X * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c))
        - PowerSeries.X ^ 2
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries a b c)) := by
    ring
  have e2 : (PowerSeries.C c - PowerSeries.C (a + b + 1) * PowerSeries.X)
        * PowerSeries.derivative ℝ (hypSeries a b c)
      = PowerSeries.C c * PowerSeries.derivative ℝ (hypSeries a b c)
        - PowerSeries.C (a + b + 1)
            * (PowerSeries.X * PowerSeries.derivative ℝ (hypSeries a b c)) := by
    ring
  ext m
  rcases m with _ | _ | k
  · -- `m = 0`: only `c h₁ − ab h₀` survives, and `h₁ = ab h₀ / c`.
    rw [map_zero, e1, e2, show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring]
    simp only [map_add, map_sub, add_mul, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]
    repeat rw [coeff_hypSeries]
    rw [hypCoeff_succ a b c 0, h0]
    field_simp [hc0]
    ring
  · -- `m = 1`: `2(1+c) h₂ − (a+1)(b+1) h₁`, and `h₂ = h₁ (a+1)(b+1) / (2(c+1))`.
    rw [map_zero, e1, e2, show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring]
    simp only [map_add, map_sub, add_mul, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]
    repeat rw [coeff_hypSeries]
    rw [hypCoeff_succ a b c 1, hypCoeff_succ a b c 0, h0]
    field_simp [hc0, hc1]
    ring
  · -- `m = k + 2`: `(k+3)(k+2+c) h_{k+3} − (k+2+a)(k+2+b) h_{k+2}`.
    rw [map_zero, e1, e2, show PowerSeries.X ^ 2 = PowerSeries.X * PowerSeries.X by ring]
    simp only [map_add, map_sub, add_mul, PowerSeries.coeff_C_mul, mul_assoc,
      PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative]
    repeat rw [coeff_hypSeries]
    rw [show k + 1 + 1 + 1 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega]
    push_cast
    have hc2 : c + (k : ℝ) + 2 ≠ 0 := by
      intro h
      apply hc (k + 2)
      push_cast
      linarith
    -- Cross-multiplied form of `hypCoeff_succ`, free of division.
    have hCN : (c + ((k : ℝ) + 2)) * ((k : ℝ) + 2 + 1) ≠ 0 := by
      apply mul_ne_zero
      · intro h
        exact hc2 (by linarith)
      · positivity
    have hrec : (c + ((k : ℝ) + 2)) * ((k : ℝ) + 2 + 1) * hypCoeff a b c (k + 3)
        = (a + ((k : ℝ) + 2)) * (b + ((k : ℝ) + 2)) * hypCoeff a b c (k + 2) := by
      rw [hypCoeff_succ a b c (k + 2)]
      push_cast
      rw [mul_comm ((c + ((k : ℝ) + 2)) * ((k : ℝ) + 2 + 1)), mul_assoc,
        div_mul_cancel₀ _ hCN]
      ring
    linear_combination hrec

end

end Pconstructible
