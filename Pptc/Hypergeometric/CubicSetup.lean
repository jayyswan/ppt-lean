/-
Copyright (c) 2024 Lean Community. All rights reserved.

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

-- Targeted imports rather than `import Mathlib`.
-- `Pptc.Hypergeometric.SqrtSeries` provides `sqrtInvSeries = (1+X)^(-1/2)` and the two
-- identities `sqrtInvSeries_mul_self` and `one_add_X_mul_derivative_sqrtInvSeries`;
-- `Mathlib.RingTheory.PowerSeries.Substitution` supplies `PowerSeries.subst`, its algebra
-- homomorphism `substAlgHom`, the chain rule `derivative_subst` and `PowerSeries.rescale`;
-- `Mathlib.RingTheory.PowerSeries.Inverse` supplies `PowerSeries.inv_mul_cancel`, which
-- clears the denominators of `alphaSeries` and `betaSeries`.
import Pptc.Hypergeometric.SqrtSeries
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Pptc.Hypergeometric.CubicSetup

The four formal power series that appear in Ramanujan's **cubic** signature transformation

`₂F₁(1/3, 2/3; 1; β(p)) = γ(p) · ₂F₁(1/2, 1/2; 1; α(p))`,

together with the elementary algebraic identities they satisfy. Writing

* `α(p) = p³(2+p)/(1+2p)`,
* `β(p) = 27p²(1+p)² / (4(1+p+p²)³)`,
* `γ(p) = (1+p+p²)/√(1+2p)`,

the transformation is proved by checking that both sides satisfy the same hypergeometric
differential equation and the same initial condition. The present file isolates the
*scalar* bookkeeping: the square root `γ` is a power series only after the factor
`1/√(1+2p)` is expanded as `(1+2p)^(-1/2) = subst (2X) sqrtInvSeries`, and the rational
functions `α`, `β` must be shown to be invertible algebraic rewrites. The four
statements below are exactly what that verification consumes:

* `gSeries_mul_self` inverts the square root (`g²(1+2X) = 1`);
* `one_add_two_X_mul_derivative_gSeries` is the logarithmic derivative `g'/g = -1/(1+2X)`,
  the formal ODE that transports a differential equation through the prefactor;
* `gammaSeries_mul_self` says `γ²(1+2X) = (1+X+X²)²`, so `γ` is a genuine square root of a
  rational function and can be cancelled after squaring;
* `alphaSeries_mul` and `betaSeries_mul` clear the denominators of `α` and `β`, and
  `hasSubst_alphaSeries` / `hasSubst_betaSeries` record that both vanish at `p = 0`, which is
  what makes them legal substitutions into a power series.

Everything is a formal identity over `ℝ`; no convergence is used. -/

namespace Pconstructible

noncomputable section

/-! ### The four series

`gSeries` is the square-root prefactor, `gammaSeries = (1+X+X²) gSeries` multiplies it by
the numerator `1+p+p²`, and `alphaSeries`/`betaSeries` are the two modular-`p` variables,
written as rational functions. Each of `alphaSeries` and `betaSeries` has a unit denominator
(`1+2X` and `4(1+X+X²)³` both have constant coefficient `≠ 0`), and each carries an explicit
factor of `X³` respectively `X²` in its numerator, hence vanishes at `X = 0`. -/

/-- `(1+2X)^(-1/2)`, the square-root prefactor of the cubic transformation. -/
noncomputable def gSeries : PowerSeries ℝ :=
  PowerSeries.subst (2 * PowerSeries.X) sqrtInvSeries

/-- `γ(p) = (1+p+p²)/√(1+2p)`. -/
noncomputable def gammaSeries : PowerSeries ℝ :=
  (1 + PowerSeries.X + PowerSeries.X ^ 2) * gSeries

/-- `α(p) = p³(2+p)/(1+2p)`. -/
noncomputable def alphaSeries : PowerSeries ℝ :=
  PowerSeries.X ^ 3 * (2 + PowerSeries.X) * (1 + 2 * PowerSeries.X)⁻¹

/-- `β(p) = 27p²(1+p)²/(4(1+p+p²)³)`. -/
noncomputable def betaSeries : PowerSeries ℝ :=
  27 * PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 2
    * (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3)⁻¹

/-! ### The substitution `w = 2X` and its derivative

`gSeries` is `sqrtInvSeries` composed with `2X`; the two inputs to the chain rule are that
`2X` vanishes at the origin (so it can be substituted) and that `d(2X)/dX = 2`. -/

/-- `2X` has zero constant coefficient, so it is an admissible substitution. -/
-- Theorem: `HasSubst (2 * X)`.
theorem hasSubst_two_mul_X : PowerSeries.HasSubst (2 * PowerSeries.X : PowerSeries ℝ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

/-- The chain-rule factor `d(2X)/dX = 2`. -/
-- Theorem: `derivative ℝ (2 * X) = 2`.
theorem derivative_two_mul_X :
    PowerSeries.derivative ℝ (2 * PowerSeries.X : PowerSeries ℝ) = 2 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl]
  simp only [Derivation.leibniz, PowerSeries.derivative_X, PowerSeries.derivative_C,
    smul_eq_mul, mul_one, mul_zero, add_zero]

/-! ### The square-root prefactor -/

/-- `gSeries` is the rescaling `f ↦ f(2X)` of `sqrtInvSeries`, which makes its constant term
immediately computable from `PowerSeries.coeff_rescale`. -/
-- Theorem: `gSeries = rescale 2 sqrtInvSeries`.
theorem gSeries_eq_rescale : gSeries = PowerSeries.rescale 2 sqrtInvSeries := by
  rw [gSeries, PowerSeries.rescale_eq_subst]
  congr 1
  rw [PowerSeries.smul_eq_C_mul, show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl]

/-- The constant coefficient of `(1+2X)^(-1/2)` is `1`. -/
-- Theorem: `constantCoeff gSeries = 1`.
theorem constantCoeff_gSeries : PowerSeries.constantCoeff gSeries = 1 := by
  rw [gSeries_eq_rescale, ← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    PowerSeries.coeff_rescale, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    constantCoeff_sqrtInvSeries]
  norm_num

/-- `g*g*(1+2X) = 1`, i.e. `g = (1+2X)^(-1/2)`: this is `sqrtInvSeries_mul_self` pushed
forward along the substitution `X ↦ 2X`. -/
-- Theorem: `gSeries * gSeries * (1 + 2 * X) = 1`.
theorem gSeries_mul_self : gSeries * gSeries * (1 + 2 * PowerSeries.X) = 1 := by
  have h2 : PowerSeries.HasSubst (2 * PowerSeries.X : PowerSeries ℝ) := hasSubst_two_mul_X
  have h := congrArg (PowerSeries.subst (2 * PowerSeries.X : PowerSeries ℝ))
    sqrtInvSeries_mul_self
  rw [gSeries]
  simp only [← PowerSeries.coe_substAlgHom h2, map_mul, map_add, map_one,
    PowerSeries.substAlgHom_X h2] at h ⊢
  exact h

/-- `(1+2X) g' = -g`: the logarithmic derivative of `(1+2X)^(-1/2)`, obtained by pushing
`(1+X) h' = -(1/2) h` through `X ↦ 2X` with the chain rule. -/
-- Theorem: `(1 + 2 * X) * derivative ℝ gSeries = -gSeries`.
theorem one_add_two_X_mul_derivative_gSeries :
    (1 + 2 * PowerSeries.X) * PowerSeries.derivative ℝ gSeries = -gSeries := by
  have h2 : PowerSeries.HasSubst (2 * PowerSeries.X : PowerSeries ℝ) := hasSubst_two_mul_X
  have hder : PowerSeries.derivative ℝ gSeries
      = PowerSeries.subst (2 * PowerSeries.X : PowerSeries ℝ)
          (PowerSeries.derivative ℝ sqrtInvSeries) * 2 := by
    rw [gSeries, PowerSeries.derivative_subst h2, derivative_two_mul_X]
  have hone : (1 + 2 * PowerSeries.X : PowerSeries ℝ)
      = PowerSeries.subst (2 * PowerSeries.X : PowerSeries ℝ)
          (1 + PowerSeries.X : PowerSeries ℝ) := by
    rw [← PowerSeries.coe_substAlgHom h2, map_add, map_one, PowerSeries.substAlgHom_X h2]
  have hc : PowerSeries.C (-(1 / 2) : ℝ) * (2 : PowerSeries ℝ) = -1 := by
    rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, ← map_mul]
    simp
  rw [hder, hone, ← mul_assoc, ← PowerSeries.subst_mul h2,
    one_add_X_mul_derivative_sqrtInvSeries, PowerSeries.subst_smul h2, gSeries]
  rw [PowerSeries.smul_eq_C_mul]
  linear_combination hc * (PowerSeries.subst (2 * PowerSeries.X : PowerSeries ℝ) sqrtInvSeries)

/-! ### The numerator `1+X+X²` and the first coordinate `α` -/

/-- `γ²(1+2X) = (1+X+X²)²`, obtained from `g²(1+2X) = 1` by multiplying through by the
square of the numerator `1+X+X²`. -/
-- Theorem: `gammaSeries * gammaSeries * (1 + 2 * X) = (1 + X + X^2)^2`.
theorem gammaSeries_mul_self :
    gammaSeries * gammaSeries * (1 + 2 * PowerSeries.X)
      = (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2 := by
  rw [gammaSeries]
  linear_combination ((1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 2) * gSeries_mul_self

/-- `α(1+2X) = X³(2+X)`: `1+2X` is a unit (its constant term is `1`), so the denominator of
`alphaSeries` cancels against the factor `(1+2X)` on the left. -/
-- Theorem: `alphaSeries * (1 + 2 * X) = X^3 * (2 + X)`.
theorem alphaSeries_mul :
    alphaSeries * (1 + 2 * PowerSeries.X) = PowerSeries.X ^ 3 * (2 + PowerSeries.X) := by
  have h : (1 + 2 * PowerSeries.X : PowerSeries ℝ)⁻¹
        * (1 + 2 * PowerSeries.X) = 1 :=
    PowerSeries.inv_mul_cancel _ (by simp)
  rw [alphaSeries, mul_assoc, h, mul_one]

/-- `β · 4(1+X+X²)³ = 27X²(1+X)²`: `4(1+X+X²)³` has constant coefficient `4 ≠ 0`, hence is a
unit, and cancels against the denominator of `betaSeries`. -/
-- Theorem: `betaSeries * (4 * (1 + X + X^2)^3) = 27 * X^2 * (1 + X)^2`.
theorem betaSeries_mul :
    betaSeries * (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3)
      = 27 * PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 2 := by
  have hden : PowerSeries.constantCoeff
      (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3 : PowerSeries ℝ) = 4 := by
    rw [show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl]
    simp [PowerSeries.constantCoeff_X]
  have h : (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3 : PowerSeries ℝ)⁻¹
        * (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3) = 1 :=
    PowerSeries.inv_mul_cancel (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3
      : PowerSeries ℝ) (by rw [hden]; norm_num)
  rw [betaSeries, mul_assoc, h, mul_one]

/-! ### `α` and `β` are admissible substitutions

Both vanish at `p = 0`: the explicit numerator `X³` resp. `X²` forces the constant
coefficient to be `0`, so `HasSubst` holds. -/

/-- `alphaSeries` vanishes at the origin, hence is an admissible substitution. -/
-- Theorem: `HasSubst alphaSeries`.
theorem hasSubst_alphaSeries : PowerSeries.HasSubst alphaSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [alphaSeries]
    simp)

/-- `betaSeries` vanishes at the origin, hence is an admissible substitution. -/
-- Theorem: `HasSubst betaSeries`.
theorem hasSubst_betaSeries : PowerSeries.HasSubst betaSeries :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by
    rw [betaSeries]
    simp)

end

end Pconstructible
