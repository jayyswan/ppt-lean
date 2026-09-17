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
-- `Central` supplies the central-binomial recurrence `Nat.succ_mul_centralBinom_succ`,
-- `Derivative` the formal derivation `PowerSeries.derivative` and its coefficient rule,
-- `Real.Basic` the field `ℝ` (the `PowerSeries` files are generic over the coefficient ring).
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Pptc.Hypergeometric.SqrtSeries

The formal power series `h = (1 + X)^(-1/2) = ∑ₙ (-1)ⁿ C(2n,n)/4ⁿ Xⁿ`, together with the
three properties needed to handle the square-root prefactor in a quadratic hypergeometric
transformation (Goursat's V7).

The prefactor arises on the *elliptic* side of the transformation: in
`₂F₁(a,b;c;z) = (1-z)^(-1/2) ₂F₁(...)` the binomial prefactor is a square root, so a proof that
lifts the coefficient identity to the analytic level must multiply through by `√(1-z)`
(or, dually, by `1/√(1+z)` after a change of variable). Working formally, that is exactly the
series `h` here, and the two identities recorded below are what make it invertible:

* `sqrtInvSeries_mul_self : h * h * (1 + X) = 1`, i.e. `h` really is `(1+X)^(-1/2)`. This is
  the algebraic fact that lets one cancel the prefactor after multiplying both sides.
* `one_add_X_mul_derivative_sqrtInvSeries : (1 + X) * h' = -(1/2) • h`, the logarithmic
  derivative `h'/h = -1/(2(1+X))`, which is the formal ODE characterisation of the prefactor
  and is used to transport a differential equation through it.

The definition is the plain coefficient formula; all three statements are proved by
coefficient extraction, using the central-binomial recurrence
`(n+1) C(2n+2,n+1) = 2(2n+1) C(2n,n)`. -/

namespace Pconstructible

noncomputable section

/-! ### The coefficient family

The generating function of the central binomial coefficients with alternating signs and the
scale factor `1/4ⁿ`. This is the binomial expansion of `(1 + X)^(-1/2)`:
`(1+X)^(-1/2) = ∑ₙ (-1/2 choose n) Xⁿ` and `(-1/2 choose n) = (-1)ⁿ C(2n,n)/4ⁿ`. -/

/-- The `n`-th coefficient of `(1 + X)^(-1/2)`: `(-1)ⁿ C(2n,n) / 4ⁿ`. -/
-- Definition: `sqrtInvCoeff n = (-1)^n * C(2n,n) / 4^n`.
noncomputable def sqrtInvCoeff (n : ℕ) : ℝ :=
  (-1 : ℝ) ^ n * (Nat.choose (2 * n) n : ℝ) / 4 ^ n

/-- `(1 + X)^(-1/2)` as a formal power series over `ℝ`. -/
-- Definition: the power series whose `n`-th coefficient is `sqrtInvCoeff n`.
noncomputable def sqrtInvSeries : PowerSeries ℝ := PowerSeries.mk sqrtInvCoeff

/-- The coefficients of `sqrtInvSeries` are `sqrtInvCoeff`. -/
-- Theorem: `[Xⁿ] sqrtInvSeries = sqrtInvCoeff n`.
@[simp] theorem coeff_sqrtInvSeries (n : ℕ) :
    PowerSeries.coeff n sqrtInvSeries = sqrtInvCoeff n :=
  PowerSeries.coeff_mk n sqrtInvCoeff

/-- The constant coefficient of `sqrtInvCoeff` is `1`. -/
-- Theorem: `sqrtInvCoeff 0 = 1`.
theorem sqrtInvCoeff_zero : sqrtInvCoeff 0 = 1 := by
  norm_num [sqrtInvCoeff]

/-- The first-order coefficient recurrence of `(1 + X)^(-1/2)`:
`h_{n+1} = -((n + 1/2)/(n + 1)) h_n`, the coefficient form of `(1+X) h' = -(1/2) h`. -/
-- Theorem: `sqrtInvCoeff (n+1) = -(((n:ℝ)+1/2)/((n:ℝ)+1)) * sqrtInvCoeff n`.
theorem sqrtInvCoeff_succ (n : ℕ) :
    sqrtInvCoeff (n + 1) =
      -(((n : ℝ) + 1 / 2) / ((n : ℝ) + 1)) * sqrtInvCoeff n := by
  unfold sqrtInvCoeff
  have hrec := Nat.succ_mul_centralBinom_succ n
  simp only [Nat.centralBinom_eq_two_mul_choose] at hrec
  have hcast : ((n : ℝ) + 1) * (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) := by
    exact_mod_cast hrec
  have hC : (Nat.choose (2 * (n + 1)) (n + 1) : ℝ)
      = 2 * (2 * (n : ℝ) + 1) * (Nat.choose (2 * n) n : ℝ) / ((n : ℝ) + 1) := by
    rw [eq_div_iff (by positivity)]
    nlinarith [hcast]
  have h4 : (4 : ℝ) ^ n ≠ 0 := by positivity
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  rw [hC, pow_succ, pow_succ]
  field_simp
  ring

/-- The coefficient recurrence in the form used by the derivative identity:
`n h_n + (n + 1) h_{n+1} = -(1/2) h_n` for every `n` (the `n = 0` case included). -/
-- Theorem: `(n:ℝ)*sqrtInvCoeff n + ((n:ℝ)+1)*sqrtInvCoeff (n+1) = -(1/2)*sqrtInvCoeff n`.
theorem sqrtInvCoeff_add_succ (n : ℕ) :
    (n : ℝ) * sqrtInvCoeff n + ((n : ℝ) + 1) * sqrtInvCoeff (n + 1)
      = -(1 / 2 : ℝ) * sqrtInvCoeff n := by
  rw [sqrtInvCoeff_succ]
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp
  ring

/-! ### The three required properties -/

/-- The constant coefficient of `(1 + X)^(-1/2)` is `1`. -/
-- Theorem: `constantCoeff sqrtInvSeries = 1`.
theorem constantCoeff_sqrtInvSeries : PowerSeries.constantCoeff sqrtInvSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_sqrtInvSeries]
  exact sqrtInvCoeff_zero

/-- The coefficient of `Xⁿ` in `(1 + X) f'`: `n [Xⁿ]f + (n+1) [X^(n+1)]f`. This is the
`X`-mul coefficient rule `[Xⁿ](X f') = [Xⁿ⁻¹]f'` together with `[Xⁿ]f' = (n+1)[X^(n+1)]f`;
the formula also holds at `n = 0`, where the first term vanishes. -/
-- Theorem: `[Xⁿ]((1+X)*f') = n*[Xⁿ]f + (n+1)*[X^(n+1)]f`.
theorem coeff_one_add_X_mul_derivative (f : PowerSeries ℝ) (n : ℕ) :
    PowerSeries.coeff n ((1 + PowerSeries.X) * PowerSeries.derivative ℝ f)
      = (n : ℝ) * PowerSeries.coeff n f
        + ((n : ℝ) + 1) * PowerSeries.coeff (n + 1) f := by
  have e : (1 + PowerSeries.X) * PowerSeries.derivative ℝ f
      = PowerSeries.derivative ℝ f
        + PowerSeries.X * PowerSeries.derivative ℝ f := by
    ring
  rw [e]
  rcases n with _ | m
  · rw [map_add, PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative]
    norm_num
  · rw [map_add, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_derivative,
      PowerSeries.coeff_derivative]
    push_cast
    ring

/-- The logarithmic-derivative relation `(1 + X) h' = -(1/2) h`, i.e. `h'/h = -1/(2(1+X))`.
This is the formal ODE that singles out the square-root prefactor. -/
-- Theorem: `(1 + X) * derivative ℝ sqrtInvSeries = -(1/2) • sqrtInvSeries`.
theorem one_add_X_mul_derivative_sqrtInvSeries :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries
      = -(1 / 2 : ℝ) • sqrtInvSeries := by
  ext n
  rw [coeff_one_add_X_mul_derivative, map_smul, smul_eq_mul]
  simpa [coeff_sqrtInvSeries] using sqrtInvCoeff_add_succ n

/-- A power series with zero formal derivative is the constant series given by its constant
coefficient. This is the coefficient-induction form of the uniqueness of solutions of `f' = 0`,
used to integrate the ODE for `h² (1+X)`. -/
-- Theorem: if `derivative ℝ f = 0` then `f = C (constantCoeff f)`.
theorem eq_C_of_derivative_eq_zero {f : PowerSeries ℝ}
    (hf : PowerSeries.derivative ℝ f = 0) :
    f = PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext n
  rcases n with _ | n
  · rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_zero_C]
  · have h : PowerSeries.coeff n (PowerSeries.derivative ℝ f) = 0 := by rw [hf, map_zero]
    rw [PowerSeries.coeff_derivative] at h
    rw [PowerSeries.coeff_succ_C]
    exact (mul_eq_zero.mp h).resolve_right (by positivity : ((n : ℝ) + 1) ≠ 0)

/-- The defining square-root identity `h * h * (1 + X) = 1`: `(1+X)^(-1/2)` is the inverse
square root of `1 + X`. It follows by integrating `(h² (1+X))' = 2h((1+X)h') + h² = 0`. -/
-- Theorem: `sqrtInvSeries * sqrtInvSeries * (1 + X) = 1`.
theorem sqrtInvSeries_mul_self :
    sqrtInvSeries * sqrtInvSeries * (1 + PowerSeries.X) = 1 := by
  have hder : PowerSeries.derivative ℝ
      (sqrtInvSeries * sqrtInvSeries * (1 + PowerSeries.X)) = 0 := by
    have hodeC : (1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries
        = PowerSeries.C (-(1 / 2)) * sqrtInvSeries := by
      rw [one_add_X_mul_derivative_sqrtInvSeries, PowerSeries.smul_eq_C_mul]
    have hC2 : (2 : PowerSeries ℝ) * PowerSeries.C (-(1 / 2)) = -1 := by
      rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, ← map_mul]
      norm_num
    have e : PowerSeries.derivative ℝ
        (sqrtInvSeries * sqrtInvSeries * (1 + PowerSeries.X))
        = 2 * sqrtInvSeries
            * ((1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries)
          + sqrtInvSeries * sqrtInvSeries := by
      simp only [Derivation.leibniz, map_add, Derivation.map_one_eq_zero,
        PowerSeries.derivative_X, zero_add, smul_eq_mul, mul_one]
      ring
    rw [e, hodeC]
    rw [show (2 : PowerSeries ℝ) * sqrtInvSeries
          * (PowerSeries.C (-(1 / 2)) * sqrtInvSeries)
        = (2 * PowerSeries.C (-(1 / 2))) * (sqrtInvSeries * sqrtInvSeries) by ring,
      hC2]
    ring
  have hconst : PowerSeries.constantCoeff
      (sqrtInvSeries * sqrtInvSeries * (1 + PowerSeries.X)) = 1 := by
    rw [map_mul, map_mul, map_add, constantCoeff_sqrtInvSeries,
      PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_one]
    ring
  rw [eq_C_of_derivative_eq_zero hder, hconst]
  exact map_one PowerSeries.C

end

end Pconstructible
