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

-- Targeted imports: `Goursat` supplies the general hypergeometric ODE
-- `hypSeries_ode`; `SqrtSeries` supplies the square-root prefactor `sqrtInvSeries`
-- and its logarithmic-derivative identities.
import Pptc.Hypergeometric.Goursat
import Pptc.Hypergeometric.SqrtSeries
import Mathlib.RingTheory.PowerSeries.Inverse

/-! # Pptc.Hypergeometric.HeunMobius

The right-hand side of Goursat's quadratic transformation (V7),

`₂F₁(1/4, 3/4; 1; z) = (1 + √z)^(−1/2) · ₂F₁(1/2, 1/2; 1; 2√z / (1 + √z))`,

in the variable `w = √z`. Writing `M(w) = ₂F₁(1/2, 1/2; 1; 2w/(1+w))` for the Möbius
pullback `mobius : w ↦ 2w/(1+w)` of the hypergeometric series, and `R(w) = (1+w)^(−1/2) M(w)`
for its square-root prefactor, both `M` and `R` are power series in `w` with no square roots.

* `mSeries_ode` shows that `M` satisfies the Möbius pullback of the hypergeometric equation
  `X(1−X)M'' + (1−2X)M' − (1/4)M = 0`, namely
  `X(1−X)(1+X)²M'' + (1−2X)(1+X)²M' − (1/2)M = 0`. The pullback is direct: `mobius'=2g²`,
  `mobius''=−4g³` and `mobius(1−mobius)=2X(1−X)g²` with `g=(1+X)⁻¹`, so multiplying the
  substituted equation by `2` reproduces the stated coefficients.

* `rSeries_heun` shows that `R` satisfies the Heun-type equation
  `X(1−X²)R'' + (1−3X²)R' − (3/4)X R = 0`. This is the prefactor computation: after
  `(1+X)R' = −(1/2)RM/M + (1+X)M'` and `(1+X)²R'' = (3/4)M − (1+X)M' + (1+X)²M''`,
  the left side factors as `(1+X)·mSeries_ode`. The factor `(1+X)²` is a unit (constant
  coefficient `1`), so `rSeries_heun` follows.

The substitution `X ↦ 2X/(1+X)` is the Möbius map sending the singularities `0, 1, ∞` of the
hypergeometric equation to `0, 1, −1`; the three prefactor identities
`(1+X)h' = −(1/2)h`, `(1+X)h'' = −(3/2)h'`, `(1+X)²h'' = (3/4)h` (with `h = sqrtInvSeries`)
avoid all series inverses. -/

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-- The Möbius substitution `X ↦ 2X/(1+X)`. -/
noncomputable def mobius : PowerSeries ℝ := 2 * PowerSeries.X * (1 + PowerSeries.X)⁻¹

/-- `(1+X)⁻¹`, the reciprocal prefactor appearing in `mobius`. -/
private noncomputable def invOnePlusX : PowerSeries ℝ := (1 + PowerSeries.X)⁻¹

private theorem invOnePlusX_mul : invOnePlusX * (1 + PowerSeries.X) = 1 := by
  rw [invOnePlusX]
  exact PowerSeries.inv_mul_cancel _ (by simp)

private theorem onePlusX_mul_invOnePlusX : (1 + PowerSeries.X) * invOnePlusX = 1 := by
  rw [invOnePlusX]
  exact PowerSeries.mul_inv_cancel _ (by simp)

private theorem mobius_eq : mobius = 2 * PowerSeries.X * invOnePlusX := by
  rw [mobius, invOnePlusX]

private theorem onePlusX_ne_zero : (1 + PowerSeries.X : PowerSeries ℝ) ≠ 0 := by
  intro h
  have hc : (1 : ℝ) = 0 := by
    simpa using congrArg PowerSeries.constantCoeff h
  exact one_ne_zero hc

private theorem constantCoeff_mobius : PowerSeries.constantCoeff mobius = 0 := by
  rw [mobius]
  simp

/-- `mobius` has zero constant coefficient, hence is an admissible substitution. -/
-- Theorem: `HasSubst mobius`.
theorem hasSubst_mobius : PowerSeries.HasSubst mobius :=
  PowerSeries.HasSubst.of_constantCoeff_zero' constantCoeff_mobius

/-- `₂F₁(1/2,1/2;1;·)` composed with `mobius`. -/
noncomputable def mSeries : PowerSeries ℝ :=
  PowerSeries.subst mobius (hypSeries (1 / 2) (1 / 2) 1)

private theorem derivative_invOnePlusX :
    PowerSeries.derivative ℝ invOnePlusX = -invOnePlusX ^ 2 := by
  rw [invOnePlusX, PowerSeries.derivative_inv']
  simp

private theorem derivative_two : PowerSeries.derivative ℝ (2 : PowerSeries ℝ) = 0 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]

private theorem derivative_two_mul_X :
    PowerSeries.derivative ℝ (2 * PowerSeries.X) = (2 : PowerSeries ℝ) := by
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_two, PowerSeries.derivative_X,
    mul_one, mul_zero, add_zero]

private theorem derivative_mobius :
    PowerSeries.derivative ℝ mobius = 2 * invOnePlusX ^ 2 := by
  rw [mobius_eq, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_two_mul_X,
    derivative_invOnePlusX]
  have hu : invOnePlusX * (1 + PowerSeries.X) = 1 := invOnePlusX_mul
  linear_combination (-2 * invOnePlusX) * hu

private theorem mobius_mul_onePlusX : mobius * (1 + PowerSeries.X) = 2 * PowerSeries.X := by
  rw [mobius_eq]
  calc 2 * PowerSeries.X * invOnePlusX * (1 + PowerSeries.X)
      = 2 * PowerSeries.X * (invOnePlusX * (1 + PowerSeries.X)) := by ring
    _ = 2 * PowerSeries.X * 1 := by rw [invOnePlusX_mul]
    _ = 2 * PowerSeries.X := by ring

private theorem onePlusX_mul_mobius :
    (1 + PowerSeries.X) * mobius = 2 * PowerSeries.X := by
  rw [mul_comm, mobius_mul_onePlusX]

private theorem onePlusX_mul_one_sub_mobius :
    (1 + PowerSeries.X) * (1 - mobius) = 1 - PowerSeries.X := by
  rw [mul_sub, mul_one, onePlusX_mul_mobius]
  ring

private theorem sq_mul_derivative_mobius :
    (1 + PowerSeries.X) ^ 2 * PowerSeries.derivative ℝ mobius = 2 := by
  rw [derivative_mobius]
  calc (1 + PowerSeries.X) ^ 2 * (2 * invOnePlusX ^ 2)
      = 2 * ((1 + PowerSeries.X) * invOnePlusX) ^ 2 := by ring
    _ = 2 * 1 ^ 2 := by rw [onePlusX_mul_invOnePlusX]
    _ = 2 := by ring

private theorem derivative_derivative_mobius :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius) = -4 * invOnePlusX ^ 3 := by
  rw [derivative_mobius, Derivation.leibniz, smul_eq_mul, smul_eq_mul, derivative_two,
    PowerSeries.derivative_pow, derivative_invOnePlusX]
  ring

private theorem cube_mul_deriv2_mobius :
    (1 + PowerSeries.X) ^ 3 * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius)
      = -4 := by
  rw [derivative_derivative_mobius]
  calc (1 + PowerSeries.X) ^ 3 * (-4 * invOnePlusX ^ 3)
      = -4 * ((1 + PowerSeries.X) * invOnePlusX) ^ 3 := by ring
    _ = -4 * 1 ^ 3 := by rw [onePlusX_mul_invOnePlusX]
    _ = -4 := by ring

/-- The quadratic coefficient identity of the Möbius pullback:
`X(1−X)(1+X)² · (mobius')² = 2 · mobius(1−mobius)`. -/
-- Theorem: `X(1−X)(1+X)²(mobius')² = 2·mobius(1−mobius)`.
private theorem mobius_quad_identity :
    PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
        * (PowerSeries.derivative ℝ mobius) ^ 2
      = 2 * (mobius * (1 - mobius)) := by
  refine mul_left_cancel₀ (pow_ne_zero 2 onePlusX_ne_zero) ?_
  calc (1 + PowerSeries.X) ^ 2
        * (PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
            * (PowerSeries.derivative ℝ mobius) ^ 2)
      = PowerSeries.X * (1 - PowerSeries.X)
          * ((1 + PowerSeries.X) ^ 2 * PowerSeries.derivative ℝ mobius) ^ 2 := by ring
    _ = PowerSeries.X * (1 - PowerSeries.X) * 2 ^ 2 := by rw [sq_mul_derivative_mobius]
    _ = 4 * (PowerSeries.X * (1 - PowerSeries.X)) := by ring
    _ = (1 + PowerSeries.X) ^ 2 * (2 * (mobius * (1 - mobius))) := by
      rw [show (1 + PowerSeries.X) ^ 2 * (2 * (mobius * (1 - mobius)))
            = 2 * ((1 + PowerSeries.X) * mobius)
                * ((1 + PowerSeries.X) * (1 - mobius)) by ring]
      rw [onePlusX_mul_mobius, onePlusX_mul_one_sub_mobius]
      ring

/-- The linear coefficient identity of the Möbius pullback:
`X(1−X)(1+X)² · mobius'' + (1−2X)(1+X)² · mobius' = 2·(1−2·mobius)`. -/
-- Theorem: `X(1−X)(1+X)² mobius'' + (1−2X)(1+X)² mobius' = 2(1−2mobius)`.
private theorem mobius_lin_identity :
    PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius)
      + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ mobius
      = 2 * (1 - 2 * mobius) := by
  refine mul_left_cancel₀ (pow_ne_zero 2 onePlusX_ne_zero) ?_
  calc (1 + PowerSeries.X) ^ 2
        * (PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
              * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius)
            + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
              * PowerSeries.derivative ℝ mobius)
      = PowerSeries.X * (1 - PowerSeries.X)
          * ((1 + PowerSeries.X)
              * ((1 + PowerSeries.X) ^ 3
                  * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius)))
        + (1 - 2 * PowerSeries.X)
            * ((1 + PowerSeries.X) ^ 2 * PowerSeries.derivative ℝ mobius)
            * (1 + PowerSeries.X) ^ 2 := by ring
    _ = PowerSeries.X * (1 - PowerSeries.X) * ((1 + PowerSeries.X) * (-4))
        + (1 - 2 * PowerSeries.X) * 2 * (1 + PowerSeries.X) ^ 2 := by
      rw [cube_mul_deriv2_mobius, sq_mul_derivative_mobius]
    _ = (1 + PowerSeries.X) ^ 2 * (2 * (1 - 2 * mobius)) := by
      rw [show (1 + PowerSeries.X) ^ 2 * (2 * (1 - 2 * mobius))
            = 2 * (1 + PowerSeries.X) ^ 2
                - 4 * ((1 + PowerSeries.X) * mobius) * (1 + PowerSeries.X) by ring]
      rw [show (1 + PowerSeries.X) * mobius = 2 * PowerSeries.X by
        rw [mul_comm, mobius_mul_onePlusX]]
      ring

/-- The pulled-back (Möbius) equation for `mSeries`. -/
-- Theorem: `X(1-X)(1+X)²M'' + (1-2X)(1+X)²M' - (1/2)M = 0` for `M = mSeries`.
theorem mSeries_ode :
    PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mSeries)
      + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ mSeries
      - PowerSeries.C (1 / 2) * mSeries = 0 := by
  have hsub : PowerSeries.HasSubst mobius := hasSubst_mobius
  have hzero : PowerSeries.subst mobius (0 : PowerSeries ℝ) = 0 := by
    simp only [← PowerSeries.coe_substAlgHom hsub, map_zero]
  have hY : PowerSeries.X * (1 - PowerSeries.X)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
      + (1 - 2 * PowerSeries.X)
        * PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)
      - PowerSeries.C (1 / 4) * hypSeries (1 / 2) (1 / 2) 1 = 0 := by
    have h := hypSeries_ode (1 / 2) (1 / 2) 1 (by
      intro n hc
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith)
    have h2 : PowerSeries.C (1 / 2 + 1 / 2 + 1 : ℝ) = (2 : PowerSeries ℝ) := by
      rw [show (1 / 2 + 1 / 2 + 1 : ℝ) = 2 by norm_num]
      rfl
    have h4 : PowerSeries.C ((1 / 2) * (1 / 2) : ℝ) = PowerSeries.C (1 / 4) := by
      rw [show ((1 / 2) * (1 / 2) : ℝ) = 1 / 4 by norm_num]
    rw [h2, h4] at h
    simpa using h
  have hsubst : PowerSeries.subst mobius
      (PowerSeries.X * (1 - PowerSeries.X)
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
        + (1 - 2 * PowerSeries.X)
          * PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)
        - PowerSeries.C (1 / 4) * hypSeries (1 / 2) (1 / 2) 1) = 0 := by
    rw [hY, hzero]
  have key : mobius * (1 - mobius)
        * PowerSeries.subst mobius
            (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)))
      + (1 - 2 * mobius)
        * PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
      - PowerSeries.C (1 / 4) * PowerSeries.subst mobius (hypSeries (1 / 2) (1 / 2) 1) = 0 := by
    rw [← hsubst]
    simp only [← PowerSeries.coe_substAlgHom hsub, map_add, map_sub, map_mul, map_one,
      map_ofNat, PowerSeries.C_eq_algebraMap, AlgHom.commutes, PowerSeries.substAlgHom_X hsub]
  have hM1 : PowerSeries.derivative ℝ mSeries
      = PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
        * PowerSeries.derivative ℝ mobius := by
    rw [mSeries, PowerSeries.derivative_subst hsub]
  have hM2 : PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mSeries)
      = (PowerSeries.subst mobius
              (PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)))
            * PowerSeries.derivative ℝ mobius) * PowerSeries.derivative ℝ mobius
        + PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius) := by
    rw [hM1, Derivation.leibniz, PowerSeries.derivative_subst hsub, smul_eq_mul, smul_eq_mul]
    ring
  rw [hM2, hM1]
  have hrearr :
      PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
          * (PowerSeries.subst mobius
                (PowerSeries.derivative ℝ
                  (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)))
              * PowerSeries.derivative ℝ mobius * PowerSeries.derivative ℝ mobius
            + PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
              * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius))
        + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
          * (PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
            * PowerSeries.derivative ℝ mobius)
        - PowerSeries.C (1 / 2) * mSeries
      = PowerSeries.subst mobius
            (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1)))
          * (PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
              * (PowerSeries.derivative ℝ mobius) ^ 2)
        + PowerSeries.subst mobius (PowerSeries.derivative ℝ (hypSeries (1 / 2) (1 / 2) 1))
          * (PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
                * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mobius)
              + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
                * PowerSeries.derivative ℝ mobius)
        - PowerSeries.C (1 / 2) * mSeries := by ring
  rw [hrearr, mobius_quad_identity, mobius_lin_identity, mSeries]
  have hconst : (2 : PowerSeries ℝ) * PowerSeries.C (1 / 4) = PowerSeries.C (1 / 2) := by
    rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, ← map_mul,
      show (2 * (1 / 4 : ℝ)) = (1 / 2 : ℝ) by norm_num]
  rw [← hconst]
  linear_combination 2 * key

/-! ### The square-root prefactor

Writing `h = sqrtInvSeries`, the logarithmic derivative relation `(1+X)h' = -(1/2)h` and its
derivative give the three identities `(1+X)h' = -(1/2)h`, `(1+X)h'' = -(3/2)h'` and
`(1+X)²h'' = (3/4)h`. They clear the inverse that the Möbius substitution introduces, so
`R = h·M` satisfies the Heun equation with no series inversion. -/

/-- The constant coefficient of `hypSeries (1/2) (1/2) 1` is `1`. -/
-- Theorem: `constantCoeff (hypSeries (1/2)(1/2)1) = 1`.
private theorem constantCoeff_hypSeries_half :
    PowerSeries.constantCoeff (hypSeries (1 / 2) (1 / 2) 1) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hypSeries]
  norm_num [hypCoeff, ordinaryHypergeometricCoefficient]

/-- Substitution along `mobius` leaves the constant coefficient unchanged. -/
-- Theorem: `constantCoeff (subst mobius f) = constantCoeff f`.
private theorem constantCoeff_subst_mobius (f : PowerSeries ℝ) :
    PowerSeries.constantCoeff (PowerSeries.subst mobius f) = PowerSeries.constantCoeff f := by
  have hzero := PowerSeries.constantCoeff_subst_eq_zero constantCoeff_mobius
    (f - PowerSeries.C (PowerSeries.constantCoeff f)) (by simp)
  rw [PowerSeries.subst_sub hasSubst_mobius, PowerSeries.subst_C, map_sub,
    MvPowerSeries.constantCoeff_C, sub_eq_zero] at hzero
  exact hzero

/-- The right-hand side of Goursat's V7 in the variable `w = √z`. -/
noncomputable def rSeries : PowerSeries ℝ := sqrtInvSeries * mSeries

/-- The constant coefficient of `rSeries` is `1`. -/
-- Theorem: `PowerSeries.coeff 0 rSeries = 1`.
theorem coeff_zero_rSeries : PowerSeries.coeff 0 rSeries = 1 := by
  rw [rSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul,
    constantCoeff_sqrtInvSeries, one_mul, mSeries, constantCoeff_subst_mobius,
    constantCoeff_hypSeries_half]

/-- The logarithmic derivative of `h = sqrtInvSeries`: `(1+X)h' = -(1/2)h`. -/
-- Theorem: `(1+X) * derivative ℝ sqrtInvSeries = -(C (1/2)) * sqrtInvSeries`.
private theorem one_add_X_mul_derivative_sqrtInv :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries
      = -(PowerSeries.C (1 / 2)) * sqrtInvSeries := by
  rw [one_add_X_mul_derivative_sqrtInvSeries, PowerSeries.smul_eq_C_mul, map_neg]

/-- The derivative of the logarithmic derivative: `(1+X)h'' = -(3/2)h'`. -/
-- Theorem: `(1+X) * derivative ℝ (derivative ℝ sqrtInvSeries)
--   = -(C (3/2)) * derivative ℝ sqrtInvSeries`.
private theorem one_add_X_mul_deriv2_sqrtInv :
    (1 + PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries)
      = -(PowerSeries.C (3 / 2)) * PowerSeries.derivative ℝ sqrtInvSeries := by
  have hp1d := congrArg (PowerSeries.derivative ℝ) one_add_X_mul_derivative_sqrtInv
  have e1 : PowerSeries.derivative ℝ
        ((1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries)
      = (1 + PowerSeries.X) * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries)
        + PowerSeries.derivative ℝ sqrtInvSeries := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    rw [show PowerSeries.derivative ℝ (1 + PowerSeries.X) = 1 by
      rw [map_add, Derivation.map_one_eq_zero, PowerSeries.derivative_X, zero_add]]
    ring
  have e2 : PowerSeries.derivative ℝ (-(PowerSeries.C (1 / 2)) * sqrtInvSeries)
      = -(PowerSeries.C (1 / 2)) * PowerSeries.derivative ℝ sqrtInvSeries := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, map_neg, PowerSeries.derivative_C,
      neg_zero, mul_zero, add_zero]
  rw [e1, e2] at hp1d
  have hC32 : PowerSeries.C (3 / 2 : ℝ) - PowerSeries.C (1 / 2 : ℝ)
      = (1 : PowerSeries ℝ) := by
    rw [← map_sub, show (3 / 2 : ℝ) - 1 / 2 = 1 by norm_num]
    rfl
  linear_combination hp1d + PowerSeries.derivative ℝ sqrtInvSeries * hC32

/-- The squared prefactor identity: `(1+X)²h'' = (3/4)h`, clearing the inverse. -/
-- Theorem: `(1+X)^2 * derivative ℝ (derivative ℝ sqrtInvSeries) = (C (3/4)) * sqrtInvSeries`.
private theorem sq_mul_deriv2_sqrtInv :
    (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries)
      = PowerSeries.C (3 / 4) * sqrtInvSeries := by
  have hCmul : PowerSeries.C (3 / 2 : ℝ) * PowerSeries.C (1 / 2 : ℝ)
      = PowerSeries.C (3 / 4 : ℝ) := by
    rw [← map_mul, show (3 / 2 : ℝ) * (1 / 2) = 3 / 4 by norm_num]
  calc (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries)
      = (1 + PowerSeries.X)
          * ((1 + PowerSeries.X)
              * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries)) := by ring
    _ = (1 + PowerSeries.X)
          * (-(PowerSeries.C (3 / 2)) * PowerSeries.derivative ℝ sqrtInvSeries) := by
      rw [one_add_X_mul_deriv2_sqrtInv]
    _ = -(PowerSeries.C (3 / 2))
          * ((1 + PowerSeries.X) * PowerSeries.derivative ℝ sqrtInvSeries) := by ring
    _ = -(PowerSeries.C (3 / 2))
          * (-(PowerSeries.C (1 / 2)) * sqrtInvSeries) := by
      rw [one_add_X_mul_derivative_sqrtInv]
    _ = PowerSeries.C (3 / 4) * sqrtInvSeries := by
      rw [show -(PowerSeries.C (3 / 2)) * (-(PowerSeries.C (1 / 2)) * sqrtInvSeries)
            = (PowerSeries.C (3 / 2) * PowerSeries.C (1 / 2)) * sqrtInvSeries by ring, hCmul]

/-- The Heun-type equation satisfied by `rSeries = sqrtInvSeries * mSeries`. -/
-- Theorem: `X(1-X²)R'' + (1-3X²)R' - (3/4)X R = 0` for `R = rSeries`.
theorem rSeries_heun :
    PowerSeries.X * (1 - PowerSeries.X ^ 2)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ rSeries)
      + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ rSeries
      - PowerSeries.C (3 / 4) * PowerSeries.X * rSeries = 0 := by
  rw [rSeries]
  have hR' : PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)
      = PowerSeries.derivative ℝ sqrtInvSeries * mSeries
        + sqrtInvSeries * PowerSeries.derivative ℝ mSeries := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]
    ring
  have hR'' : PowerSeries.derivative ℝ
        (PowerSeries.derivative ℝ (sqrtInvSeries * mSeries))
      = PowerSeries.derivative ℝ (PowerSeries.derivative ℝ sqrtInvSeries) * mSeries
        + 2 * PowerSeries.derivative ℝ sqrtInvSeries
            * PowerSeries.derivative ℝ mSeries
        + sqrtInvSeries
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mSeries) := by
    rw [hR', map_add]
    simp only [Derivation.leibniz, smul_eq_mul]
    ring
  have c1 : (1 + PowerSeries.X) * PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)
      = -(PowerSeries.C (1 / 2)) * (sqrtInvSeries * mSeries)
        + (1 + PowerSeries.X)
            * (sqrtInvSeries * PowerSeries.derivative ℝ mSeries) := by
    rw [hR']
    linear_combination mSeries * one_add_X_mul_derivative_sqrtInv
  have c2 : (1 + PowerSeries.X) ^ 2
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ (sqrtInvSeries * mSeries))
      = PowerSeries.C (3 / 4) * (sqrtInvSeries * mSeries)
        - (1 + PowerSeries.X)
            * (sqrtInvSeries * PowerSeries.derivative ℝ mSeries)
        + (1 + PowerSeries.X) ^ 2
            * (sqrtInvSeries
                * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mSeries)) := by
    rw [hR'']
    have h2half : (2 : PowerSeries ℝ) * PowerSeries.C (1 / 2 : ℝ) = 1 := by
      rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, ← map_mul,
        show (2 * (1 / 2 : ℝ)) = 1 by norm_num]
      rfl
    linear_combination mSeries * sq_mul_deriv2_sqrtInv
      + (2 * (1 + PowerSeries.X) * PowerSeries.derivative ℝ mSeries)
          * one_add_X_mul_derivative_sqrtInv
      - ((1 + PowerSeries.X) * sqrtInvSeries * PowerSeries.derivative ℝ mSeries) * h2half
  have hLHS : (1 + PowerSeries.X) ^ 2
        * (PowerSeries.X * (1 - PowerSeries.X ^ 2)
              * PowerSeries.derivative ℝ
                  (PowerSeries.derivative ℝ (sqrtInvSeries * mSeries))
            + (1 - 3 * PowerSeries.X ^ 2)
              * PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)
            - PowerSeries.C (3 / 4) * PowerSeries.X * (sqrtInvSeries * mSeries))
      = PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * ((1 + PowerSeries.X) ^ 2
                * PowerSeries.derivative ℝ
                    (PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)))
        + (1 - 3 * PowerSeries.X ^ 2)
            * ((1 + PowerSeries.X)
                * ((1 + PowerSeries.X)
                    * PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)))
        - PowerSeries.C (3 / 4) * PowerSeries.X
            * ((1 + PowerSeries.X) ^ 2 * (sqrtInvSeries * mSeries)) := by ring
  have hfactor : (1 + PowerSeries.X) ^ 2
        * (PowerSeries.X * (1 - PowerSeries.X ^ 2)
              * PowerSeries.derivative ℝ
                  (PowerSeries.derivative ℝ (sqrtInvSeries * mSeries))
            + (1 - 3 * PowerSeries.X ^ 2)
              * PowerSeries.derivative ℝ (sqrtInvSeries * mSeries)
            - PowerSeries.C (3 / 4) * PowerSeries.X * (sqrtInvSeries * mSeries))
      = sqrtInvSeries * (1 + PowerSeries.X)
        * (PowerSeries.X * (1 - PowerSeries.X) * (1 + PowerSeries.X) ^ 2
              * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ mSeries)
            + (1 - 2 * PowerSeries.X) * (1 + PowerSeries.X) ^ 2
              * PowerSeries.derivative ℝ mSeries
            - PowerSeries.C (1 / 2) * mSeries) := by
    rw [hLHS, c2, c1]
    have h34 : (2 : PowerSeries ℝ) * PowerSeries.C (3 / 4 : ℝ)
        = 3 * PowerSeries.C (1 / 2 : ℝ) := by
      rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl,
        show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl, ← map_mul, ← map_mul,
        show (2 * (3 / 4 : ℝ)) = (3 * (1 / 2 : ℝ)) by norm_num]
    linear_combination
      (-(sqrtInvSeries * mSeries * PowerSeries.X ^ 2 * (1 + PowerSeries.X))) * h34
  rw [mSeries_ode, mul_zero] at hfactor
  exact (mul_eq_zero.mp hfactor).resolve_left (pow_ne_zero 2 onePlusX_ne_zero)

end

end Pconstructible
