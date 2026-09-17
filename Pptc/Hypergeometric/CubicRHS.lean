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

-- Targeted imports rather than `import Mathlib`; see the note in `Pptc.Defs`.
import Pptc.Hypergeometric.Cubic
import Pptc.Hypergeometric.SubstODE

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.CubicRHS

The **right-hand side** of Ramanujan's cubic transformation,
`γ(p) · ₂F₁(1/2, 1/2; 1; α(p))`, solves the same operator `cubicOp` as the left-hand side
(`cubicOp_lhs`).

Write `A = alphaSeries`, `B = betaSeries`, `G = gammaSeries` and
`Y = subst A (hypSeries (1/2) (1/2) 1)`. `hypSeries_subst_ode` gives

`a·Y'' + b·Y' + c·Y = 0`, `a = A(1−A)A'`, `b = −A(1−A)A'' + (1−2A)(A')²`, `c = −C(1/4)(A')³`,

while `cubicOp (G·Y) = d·Y'' + e·Y' + f·Y`. The proof reduces to the algebraic identities

`a·e = d·b`, `a·f = d·c`  (in `ℝ⟦X⟧`),

i.e. the two operators are proportional. Both are rational identities in `p`; they are proved
in `FractionRing ℝ⟦X⟧`, where `field_simp` may clear the unit denominators `1+2X` and
`4(1+X+X²)³`, and then pulled back along the injective map `ℝ⟦X⟧ → FractionRing ℝ⟦X⟧`.
Since `a` has order `5` at the origin, it is nonzero, and `a · cubicOp (G·Y) = 0` forces
`cubicOp (G·Y) = 0`. -/

/-! ### The auxiliary polynomial units and the slope coefficient -/

private def uC : PowerSeries ℝ := 1 + 2 * PowerSeries.X
private def vC : PowerSeries ℝ := 1 + PowerSeries.X + PowerSeries.X ^ 2
private def eC : PowerSeries ℝ := 4 * vC ^ 3
private def nC : PowerSeries ℝ := 27 * PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 2
private def hC : PowerSeries ℝ := 3 * PowerSeries.X * (1 + PowerSeries.X)

private theorem constantCoeff_uC : PowerSeries.constantCoeff uC = 1 := by simp [uC]

private theorem constantCoeff_vC : PowerSeries.constantCoeff vC = 1 := by simp [vC]

private theorem constantCoeff_uC_ne : PowerSeries.constantCoeff uC ≠ 0 := by
  rw [constantCoeff_uC]; norm_num

private theorem constantCoeff_eC : PowerSeries.constantCoeff eC = 4 := by
  rw [eC, show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl]
  simp [vC]

private theorem constantCoeff_eC_ne : PowerSeries.constantCoeff eC ≠ 0 := by
  rw [constantCoeff_eC]; norm_num

private theorem uC_ne_zero : uC ≠ 0 := fun h => by
  simpa [h] using constantCoeff_uC_ne

/-! ### Derivatives of numerals, to let `simp` see through constant coefficients -/

@[simp] private theorem deriv_1 : PowerSeries.derivative ℝ (1 : PowerSeries ℝ) = 0 := by
  rw [show (1 : PowerSeries ℝ) = PowerSeries.C 1 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_2 : PowerSeries.derivative ℝ (2 : PowerSeries ℝ) = 0 := by
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_3 : PowerSeries.derivative ℝ (3 : PowerSeries ℝ) = 0 := by
  rw [show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_4 : PowerSeries.derivative ℝ (4 : PowerSeries ℝ) = 0 := by
  rw [show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_6 : PowerSeries.derivative ℝ (6 : PowerSeries ℝ) = 0 := by
  rw [show (6 : PowerSeries ℝ) = PowerSeries.C 6 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_12 : PowerSeries.derivative ℝ (12 : PowerSeries ℝ) = 0 := by
  rw [show (12 : PowerSeries ℝ) = PowerSeries.C 12 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_27 : PowerSeries.derivative ℝ (27 : PowerSeries ℝ) = 0 := by
  rw [show (27 : PowerSeries ℝ) = PowerSeries.C 27 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_54 : PowerSeries.derivative ℝ (54 : PowerSeries ℝ) = 0 := by
  rw [show (54 : PowerSeries ℝ) = PowerSeries.C 54 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_108 : PowerSeries.derivative ℝ (108 : PowerSeries ℝ) = 0 := by
  rw [show (108 : PowerSeries ℝ) = PowerSeries.C 108 from rfl, PowerSeries.derivative_C]

@[simp] private theorem deriv_162 : PowerSeries.derivative ℝ (162 : PowerSeries ℝ) = 0 := by
  rw [show (162 : PowerSeries ℝ) = PowerSeries.C 162 from rfl, PowerSeries.derivative_C]

/-! ### The defining identities of `α`, `β`, `γ` and the derivatives -/

private theorem alphaSeries_eq :
    alphaSeries = PowerSeries.X ^ 3 * (2 + PowerSeries.X) * uC⁻¹ := rfl

private theorem betaSeries_eq : betaSeries = nC * eC⁻¹ := rfl

private theorem gammaSeries_eq : gammaSeries = vC * gSeries := rfl

private theorem deriv_vC : PowerSeries.derivative ℝ vC = uC := by
  have h21 : (2 - 1 : ℕ) = 1 := by norm_num
  simp only [vC, uC, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, deriv_1, deriv_2, Derivation.map_natCast,
    Nat.cast_ofNat, h21, pow_one, mul_one, mul_zero, add_zero, zero_add, one_mul]

private theorem deriv_uC : PowerSeries.derivative ℝ uC = 2 := by
  simp only [uC, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    map_add, deriv_1, deriv_2, mul_one, mul_zero, add_zero, zero_add]

private theorem deriv_nC :
    PowerSeries.derivative ℝ nC
      = 54 * PowerSeries.X + 162 * PowerSeries.X ^ 2 + 108 * PowerSeries.X ^ 3 := by
  simp only [nC, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, deriv_1, deriv_27, Derivation.map_natCast,
    Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add, one_mul]
  ring

private theorem deriv2_nC :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ nC)
      = 54 + 324 * PowerSeries.X + 324 * PowerSeries.X ^ 2 := by
  rw [deriv_nC]
  simp only [Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, deriv_54, deriv_108, deriv_162,
    Derivation.map_natCast, Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add,
    one_mul]
  ring

private theorem deriv_eC : PowerSeries.derivative ℝ eC = 12 * vC ^ 2 * uC := by
  simp only [eC, deriv_vC, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, deriv_4, Derivation.map_natCast,
    Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add, one_mul]
  ring

private theorem deriv2_eC :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ eC)
      = 24 * vC * (2 + 5 * PowerSeries.X + 5 * PowerSeries.X ^ 2) := by
  rw [deriv_eC]
  simp only [deriv_vC, deriv_uC, Derivation.leibniz, smul_eq_mul,
    PowerSeries.derivative_X, PowerSeries.derivative_pow, map_add, deriv_2, deriv_12,
    Derivation.map_natCast, Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add,
    one_mul]
  simp only [uC, vC]
  ring

private theorem deriv_alphaSeries_mul :
    PowerSeries.derivative ℝ alphaSeries * uC
      = 6 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * alphaSeries := by
  have h := congrArg (PowerSeries.derivative ℝ) alphaSeries_mul
  rw [show (1 + 2 * PowerSeries.X : PowerSeries ℝ) = uC from rfl] at h
  simp only [Derivation.leibniz, smul_eq_mul, deriv_uC, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, map_sub, deriv_1, deriv_2, deriv_4, deriv_6,
    Derivation.map_natCast, Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add,
    one_mul] at h
  linear_combination h

private theorem deriv_alphaSeries :
    PowerSeries.derivative ℝ alphaSeries
      = (6 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * alphaSeries) * uC⁻¹ := by
  rw [← deriv_alphaSeries_mul, mul_assoc, mul_comm uC uC⁻¹,
    PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne, mul_one]

private theorem deriv2_alphaSeries_mul :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ alphaSeries) * uC
      = 12 * PowerSeries.X + 12 * PowerSeries.X ^ 2
        - 4 * PowerSeries.derivative ℝ alphaSeries := by
  have h := congrArg (PowerSeries.derivative ℝ) deriv_alphaSeries_mul
  simp only [Derivation.leibniz, smul_eq_mul, deriv_uC, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, map_sub, deriv_2, deriv_4, deriv_6, deriv_12,
    Derivation.map_natCast, Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add,
    one_mul] at h
  linear_combination h

private theorem deriv2_alphaSeries :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ alphaSeries)
      = (12 * PowerSeries.X + 12 * PowerSeries.X ^ 2
          - 4 * PowerSeries.derivative ℝ alphaSeries) * uC⁻¹ := by
  rw [← deriv2_alphaSeries_mul, mul_assoc, mul_comm uC uC⁻¹,
    PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne, mul_one]

private theorem deriv_betaSeries_mul :
    PowerSeries.derivative ℝ betaSeries * eC
      = PowerSeries.derivative ℝ nC - betaSeries * PowerSeries.derivative ℝ eC := by
  have h := congrArg (PowerSeries.derivative ℝ) betaSeries_mul
  rw [show (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3 : PowerSeries ℝ) = eC
    from rfl,
    show (27 * PowerSeries.X ^ 2 * (1 + PowerSeries.X) ^ 2 : PowerSeries ℝ) = nC
    from rfl] at h
  simp only [Derivation.leibniz, smul_eq_mul] at h
  linear_combination h

private theorem deriv_betaSeries :
    PowerSeries.derivative ℝ betaSeries
      = (PowerSeries.derivative ℝ nC - betaSeries * PowerSeries.derivative ℝ eC)
        * eC⁻¹ := by
  rw [← deriv_betaSeries_mul, mul_assoc, mul_comm eC eC⁻¹,
    PowerSeries.inv_mul_cancel _ constantCoeff_eC_ne, mul_one]

private theorem deriv2_betaSeries_mul :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries) * eC
      = PowerSeries.derivative ℝ (PowerSeries.derivative ℝ nC)
        - 2 * PowerSeries.derivative ℝ betaSeries * PowerSeries.derivative ℝ eC
        - betaSeries * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ eC) := by
  have h := congrArg (PowerSeries.derivative ℝ) deriv_betaSeries_mul
  simp only [Derivation.leibniz, smul_eq_mul, map_sub] at h
  linear_combination h

private theorem deriv2_betaSeries :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries)
      = (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ nC)
          - 2 * PowerSeries.derivative ℝ betaSeries * PowerSeries.derivative ℝ eC
          - betaSeries * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ eC))
        * eC⁻¹ := by
  rw [← deriv2_betaSeries_mul, mul_assoc, mul_comm eC eC⁻¹,
    PowerSeries.inv_mul_cancel _ constantCoeff_eC_ne, mul_one]

/-! ### Derivatives of `γ` -/

private theorem deriv_gSeries :
    PowerSeries.derivative ℝ gSeries = -uC⁻¹ * gSeries := by
  have h := one_add_two_X_mul_derivative_gSeries
  rw [show (1 + 2 * PowerSeries.X : PowerSeries ℝ) = uC from rfl] at h
  calc PowerSeries.derivative ℝ gSeries
      = uC⁻¹ * (uC * PowerSeries.derivative ℝ gSeries) := by
        rw [← mul_assoc, PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne, one_mul]
    _ = uC⁻¹ * (-gSeries) := by rw [h]
    _ = -uC⁻¹ * gSeries := by ring

private theorem deriv_gammaSeries_mul :
    PowerSeries.derivative ℝ gammaSeries * uC = hC * gSeries := by
  have hcu : uC⁻¹ * uC = 1 := PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne
  rw [gammaSeries_eq, Derivation.leibniz, deriv_vC, deriv_gSeries, hC]
  simp only [smul_eq_mul]
  have h3 : uC * uC - vC = 3 * PowerSeries.X * (1 + PowerSeries.X) := by
    simp only [uC, vC]; ring
  linear_combination (-(vC * gSeries)) * hcu + gSeries * h3

private theorem deriv_gammaSeries :
    PowerSeries.derivative ℝ gammaSeries = hC * gSeries * uC⁻¹ := by
  rw [← deriv_gammaSeries_mul, mul_assoc, mul_comm uC uC⁻¹,
    PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne, mul_one]

private theorem deriv_hC : PowerSeries.derivative ℝ hC = 3 + 6 * PowerSeries.X := by
  simp only [hC, Derivation.leibniz, smul_eq_mul, PowerSeries.derivative_X,
    PowerSeries.derivative_pow, map_add, deriv_1, deriv_3, Derivation.map_natCast,
    Nat.cast_ofNat, mul_one, mul_zero, add_zero, zero_add, one_mul]
  ring

private theorem deriv2_gammaSeries_mul :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ gammaSeries) * (uC * uC)
      = 3 * gammaSeries := by
  have hcu : uC⁻¹ * uC = 1 := PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne
  have hgu : PowerSeries.derivative ℝ gSeries * uC = -gSeries := by
    rw [deriv_gSeries]
    linear_combination (-gSeries) * hcu
  have h3 : PowerSeries.derivative ℝ gammaSeries * uC = hC * gSeries :=
    deriv_gammaSeries_mul
  have hd := congrArg (PowerSeries.derivative ℝ) h3
  simp only [Derivation.leibniz, smul_eq_mul, deriv_uC] at hd
  have hCkey : PowerSeries.derivative ℝ hC * uC - 3 * hC = 3 * vC := by
    rw [deriv_hC]; simp only [hC, uC, vC]; ring
  rw [gammaSeries_eq]
  calc PowerSeries.derivative ℝ (PowerSeries.derivative ℝ gammaSeries) * (uC * uC)
      = (PowerSeries.derivative ℝ gammaSeries * 2
            + uC * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ gammaSeries)) * uC
          - 2 * (PowerSeries.derivative ℝ gammaSeries * uC) := by ring
    _ = (PowerSeries.derivative ℝ hC * gSeries + hC * PowerSeries.derivative ℝ gSeries)
            * uC - 2 * (hC * gSeries) := by rw [hd, h3]; ring
    _ = (PowerSeries.derivative ℝ hC * gSeries) * uC
          + hC * (PowerSeries.derivative ℝ gSeries * uC)
          - 2 * (hC * gSeries) := by ring
    _ = (PowerSeries.derivative ℝ hC * gSeries) * uC + hC * (-gSeries)
          - 2 * (hC * gSeries) := by rw [hgu]
    _ = (PowerSeries.derivative ℝ hC * uC - 3 * hC) * gSeries := by ring
    _ = (3 * vC) * gSeries := by rw [hCkey]
    _ = 3 * (vC * gSeries) := by ring

private theorem deriv2_gammaSeries :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ gammaSeries)
      = 3 * gammaSeries * (uC⁻¹ * uC⁻¹) := by
  have hcu : uC⁻¹ * uC = 1 := PowerSeries.inv_mul_cancel _ constantCoeff_uC_ne
  have hY : (uC * uC) * (uC⁻¹ * uC⁻¹) = 1 := by
    have hcu' : uC * uC⁻¹ = 1 := by rw [mul_comm, hcu]
    calc (uC * uC) * (uC⁻¹ * uC⁻¹) = (uC * uC⁻¹) * (uC * uC⁻¹) := by ring
      _ = 1 := by rw [hcu', mul_one]
  rw [← deriv2_gammaSeries_mul, mul_assoc, hY, mul_one]

/-! ### The coefficient series `a,b,c` of the `(1/2,1/2)` operator and
`P₂,P₁,P₀` of the cubic operator -/

private def p2C : PowerSeries ℝ :=
  betaSeries * (1 - betaSeries) * PowerSeries.derivative ℝ betaSeries

private def p1C : PowerSeries ℝ :=
  -(betaSeries * (1 - betaSeries)
      * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries))
    + (1 - 2 * betaSeries) * (PowerSeries.derivative ℝ betaSeries) ^ 2

private def p0C : PowerSeries ℝ :=
  -(PowerSeries.C (2 / 9) * (PowerSeries.derivative ℝ betaSeries) ^ 3)

private def aC : PowerSeries ℝ :=
  alphaSeries * (1 - alphaSeries) * PowerSeries.derivative ℝ alphaSeries

private def bC : PowerSeries ℝ :=
  -(alphaSeries * (1 - alphaSeries)
      * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ alphaSeries))
    + (1 - 2 * alphaSeries) * (PowerSeries.derivative ℝ alphaSeries) ^ 2

private def cC : PowerSeries ℝ :=
  -(PowerSeries.C (1 / 4) * (PowerSeries.derivative ℝ alphaSeries) ^ 3)

/-! ### `γ`-free forms of `d, e, f`

Since `γ = (1+X+X²)g` and `γ' = 3X(1+X)g/(1+2X)`, `γ'' = 3γ/(1+2X)²`, every term of
`e` and `f` carries exactly one factor of `g`; writing `d̃ = P₂(1+X+X²)`,
`ẽ = 2P₂·3X(1+X)/(1+2X) + P₁(1+X+X²)` and
`f̃ = 3P₂(1+X+X²)/(1+2X)² + P₁·3X(1+X)/(1+2X) + P₀(1+X+X²)` leaves the purely rational
identities `a·ẽ = d̃·b`, `a·f̃ = d̃·c`. -/

private def dT : PowerSeries ℝ := p2C * vC

private def eT : PowerSeries ℝ := 2 * p2C * (hC * uC⁻¹) + p1C * vC

private def fT : PowerSeries ℝ :=
  p2C * (3 * vC * (uC⁻¹ * uC⁻¹)) + p1C * (hC * uC⁻¹) + p0C * vC

private theorem he_lin :
    2 * p2C * PowerSeries.derivative ℝ gammaSeries + p1C * gammaSeries
      = eT * gSeries := by
  rw [deriv_gammaSeries, gammaSeries_eq, eT]
  ring

private theorem hd_lin : p2C * gammaSeries = dT * gSeries := by
  rw [gammaSeries_eq, dT]
  ring

private theorem hf_lin :
    p2C * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ gammaSeries)
        + p1C * PowerSeries.derivative ℝ gammaSeries + p0C * gammaSeries
      = fT * gSeries := by
  rw [deriv2_gammaSeries, deriv_gammaSeries, gammaSeries_eq, fT]
  ring

/-! ### The proportionality identities, in the fraction field

Both `a·ẽ = d̃·b` and `a·f̃ = d̃·c` are rational identities in `p`. After mapping to
`FractionRing ℝ⟦X⟧` and substituting the derivative formulas they become rational identities
in `algebraMap X`, which `field_simp` clears and `ring` closes. -/

private theorem algebraMap_inv_eq {w : PowerSeries ℝ}
    (hw : PowerSeries.constantCoeff w ≠ 0) :
    algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) w⁻¹
      = (algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) w)⁻¹ := by
  have h : algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) w⁻¹
      * algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) w = 1 := by
    rw [← map_mul, PowerSeries.inv_mul_cancel _ hw, map_one]
  exact eq_inv_of_mul_eq_one_left h

private theorem algebraMap_uC_ne_zero :
    algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) uC ≠ 0 := fun h =>
  uC_ne_zero (IsFractionRing.injective (PowerSeries ℝ)
    (FractionRing (PowerSeries ℝ)) (by rw [h, map_zero]))

private theorem eC_ne_zero : eC ≠ 0 := fun h => by
  simpa [h] using constantCoeff_eC_ne

private theorem algebraMap_eC_ne_zero :
    algebraMap (PowerSeries ℝ) (FractionRing (PowerSeries ℝ)) eC ≠ 0 := fun h =>
  eC_ne_zero (IsFractionRing.injective (PowerSeries ℝ)
    (FractionRing (PowerSeries ℝ)) (by rw [h, map_zero]))

private theorem constantCoeff_alphaSeries : PowerSeries.constantCoeff alphaSeries = 0 := by
  rw [alphaSeries_eq]
  simp [PowerSeries.constantCoeff_X]

private def UC : PowerSeries ℝ := (2 + PowerSeries.X) * uC⁻¹

private def WC : PowerSeries ℝ := (6 + 4 * PowerSeries.X - 2 * PowerSeries.X * UC) * uC⁻¹

private theorem alphaSeries_eq' : alphaSeries = PowerSeries.X ^ 3 * UC := by
  rw [alphaSeries_eq, UC, mul_assoc]

private theorem deriv_alphaSeries_eq' :
    PowerSeries.derivative ℝ alphaSeries = PowerSeries.X ^ 2 * WC := by
  rw [deriv_alphaSeries, alphaSeries_eq', WC]
  ring

private theorem constantCoeff_UC : PowerSeries.constantCoeff UC = 2 := by
  simp only [UC, map_mul, map_add, map_ofNat, PowerSeries.constantCoeff_inv,
    constantCoeff_uC, PowerSeries.constantCoeff_X, map_zero, add_zero]
  norm_num

private theorem constantCoeff_WC : PowerSeries.constantCoeff WC = 6 := by
  simp only [WC, map_mul, map_add, map_sub, map_ofNat, PowerSeries.constantCoeff_inv,
    constantCoeff_uC, PowerSeries.constantCoeff_X, map_zero, mul_zero, sub_zero]
  ring

private theorem isUnit_UC : IsUnit UC := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_UC]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem isUnit_WC : IsUnit WC := by
  rw [PowerSeries.isUnit_iff_constantCoeff, constantCoeff_WC]
  exact isUnit_iff_ne_zero.mpr (by norm_num)

private theorem isUnit_one_sub_alphaSeries : IsUnit (1 - alphaSeries) := by
  rw [PowerSeries.isUnit_iff_constantCoeff]
  have h : PowerSeries.constantCoeff (1 - alphaSeries) = 1 := by
    rw [map_sub, map_one, constantCoeff_alphaSeries]; norm_num
  rw [h]
  exact isUnit_iff_ne_zero.mpr one_ne_zero

private theorem aC_eq_factor :
    aC = PowerSeries.X ^ 5 * (UC * (1 - alphaSeries) * WC) := by
  rw [aC, deriv_alphaSeries_eq', alphaSeries_eq']
  ring

private theorem aC_ne_zero : aC ≠ 0 := by
  rw [aC_eq_factor]
  intro h
  rcases mul_eq_zero.mp h with h' | h'
  · exact pow_ne_zero 5 PowerSeries.X_ne_zero h'
  · exact (mul_ne_zero (mul_ne_zero isUnit_UC.ne_zero
      isUnit_one_sub_alphaSeries.ne_zero) isUnit_WC.ne_zero) h'

end

end Pconstructible
