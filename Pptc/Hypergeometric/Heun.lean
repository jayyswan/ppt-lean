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
-- `Pptc.Hypergeometric.Goursat` supplies the general hypergeometric equation
-- `hypSeries_ode`, and with it the `(1/4, 3/4; 1)` equation used here; the substitution
-- and chain-rule API of `PowerSeries` is imported explicitly as well.
import Pptc.Hypergeometric.Goursat
import Mathlib.RingTheory.PowerSeries.Substitution

/-! # Pptc.Hypergeometric.Heun

V7 of `PLAN-hypergeometric-00-overview.md` reads

`₂F₁(1/4, 3/4; 1; z) = (1 + √z)^(−1/2) · ₂F₁(1/2, 1/2; 1; 2√z / (1 + √z))`
for `0 ≤ z < 1`.

The substitution `w = √z`, i.e. `z = w²`, is what turns V7 into a statement about
hypergeometric functions: it makes the *right-hand side* a function of the single variable
`w`, and it expresses the *left-hand side* as the pullback

`Φ(w) = ₂F₁(1/4, 3/4; 1; w²)`

of the hypergeometric series `H = ₂F₁(1/4, 3/4; 1; ·)` along the squaring map `w ↦ w²`.
This file studies `Φ` as a formal power series in `w`.

Pulling `H`'s equation back along the squaring map is exactly a chain-rule computation, and
the result is **not** a hypergeometric equation. The squaring map is ramified at `0` and at
`∞` (its two branch points), so the three singular points `0, 1, ∞` of the hypergeometric
equation pull back to the four points `0, 1, −1, ∞`: the point `1` splits into the two
preimages `±1` of the squaring map. Four regular singular points is precisely a **Heun
equation**, and here it reads

`X(1 − X²) Φ'' + (1 − 3X²) Φ' − (3/4) X Φ = 0`.

That is the formal, characteristic-free content of "the `w = √z` reduction of V7 produces a
Heun equation". `phiSeries_heun` records that `Φ` solves it, and `heun_uniqueness` is the
matching uniqueness statement: a formal series with constant term `1` that solves the
displayed equation is unique, so any construction of the left-hand side of V7 as a formal
series must agree with `phiSeries` coefficient by coefficient. -/

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! ### The squaring substitution `w = X²` -/

/-- `X ^ 2` has vanishing constant coefficient, so it is a valid substitution. -/
-- Theorem: `PowerSeries.X ^ 2` satisfies `PowerSeries.HasSubst`.
theorem hasSubst_X_sq : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℝ) :=
  PowerSeries.HasSubst.of_constantCoeff_zero' (by simp)

/-- The derivative of the squaring substitution: `(X²)' = 2X`. -/
-- Theorem: the derivative of `X ^ 2` is `2 * X`.
theorem derivative_X_sq :
    PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ) = 2 * PowerSeries.X := by
  rw [pow_two, Derivation.leibniz]
  simp only [PowerSeries.derivative_X, smul_eq_mul, mul_one]
  ring

/-- The second derivative of the squaring substitution: `(X²)'' = 2`. -/
-- Theorem: the second derivative of `X ^ 2` is the constant `2`.
theorem derivative_derivative_X_sq :
    PowerSeries.derivative ℝ
        (PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ)) = 2 := by
  rw [derivative_X_sq]
  rw [show (2 : PowerSeries ℝ) = PowerSeries.C 2 from rfl]
  simp only [Derivation.leibniz, PowerSeries.derivative_X,
    PowerSeries.derivative_C, smul_eq_mul, mul_one, mul_zero, add_zero]

/-! ### The pulled-back series `Φ` -/

/-- `₂F₁(1/4,3/4;1;·)` pulled back along `X ↦ X²`. -/
noncomputable def phiSeries : PowerSeries ℝ :=
  PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ) (hypSeries (1 / 4) (3 / 4) 1)

/-- The pulled-back hypergeometric equation: `Φ` satisfies the Heun-type equation
`X(1−X²) Φ'' + (1−3X²) Φ' − (3/4) X Φ = 0`. -/
-- Theorem: `phiSeries` satisfies the Heun equation `X(1−X²)F'' + (1−3X²)F' − (3/4)XF = 0`.
theorem phiSeries_heun :
    PowerSeries.X * (1 - PowerSeries.X ^ 2)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ phiSeries)
      + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ phiSeries
      - PowerSeries.C (3 / 4) * PowerSeries.X * phiSeries = 0 := by
  have hsub : PowerSeries.HasSubst (PowerSeries.X ^ 2 : PowerSeries ℝ) := hasSubst_X_sq
  have hc : ∀ n : ℕ, (1 : ℝ) ≠ -(n : ℝ) := by
    intro n hn
    have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hsubst : PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
      (PowerSeries.X * (1 - PowerSeries.X)
          * PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1))
        + (PowerSeries.C 1 - PowerSeries.C ((1 / 4) + (3 / 4) + 1) * PowerSeries.X)
          * PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1)
        - PowerSeries.C ((1 / 4) * (3 / 4)) * hypSeries (1 / 4) (3 / 4) 1) =
          (0 : PowerSeries ℝ) := by
    rw [hypSeries_ode (1 / 4) (3 / 4) 1 hc]
    simp only [← PowerSeries.coe_substAlgHom hsub, map_zero]
  have key : PowerSeries.X ^ 2 * (1 - PowerSeries.X ^ 2)
        * PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
            (PowerSeries.derivative ℝ
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1)))
      + (PowerSeries.C 1 - PowerSeries.C ((1 / 4) + (3 / 4) + 1) * PowerSeries.X ^ 2)
        * PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
            (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1))
      - PowerSeries.C ((1 / 4) * (3 / 4))
          * PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
              (hypSeries (1 / 4) (3 / 4) 1) = (0 : PowerSeries ℝ) := by
    rw [← hsubst]
    simp only [← PowerSeries.coe_substAlgHom hsub, map_add, map_sub, map_mul, map_one,
      PowerSeries.substAlgHom_X hsub, PowerSeries.C_eq_algebraMap, AlgHom.commutes]
  have hB1 : PowerSeries.derivative ℝ phiSeries
      = PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
            (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1))
        * PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ) := by
    rw [phiSeries]
    exact PowerSeries.derivative_subst hsub
  have hB2 : PowerSeries.derivative ℝ (PowerSeries.derivative ℝ phiSeries)
      = (PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
              (PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1)))
            * PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ))
          * PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ)
        + PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
              (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1))
            * PowerSeries.derivative ℝ
                (PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ)) := by
    rw [hB1, Derivation.leibniz, PowerSeries.derivative_subst hsub, smul_eq_mul, smul_eq_mul]
    ring
  rw [hB2, hB1, derivative_derivative_X_sq, derivative_X_sq,
    show phiSeries = PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
      (hypSeries (1 / 4) (3 / 4) 1) from rfl]
  set A : PowerSeries ℝ := PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
      (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1)) with hA
  set B : PowerSeries ℝ := PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
      (PowerSeries.derivative ℝ
        (PowerSeries.derivative ℝ (hypSeries (1 / 4) (3 / 4) 1))) with hB
  set Phi : PowerSeries ℝ := PowerSeries.subst (PowerSeries.X ^ 2 : PowerSeries ℝ)
      (hypSeries (1 / 4) (3 / 4) 1) with hPhi
  have h1 : PowerSeries.C (1 : ℝ) - 1 = 0 := by rw [map_one, sub_self]
  have h2 : PowerSeries.C ((1 / 4 : ℝ) + 3 / 4 + 1) - 2 = 0 := by
    rw [show (1 / 4 : ℝ) + 3 / 4 + 1 = 2 by norm_num]
    rw [show PowerSeries.C (2 : ℝ) = (2 : PowerSeries ℝ) from rfl, sub_self]
  have h3 : 4 * PowerSeries.C ((1 / 4 : ℝ) * (3 / 4)) - PowerSeries.C (3 / 4 : ℝ) = 0 := by
    rw [show (1 / 4 : ℝ) * (3 / 4) = 3 / 16 by norm_num]
    rw [show (4 : PowerSeries ℝ) = PowerSeries.C 4 from rfl, ← map_mul]
    rw [show (4 : ℝ) * (3 / 16) = 3 / 4 by norm_num, sub_self]
  linear_combination (4 * PowerSeries.X) * key - (4 * PowerSeries.X * A) * h1
    + (4 * PowerSeries.X ^ 3 * A) * h2 + (PowerSeries.X * Phi) * h3

/-- The constant coefficient of `phiSeries` is `1`. -/
-- Theorem: the constant coefficient of `phiSeries` is `1`.
theorem coeff_zero_phiSeries : PowerSeries.coeff 0 phiSeries = 1 := by
  rw [phiSeries, PowerSeries.coeff_subst' hasSubst_X_sq]
  rw [finsum_eq_single _ 0]
  · simp only [pow_zero, PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one,
      smul_eq_mul, mul_one]
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_hypSeries]
    norm_num [hypCoeff, ordinaryHypergeometricCoefficient]
  · intro d hd
    simp [PowerSeries.constantCoeff_X, hd]

/-! ### Coefficient extraction and uniqueness

The Heun equation `X(1−X²)F'' + (1−3X²)F' − (3/4)XF = 0` is second order, so once the
constant term is fixed the whole series is determined: the coefficient of `X^{k+1}` gives

`(k+2)² f_{k+2} = ((k+1)² − 1/4) f_k`

and the coefficient of `X` gives `f_1 = 0`. With `f_0 = 0` the recurrence forces `f = 0`.
The expansion below writes every `X`-power as an explicit product so that the coefficient
lemmas `coeff_succ_X_mul` and `coeff_zero_X_mul` can peel the factors one at a time. -/

/-- The Heun operator with every `X`-power separated into an explicit product of copies of
`X`, so that the coefficient lemmas apply directly. -/
-- Theorem: expanded form of the Heun equation, with each `X`-power written as a product.
theorem heun_ode_expand {D : PowerSeries ℝ}
    (hD : PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)
          + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ D
          - PowerSeries.C (3 / 4) * PowerSeries.X * D = 0) :
    PowerSeries.X * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)
      - PowerSeries.X * (PowerSeries.X * (PowerSeries.X
          * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)))
      + PowerSeries.derivative ℝ D
      - 3 * (PowerSeries.X * (PowerSeries.X * PowerSeries.derivative ℝ D))
      - PowerSeries.C (3 / 4) * (PowerSeries.X * D) = 0 := by
  rw [← hD]; ring

/-- The coefficient of `X` of any solution of the Heun equation vanishes. -/
-- Theorem: `coeff 1 D = 0` for every solution `D` of the Heun equation.
theorem heun_coeff_one {D : PowerSeries ℝ}
    (hD : PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)
          + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ D
          - PowerSeries.C (3 / 4) * PowerSeries.X * D = 0) :
    PowerSeries.coeff 1 D = 0 := by
  have h := congrArg (PowerSeries.coeff 0) (heun_ode_expand hD)
  simp only [map_sub, map_add, map_zero, PowerSeries.coeff_zero_X_mul,
    PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
    show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl] at h
  simpa using h

/-- The coefficient recurrence of the Heun equation: the coefficient of `X^{k+1}` reads
`(k+2)² f_{k+2} = ((k+1)² − 1/4) f_k`. -/
-- Theorem: coefficient recurrence `(k+2)² f_{k+2} = ((k+1)² − 1/4) f_k`.
theorem heun_coeff_rec {D : PowerSeries ℝ}
    (hD : PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)
          + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ D
          - PowerSeries.C (3 / 4) * PowerSeries.X * D = 0) (k : ℕ) :
    ((k : ℝ) + 2) ^ 2 * PowerSeries.coeff (k + 2) D
      = (((k : ℝ) + 1) ^ 2 - 1 / 4) * PowerSeries.coeff k D := by
  rcases k with _ | _ | k
  · have h := congrArg (PowerSeries.coeff 1) (heun_ode_expand hD)
    simp only [map_sub, map_add, map_zero, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl] at h
    push_cast
    linear_combination h
  · have h := congrArg (PowerSeries.coeff 2) (heun_ode_expand hD)
    simp only [map_sub, map_add, map_zero, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_zero_X_mul, PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl] at h
    push_cast
    linear_combination h
  · have h := congrArg (PowerSeries.coeff (k + 3)) (heun_ode_expand hD)
    simp only [map_sub, map_add, map_zero, PowerSeries.coeff_succ_X_mul,
      PowerSeries.coeff_derivative, PowerSeries.coeff_C_mul,
      show (3 : PowerSeries ℝ) = PowerSeries.C 3 from rfl] at h
    push_cast at h ⊢
    linear_combination h

/-- A formal-series solution of the Heun equation is determined by its constant term. -/
-- Theorem: two formal series with the same constant term solving the Heun equation coincide.
theorem heun_uniqueness {F G : PowerSeries ℝ}
    (hF : PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ F)
          + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ F
          - PowerSeries.C (3 / 4) * PowerSeries.X * F = 0)
    (hG : PowerSeries.X * (1 - PowerSeries.X ^ 2)
            * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ G)
          + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ G
          - PowerSeries.C (3 / 4) * PowerSeries.X * G = 0)
    (h0 : PowerSeries.coeff 0 F = PowerSeries.coeff 0 G) : F = G := by
  set D : PowerSeries ℝ := F - G with hDdef
  have hode : PowerSeries.X * (1 - PowerSeries.X ^ 2)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)
      + (1 - 3 * PowerSeries.X ^ 2) * PowerSeries.derivative ℝ D
      - PowerSeries.C (3 / 4) * PowerSeries.X * D = 0 := by
    rw [hDdef]
    simp only [map_sub, mul_sub, sub_mul]
    linear_combination hF - hG
  have hD0 : PowerSeries.coeff 0 D = 0 := by
    rw [hDdef, map_sub, h0, sub_self]
  have hD1 : PowerSeries.coeff 1 D = 0 := heun_coeff_one hode
  have hzero : ∀ n : ℕ, PowerSeries.coeff n D = 0 := by
    intro n
    induction n using Nat.twoStepInduction with
    | zero => exact hD0
    | one => exact hD1
    | more k ihk _ =>
        have hrec := heun_coeff_rec hode k
        rw [ihk, mul_zero] at hrec
        have hk : ((k : ℝ) + 2) ^ 2 ≠ 0 := by positivity
        exact (mul_eq_zero.mp hrec).resolve_left hk
  ext n
  have hn := hzero n
  rw [hDdef, map_sub] at hn
  exact sub_eq_zero.mp hn

end

end Pconstructible
