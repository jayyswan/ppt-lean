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
-- `Pptc.Hypergeometric.Cubic` supplies `cubicOp` and `betaSeries`, together with the
-- denominator-clearing identity `betaSeries_mul`; the coefficient API of `PowerSeries`
-- (`coeff_X_pow_mul`, `coeff_derivative`, `X_pow_dvd_iff`) comes with it.
import Pptc.Hypergeometric.Cubic

open scoped PowerSeries

namespace Pconstructible

noncomputable section

/-! # Pptc.Hypergeometric.CubicUnique

Uniqueness of the formal power series solution of Ramanujan's cubic operator

`cubicOp F = β(1−β)β' F'' + [−β(1−β)β'' + (1−2β)(β')²] F' − (2/9)(β')³ F`

(`Pptc.Hypergeometric.Cubic`), where `β = betaSeries = 27X²(1+X)²/(4(1+X+X²)³)`.

The point is that `cubicOp` has *no* constant term: the coefficient `P₂ = β(1−β)β'` of `F''`
starts at order `3`, the coefficient `P₁ = −β(1−β)β'' + (1−2β)(β')²` of `F'` starts at
order `2`, and the coefficient `P₀ = −(2/9)(β')³` of `F` starts at order `3`. Writing
`β = X²·R` with `R = 27(1+X)²/(4(1+X+X²)³)` and `β' = X·V`, this is

`cubicOp F = X³·(U·F'') + X²·(Vp·F') − X³·(W·F)`,

with `U = R(1−β)V`, `Vp = −R(1−β)β'' + (1−2β)V²` and `W = (2/9)V³`. The leading
coefficients are `U(0) = Vp(0) = 729/8 > 0`, so reading off the coefficient of `X^{n+1}` in
`cubicOp F = 0` for a series whose coefficients below `n` vanish pins down `[Xⁿ]F`:

`[X^{n+1}](cubicOp F) = n·((n−1)·U(0) + Vp(0))·[Xⁿ]F`,

and the factor is nonzero for every `n ≥ 1`. Together with the two base cases (`n = 1` from
the coefficient of `X²`, giving `[X]F = 0`, and `n = 2` from the coefficient of `X³`, giving
`[X²]F` in terms of `[X⁰]F`) this shows a solution is determined by its constant term:
`cubicOp_unique`. -/

/-! ### The leading factor of `β`

`β` vanishes to order two, so `β = X²·R` for a unit `R`; `R`'s constant coefficient is
`27/4`. Likewise `β' = X·V` with `V(0) = 2·R(0) = 27/2`. -/

/-- The unit `R` with `betaSeries = X² · R`. -/
noncomputable def betaUnit : PowerSeries ℝ :=
  27 * (1 + PowerSeries.X) ^ 2
    * (4 * (1 + PowerSeries.X + PowerSeries.X ^ 2) ^ 3)⁻¹

/-- The series `V` with `betaSeries' = X · V`. -/
noncomputable def betaV : PowerSeries ℝ :=
  2 * betaUnit + PowerSeries.X * PowerSeries.derivative ℝ betaUnit

/-- The coefficient `U` of `F''` after dividing out the minimal order `X³`. -/
noncomputable def betaU : PowerSeries ℝ := betaUnit * (1 - betaSeries) * betaV

/-- The coefficient `Vp` of `F'` after dividing out the minimal order `X²`. -/
noncomputable def betaVp : PowerSeries ℝ :=
  -(betaUnit * (1 - betaSeries)
      * (betaV + PowerSeries.X * PowerSeries.derivative ℝ betaV))
    + (1 - 2 * betaSeries) * betaV ^ 2

/-- The coefficient `W` of `F` after dividing out the minimal order `X³`. -/
noncomputable def betaW : PowerSeries ℝ := PowerSeries.C (2 / 9) * betaV ^ 3

-- Theorem: `betaSeries = X^2 * betaUnit`.
theorem betaSeries_eq_X_sq_mul_betaUnit :
    betaSeries = PowerSeries.X ^ 2 * betaUnit := by
  rw [betaSeries, betaUnit]
  ring

-- Theorem: the constant coefficient of `betaUnit` is `27/4`.
theorem constantCoeff_betaUnit : PowerSeries.constantCoeff betaUnit = 27 / 4 := by
  rw [betaUnit]
  simp only [map_mul, map_pow, map_add, map_one,
    PowerSeries.constantCoeff_X, PowerSeries.constantCoeff_inv]
  rw [show PowerSeries.constantCoeff (27 : PowerSeries ℝ) = 27 from rfl,
    show PowerSeries.constantCoeff (4 : PowerSeries ℝ) = 4 from rfl]
  norm_num

-- Theorem: `betaSeries` vanishes at the origin.
theorem constantCoeff_betaSeries : PowerSeries.constantCoeff betaSeries = 0 := by
  rw [betaSeries_eq_X_sq_mul_betaUnit]
  simp [PowerSeries.constantCoeff_X]

-- Theorem: the constant coefficient of `betaV` is `27/2`.
theorem constantCoeff_betaV : PowerSeries.constantCoeff betaV = 27 / 2 := by
  rw [betaV]
  simp only [map_add, map_mul, PowerSeries.constantCoeff_X, constantCoeff_betaUnit]
  rw [show PowerSeries.constantCoeff (2 : PowerSeries ℝ) = 2 from rfl]
  norm_num

-- Theorem: the constant coefficient of `betaU` is `729/8 > 0`.
theorem constantCoeff_betaU : PowerSeries.constantCoeff betaU = 729 / 8 := by
  rw [betaU]
  simp only [map_mul, map_sub, map_one, constantCoeff_betaUnit, constantCoeff_betaSeries,
    constantCoeff_betaV]
  norm_num

-- Theorem: the constant coefficient of `betaVp` is `729/8 > 0`.
theorem constantCoeff_betaVp : PowerSeries.constantCoeff betaVp = 729 / 8 := by
  rw [betaVp]
  simp only [map_add, map_sub, map_mul, map_pow, map_neg, map_one,
    PowerSeries.constantCoeff_X, constantCoeff_betaUnit,
    constantCoeff_betaSeries, constantCoeff_betaV]
  rw [show PowerSeries.constantCoeff (2 : PowerSeries ℝ) = 2 from rfl]
  norm_num

-- Theorem: `coeff 0 betaU = 729/8`.
theorem coeff_zero_betaU : PowerSeries.coeff 0 betaU = 729 / 8 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_betaU]

-- Theorem: `coeff 0 betaVp = 729/8`.
theorem coeff_zero_betaVp : PowerSeries.coeff 0 betaVp = 729 / 8 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_betaVp]

/-! ### Derivatives of `β` in factored form -/

-- Theorem: `(X^2)' = 2X`.
theorem derivative_X_sq :
    PowerSeries.derivative ℝ (PowerSeries.X ^ 2 : PowerSeries ℝ) = 2 * PowerSeries.X := by
  rw [pow_two, Derivation.leibniz]
  simp only [PowerSeries.derivative_X, smul_eq_mul, mul_one]
  ring

-- Theorem: `betaSeries' = X * betaV`.
theorem derivative_betaSeries_eq :
    PowerSeries.derivative ℝ betaSeries = PowerSeries.X * betaV := by
  rw [betaSeries_eq_X_sq_mul_betaUnit, betaV, Derivation.leibniz, derivative_X_sq,
    smul_eq_mul, smul_eq_mul]
  ring

-- Theorem: `betaSeries'' = betaV + X * betaV'`.
theorem derivative_derivative_betaSeries_eq :
    PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries)
      = betaV + PowerSeries.X * PowerSeries.derivative ℝ betaV := by
  rw [derivative_betaSeries_eq, Derivation.leibniz, PowerSeries.derivative_X, smul_eq_mul,
    smul_eq_mul, mul_one]
  ring

/-! ### Factorizations of the operator coefficients -/

-- Theorem: `β(1−β)β' = X^3 * betaU`.
theorem betaSeries_factor :
    betaSeries * (1 - betaSeries) * PowerSeries.derivative ℝ betaSeries
      = PowerSeries.X ^ 3 * betaU := by
  rw [betaU, derivative_betaSeries_eq, betaSeries_eq_X_sq_mul_betaUnit]
  ring

-- Theorem: `−β(1−β)β'' + (1−2β)(β')² = X^2 * betaVp`.
theorem betaP1_factor :
    -(betaSeries * (1 - betaSeries)
        * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ betaSeries))
      + (1 - 2 * betaSeries) * (PowerSeries.derivative ℝ betaSeries) ^ 2
      = PowerSeries.X ^ 2 * betaVp := by
  rw [betaVp, derivative_derivative_betaSeries_eq, derivative_betaSeries_eq,
    betaSeries_eq_X_sq_mul_betaUnit]
  ring

-- Theorem: `(2/9)(β')³ = X^3 * betaW`.
theorem betaP0_factor :
    PowerSeries.C (2 / 9) * (PowerSeries.derivative ℝ betaSeries) ^ 3
      = PowerSeries.X ^ 3 * betaW := by
  rw [betaW, derivative_betaSeries_eq]
  ring

-- Theorem: `cubicOp F = X³(U·F'') + X²(Vp·F') − X³(W·F)`.
theorem cubicOp_eq (F : PowerSeries ℝ) :
    cubicOp F
      = PowerSeries.X ^ 3
          * (betaU * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ F))
        + PowerSeries.X ^ 2 * (betaVp * PowerSeries.derivative ℝ F)
        - PowerSeries.X ^ 3 * (betaW * F) := by
  rw [cubicOp, betaSeries_factor, betaP1_factor, betaP0_factor]
  ring

-- Theorem: `cubicOp` is linear, `cubicOp (F - G) = cubicOp F - cubicOp G`.
theorem cubicOp_sub (F G : PowerSeries ℝ) :
    cubicOp (F - G) = cubicOp F - cubicOp G := by
  rw [cubicOp_eq F, cubicOp_eq G, cubicOp_eq (F - G)]
  simp only [map_sub]
  ring

/-! ### Coefficient extraction -/

-- Theorem: the constant coefficient of a product is the product of constant coefficients.
theorem coeff_zero_mul_PS (φ ψ : PowerSeries ℝ) :
    PowerSeries.coeff 0 (φ * ψ)
      = PowerSeries.coeff 0 φ * PowerSeries.coeff 0 ψ := by
  simp only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_mul]

/-- If `ψ` has vanishing coefficients below `k`, then the coefficient of `X^k` in `φ * ψ`
only sees the constant coefficient of `φ`. -/
-- Theorem: `coeff k (φ * ψ) = coeff 0 φ * coeff k ψ` when `coeff j ψ = 0` for `j < k`.
theorem coeff_mul_of_coeff_eq_zero {φ ψ : PowerSeries ℝ} {k : ℕ}
    (hψ : ∀ j < k, PowerSeries.coeff j ψ = 0) :
    PowerSeries.coeff k (φ * ψ)
      = PowerSeries.coeff 0 φ * PowerSeries.coeff k ψ := by
  have hdiv : PowerSeries.X ^ k ∣ ψ := PowerSeries.X_pow_dvd_iff.mpr hψ
  obtain ⟨ψ', rfl⟩ := hdiv
  have h1 : PowerSeries.coeff k (φ * (PowerSeries.X ^ k * ψ'))
      = PowerSeries.coeff 0 (φ * ψ') := by
    rw [← mul_assoc, mul_comm φ (PowerSeries.X ^ k), mul_assoc]
    rw [PowerSeries.coeff_X_pow_mul']
    simp
  have h2 : PowerSeries.coeff k (PowerSeries.X ^ k * ψ') = PowerSeries.coeff 0 ψ' := by
    rw [PowerSeries.coeff_X_pow_mul']
    simp
  rw [h1, h2, coeff_zero_mul_PS]

-- Theorem: `coeff 2 (cubicOp F) = Vp(0) * coeff 1 F`.
theorem cubicOp_coeff_two (F : PowerSeries ℝ) :
    PowerSeries.coeff 2 (cubicOp F)
      = PowerSeries.coeff 0 betaVp * PowerSeries.coeff 1 F := by
  rw [cubicOp_eq F]
  simp only [map_add, map_sub]
  have hA : PowerSeries.coeff 2
      (PowerSeries.X ^ 3 * (betaU * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ F)))
      = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    norm_num
  have hB : PowerSeries.coeff 2
      (PowerSeries.X ^ 2 * (betaVp * PowerSeries.derivative ℝ F))
      = PowerSeries.coeff 0 betaVp * PowerSeries.coeff 1 F := by
    rw [PowerSeries.coeff_X_pow_mul', if_pos (le_refl 2), Nat.sub_self, coeff_zero_mul_PS,
      PowerSeries.coeff_derivative]
    ring
  have hC : PowerSeries.coeff 2 (PowerSeries.X ^ 3 * (betaW * F)) = 0 := by
    rw [PowerSeries.coeff_X_pow_mul']
    norm_num
  rw [hA, hB, hC]
  ring

-- Theorem: for `n ≥ 2`, `[X^{n+1}](cubicOp D) = n((n−1)U(0)+Vp(0))[Xⁿ]D` when `D`'s
-- coefficients below `n` vanish.
theorem cubicOp_coeff_rec {D : PowerSeries ℝ} (n : ℕ) (hn : 2 ≤ n)
    (hD : ∀ j < n, PowerSeries.coeff j D = 0) :
    PowerSeries.coeff (n + 1) (cubicOp D)
      = (n : ℝ) * (((n : ℝ) - 1) * PowerSeries.coeff 0 betaU
          + PowerSeries.coeff 0 betaVp) * PowerSeries.coeff n D := by
  obtain ⟨E, hE⟩ := PowerSeries.X_pow_dvd_iff.mpr hD
  have hD' : ∀ j < n - 1, PowerSeries.coeff j (PowerSeries.derivative ℝ D) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_derivative, hD (j + 1) (by omega), zero_mul]
  have hD'' : ∀ j < n - 2, PowerSeries.coeff j
      (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)) = 0 := by
    intro j hj
    rw [PowerSeries.coeff_derivative, hD' (j + 1) (by omega), zero_mul]
  have hcD' : PowerSeries.coeff (n - 1) (PowerSeries.derivative ℝ D)
      = (n : ℝ) * PowerSeries.coeff n D := by
    rw [PowerSeries.coeff_derivative, show n - 1 + 1 = n by omega,
      Nat.cast_sub (show 1 ≤ n by omega)]
    ring
  have hcD'' : PowerSeries.coeff (n - 2)
      (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D))
      = (n : ℝ) * ((n : ℝ) - 1) * PowerSeries.coeff n D := by
    rw [PowerSeries.coeff_derivative, show n - 2 + 1 = n - 1 by omega, hcD',
      Nat.cast_sub (show 2 ≤ n by omega)]
    ring
  have hcn : PowerSeries.coeff n D = PowerSeries.coeff 0 E := by
    rw [hE, PowerSeries.coeff_X_pow_mul']
    simp
  have hA : PowerSeries.coeff (n + 1)
      (PowerSeries.X ^ 3
        * (betaU * PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)))
      = PowerSeries.coeff 0 betaU * PowerSeries.coeff (n - 2)
          (PowerSeries.derivative ℝ (PowerSeries.derivative ℝ D)) := by
    rw [show n + 1 = (n - 2) + 3 by omega, PowerSeries.coeff_X_pow_mul]
    exact coeff_mul_of_coeff_eq_zero hD''
  have hB : PowerSeries.coeff (n + 1)
      (PowerSeries.X ^ 2 * (betaVp * PowerSeries.derivative ℝ D))
      = PowerSeries.coeff 0 betaVp
          * PowerSeries.coeff (n - 1) (PowerSeries.derivative ℝ D) := by
    rw [show n + 1 = (n - 1) + 2 by omega, PowerSeries.coeff_X_pow_mul]
    exact coeff_mul_of_coeff_eq_zero hD'
  have hC : PowerSeries.coeff (n + 1) (PowerSeries.X ^ 3 * (betaW * D)) = 0 := by
    rw [hE]
    rw [show PowerSeries.X ^ 3 * (betaW * (PowerSeries.X ^ n * E))
        = PowerSeries.X ^ (n + 3) * (betaW * E) from by
      rw [show n + 3 = 3 + n by omega, pow_add]; ring]
    rw [PowerSeries.coeff_X_pow_mul', if_neg (by omega)]
  rw [cubicOp_eq D]
  simp only [map_add, map_sub]
  rw [hA, hB, hC, hcD'', hcD', hcn]
  ring

/-! ### Uniqueness -/

-- Theorem: a power series solution of `cubicOp F = 0` is determined by its constant term.
theorem cubicOp_unique {F G : PowerSeries ℝ} (hF : cubicOp F = 0) (hG : cubicOp G = 0)
    (h0 : PowerSeries.coeff 0 F = PowerSeries.coeff 0 G) : F = G := by
  set D : PowerSeries ℝ := F - G with hD
  have hode : cubicOp D = 0 := by
    rw [hD, cubicOp_sub, hF, hG, sub_zero]
  have hD0 : PowerSeries.coeff 0 D = 0 := by
    rw [hD, map_sub, h0, sub_self]
  have hD1 : PowerSeries.coeff 1 D = 0 := by
    have h := cubicOp_coeff_two D
    rw [hode, map_zero] at h
    have hv : PowerSeries.coeff 0 betaVp ≠ 0 := by
      rw [coeff_zero_betaVp]; norm_num
    exact (mul_eq_zero.mp h.symm).resolve_left hv
  have hDn : ∀ n : ℕ, PowerSeries.coeff n D = 0 := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
        rcases n with _ | _ | n
        · exact hD0
        · exact hD1
        · have hrec := cubicOp_coeff_rec (n + 2) (by omega)
            (fun j hj => ih j hj)
          rw [hode, map_zero] at hrec
          have hfac : ((n + 2 : ℕ) : ℝ)
              * ((((n + 2 : ℕ) : ℝ) - 1) * PowerSeries.coeff 0 betaU
                  + PowerSeries.coeff 0 betaVp) ≠ 0 := by
            rw [coeff_zero_betaU, coeff_zero_betaVp]
            have hn2 : (2 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
              have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
              push_cast
              linarith
            apply mul_ne_zero
            · exact ne_of_gt (by linarith)
            · exact ne_of_gt (by nlinarith)
          exact (mul_eq_zero.mp hrec.symm).resolve_left hfac
  ext n
  have hn := hDn n
  rw [hD, map_sub] at hn
  exact sub_eq_zero.mp hn

end

end Pconstructible
