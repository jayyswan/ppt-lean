/- Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0; see LICENSE. Part of the Pptc project. -/
import Pptc.Level24Alg

/-! # The level-24 substitution

`Pptc.Level24Alg` records the four polynomials `S, Q, T, U` and the three identities
that certify the degree-12 substitution `x = N(v)/M(v)`.  This file turns them into the
analytic statement: with `κ = -34 + 24√2 + 20√3 - 14√6`,

`∫ v in (0,1), P v / √(v - v¹³) = 2 · F(κ, π/2)`,

where `P` is the differential `ρ (1 + (√3+√6) v² + (3+√6) v³ + cot(π/24) v⁵)`.

The amplitude is taken as `arccos` of `-T √G / W`, which runs from `1` at `v = 0` to
`-1` at `v = 1`; so the amplitude sweeps `0` to `π` in one monotone pass and the
substitution needs no splitting of the interval. -/

namespace Pconstructible

open MeasureTheory Set

/-! ### `U` is positive on the unit interval -/

theorem lvU_pos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) : 0 < lvU v := by
  have h2l := lv_2_lb; have h2u := lv_2_ub; have h3l := lv_3_lb; have h3u := lv_3_ub
  have h6l := lv_6_lb; have h6u := lv_6_ub
  have hp2 : v ^ 2 ≤ 1 := pow_le_one₀ hv0 hv1
  have hp5 : v ^ 5 ≤ 1 := pow_le_one₀ hv0 hv1
  have hp6 : (0 : ℝ) ≤ v ^ 6 := by positivity
  have hq : (0 : ℝ) ≤ (8 * v ^ 2 - 5) ^ 2 := sq_nonneg _
  simp only [lvU]
  nlinarith [hp2, hp5, hp6, hq, hv0, hv1, mul_nonneg hv0 hv0]

/-! ### The amplitude -/

/-- `cos` of the amplitude attached to the parameter `v`. -/
noncomputable def lvCos (v : ℝ) : ℝ := -(lvT v * Real.sqrt (lvG v)) / lvW v

/-- The amplitude itself. -/
noncomputable def lvAmp (v : ℝ) : ℝ := Real.arccos (lvCos v)

theorem lvGsq (v : ℝ) : Real.sqrt (lvG v) ^ 2 = lvG v := Real.sq_sqrt (lvG_pos v).le

theorem lvG_sqrt_pos (v : ℝ) : 0 < Real.sqrt (lvG v) := Real.sqrt_pos.mpr (lvG_pos v)

-- Theorem: `cos²` of the amplitude is `(M - N)/M`, the complement of the elliptic sine.
theorem lvCos_sq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    lvCos v ^ 2 = (lvM v - lvN v) / lvM v := by
  have hW := (lvW_pos hv0 hv1).ne'
  have hS := (lvS_pos hv0 hv1).ne'
  have hD := (lvD_pos v).ne'
  have h1 : lvCos v ^ 2 = lvT v ^ 2 * lvG v / lvW v ^ 2 := by
    rw [lvCos, div_pow, neg_sq, mul_pow, lvGsq]
  rw [h1, lvM_sub_lvN]
  simp only [lvW, lvG, lvM, lvD]
  field_simp
  try ring

-- Theorem: hence `sin²` of the amplitude is `N/M`.
theorem one_sub_lvCos_sq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    1 - lvCos v ^ 2 = lvN v / lvM v := by
  have hM := (lvM_pos hv0 hv1).ne'
  rw [lvCos_sq hv0 hv1]
  field_simp
  try ring

theorem lvCos_sq_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : lvCos v ^ 2 < 1 := by
  have h := one_sub_lvCos_sq hv0.le hv1.le
  have hpos : 0 < lvN v / lvM v := div_pos (lvN_pos hv0 hv1) (lvM_pos hv0.le hv1.le)
  linarith

theorem lvCos_lt_one {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : lvCos v < 1 := by
  nlinarith [lvCos_sq_lt_one hv0 hv1]

theorem neg_one_lt_lvCos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : -1 < lvCos v := by
  nlinarith [lvCos_sq_lt_one hv0 hv1]

-- Theorem: `sin²` of the amplitude, in the form the elliptic integrand wants.
theorem sin_lvAmp_sq {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    Real.sin (lvAmp v) ^ 2 = lvN v / lvM v := by
  have h := lvCos_sq_lt_one hv0 hv1
  rw [lvAmp, Real.sin_arccos, Real.sq_sqrt (by nlinarith)]
  exact one_sub_lvCos_sq hv0.le hv1.le

-- Theorem: the elliptic integrand of the first kind collapses to `S √D / U`.
theorem lvAmp_integrand {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    ellipticFIntegrand lvPar (lvAmp v) = lvS v * Real.sqrt (lvD v) / lvU v := by
  have hS := lvS_pos hv0.le hv1.le
  have hU := lvU_pos hv0.le hv1.le
  have hD := lvD_pos v
  have hM := (lvM_pos hv0.le hv1.le).ne'
  have hkey : 1 - lvPar * Real.sin (lvAmp v) ^ 2 = lvU v ^ 2 / lvM v := by
    rw [sin_lvAmp_sq hv0 hv1, ← lvM_sub_par_lvN]
    field_simp
    try ring
  have hMe : lvM v = lvD v * lvS v ^ 2 := rfl
  rw [ellipticFIntegrand, ellipticEIntegrand, hkey,
    Real.sqrt_div (by positivity) (lvM v), Real.sqrt_sq hU.le, hMe,
    Real.sqrt_mul hD.le, Real.sqrt_sq hS.le, inv_div]
  ring


/-! ### The derivative of the amplitude -/

/-- The derivative of `cos` of the amplitude, in the form the differential identity
gives it: `-A Q U D · shape · √G` over `cot(π/24) · 2 G W²`. -/
noncomputable def lvCosDeriv (v : ℝ) : ℝ :=
  -lvA * (lvQ v * lvU v * lvD v * lvShape v) * Real.sqrt (lvG v)
    / (lvCot * (2 * lvG v * lvW v ^ 2))

theorem lvCot_pos : 0 < lvCot := by have := lvCot_bounds.1; linarith

theorem lvCosDeriv_eq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    (-(lvTd v * Real.sqrt (lvG v) + lvT v * (lvGd v / (2 * Real.sqrt (lvG v)))) * lvW v
        - -(lvT v * Real.sqrt (lvG v)) * lvWd v) / lvW v ^ 2
      = lvCosDeriv v := by
  have hG := lvG_pos v
  have hs0 := (lvG_sqrt_pos v).ne'
  have hGs := lvGsq v
  have hW := (lvW_pos hv0 hv1).ne'
  have hcot := lvCot_pos.ne'
  have h3 := lv_identity_three v
  rw [lvCosDeriv]
  field_simp
  linear_combination (lvG v) * h3
    + (lvCot * lvG v * (2 * lvT v * lvWd v - 2 * lvTd v * lvW v)
        + lvA * (lvQ v * lvU v * lvD v * lvShape v)) * hGs

end Pconstructible
