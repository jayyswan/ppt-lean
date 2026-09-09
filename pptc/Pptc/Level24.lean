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


/-! ### The integrand collapses

`ρ = √(-A) / (2 cot(π/24))`.  Squaring both sides removes every square root and leaves a
rational identity in the polynomials, whose one non-obvious ingredient is
`G · (v - v⁵)(v² - v + 1) = v - v¹³`. -/

theorem lv_eq_of_sq_eq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 = b ^ 2) :
    a = b := by
  rw [← Real.sqrt_sq ha, ← Real.sqrt_sq hb, h]

theorem lvShape_pos {v : ℝ} (hv0 : 0 ≤ v) : 0 < lvShape v := by
  have h2 := Real.sqrt_nonneg 2
  have h3 := Real.sqrt_nonneg 3
  have hc := lvCot_pos
  have : (0 : ℝ) ≤ Real.sqrt 2 * Real.sqrt 3 := by positivity
  simp only [lvShape]
  have e2 : (0 : ℝ) ≤ (Real.sqrt 3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 2 := by positivity
  have e3 : (0 : ℝ) ≤ (3 + Real.sqrt 2 * Real.sqrt 3) * v ^ 3 := by positivity
  have e5 : (0 : ℝ) ≤ lvCot * v ^ 5 := by positivity
  linarith

theorem lvA_pos_neg : 0 < -lvA := by linarith [lvA_neg]

/-- The constant of the differential, `ρ = √(-A) / (2 cot(π/24))`. -/
noncomputable def lvRho : ℝ := Real.sqrt (-lvA) / (2 * lvCot)

theorem lvRho_pos : 0 < lvRho :=
  div_pos (Real.sqrt_pos.mpr lvA_pos_neg) (by linarith [lvCot_pos])

/-- The `v`-side integrand `ρ · shape(v) / √(v - v¹³)`. -/
noncomputable def lvIntegrand (v : ℝ) : ℝ := lvRho * lvShape v / Real.sqrt (v - v ^ 13)

theorem hasDerivAt_lvCos {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    HasDerivAt lvCos (lvCosDeriv v) v := by
  have hG := lvG_pos v
  have hW := (lvW_pos hv0 hv1).ne'
  have hsqrt : HasDerivAt (fun x => Real.sqrt (lvG x)) (lvGd v / (2 * Real.sqrt (lvG v))) v :=
    (hasDerivAt_lvG v).sqrt hG.ne'
  exact ((((hasDerivAt_lvT v).mul hsqrt).neg).div (hasDerivAt_lvW v) hW).congr_deriv
    (lvCosDeriv_eq hv0 hv1)

theorem lvCosDeriv_neg {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : lvCosDeriv v < 0 := by
  have hQ := lvQ_neg hv0.le hv1.le
  have hU := lvU_pos hv0.le hv1.le
  have hD := lvD_pos v
  have hSh := lvShape_pos hv0.le
  have hGs := lvG_sqrt_pos v
  have hW := lvW_pos hv0.le hv1.le
  have hG := lvG_pos v
  have hcot := lvCot_pos
  have hA := lvA_pos_neg
  have hnum : -lvA * (lvQ v * lvU v * lvD v * lvShape v) * Real.sqrt (lvG v) < 0 := by
    have h2 : 0 < lvU v * lvD v * lvShape v := by positivity
    have h1 : lvQ v * lvU v * lvD v * lvShape v < 0 := by
      calc lvQ v * lvU v * lvD v * lvShape v
          = lvQ v * (lvU v * lvD v * lvShape v) := by ring
        _ < 0 := mul_neg_of_neg_of_pos hQ h2
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA h1) hGs
  rw [lvCosDeriv]
  exact div_neg_of_neg_of_pos hnum (by positivity)

/-- The derivative of the amplitude. -/
noncomputable def lvAmpDeriv (v : ℝ) : ℝ := -lvCosDeriv v / Real.sqrt (1 - lvCos v ^ 2)

theorem hasDerivAt_lvAmp {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    HasDerivAt lvAmp (lvAmpDeriv v) v := by
  have h1 : lvCos v ≠ -1 := ne_of_gt (neg_one_lt_lvCos hv0 hv1)
  have h2 : lvCos v ≠ 1 := ne_of_lt (lvCos_lt_one hv0 hv1)
  have hc := (Real.hasDerivAt_arccos h1 h2).comp v (hasDerivAt_lvCos hv0.le hv1.le)
  refine hc.congr_deriv ?_
  rw [lvAmpDeriv]
  ring

theorem lvAmpDeriv_pos {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) : 0 < lvAmpDeriv v := by
  have h := lvCos_sq_lt_one hv0 hv1
  have hs : 0 < Real.sqrt (1 - lvCos v ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  exact div_pos (by linarith [lvCosDeriv_neg hv0 hv1]) hs

-- Theorem: the substitution collapses the elliptic integrand onto `ρ shape(v)/√(v - v¹³)`.
theorem lvIntegrand_eq {v : ℝ} (hv0 : 0 < v) (hv1 : v < 1) :
    |lvAmpDeriv v| • ellipticFIntegrand lvPar (lvAmp v) = lvIntegrand v := by
  have hG := lvG_pos v
  have hN := lvN_pos hv0 hv1
  have hM := lvM_pos hv0.le hv1.le
  have hS := lvS_pos hv0.le hv1.le
  have hU := lvU_pos hv0.le hv1.le
  have hD := lvD_pos v
  have hSh := lvShape_pos hv0.le
  have h13 := lv_v13_pos hv0 hv1
  have hA := lvA_pos_neg
  have hcot := lvCot_pos
  have hW := lvW_pos hv0.le hv1.le
  have hcs := lvCos_sq_lt_one hv0 hv1
  have hcs' : 0 < 1 - lvCos v ^ 2 := by nlinarith
  rw [smul_eq_mul, abs_of_pos (lvAmpDeriv_pos hv0 hv1), lvAmp_integrand hv0 hv1]
  refine lv_eq_of_sq_eq (mul_nonneg (lvAmpDeriv_pos hv0 hv1).le (by positivity))
    (le_of_lt (by rw [lvIntegrand]
                  exact div_pos (mul_pos lvRho_pos hSh) (Real.sqrt_pos.mpr h13))) ?_
  have e1 : lvAmpDeriv v ^ 2 = lvCosDeriv v ^ 2 * lvM v / lvN v := by
    rw [lvAmpDeriv, div_pow, neg_pow, Real.sq_sqrt hcs'.le, one_sub_lvCos_sq hv0.le hv1.le]
    field_simp
    try ring
  have e2 : lvCosDeriv v ^ 2
      = lvA ^ 2 * (lvQ v * lvU v * lvD v * lvShape v) ^ 2 * lvG v
          / (lvCot * (2 * lvG v * lvW v ^ 2)) ^ 2 := by
    rw [lvCosDeriv, div_pow, mul_pow, mul_pow, lvGsq, neg_pow]
    ring
  have e3 : lvIntegrand v ^ 2 = -lvA / (4 * lvCot ^ 2) * lvShape v ^ 2 / (v - v ^ 13) := by
    rw [lvIntegrand, div_pow, mul_pow, lvRho, div_pow, Real.sq_sqrt hA.le,
      Real.sq_sqrt h13.le, mul_pow]
    field_simp
    ring
  -- `G · (v⁵ - v)(v² - v + 1) = -(v - v¹³)`: the one non-obvious cancellation.
  have hz : (v ^ 5 - v) * (v ^ 2 - v + 1) ≠ 0 := by
    have h5 : v ^ 5 - v < 0 := by
      have := pow_lt_pow_right_of_lt_one₀ hv0 hv1 (by norm_num : 1 < 5)
      simpa using this
    exact (mul_neg_of_neg_of_pos h5 (lv_V2_pos v)).ne
  have h13e : v - v ^ 13 = -(lvG v * ((v ^ 5 - v) * (v ^ 2 - v + 1))) := by
    simp only [lvG, lvD]; ring
  have hNe : lvN v = lvA * ((v ^ 5 - v) * (v ^ 2 - v + 1)) * lvQ v ^ 2 := by
    simp only [lvN]; ring
  have hMe : lvM v = lvD v * lvS v ^ 2 := rfl
  have hWe : lvW v = lvS v * lvD v := rfl
  have hQ0 : lvQ v ≠ 0 := (lvQ_neg hv0.le hv1.le).ne
  have hG0 : lvG v ≠ 0 := hG.ne'
  have hD0 : lvD v ≠ 0 := hD.ne'
  have hS0 : lvS v ≠ 0 := hS.ne'
  have hU0 : lvU v ≠ 0 := hU.ne'
  have hcot0 : lvCot ≠ 0 := hcot.ne'
  have hA0 : lvA ≠ 0 := by intro h; rw [h] at hA; norm_num at hA
  rw [mul_pow, e1, e2, e3]
  simp only [mul_pow, div_pow]
  rw [Real.sq_sqrt hD.le, hNe, hMe, hWe, h13e]
  field_simp
  ring

end Pconstructible
