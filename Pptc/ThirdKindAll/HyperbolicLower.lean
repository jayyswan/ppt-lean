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

import Pptc.ThirdKindAll.Circular
import Pptc.ThirdKindAll.CircularUpper
import Pptc.ThirdKindAll.Pseudo
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # Pptc.ThirdKindAll.HyperbolicLower

The hyperbolic range `0 < n < c`.

The first reduction is DLMF 19.7.8, the reciprocal-parameter connection:

  `Π(n,φ) = F(φ) + artanh(r tanφ / Δ(φ))/r - Π(c/n,φ)`,
  `r = √((c/n - 1)(1 - n))`,

valid while `(c/n) sin²φ < 1`. -/

namespace Pconstructible

/-- The reciprocal parameter `c/n > 1`. -/
noncomputable def hypNu (c n : ℝ) : ℝ := c / n

/-- `r = √((c/n - 1)(1 - n))`. -/
noncomputable def hypR (c n : ℝ) : ℝ :=
  Real.sqrt ((c / n - 1) * (1 - n))

/-- The `artanh` argument `r tanφ / Δ(φ)`. -/
noncomputable def hypA (c n φ : ℝ) : ℝ :=
  hypR c n * (Real.tan φ / ellipticEIntegrand c φ)

/-- The elementary term of the connection formula. -/
noncomputable def hypLog (c n φ : ℝ) : ℝ :=
  Real.artanh (hypA c n φ) / hypR c n

/-- The right-hand side of DLMF 19.7.8. -/
noncomputable def hypRHS (c n φ : ℝ) : ℝ :=
  ellipticF c φ + hypLog c n φ - ellipticPiInc c (hypNu c n) φ

/-! ### The elementary algebra of the connection formula -/

theorem hypA_deriv_alg {s w E c r : ℝ} (hs : s ^ 2 + w ^ 2 = 1)
    (hE : E ^ 2 = 1 - c * s ^ 2) (hw : w ≠ 0) (hEne : E ≠ 0) :
    r * (((1 / w ^ 2) * E - (s / w) * (-(2 * c * s * w) / (2 * E))) / E ^ 2)
      = r * ((1 - c * s ^ 4) / (w ^ 2 * E ^ 3)) := by
  have hw2 : w ^ 2 = 1 - s ^ 2 := by linarith
  field_simp [hw, hEne]
  rw [hw2, hE]
  ring

theorem hypA_sq_sub_alg {s w E c r n : ℝ} (hs : s ^ 2 + w ^ 2 = 1)
    (hE : E ^ 2 = 1 - c * s ^ 2) (hr : r ^ 2 = (c / n - 1) * (1 - n))
    (hn : n ≠ 0) :
    w ^ 2 * E ^ 2 - r ^ 2 * s ^ 2 = (1 - n * s ^ 2) * (1 - c / n * s ^ 2) := by
  have hr' : n * r ^ 2 = (c - n) * (1 - n) := by
    calc n * r ^ 2 = n * ((c / n - 1) * (1 - n)) := by rw [hr]
      _ = (c - n) * (1 - n) := by field_simp [hn]
  field_simp [hn]
  ring_nf
  linear_combination (-n * (c * s ^ 2 - c * w ^ 2 - 1)) * hs + (n * w ^ 2) * hE
    + (-s ^ 2) * hr' + (-n * c * w ^ 2) * hs

theorem one_sub_hypA_sq_alg {s w E c r n : ℝ} (hs : s ^ 2 + w ^ 2 = 1)
    (hE : E ^ 2 = 1 - c * s ^ 2) (hr : r ^ 2 = (c / n - 1) * (1 - n))
    (hw : w ≠ 0) (hEne : E ≠ 0) (hn : n ≠ 0) :
    1 - (r * (s / (w * E))) ^ 2
      = (1 - n * s ^ 2) * (1 - c / n * s ^ 2) / (w ^ 2 * E ^ 2) := by
  have hprod := hypA_sq_sub_alg hs hE hr hn
  have hprod' : n * (w ^ 2 * E ^ 2 - r ^ 2 * s ^ 2)
      = (1 - n * s ^ 2) * (n - c * s ^ 2) := by
    rw [hprod]
    field_simp [hn]
  field_simp [hw, hEne, hn]
  linarith [hprod']

theorem hyp_deriv_alg {E s c n : ℝ} (hE : E ≠ 0)
    (h1 : 1 - n * s ^ 2 ≠ 0) (h2 : 1 - c / n * s ^ 2 ≠ 0) (hn : n ≠ 0) :
    1 / E + (1 - c * s ^ 4) / (E * (1 - n * s ^ 2) * (1 - c / n * s ^ 2))
        - 1 / (E * (1 - c / n * s ^ 2))
      = 1 / ((1 - n * s ^ 2) * E) := by
  have hD2 : n - c * s ^ 2 ≠ 0 := by
    have hm := mul_ne_zero hn h2
    convert hm using 1
    field_simp [hn]
  have hD : n - c * s ^ 2 - n ^ 2 * s ^ 2 + c * n * s ^ 4 ≠ 0 := by
    have hm := mul_ne_zero h1 hD2
    convert hm using 1
    ring
  field_simp [hE, h1, h2, hn, hD2, hD]
  field_simp [h1]
  ring

/-! ### Basic facts -/

theorem hypR_sq {c n : ℝ} (hc : c < 1) (hn : 0 < n) (hnc : n < c) :
    hypR c n ^ 2 = (c / n - 1) * (1 - n) := by
  rw [hypR]
  refine Real.sq_sqrt (mul_nonneg ?_ ?_)
  · rw [sub_nonneg]
    exact (one_le_div hn).mpr hnc.le
  · linarith

theorem hypR_pos {c n : ℝ} (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c) :
    0 < hypR c n := by
  rw [hypR]
  refine Real.sqrt_pos.mpr (mul_pos ?_ ?_)
  · rw [sub_pos]
    exact (one_lt_div hn).mpr hnc
  · linarith

theorem hypA_zero (c n : ℝ) : hypA c n 0 = 0 := by
  simp [hypA, Real.tan_zero]

theorem hypLog_zero (c n : ℝ) (hr : hypR c n ≠ 0) : hypLog c n 0 = 0 := by
  simp [hypLog, hypA_zero]

theorem hypRHS_zero (c n : ℝ) (hr : hypR c n ≠ 0) : hypRHS c n 0 = 0 := by
  unfold hypRHS
  rw [hypLog_zero c n hr]
  simp [ellipticF, ellipticPiInc]

/-- The derivative of `Π` at a parameter above `1`, as long as the path avoids the pole. -/
theorem hasDerivAt_ellipticPiInc_of_ne {c n θ : ℝ} (hc : c < 1)
    (hint : IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume 0 θ)
    (hne : 1 - n * Real.sin θ ^ 2 ≠ 0) :
    HasDerivAt (ellipticPiInc c n) (ellipticPiIntegrand c n θ) θ := by
  have hca : ContinuousAt (ellipticPiIntegrand c n) θ := by
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · exact (by fun_prop : ContinuousAt (fun x : ℝ => 1 - n * Real.sin x ^ 2) θ).mul
        (continuous_ellipticEIntegrand c).continuousAt
    · exact mul_ne_zero hne (ellipticEIntegrand_pos hc θ).ne'
  have hcont : Continuous fun x : ℝ => 1 - n * Real.sin x ^ 2 := by fun_prop
  have hs : IsOpen {x : ℝ | 1 - n * Real.sin x ^ 2 ≠ 0} := by
    have hlt : IsOpen {x : ℝ | 1 - n * Real.sin x ^ 2 < 0} :=
      isOpen_lt hcont continuous_const
    have hgt : IsOpen {x : ℝ | 0 < 1 - n * Real.sin x ^ 2} :=
      isOpen_lt continuous_const hcont
    convert hlt.union hgt using 1
    ext x
    constructor
    · intro hx
      rcases lt_or_gt_of_ne hx with h | h
      · exact Or.inl h
      · exact Or.inr h
    · rintro (h | h)
      · exact ne_of_lt h
      · exact ne_of_gt h
  have hf : ∀ x ∈ {x : ℝ | 1 - n * Real.sin x ^ 2 ≠ 0},
      ContinuousAt (ellipticPiIntegrand c n) x := by
    intro x hx
    refine ContinuousAt.div continuousAt_const ?_ ?_
    · exact (by fun_prop : ContinuousAt (fun y : ℝ => 1 - n * Real.sin y ^ 2) x).mul
        (continuous_ellipticEIntegrand c).continuousAt
    · exact mul_ne_zero hx (ellipticEIntegrand_pos hc x).ne'
  have hmeas : StronglyMeasurableAtFilter (ellipticPiIntegrand c n) (nhds θ)
      MeasureTheory.volume :=
    (ContinuousAt.stronglyMeasurableAtFilter (μ := MeasureTheory.volume) hs hf) θ hne
  change HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, ellipticPiIntegrand c n x)
    (ellipticPiIntegrand c n θ) θ
  exact intervalIntegral.integral_hasDerivAt_right hint hmeas hca

/-- Bounds for the `artanh` argument. -/
theorem hypA_bounds {c n φ : ℝ} (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (hpole : (c / n) * Real.sin φ ^ 2 < 1) :
    -1 < hypA c n φ ∧ hypA c n φ < 1 := by
  have hcos : Real.cos φ ≠ 0 := by
    intro h
    have hs : Real.sin φ ^ 2 = 1 := by rw [← Real.sin_sq_add_cos_sq φ, h]; ring
    have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
    nlinarith [hpole, hs, hdiv]
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have hsin := Real.sin_sq_add_cos_sq φ
  have hr2 := hypR_sq hc hn hnc
  have h1mA2 := one_sub_hypA_sq_alg hsin hE2 hr2 hcos hE.ne' hn.ne'
  have hAeq : hypA c n φ
      = hypR c n * (Real.sin φ / (Real.cos φ * ellipticEIntegrand c φ)) := by
    simp only [hypA, Real.tan_eq_sin_div_cos, div_div]
  have hpos1 : 0 < 1 - n * Real.sin φ ^ 2 := by nlinarith
  have hpos2 : 0 < 1 - c / n * Real.sin φ ^ 2 := by linarith
  have hpos : 0 < 1 - hypA c n φ ^ 2 := by
    rw [hAeq, h1mA2]
    exact div_pos (mul_pos hpos1 hpos2)
      (mul_pos (sq_pos_of_ne_zero hcos) (sq_pos_of_ne_zero hE.ne'))
  constructor <;> nlinarith [sq_nonneg (hypA c n φ - 1), sq_nonneg (hypA c n φ + 1)]

/-- The derivative of the elementary `artanh` term. -/
theorem hasDerivAt_hypLog {c n t : ℝ} (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (hpole : (c / n) * Real.sin t ^ 2 < 1) :
    HasDerivAt (hypLog c n)
      ((1 - c * Real.sin t ^ 4)
        / (ellipticEIntegrand c t * (1 - n * Real.sin t ^ 2)
          * (1 - c / n * Real.sin t ^ 2))) t := by
  have hrpos := hypR_pos (by linarith [hn, hnc]) hc hn hnc
  have hrne : hypR c n ≠ 0 := hrpos.ne'
  have hcos : Real.cos t ≠ 0 := by
    intro h
    have hs : Real.sin t ^ 2 = 1 := by rw [← Real.sin_sq_add_cos_sq t, h]; ring
    have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
    nlinarith [hpole, hs, hdiv]
  have hE := ellipticEIntegrand_pos hc t
  have hE2 := ellipticEIntegrand_sq hc t
  have hsin := Real.sin_sq_add_cos_sq t
  have hr2 := hypR_sq hc hn hnc
  have hΔ' : HasDerivAt (ellipticEIntegrand c)
      (-(2 * c * Real.sin t * Real.cos t) / (2 * ellipticEIntegrand c t)) t :=
    hasDerivAt_ellipticEIntegrand c t (one_sub_mul_sin_sq_pos hc t).ne'
  have hA : HasDerivAt (hypA c n)
      (hypR c n * ((1 / Real.cos t ^ 2 * ellipticEIntegrand c t
        - Real.tan t * (-(2 * c * Real.sin t * Real.cos t)
          / (2 * ellipticEIntegrand c t))) / ellipticEIntegrand c t ^ 2)) t := by
    have h := ((Real.hasDerivAt_tan hcos).div hΔ' hE.ne').const_mul (hypR c n)
    change HasDerivAt (fun y => hypR c n * (Real.tan y / ellipticEIntegrand c y)) _ t
    exact h
  have hA' : HasDerivAt (hypA c n)
      (hypR c n * ((1 - c * Real.sin t ^ 4)
        / (Real.cos t ^ 2 * ellipticEIntegrand c t ^ 3))) t := by
    refine hA.congr_deriv ?_
    simp only [Real.tan_eq_sin_div_cos]
    exact hypA_deriv_alg hsin hE2 hcos hE.ne'
  have hb := hypA_bounds hc hn hnc hpole
  have h1mA2 := one_sub_hypA_sq_alg hsin hE2 hr2 hcos hE.ne' hn.ne'
  have hAeq : hypA c n t
      = hypR c n * (Real.sin t / (Real.cos t * ellipticEIntegrand c t)) := by
    simp only [hypA, Real.tan_eq_sin_div_cos, div_div]
  have h1 : (1 : ℝ) - n * Real.sin t ^ 2 ≠ 0 := by
    have hnlt : n < 1 := by linarith
    have hs := Real.sin_sq_le_one t
    nlinarith [hs, hnlt, hn]
  have h2 : (1 : ℝ) - c / n * Real.sin t ^ 2 ≠ 0 := by linarith [hpole]
  have hlog := (hasDerivAt_artanh hb.1 hb.2).comp t hA'
  have hlogdiv := hlog.div_const (hypR c n)
  refine hlogdiv.congr_deriv ?_
  rw [hAeq]
  field_simp [hrne, hcos, hE.ne', hn.ne', h1, h2]
  rw [hypA_sq_sub_alg hsin hE2 hr2 hn.ne']
  field_simp [hcos, hE.ne', hn.ne', h1, h2]

/-- The derivative of the DLMF 19.7.8 right-hand side. -/
theorem hasDerivAt_hypRHS {c n t : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (ht0 : 0 ≤ t) (htπ : t < Real.pi / 2)
    (hpole : (c / n) * Real.sin t ^ 2 < 1) :
    HasDerivAt (hypRHS c n) (ellipticPiIntegrand c n t) t := by
  have hcos : Real.cos t ≠ 0 := by
    intro h
    have hs : Real.sin t ^ 2 = 1 := by rw [← Real.sin_sq_add_cos_sq t, h]; ring
    have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
    nlinarith [hpole, hs, hdiv]
  have hE := ellipticEIntegrand_pos hc t
  have hnu_gt : (1 : ℝ) < hypNu c n := by
    rw [hypNu]; exact (one_lt_div hn).mpr hnc
  have hnu_ne : 1 - hypNu c n * Real.sin t ^ 2 ≠ 0 := by
    rw [hypNu]; nlinarith [hpole, hnu_gt]
  have hint : IntervalIntegrable (ellipticPiIntegrand c (hypNu c n))
      MeasureTheory.volume 0 t := by
    have hcont : ContinuousOn (ellipticPiIntegrand c (hypNu c n)) (Set.uIcc (0 : ℝ) t) := by
      refine ContinuousOn.div continuousOn_const ?_ ?_
      · exact (Continuous.continuousOn (by fun_prop)).mul
          (continuous_ellipticEIntegrand c).continuousOn
      · intro x hx
        rw [Set.uIcc_of_le ht0] at hx
        have hsinle : Real.sin x ^ 2 ≤ Real.sin t ^ 2 := by
          have hle : Real.sin x ≤ Real.sin t :=
            Real.sin_le_sin_of_le_of_le_pi_div_two
              (by linarith [hx.1, Real.pi_pos]) (by linarith [htπ]) hx.2
          have hx0 : 0 ≤ Real.sin x :=
            Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, htπ, Real.pi_pos])
          nlinarith
        rw [hypNu]
        have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
        exact mul_ne_zero (by nlinarith [hpole, hsinle, hdiv])
          (ellipticEIntegrand_pos hc x).ne'
    exact hcont.intervalIntegrable
  have h1 : (1 : ℝ) - n * Real.sin t ^ 2 ≠ 0 := by
    have hnlt : n < 1 := by linarith
    have hs := Real.sin_sq_le_one t
    nlinarith [hs, hnlt, hn]
  have h2 : (1 : ℝ) - c / n * Real.sin t ^ 2 ≠ 0 := by linarith [hpole]
  have hD2 : n - c * Real.sin t ^ 2 ≠ 0 := by
    intro h
    have hc_over : c / n * Real.sin t ^ 2 = 1 := by
      field_simp [hn.ne']
      linarith [h]
    linarith [hpole]
  have hD : n - c * Real.sin t ^ 2 - n ^ 2 * Real.sin t ^ 2
      + c * n * Real.sin t ^ 4 ≠ 0 := by
    have hm := mul_ne_zero h1 hD2
    convert hm using 1
    ring
  have hF := hasDerivAt_ellipticF hc t
  have hlog := hasDerivAt_hypLog hc hn hnc hpole
  have hPi := hasDerivAt_ellipticPiInc_of_ne hc hint hnu_ne
  have htotal := (hF.add hlog).sub hPi
  refine htotal.congr_deriv ?_
  simp only [hypNu, ellipticPiIntegrand, ellipticFIntegrand]
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using
    hyp_deriv_alg hE.ne' h1 h2 hn.ne'

/-- DLMF 19.7.8, with the `n > 1` parameter on the right. -/
theorem ellipticPiInc_eq_hyp_recip {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (h0 : 0 ≤ φ) (hφ : φ ≤ Real.pi / 2)
    (hpole : (c / n) * Real.sin φ ^ 2 < 1) :
    ellipticPiInc c n φ = hypRHS c n φ := by
  have hrpos := hypR_pos hc0 hc hn hnc
  have hrne : hypR c n ≠ 0 := hrpos.ne'
  have hφlt : φ < Real.pi / 2 := by
    rcases lt_or_eq_of_le hφ with h | h
    · exact h
    · subst h
      rw [Real.sin_pi_div_two] at hpole
      have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
      nlinarith
  have hcont : ContinuousOn (ellipticPiIntegrand c n) (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul
        (continuous_ellipticEIntegrand c).continuousOn
    · intro x hx
      rw [Set.uIcc_of_le h0] at hx
      have hsinle : Real.sin x ^ 2 ≤ Real.sin φ ^ 2 := by
        have hle : Real.sin x ≤ Real.sin φ :=
          Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [hx.1, Real.pi_pos]) (by linarith [hφ]) hx.2
        have hx0 : 0 ≤ Real.sin x :=
          Real.sin_nonneg_of_nonneg_of_le_pi hx.1 (by linarith [hx.2, hφ, Real.pi_pos])
        nlinarith
      have hsinφ_lt : Real.sin φ ^ 2 < 1 := by
        have hdiv : (1 : ℝ) < c / n := (one_lt_div hn).mpr hnc
        nlinarith [hpole, hdiv]
      have hsinx_lt : Real.sin x ^ 2 < 1 := lt_of_le_of_lt hsinle hsinφ_lt
      have hnlt : n < 1 := by linarith
      exact mul_ne_zero
        (by nlinarith [hsinx_lt, hnlt, hn, sq_nonneg (Real.sin x)])
        (ellipticEIntegrand_pos hc x).ne'
  have hint : IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume 0 φ :=
    hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [Set.uIcc_of_le h0] at ht
      exact hasDerivAt_hypRHS hc0 hc hn hnc ht.1
        (lt_of_le_of_lt ht.2 hφlt)
        (by
          have hsinle : Real.sin t ^ 2 ≤ Real.sin φ ^ 2 := by
            have hle : Real.sin t ≤ Real.sin φ :=
              Real.sin_le_sin_of_le_of_le_pi_div_two
                (by linarith [ht.1, Real.pi_pos]) (by linarith [hφ]) ht.2
            have ht0 : 0 ≤ Real.sin t :=
              Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, hφ, Real.pi_pos])
            nlinarith
          have hdiv : 0 < c / n := div_pos (by linarith) hn
          have hsinle' : (c / n) * Real.sin t ^ 2 ≤ (c / n) * Real.sin φ ^ 2 :=
            mul_le_mul_of_nonneg_left hsinle hdiv.le
          nlinarith [hpole, hsinle'])) hint
  rw [ellipticPiInc, hkey, hypRHS_zero c n hrne, sub_zero]

/-- The direct branch of `0 < n < c`, where `(c/n) sin²φ < 1`. -/
theorem ellipticPiInc_Pconstructible_hyp_direct {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hpole : (c / n) * Real.sin φ ^ 2 < 1) :
    PConstructible (ellipticPiInc c n φ) := by
  rcases eq_or_lt_of_le h0 with rfl | hφpos
  · simpa [ellipticPiInc] using zero_Pconstructible
  · rw [ellipticPiInc_eq_hyp_recip hc0 hc hn hnc h0 hπ.le hpole]
    unfold hypRHS
    have hrP : PConstructible (hypR c n) := by
      unfold hypR
      pconstructible
    have hargP : PConstructible (hypA c n φ) := by
      unfold hypA
      pconstructible
    have hb := hypA_bounds hc hn hnc hpole
    have hlogP : PConstructible (hypLog c n φ) := by
      unfold hypLog
      exact PConstructible.div (artanh_Pconstructible hargP hb.1 hb.2) hrP
    have hnuP : PConstructible (hypNu c n) := by
      unfold hypNu
      pconstructible
    have hnu_gt : (1 : ℝ) < hypNu c n := by
      unfold hypNu
      exact (one_lt_div hn).mpr hnc
    have hpnu : hypNu c n * Real.sin φ ^ 2 < 1 := by
      unfold hypNu
      exact hpole
    have hPiP : PConstructible (ellipticPiInc c (hypNu c n) φ) :=
      ellipticPiInc_Pconstructible_gt_one' hcP hnuP hφP hc0 hc hnu_gt hφpos hπ hpnu
    exact PConstructible.sub (PConstructible.add
      (ellipticF_Pconstructible hcP hφP hc) hlogP) hPiP

/-- The critical angle `β = arcsin √(n/c)`. -/
noncomputable def hypBeta (c n : ℝ) : ℝ :=
  Real.arcsin (Real.sqrt (n / c))

/-- The weight `Q(t) = c sin t cos t Δ(t)` of the middle path. -/
noncomputable def hypQ (c t : ℝ) : ℝ :=
  c * Real.sin t * Real.cos t * ellipticEIntegrand c t

theorem hypBeta_nonneg {c n : ℝ} : 0 ≤ hypBeta c n := by
  unfold hypBeta
  exact Real.arcsin_nonneg.mpr (Real.sqrt_nonneg _)

theorem hypBeta_lt_pi_div_two {c n : ℝ} (hc0 : 0 < c) (hn : 0 ≤ n) (hnc : n < c) :
    hypBeta c n < Real.pi / 2 := by
  unfold hypBeta
  rw [Real.arcsin_lt_pi_div_two]
  have hnonneg : 0 ≤ n / c := div_nonneg hn hc0.le
  have hsq := Real.sq_sqrt hnonneg
  have hlt : n / c < 1 := (div_lt_one hc0).mpr hnc
  nlinarith [Real.sqrt_nonneg (n / c)]

theorem hypBeta_sin_sq {c n : ℝ} (hc0 : 0 < c) (hn : 0 ≤ n) (hnc : n < c) :
    Real.sin (hypBeta c n) ^ 2 = n / c := by
  unfold hypBeta
  have hnonneg : 0 ≤ n / c := div_nonneg hn hc0.le
  have hle : Real.sqrt (n / c) ≤ 1 := by
    have hsq := Real.sq_sqrt hnonneg
    have hlt : n / c ≤ 1 := (div_le_one hc0).mpr hnc.le
    nlinarith [Real.sqrt_nonneg (n / c)]
  rw [Real.sin_arcsin (by linarith [Real.sqrt_nonneg (n / c)]) hle, Real.sq_sqrt hnonneg]

theorem hypBeta_pos {c n : ℝ} (hc0 : 0 < c) (hn : 0 < n) (hnc : n < c) :
    0 < hypBeta c n := by
  unfold hypBeta
  exact Real.arcsin_pos.mpr (Real.sqrt_pos.mpr (div_pos hn hc0))

theorem hypBeta_cos_pos {c n : ℝ} (hc0 : 0 < c) (hn : 0 < n) (hnc : n < c) :
    0 < Real.cos (hypBeta c n) :=
  Real.cos_pos_of_mem_Ioo
    ⟨by linarith [hypBeta_nonneg (c := c) (n := n), Real.pi_pos],
      hypBeta_lt_pi_div_two hc0 hn.le hnc⟩

theorem hypQ_ne_zero {c t : ℝ} (hc0 : 0 < c) (ht0 : 0 < t) (htπ : t < Real.pi / 2)
    (hc : c < 1) : hypQ c t ≠ 0 := by
  have hs : 0 < Real.sin t := Real.sin_pos_of_pos_of_lt_pi ht0 (by linarith [htπ, Real.pi_pos])
  have hcos : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], htπ⟩
  have hE : 0 < ellipticEIntegrand c t := ellipticEIntegrand_pos hc t
  unfold hypQ
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hc0.ne' hs.ne') hcos.ne') hE.ne'

/-- The exchange right-hand side: Legendre's relation solving for the parameter below
`c sin²φ`. -/
noncomputable def hypExchangeRHS (c n φ : ℝ) : ℝ :=
  ellipticF c φ + n / hypQ c (hypBeta c n) *
    (hypQ c φ * (ellipticPiInc c (c * Real.sin φ ^ 2) (hypBeta c n)
        - ellipticF c (hypBeta c n)) / (c * Real.sin φ ^ 2)
      + ellipticF c φ * ellipticE c (hypBeta c n)
        - ellipticE c φ * ellipticF c (hypBeta c n))

theorem exchange_solve {A Qb Qf n' Fφ Eφ Fβ Eβ P' : ℝ}
    (hQb : Qb ≠ 0) (hn' : n' ≠ 0)
    (hinter : Qb * A - Qf * ((P' - Fβ) / n') = Fφ * Eβ - Eφ * Fβ) :
    A = (Qf * ((P' - Fβ) / n') + (Fφ * Eβ - Eφ * Fβ)) / Qb := by
  field_simp [hQb, hn'] at hinter ⊢
  linarith [hinter]

/-- Legendre's exchange relation, written as a formula for `Π(n,φ)` when
`n < c sin²φ`. -/
theorem ellipticPiInc_eq_exchange {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hlt : n < c * Real.sin φ ^ 2) :
    ellipticPiInc c n φ = hypExchangeRHS c n φ := by
  set β := hypBeta c n with hβdef
  set n' := c * Real.sin φ ^ 2 with hn'def
  have hβ0 : 0 ≤ β := hypBeta_nonneg
  have hβπ : β < Real.pi / 2 := hypBeta_lt_pi_div_two hc0 hn.le hnc
  have hβpos : 0 < β := hypBeta_pos hc0 hn hnc
  have hβsin : Real.sin β ^ 2 = n / c := hypBeta_sin_sq hc0 hn.le hnc
  have hcn : c * Real.sin β ^ 2 = n := by
    rw [hβsin]
    field_simp [hc0.ne']
  have hsin2pos : 0 < Real.sin φ ^ 2 := by nlinarith [hlt, hn, hc0]
  have hφpos : 0 < φ := by
    rcases eq_or_lt_of_le h0 with rfl | h
    · simp at hsin2pos
    · exact h
  have hn'pos : 0 < n' := by
    rw [hn'def]
    nlinarith [hlt, hn, hc0]
  have hn'lt : n' < c := by
    rw [hn'def]
    have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩
    have hs : Real.sin φ ^ 2 < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_ne_zero hcos.ne']
    nlinarith
  have hQβ : hypQ c β ≠ 0 := hypQ_ne_zero hc0 hβpos hβπ hc
  have hQφ : hypQ c φ ≠ 0 := hypQ_ne_zero hc0 hφpos hπ hc
  have hne_n : ∀ θ ∈ Set.uIcc (0 : ℝ) φ, 1 - n * Real.sin θ ^ 2 ≠ 0 := by
    intro θ _
    have hs := Real.sin_sq_le_one θ
    nlinarith [hs, hn, hnc, hc]
  have hne_n' : ∀ θ ∈ Set.uIcc (0 : ℝ) β, 1 - n' * Real.sin θ ^ 2 ≠ 0 := by
    intro θ _
    have hs := Real.sin_sq_le_one θ
    nlinarith [hs, hn'pos, hn'lt, hc]
  have haux := ellipticPiInc_eq_aux_of_ne hc hne_n
  have haux' := ellipticPiInc_eq_aux_of_ne hc hne_n'
  have hinter := ellipticPiAux_interchange hc β φ
  rw [hcn] at hinter
  have hA' : ellipticPiAux c n' β
      = (ellipticPiInc c n' β - ellipticF c β) / n' := by
    rw [haux']
    field_simp [hn'pos.ne']
    ring
  rw [hA'] at hinter
  have hA : ellipticPiAux c n φ
      = (hypQ c φ * ((ellipticPiInc c n' β - ellipticF c β) / n')
          + (ellipticF c φ * ellipticE c β - ellipticE c φ * ellipticF c β))
        / hypQ c β :=
    exchange_solve hQβ hn'pos.ne' hinter
  rw [haux, hA]
  unfold hypExchangeRHS
  rw [hβdef, hn'def]
  field_simp [hQβ]
  ring

/-- The exchange branch of `0 < n < c`, where `n < c sin²φ`. -/
theorem ellipticPiInc_Pconstructible_hyp_exchange {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hlt : n < c * Real.sin φ ^ 2) :
    PConstructible (ellipticPiInc c n φ) := by
  rw [ellipticPiInc_eq_exchange hc0 hc hn hnc h0 hπ hlt]
  unfold hypExchangeRHS
  set β := hypBeta c n with hβdef
  set n' := c * Real.sin φ ^ 2 with hn'def
  have hβP : PConstructible β := by
    rw [hβdef]
    unfold hypBeta
    exact arcsin_Pconstructible (sqrt_Pconstructible (by pconstructible))
  have hβ0 : 0 ≤ β := hβdef ▸ hypBeta_nonneg
  have hβπ : β < Real.pi / 2 := hβdef ▸ hypBeta_lt_pi_div_two hc0 hn.le hnc
  have hβsin : Real.sin β ^ 2 = n / c := hβdef ▸ hypBeta_sin_sq hc0 hn.le hnc
  have hn'P : PConstructible n' := by
    rw [hn'def]
    pconstructible
  have hn'pos : 0 < n' := by
    rw [hn'def]
    nlinarith [hlt, hn, hc0]
  have hn'lt : n' < c := by
    rw [hn'def]
    have hcos : 0 < Real.cos φ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩
    have hs : Real.sin φ ^ 2 < 1 := by
      nlinarith [Real.sin_sq_add_cos_sq φ, sq_pos_of_ne_zero hcos.ne']
    nlinarith
  have hpole' : c / n' * Real.sin β ^ 2 < 1 := by
    rw [hβsin]
    have : c / n' * (n / c) = n / n' := by
      field_simp [hc0.ne', hn'pos.ne']
    rw [this]
    exact (div_lt_one hn'pos).mpr hlt
  have hPiP : PConstructible (ellipticPiInc c n' β) :=
    ellipticPiInc_Pconstructible_hyp_direct hcP hn'P hβP hc0 hc hn'pos hn'lt hβ0 hβπ hpole'
  have hFφP : PConstructible (ellipticF c φ) := ellipticF_Pconstructible hcP hφP hc
  have hFβP : PConstructible (ellipticF c β) := ellipticF_Pconstructible hcP hβP hc
  have hEφP : PConstructible (ellipticE c φ) := ellipticE_Pconstructible hcP hφP hc
  have hEβP : PConstructible (ellipticE c β) := ellipticE_Pconstructible hcP hβP hc
  unfold hypQ
  pconstructible

/-! ### The DLMF 19.7.10 branch

DLMF 19.7.10 is the parameter transformation

  `(1-n)Π(n,φ) + (1-ω²)Π(ω²,φ) = F(φ) + (1-n-ω²)√(csc²φ-c) R_C(...)`,

with `ω² = c(1-n)/(c-n)`.  On the branch where the Carlson integral is the `artanh`
case its contribution collapses to an elementary `artanh`, and solving for `Π(n,φ)`
gives the identity below.  It covers, in particular, the diagonal `n = c sin²φ`
when `n(2-n) ≤ c`. -/

/-- `r = √(n(1-n)/(c-n))`. -/
noncomputable def hypDr (c n : ℝ) : ℝ :=
  Real.sqrt (n * (1 - n) / (c - n))

/-- The coefficient `q = n(1-c)/(c-n)`. -/
noncomputable def hypDq (c n : ℝ) : ℝ :=
  n * (1 - c) / (c - n)

/-- The transformed parameter `ω² = c(1-n)/(c-n) > 1`. -/
noncomputable def hypDom (c n : ℝ) : ℝ :=
  c * (1 - n) / (c - n)

/-- The `artanh` argument `r tanφ Δ(φ)`. -/
noncomputable def hypDB (c n φ : ℝ) : ℝ :=
  hypDr c n * (Real.tan φ * ellipticEIntegrand c φ)

/-- The right-hand side of the simplified 19.7.10 identity. -/
noncomputable def hypDiagRHS (c n φ : ℝ) : ℝ :=
  (ellipticF c φ - hypDr c n * Real.artanh (hypDB c n φ)
    + hypDq c n * ellipticPiInc c (hypDom c n) φ) / (1 - n)

theorem hypDr_sq {c n : ℝ} (hc : c < 1) (hn : 0 < n) (hnc : n < c) :
    hypDr c n ^ 2 = n * (1 - n) / (c - n) := by
  rw [hypDr]
  refine Real.sq_sqrt ?_
  have hn1 : 0 < 1 - n := by linarith
  have hcn : 0 < c - n := by linarith
  positivity

theorem hypDB_sq_sub {c n φ : ℝ} (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (hcos : Real.cos φ ≠ 0) :
    1 - hypDB c n φ ^ 2
      = (1 - n * Real.sin φ ^ 2) * (1 - hypDom c n * Real.sin φ ^ 2)
        / Real.cos φ ^ 2 := by
  have hs := Real.sin_sq_add_cos_sq φ
  have hr := hypDr_sq hc hn hnc
  have hE2 := ellipticEIntegrand_sq hc φ
  have hcn : c - n ≠ 0 := by linarith
  unfold hypDB hypDom
  rw [Real.tan_eq_sin_div_cos]
  have hB2 : (hypDr c n
      * (Real.sin φ / Real.cos φ * ellipticEIntegrand c φ)) ^ 2
      = (n * (1 - n) / (c - n))
        * ((Real.sin φ / Real.cos φ) ^ 2 * (1 - c * Real.sin φ ^ 2)) := by
    rw [mul_pow, hr, mul_pow, hE2]
  rw [hB2]
  field_simp [hcos, hcn]
  ring_nf
  nlinarith [hs]

/-- On the diagonal `n = c sin²φ`, the `artanh` argument is `n(1-n)/(c-n)`. -/
theorem hypDB_sq_diag {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (hcos : Real.cos φ ≠ 0)
    (hdiag : n = c * Real.sin φ ^ 2) :
    hypDB c n φ ^ 2 = (n * (1 - n) / (c - n)) ^ 2 := by
  have hs := Real.sin_sq_add_cos_sq φ
  have hr := hypDr_sq hc hn hnc
  have hE2 := ellipticEIntegrand_sq hc φ
  have hcn : c - n ≠ 0 := by linarith
  unfold hypDB
  rw [Real.tan_eq_sin_div_cos]
  rw [mul_pow, hr, mul_pow, hE2]
  rw [hdiag]
  have hden : c - c * Real.sin φ ^ 2 ≠ 0 := by
    have hw2 : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcos
    nlinarith [hs, hw2, hc0]
  have h1ms : 1 - Real.sin φ ^ 2 ≠ 0 := by
    have hw2 : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcos
    nlinarith [hs, hw2]
  field_simp [hcos, hden, h1ms, hc0.ne']
  have hcos2 : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by linarith [hs]
  rw [hcos2]

theorem hypDB_deriv_alg {s w E c r : ℝ} (hs : s ^ 2 + w ^ 2 = 1)
    (hE : E ^ 2 = 1 - c * s ^ 2) (hw : w ≠ 0) (hEne : E ≠ 0) :
    r * ((1 / w ^ 2) * E + (s / w) * (-(2 * c * s * w) / (2 * E)))
      = r * ((E ^ 2 - c * s ^ 2 * w ^ 2) / (w ^ 2 * E)) := by
  field_simp [hw, hEne]
  ring_nf

/-- Derivative of `hypDB`, in the form needed for the algebra below. -/
theorem hasDerivAt_hypDB {c n φ : ℝ} (hc : c < 1)
    (hcos : Real.cos φ ≠ 0) :
    HasDerivAt (hypDB c n)
      (hypDr c n * ((ellipticEIntegrand c φ ^ 2
        - c * Real.sin φ ^ 2 * Real.cos φ ^ 2)
        / (Real.cos φ ^ 2 * ellipticEIntegrand c φ))) φ := by
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have hsin := Real.sin_sq_add_cos_sq φ
  have hΔ' : HasDerivAt (ellipticEIntegrand c)
      (-(2 * c * Real.sin φ * Real.cos φ) / (2 * ellipticEIntegrand c φ)) φ :=
    hasDerivAt_ellipticEIntegrand c φ (one_sub_mul_sin_sq_pos hc φ).ne'
  have htan : HasDerivAt Real.tan (1 / Real.cos φ ^ 2) φ := Real.hasDerivAt_tan hcos
  have h := ((htan.mul hΔ').const_mul (hypDr c n))
  refine h.congr_deriv ?_
  change hypDr c n * ((1 / Real.cos φ ^ 2) * ellipticEIntegrand c φ
      + Real.tan φ * (-(2 * c * Real.sin φ * Real.cos φ)
        / (2 * ellipticEIntegrand c φ)))
    = hypDr c n * ((ellipticEIntegrand c φ ^ 2
        - c * Real.sin φ ^ 2 * Real.cos φ ^ 2)
        / (Real.cos φ ^ 2 * ellipticEIntegrand c φ))
  rw [Real.tan_eq_sin_div_cos]
  exact hypDB_deriv_alg hsin hE2 hcos hE.ne'

/-- The numerator identity behind the derivative of the 19.7.10 right-hand side. -/
theorem hypDiag_num_alg {c n r q om s w : ℝ}
    (hs : s ^ 2 + w ^ 2 = 1)
    (hr : r ^ 2 * (c - n) = n * (1 - n))
    (hq : q * (c - n) = n * (1 - c))
    (hom : om * (c - n) = c * (1 - n))
    (hcn : c - n ≠ 0) :
    (1 - n * s ^ 2) * (1 - om * s ^ 2) + q * (1 - n * s ^ 2)
        - r ^ 2 * ((1 - c * s ^ 2) - c * s ^ 2 * w ^ 2)
      = (1 - n) * (1 - om * s ^ 2) := by
  have hr' : r ^ 2 = n * (1 - n) / (c - n) := by
    field_simp [hcn] at hr ⊢
    linarith [hr]
  have hq' : q = n * (1 - c) / (c - n) := by
    field_simp [hcn] at hq ⊢
    linarith [hq]
  have hom' : om = c * (1 - n) / (c - n) := by
    field_simp [hcn] at hom ⊢
    linarith [hom]
  rw [hr', hq', hom']
  field_simp [hcn]
  ring_nf
  linear_combination (n * s ^ 2 * c * (1 - n)) * hs

theorem hypDB_zero (c n : ℝ) : hypDB c n 0 = 0 := by
  simp [hypDB, Real.tan_zero]

theorem hypDiagRHS_zero (c n : ℝ) : hypDiagRHS c n 0 = 0 := by
  unfold hypDiagRHS
  rw [hypDB_zero]
  simp [ellipticF, ellipticPiInc]

/-- Derivative of the simplified 19.7.10 right-hand side. -/
theorem hasDerivAt_hypDiagRHS {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hB : hypDB c n φ ^ 2 < 1) :
    HasDerivAt (hypDiagRHS c n) (ellipticPiIntegrand c n φ) φ := by
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], hπ⟩).ne'
  have hcnpos : 0 < c - n := by linarith
  have hcn : c - n ≠ 0 := hcnpos.ne'
  have h1n : (1 : ℝ) - n ≠ 0 := by linarith
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have h1nφ : 0 < 1 - n * Real.sin φ ^ 2 := by
    nlinarith [Real.sin_sq_le_one φ, hn, hc]
  have hBsub := hypDB_sq_sub hc hn hnc hcos
  have hω_gt : 1 < hypDom c n := by
    unfold hypDom
    rw [lt_div_iff₀ hcnpos]
    nlinarith [hc]
  have hω_pos : 0 < 1 - hypDom c n * Real.sin φ ^ 2 := by
    have hdivpos : 0 < (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
      rw [← hBsub]
      nlinarith [hB]
    have hw2 : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcos
    by_contra h
    have hle0 : 1 - hypDom c n * Real.sin φ ^ 2 ≤ 0 := le_of_not_gt h
    have hle : (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1nφ.le hle0
    have : (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hle hw2.le
    linarith
  have hω_ne : 1 - hypDom c n * Real.sin φ ^ 2 ≠ 0 := hω_pos.ne'
  have hB1 : -1 < hypDB c n φ := by
    nlinarith [hB, sq_nonneg (hypDB c n φ - 1), sq_nonneg (hypDB c n φ + 1)]
  have hB2 : hypDB c n φ < 1 := by
    nlinarith [hB, sq_nonneg (hypDB c n φ - 1), sq_nonneg (hypDB c n φ + 1)]
  have hcont : ContinuousOn (ellipticPiIntegrand c (hypDom c n))
      (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul
        (continuous_ellipticEIntegrand c).continuousOn
    · intro t ht
      rw [Set.uIcc_of_le h0] at ht
      have hsinle : Real.sin t ^ 2 ≤ Real.sin φ ^ 2 := by
        have hle : Real.sin t ≤ Real.sin φ :=
          Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [ht.1, Real.pi_pos]) (by linarith [hπ]) ht.2
        have ht0 : 0 ≤ Real.sin t :=
          Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, hπ, Real.pi_pos])
        nlinarith
      have hωt : 0 < 1 - hypDom c n * Real.sin t ^ 2 := by
        have hle : hypDom c n * Real.sin t ^ 2 ≤
            hypDom c n * Real.sin φ ^ 2 :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hω_gt])
        linarith [hω_pos, hle]
      exact mul_ne_zero hωt.ne' (ellipticEIntegrand_pos hc t).ne'
  have hint : IntervalIntegrable (ellipticPiIntegrand c (hypDom c n))
      MeasureTheory.volume 0 φ := hcont.intervalIntegrable
  have hF := hasDerivAt_ellipticF hc φ
  have hBd := hasDerivAt_hypDB (c := c) (n := n) (φ := φ) hc hcos
  have hArt := (hasDerivAt_artanh hB1 hB2).comp φ hBd
  have hPi := hasDerivAt_ellipticPiInc_of_ne hc hint hω_ne
  have htotal := ((hF.sub (hArt.const_mul (hypDr c n))).add
    (hPi.const_mul (hypDq c n))).div_const (1 - n)
  refine htotal.congr_deriv ?_
  simp only [ellipticFIntegrand, ellipticPiIntegrand]
  rw [hypDB_sq_sub hc hn hnc hcos]
  rw [div_eq_iff h1n]
  have hsin := Real.sin_sq_add_cos_sq φ
  have hr : hypDr c n ^ 2 * (c - n) = n * (1 - n) := by
    rw [hypDr_sq hc hn hnc]
    field_simp [hcn]
  have hq : hypDq c n * (c - n) = n * (1 - c) := by
    unfold hypDq
    field_simp [hcn]
  have hom : hypDom c n * (c - n) = c * (1 - n) := by
    unfold hypDom
    field_simp [hcn]
  have hnum := hypDiag_num_alg hsin hr hq hom hcn
  have hω_ne' : 1 - Real.sin φ ^ 2 * hypDom c n ≠ 0 := by
    rw [mul_comm]
    exact hω_ne
  field_simp [hE.ne', hcos, hcn, (sub_ne_zero.mpr hn.ne'), hω_ne, hω_ne',
    (by linarith : (1 : ℝ) - n * Real.sin φ ^ 2 ≠ 0)]
  ring_nf
  field_simp [hω_ne']
  ring_nf
  rw [hE2]
  ring_nf
  nlinarith [hnum, hsin, hr, hq, hom]

/-- The simplified DLMF 19.7.10 identity on the `artanh` branch. -/
theorem ellipticPiInc_eq_diag {c n φ : ℝ} (hc0 : 0 < c) (hc : c < 1)
    (hn : 0 < n) (hnc : n < c) (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hB : hypDB c n φ ^ 2 < 1) :
    ellipticPiInc c n φ = hypDiagRHS c n φ := by
  have hcosφ : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], hπ⟩).ne'
  have hcnpos : 0 < c - n := by linarith
  have hω_gt : 1 < hypDom c n := by
    unfold hypDom
    rw [lt_div_iff₀ hcnpos]
    nlinarith [hc]
  have h1nφ : 0 < 1 - n * Real.sin φ ^ 2 := by
    nlinarith [Real.sin_sq_le_one φ, hn, hc]
  have hBsubφ := hypDB_sq_sub hc hn hnc hcosφ
  have hωposφ : 0 < 1 - hypDom c n * Real.sin φ ^ 2 := by
    have hdivpos : 0 < (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
      rw [← hBsubφ]
      nlinarith [hB]
    have hw2 : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcosφ
    by_contra h
    have hle0 : 1 - hypDom c n * Real.sin φ ^ 2 ≤ 0 := le_of_not_gt h
    have hle : (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos h1nφ.le hle0
    have : (1 - n * Real.sin φ ^ 2)
        * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hle hw2.le
    linarith
  have hcont : ContinuousOn (ellipticPiIntegrand c n) (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Continuous.continuousOn (by fun_prop)).mul
        (continuous_ellipticEIntegrand c).continuousOn
    · intro t _
      exact mul_ne_zero
        (by
          have hs := Real.sin_sq_le_one t
          nlinarith [hs, hn, hnc, hc])
        (ellipticEIntegrand_pos hc t).ne'
  have hint : IntervalIntegrable (ellipticPiIntegrand c n) MeasureTheory.volume 0 φ :=
    hcont.intervalIntegrable
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => by
      rw [Set.uIcc_of_le h0] at ht
      have hcost : Real.cos t ≠ 0 :=
        (Real.cos_pos_of_mem_Ioo
          ⟨by linarith [Real.pi_pos, ht.1], lt_of_le_of_lt ht.2 hπ⟩).ne'
      have hsinle : Real.sin t ^ 2 ≤ Real.sin φ ^ 2 := by
        have hle : Real.sin t ≤ Real.sin φ :=
          Real.sin_le_sin_of_le_of_le_pi_div_two
            (by linarith [ht.1, Real.pi_pos]) (by linarith [hπ]) ht.2
        have ht0 : 0 ≤ Real.sin t :=
          Real.sin_nonneg_of_nonneg_of_le_pi ht.1 (by linarith [ht.2, hπ, Real.pi_pos])
        nlinarith
      have h1nt : 0 < 1 - n * Real.sin t ^ 2 := by
        nlinarith [Real.sin_sq_le_one t, hn, hc]
      have hωt : 0 < 1 - hypDom c n * Real.sin t ^ 2 := by
        have hle : hypDom c n * Real.sin t ^ 2 ≤
            hypDom c n * Real.sin φ ^ 2 :=
          mul_le_mul_of_nonneg_left hsinle (by linarith [hω_gt])
        linarith [hωposφ, hle]
      have hBt : hypDB c n t ^ 2 < 1 := by
        have hpos : 0 < 1 - hypDB c n t ^ 2 := by
          rw [hypDB_sq_sub hc hn hnc hcost]
          exact div_pos (mul_pos h1nt hωt) (sq_pos_of_ne_zero hcost)
        linarith
      exact hasDerivAt_hypDiagRHS hc0 hc hn hnc ht.1
        (lt_of_le_of_lt ht.2 hπ) hBt)
    hint
  rw [ellipticPiInc, hkey, hypDiagRHS_zero, sub_zero]

/-- The DLMF 19.7.10 branch, on its `artanh` range. -/
theorem ellipticPiInc_Pconstructible_hyp_diag {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hB : hypDB c n φ ^ 2 < 1) :
    PConstructible (ellipticPiInc c n φ) := by
  rcases eq_or_lt_of_le h0 with rfl | hφpos
  · simpa [ellipticPiInc] using zero_Pconstructible
  · rw [ellipticPiInc_eq_diag hc0 hc hn hnc h0 hπ hB]
    unfold hypDiagRHS
    have hrP : PConstructible (hypDr c n) := by
      unfold hypDr
      pconstructible
    have hqP : PConstructible (hypDq c n) := by
      unfold hypDq
      pconstructible
    have homP : PConstructible (hypDom c n) := by
      unfold hypDom
      pconstructible
    have hBP : PConstructible (hypDB c n φ) := by
      unfold hypDB
      pconstructible
    have hB1 : -1 < hypDB c n φ := by
      nlinarith [hB, sq_nonneg (hypDB c n φ - 1), sq_nonneg (hypDB c n φ + 1)]
    have hB2 : hypDB c n φ < 1 := by
      nlinarith [hB, sq_nonneg (hypDB c n φ - 1), sq_nonneg (hypDB c n φ + 1)]
    have hArtP : PConstructible (Real.artanh (hypDB c n φ)) :=
      artanh_Pconstructible hBP hB1 hB2
    have hcos : Real.cos φ ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], hπ⟩).ne'
    have hcnpos : 0 < c - n := by linarith
    have hω_gt : 1 < hypDom c n := by
      unfold hypDom
      rw [lt_div_iff₀ hcnpos]
      nlinarith [hc]
    have h1nφ : 0 < 1 - n * Real.sin φ ^ 2 := by
      nlinarith [Real.sin_sq_le_one φ, hn, hc]
    have hBsub := hypDB_sq_sub hc hn hnc hcos
    have hω_pos : 0 < 1 - hypDom c n * Real.sin φ ^ 2 := by
      have hdivpos : 0 < (1 - n * Real.sin φ ^ 2)
          * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 := by
        rw [← hBsub]
        nlinarith [hB]
      have hw2 : 0 < Real.cos φ ^ 2 := sq_pos_of_ne_zero hcos
      by_contra h
      have hle0 : 1 - hypDom c n * Real.sin φ ^ 2 ≤ 0 := le_of_not_gt h
      have hle : (1 - n * Real.sin φ ^ 2)
          * (1 - hypDom c n * Real.sin φ ^ 2) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h1nφ.le hle0
      have : (1 - n * Real.sin φ ^ 2)
          * (1 - hypDom c n * Real.sin φ ^ 2) / Real.cos φ ^ 2 ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg hle hw2.le
      linarith
    have hωs : hypDom c n * Real.sin φ ^ 2 < 1 := by linarith
    have hPiP : PConstructible (ellipticPiInc c (hypDom c n) φ) :=
      ellipticPiInc_Pconstructible_gt_one' hcP homP hφP hc0 hc hω_gt hφpos hπ hωs
    have hFφP : PConstructible (ellipticF c φ) := ellipticF_Pconstructible hcP hφP hc
    pconstructible

/-- The diagonal `n = c sin²φ` above the pseudo-elliptic fixed point, reduced by\nDLMF 19.7.9 to the `artanh` branch. -/
theorem ellipticPiInc_Pconstructible_hyp_diag_gt {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hdiag : n = c * Real.sin φ ^ 2) (hgt : c < n * (2 - n)) :
    PConstructible (ellipticPiInc c n φ) := by
  have hφpos : 0 < φ := by
    rcases eq_or_lt_of_le h0 with rfl | h
    · simp at hdiag
      nlinarith [hdiag, hn]
    · exact h
  have hcos : Real.cos φ ≠ 0 :=
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], hπ⟩).ne'
  rw [ellipticPiInc_eq_circUpper_of_lt hc0 hc hnc h0 hπ.le]
  unfold circUpperRHS
  set n1 := circUpperNu c n with hn1def
  set p1 := circUpperPhi c φ with hp1def
  have hn1pos : 0 < n1 := by
    rw [hn1def]
    unfold circUpperNu
    exact div_pos (by linarith) (by linarith)
  have hn1lt : n1 < c := by
    rw [hn1def]
    unfold circUpperNu
    rw [div_lt_iff₀ (by linarith : (0 : ℝ) < 1 - n)]
    nlinarith [hc]
  have hn1P : PConstructible n1 := by
    rw [hn1def]
    unfold circUpperNu
    pconstructible
  have hp1P : PConstructible p1 := by
    rw [hp1def]
    unfold circUpperPhi
    pconstructible
  have hp1pos : 0 < p1 := by
    rw [hp1def]
    unfold circUpperPhi
    rw [Real.arcsin_pos]
    exact div_pos (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hπ⟩)
      (ellipticEIntegrand_pos hc φ)
  have hp1lt : p1 < Real.pi / 2 := by
    rw [hp1def]
    unfold circUpperPhi
    rw [Real.arcsin_lt_pi_div_two]
    exact (circUpperArg_bounds hc hφpos hπ).2
  have hsinp1 : Real.sin p1 = Real.cos φ / ellipticEIntegrand c φ := by
    rw [hp1def]
    exact circUpperPhi_sin hc hφpos hπ
  have hE := ellipticEIntegrand_pos hc φ
  have hE2 := ellipticEIntegrand_sq hc φ
  have hsinp1sq : Real.sin p1 ^ 2 = n1 / c := by
    rw [hsinp1, hn1def]
    unfold circUpperNu
    rw [div_pow, hE2]
    have hcos2 : Real.cos φ ^ 2 = 1 - Real.sin φ ^ 2 := by
      linarith [Real.sin_sq_add_cos_sq φ]
    rw [hcos2, hdiag]
    field_simp [hcos, hE.ne', hc0.ne']
  have hdiag1 : n1 = c * Real.sin p1 ^ 2 := by
    rw [hsinp1sq]
    field_simp [hc0.ne']
  have hgt1 : n1 * (2 - n1) < c := by
    have h1n : (1 : ℝ) - n ≠ 0 := by linarith
    have hfactor : c - n1 * (2 - n1)
        = (1 - c) * (n * (2 - n) - c) / (1 - n) ^ 2 := by
      rw [hn1def]
      unfold circUpperNu
      field_simp [h1n]
      ring
    have hpos : 0 < c - n1 * (2 - n1) := by
      rw [hfactor]
      have hnum : 0 < n * (2 - n) - c := by linarith
      exact div_pos (mul_pos (by linarith) hnum)
        (sq_pos_of_ne_zero h1n)
    linarith
  have hB1 : hypDB c n1 p1 ^ 2 < 1 := by
    have hcosp1 : Real.cos p1 ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo
        ⟨by linarith [Real.pi_pos, hp1pos], hp1lt⟩).ne'
    have hdiagB := hypDB_sq_diag hc0 hc hn1pos hn1lt hcosp1 hdiag1
    have hApos : 0 < n1 * (1 - n1) / (c - n1) := by
      have h1 : 0 < 1 - n1 := by linarith [hn1lt, hc]
      positivity
    have hAlt : n1 * (1 - n1) / (c - n1) < 1 := by
      rw [div_lt_one (by linarith [hn1lt])]
      nlinarith [hgt1]
    rw [hdiagB]
    nlinarith [hApos, hAlt]
  have hPiP : PConstructible (ellipticPiInc c n1 p1) :=
    ellipticPiInc_Pconstructible_hyp_diag hcP hn1P hp1P hc0 hc hn1pos hn1lt
      hp1pos.le hp1lt hB1
  have hPiComplete : PConstructible (ellipticPi c n1) :=
    ellipticPi_Pconstructible hcP hn1P hc0 hc (lt_trans hn1lt hc)
  have hFφP : PConstructible (ellipticF c φ) := ellipticF_Pconstructible hcP hφP hc
  pconstructible

/-- The whole diagonal `n = c sin²φ`, including the pseudo-elliptic fixed point. -/
theorem ellipticPiInc_Pconstructible_hyp_diag_all {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2)
    (hdiag : n = c * Real.sin φ ^ 2) :
    PConstructible (ellipticPiInc c n φ) := by
  rcases lt_trichotomy (n * (2 - n)) c with hlt | heq | hgt
  · have hcos : Real.cos φ ≠ 0 :=
      (Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, h0], hπ⟩).ne'
    have hB : hypDB c n φ ^ 2 < 1 := by
      have hdiagB := hypDB_sq_diag hc0 hc hn hnc hcos hdiag
      have h1n : 0 < 1 - n := by linarith
      have hApos : 0 < n * (1 - n) / (c - n) := by positivity
      have hAlt : n * (1 - n) / (c - n) < 1 := by
        rw [div_lt_one (by linarith)]
        nlinarith
      rw [hdiagB]
      nlinarith [hApos, hAlt]
    exact ellipticPiInc_Pconstructible_hyp_diag hcP hnP hφP hc0 hc hn hnc h0 hπ hB
  · have hsquare : (1 - n) ^ 2 = 1 - c := by nlinarith [heq]
    have hsqrt : Real.sqrt (1 - c) = 1 - n := by
      rw [← hsquare]
      exact Real.sqrt_sq (by linarith)
    have hn_eq : n = 1 - Real.sqrt (1 - c) := by linarith
    rw [hn_eq]
    exact ellipticPiInc_pseudo_minus_Pconstructible hcP hφP hc0 hc
  · exact ellipticPiInc_Pconstructible_hyp_diag_gt hcP hnP hφP hc0 hc hn hnc h0 hπ hdiag hgt

/-- The hyperbolic range `0 < n < c` for `0 ≤ φ < π/2`. -/
theorem ellipticPiInc_Pconstructible_hyp_lower {c n φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hφP : PConstructible φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c)
    (h0 : 0 ≤ φ) (hπ : φ < Real.pi / 2) :
    PConstructible (ellipticPiInc c n φ) := by
  rcases eq_or_ne (n) (c * Real.sin φ ^ 2) with hdiag | hne
  · exact ellipticPiInc_Pconstructible_hyp_diag_all hcP hnP hφP hc0 hc hn hnc h0 hπ hdiag
  · rcases lt_trichotomy ((c / n) * Real.sin φ ^ 2) 1 with hlt | heq | hgt
    · exact ellipticPiInc_Pconstructible_hyp_direct hcP hnP hφP hc0 hc hn hnc h0 hπ hlt
    · exfalso
      apply hne
      have hsin : Real.sin φ ^ 2 = n / c := by
        field_simp [hc0.ne', hn.ne'] at heq ⊢
        linarith [heq]
      rw [hsin]
      field_simp [hc0.ne']
    · have hlt2 : n < c * Real.sin φ ^ 2 := by
        have := mul_lt_mul_of_pos_left hgt hn
        field_simp [hn.ne'] at this
        linarith
      exact ellipticPiInc_Pconstructible_hyp_exchange hcP hnP hφP hc0 hc hn hnc h0 hπ hlt2

/-- The hyperbolic range `0 < n < c`, for every real upper limit. -/
theorem ellipticPiInc_Pconstructible_hyp_lower_all {c n Φ : ℝ}
    (hcP : PConstructible c) (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hc0 : 0 < c) (hc : c < 1) (hn : 0 < n) (hnc : n < c) :
    PConstructible (ellipticPiInc c n Φ) := by
  obtain ⟨m, h0, hpi⟩ := exists_int_half_turns Φ
  set θ := Φ - m * Real.pi with hθdef
  have hθP : PConstructible θ := by
    rw [hθdef]
    exact PConstructible.sub hΦP (PConstructible.mul (int_Pconstructible m) pi_Pconstructible)
  have hkey := ellipticPiInc_add_int_mul_pi hc (by linarith : n < 1) θ m
  have hΦ_eq : θ + m * Real.pi = Φ := by rw [hθdef]; ring
  rw [hΦ_eq] at hkey
  have hK : PConstructible (ellipticPi c n) :=
    ellipticPi_Pconstructible hcP hnP hc0 hc (by linarith)
  have hterm : PConstructible (m * (2 * ellipticPi c n)) :=
    PConstructible.mul (int_Pconstructible m)
      (PConstructible.mul two_Pconstructible hK)
  rw [hkey]
  rcases le_or_gt θ (Real.pi / 2) with hle | hgt
  · rcases lt_or_eq_of_le hle with hlt | heq
    · exact PConstructible.add
        (ellipticPiInc_Pconstructible_hyp_lower hcP hnP hθP hc0 hc hn hnc h0 hlt) hterm
    · have hPiEq : ellipticPiInc c n θ = ellipticPi c n := by
        rw [heq]
        exact (ellipticPi_eq_inc c n).symm
      rw [hPiEq]
      exact PConstructible.add hK hterm
  · have h1 : Real.pi / 2 ≤ θ := hgt.le
    have hsym := ellipticPiInc_eq_two_complete_sub hc (by linarith : n < 1) h1 hpi
    rw [hsym]
    have hθ'P : PConstructible (Real.pi - θ) :=
      PConstructible.sub pi_Pconstructible hθP
    have hpart : PConstructible (ellipticPiInc c n (Real.pi - θ)) :=
      ellipticPiInc_Pconstructible_hyp_lower hcP hnP hθ'P hc0 hc hn hnc
        (by linarith) (by linarith)
    exact PConstructible.add
      (PConstructible.sub (PConstructible.mul two_Pconstructible hK) hpart) hterm

end Pconstructible
