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

import Pptc.Basic
import Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Gauss's arithmetic-geometric mean theorem

`ellipticF c (π/2) = π / (2 · agm 1 √(1 - c))`, and consequently the AGM of
P-constructible inputs is P-constructible.

The proof follows Newman's route: the complete first-kind integral

    I(a, b) = ∫₀^{π/2} dθ / √(a² cos²θ + b² sin²θ)

is invariant under one AGM step `(a, b) ↦ (√(ab), (a + b)/2)`, and it is squeezed between
`π/(2q)` and `π/(2p)` for `0 < p ≤ q`. Iterating the invariance along `agmSequences` and
squeezing gives `I(a, b) = π/(2 · agm a b)` with no continuity argument.

## Main results

* `ellipticF_pi_div_two_eq_pi_div_agm`
* `agm_Pconstructible`
* `gaussConstant_Pconstructible`
-/

noncomputable section

open MeasureTheory Set intervalIntegral Real NNReal Filter Topology

namespace Pconstructible

/-! ### The two integral forms -/

/-- `I(a, b) = ∫₀^{π/2} dθ / √(a² cos²θ + b² sin²θ)`. -/
def agmI (a b : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..Real.pi / 2, (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹

/-- `J(a, b) = ∫₀^∞ dt / √((t² + a²)(t² + b²))`. -/
def agmJ (a b : ℝ) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹

/-! ### Algebra for the substitution `φ x = (x - ab/x)/2` -/

private lemma agmJ_alg_g {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    ((x - a * b / x) / 2) ^ 2 + (Real.sqrt (a * b)) ^ 2 = (x ^ 2 + a * b) ^ 2 / (4 * x ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  rw [Real.sq_sqrt (mul_nonneg ha.le hb.le)]
  field_simp
  ring

private lemma agmJ_alg_m {a b x : ℝ} (hx : 0 < x) :
    ((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2 =
      (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) / (4 * x ^ 2) := by
  have hx0 : x ≠ 0 := ne_of_gt hx
  field_simp
  ring

private lemma agmJ_deriv (a b x : ℝ) (hx : x ≠ 0) :
    HasDerivAt (fun y : ℝ => (y - a * b / y) / 2) ((1 + a * b / x ^ 2) / 2) x := by
  have h1 : HasDerivAt (fun y : ℝ => a * b / y) (-(a * b) / x ^ 2) x := by
    simpa [div_eq_mul_inv, neg_div] using (hasDerivAt_inv hx).const_mul (a * b)
  have h2 : HasDerivAt (fun y : ℝ => y - a * b / y) (1 - (-(a * b) / x ^ 2)) x :=
    (hasDerivAt_id x).sub h1
  have h3 : HasDerivAt (fun y : ℝ => (y - a * b / y) / 2) ((1 - (-(a * b) / x ^ 2)) / 2) x :=
    h2.div_const 2
  convert h3 using 1
  ring

private lemma agmJ_key {a b x : ℝ} (ha : 0 < a) (hb : 0 < b) (hx : 0 < x) :
    |(1 + a * b / x ^ 2) / 2| *
        (Real.sqrt ((((x - a * b / x) / 2) ^ 2 + ((a + b) / 2) ^ 2) *
          (((x - a * b / x) / 2) ^ 2 + (Real.sqrt (a * b)) ^ 2)))⁻¹
      = 2 * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
  have hx2 : (0 : ℝ) < x ^ 2 := by nlinarith
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hP : 0 < (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) :=
    mul_pos (by nlinarith [sq_nonneg x]) (by nlinarith [sq_nonneg x])
  have hQ : 0 < x ^ 2 + a * b := by nlinarith [mul_pos ha hb]
  have h4x : (0 : ℝ) < 4 * x ^ 2 := by nlinarith
  rw [agmJ_alg_g ha hb hx, agmJ_alg_m hx]
  have hsq : ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) / (4 * x ^ 2)) *
        ((x ^ 2 + a * b) ^ 2 / (4 * x ^ 2)) =
      (x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2) * ((x ^ 2 + a * b) / (4 * x ^ 2)) ^ 2 := by
    field_simp
  rw [hsq, Real.sqrt_mul hP.le, Real.sqrt_sq_eq_abs,
    abs_of_pos (div_pos hQ h4x)]
  have habs : |(1 + a * b / x ^ 2) / 2| = (x ^ 2 + a * b) / (2 * x ^ 2) := by
    have hsum : 1 + a * b / x ^ 2 = (x ^ 2 + a * b) / x ^ 2 := by
      field_simp
    have hpos : 0 < (x ^ 2 + a * b) / x ^ 2 / 2 := by
      have := div_pos hQ hx2
      linarith
    rw [hsum, abs_of_pos hpos, div_div, mul_comm (x ^ 2) 2]
  rw [habs]
  field_simp
  ring

private lemma agmJ_surj {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (fun x : ℝ => (x - a * b / x) / 2) '' Ioi (0 : ℝ) = univ := by
  ext t
  constructor
  · intro _; trivial
  · intro _
    have h1 : 0 < t ^ 2 + a * b := by nlinarith [sq_nonneg t]
    have hspos : 0 < Real.sqrt (t ^ 2 + a * b) := Real.sqrt_pos.2 h1
    have hs : Real.sqrt (t ^ 2 + a * b) * Real.sqrt (t ^ 2 + a * b) = t ^ 2 + a * b :=
      Real.mul_self_sqrt h1.le
    have hxpos : 0 < t + Real.sqrt (t ^ 2 + a * b) := by
      by_contra hcon
      push Not at hcon
      nlinarith [hs, hspos, hcon, sq_nonneg (t + Real.sqrt (t ^ 2 + a * b))]
    refine ⟨t + Real.sqrt (t ^ 2 + a * b), hxpos, ?_⟩
    have hx : t + Real.sqrt (t ^ 2 + a * b) ≠ 0 := ne_of_gt hxpos
    change (t + Real.sqrt (t ^ 2 + a * b) - a * b / (t + Real.sqrt (t ^ 2 + a * b))) / 2 = t
    field_simp
    nlinarith [hs]

/-! ### Step 1: the bridge to `ellipticF` -/

/-- The complete first-kind integral is `I(1, √(1 - c))`. -/
theorem ellipticF_pi_div_two_eq_agmI {c : ℝ} (hc : c < 1) :
    ellipticF c (Real.pi / 2) = agmI 1 (Real.sqrt (1 - c)) := by
  have hsq : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  unfold ellipticF agmI
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp only [ellipticFIntegrand, ellipticEIntegrand, one_pow, one_mul, hsq]
  congr 2
  linarith [Real.sin_sq_add_cos_sq θ]

/-! ### Step 5: the two-sided bound on `I` -/

/-- The radicand of the `I` integrand is squeezed between `p²` and `q²`. -/
theorem agmI_radicand_bounds {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (θ : ℝ) :
    p ^ 2 ≤ p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2 ∧
      p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2 ≤ q ^ 2 := by
  have hs := Real.sin_sq_add_cos_sq θ
  have hp2q2 : p ^ 2 ≤ q ^ 2 := by nlinarith
  constructor <;> nlinarith [sq_nonneg (Real.sin θ), sq_nonneg (Real.cos θ),
    sq_nonneg (Real.sin θ - Real.cos θ)]

/-- The `I` integrand lies between `1/q` and `1/p`. -/
theorem agmI_integrand_bounds {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) (θ : ℝ) :
    q⁻¹ ≤ (Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2))⁻¹ ∧
      (Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2))⁻¹ ≤ p⁻¹ := by
  have hq : 0 < q := lt_of_lt_of_le hp hpq
  obtain ⟨h1, h2⟩ := agmI_radicand_bounds hp hpq θ
  have hR : 0 < p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2 := by
    nlinarith [sq_nonneg p, sq_pos_of_pos hp]
  have hsq : 0 < Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2) :=
    Real.sqrt_pos.mpr hR
  have hple : p ≤ Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2) := by
    have h := Real.sqrt_le_sqrt h1
    rwa [Real.sqrt_sq hp.le] at h
  have hqle : Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2) ≤ q := by
    have h := Real.sqrt_le_sqrt h2
    rwa [Real.sqrt_sq hq.le] at h
  exact ⟨(inv_le_inv₀ hq hsq).mpr hqle, (inv_le_inv₀ hsq hp).mpr hple⟩

/-- The `I` integrand is continuous. -/
theorem continuous_agmI_integrand {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    Continuous fun θ : ℝ =>
      (Real.sqrt (p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2))⁻¹ := by
  refine (Real.continuous_sqrt.comp (by fun_prop)).inv₀ fun θ => ?_
  have hR : 0 < p ^ 2 * Real.cos θ ^ 2 + q ^ 2 * Real.sin θ ^ 2 :=
    lt_of_lt_of_le (by positivity) (agmI_radicand_bounds hp hpq θ).1
  exact (Real.sqrt_pos.mpr hR).ne'

/-- **Bounds.** For `0 < p ≤ q`, `π/(2q) ≤ I(p,q) ≤ π/(2p)`. -/
theorem agmI_bounds {p q : ℝ} (hp : 0 < p) (hpq : p ≤ q) :
    Real.pi / (2 * q) ≤ agmI p q ∧ agmI p q ≤ Real.pi / (2 * p) := by
  have hle : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  have hint := (continuous_agmI_integrand hp hpq).intervalIntegrable (μ := volume) 0
    (Real.pi / 2)
  have hloint : IntervalIntegrable (fun _ : ℝ => q⁻¹) volume 0 (Real.pi / 2) :=
    intervalIntegrable_const
  have hhiint : IntervalIntegrable (fun _ : ℝ => p⁻¹) volume 0 (Real.pi / 2) :=
    intervalIntegrable_const
  have hlow : Real.pi / (2 * q) ≤ agmI p q := by
    have h := integral_mono_on hle hloint hint
      (fun θ _ => (agmI_integrand_bounds hp hpq θ).1)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    have : Real.pi / 2 * q⁻¹ = Real.pi / (2 * q) := by
      field_simp
    rwa [this] at h
  have hhigh : agmI p q ≤ Real.pi / (2 * p) := by
    have h := integral_mono_on hle hint hhiint
      (fun θ _ => (agmI_integrand_bounds hp hpq θ).2)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at h
    have : Real.pi / 2 * p⁻¹ = Real.pi / (2 * p) := by
      field_simp
    rwa [this] at h
  exact ⟨hlow, hhigh⟩

/-! ### Steps 2 and 3: the substitution identities -/

/-- Step 2: `I = J`, by `t = b tan θ`. -/
theorem agmI_eq_agmJ {a b : ℝ} (ha : 0 < a) (hb : 0 < b) : agmI a b = agmJ a b := by
  -- Rewrite the interval integral over the half-open interval as one over the open interval.
  have hI : agmI a b
      = ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹ := by
    unfold agmI
    rw [intervalIntegral.integral_of_le (by positivity)]
    exact integral_Ioc_eq_integral_Ioo
  -- The substitution `t = b * tan θ` maps `(0, π/2)` onto `(0, ∞)`.
  have himg : (fun θ : ℝ => b * Real.tan θ) '' Ioo (0 : ℝ) (Real.pi / 2) = Ioi (0 : ℝ) := by
    ext t
    constructor
    · rintro ⟨θ, hθ, rfl⟩
      have hpi := Real.pi_pos
      have hc : 0 < Real.cos θ :=
        Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
      have hs : 0 < Real.sin θ :=
        Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, hpi]⟩
      have htan : 0 < Real.tan θ := by
        rw [Real.tan_eq_sin_div_cos]
        positivity
      exact mul_pos hb htan
    · intro ht
      have ht0 : 0 < t := ht
      refine ⟨Real.arctan (t / b), ⟨?_, ?_⟩, ?_⟩
      · exact Real.arctan_pos.mpr (div_pos ht0 hb)
      · exact Real.arctan_lt_pi_div_two (t / b)
      · change b * Real.tan (Real.arctan (t / b)) = t
        rw [Real.tan_arctan]
        exact mul_div_cancel₀ t hb.ne'
  -- Derivative of the substitution.
  have hderiv : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      HasDerivWithinAt (fun θ : ℝ => b * Real.tan θ) (b * (1 / Real.cos θ ^ 2))
        (Ioo (0 : ℝ) (Real.pi / 2)) θ := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
    exact ((Real.hasDerivAt_tan hc.ne').const_mul b).hasDerivWithinAt
  -- Injectivity of the substitution.
  have hinj : InjOn (fun θ : ℝ => b * Real.tan θ) (Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro x hx y hy hxy
    have htan : Real.tan x = Real.tan y := mul_left_cancel₀ hb.ne' hxy
    have hsub : Ioo (0 : ℝ) (Real.pi / 2) ⊆ Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
      intro z hz
      exact ⟨by linarith [hz.1, Real.pi_pos], hz.2⟩
    exact Real.injOn_tan (hsub hx) (hsub hy) htan
  -- Pointwise collapse of the pulled-back integrand.
  have hpt : ∀ θ ∈ Ioo (0 : ℝ) (Real.pi / 2),
      (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
        = |b * (1 / Real.cos θ ^ 2)| •
            (Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
              * ((b * Real.tan θ) ^ 2 + b ^ 2)))⁻¹ := by
    intro θ hθ
    have hpi := Real.pi_pos
    have hc : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, hpi], hθ.2⟩
    have hs : 0 < Real.sin θ :=
      Real.sin_pos_of_mem_Ioo ⟨hθ.1, by linarith [hθ.2, hpi]⟩
    have hcne : Real.cos θ ≠ 0 := hc.ne'
    have h1T : 1 + Real.tan θ ^ 2 = 1 / Real.cos θ ^ 2 := by
      rw [eq_div_iff (pow_ne_zero 2 hcne)]
      exact Real.one_add_tan_sq_mul_cos_sq_eq_one hcne
    have hQ : 0 < a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2 := by positivity
    have hP2 : (b * Real.tan θ) ^ 2 + b ^ 2 = b ^ 2 / Real.cos θ ^ 2 := by
      have h : (b * Real.tan θ) ^ 2 + b ^ 2 = b ^ 2 * (1 + Real.tan θ ^ 2) := by ring
      rw [h, h1T]
      ring
    have hP1 : (b * Real.tan θ) ^ 2 + a ^ 2
        = (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) / Real.cos θ ^ 2 := by
      rw [Real.tan_eq_sin_div_cos]
      field_simp [hcne]
      ring
    have hprod : ((b * Real.tan θ) ^ 2 + a ^ 2) * ((b * Real.tan θ) ^ 2 + b ^ 2)
        = b ^ 2 * (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 4 := by
      rw [hP1, hP2]
      field_simp [hcne]
    have hsqrt : Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
          * ((b * Real.tan θ) ^ 2 + b ^ 2))
        = b * Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2)
            / Real.cos θ ^ 2 := by
      rw [hprod, Real.sqrt_div (by positivity)]
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq hb.le]
      rw [show Real.cos θ ^ 4 = (Real.cos θ ^ 2) ^ 2 by ring,
        Real.sqrt_sq (by positivity)]
    have habs : |b * (1 / Real.cos θ ^ 2)| = b / Real.cos θ ^ 2 := by
      rw [abs_of_pos (by positivity)]
      field_simp
    rw [habs, hsqrt, smul_eq_mul]
    field_simp [hb.ne', hcne, (Real.sqrt_pos.mpr hQ).ne']
  rw [hI]
  calc
    ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
        (Real.sqrt (a ^ 2 * Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2))⁻¹
        = ∫ θ in Ioo (0 : ℝ) (Real.pi / 2),
            |b * (1 / Real.cos θ ^ 2)| •
              (Real.sqrt (((b * Real.tan θ) ^ 2 + a ^ 2)
                * ((b * Real.tan θ) ^ 2 + b ^ 2)))⁻¹ :=
          setIntegral_congr_fun measurableSet_Ioo hpt
    _ = ∫ t in (fun θ : ℝ => b * Real.tan θ) '' Ioo (0 : ℝ) (Real.pi / 2),
          (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
          rw [integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo hderiv hinj]
    _ = ∫ t in Ioi (0 : ℝ), (Real.sqrt ((t ^ 2 + a ^ 2) * (t ^ 2 + b ^ 2)))⁻¹ := by
          rw [himg]
    _ = agmJ a b := rfl

/-- Step 3: Newman's invariance `J(√(ab), (a+b)/2) = J(a, b)`. -/
theorem agmJ_newman {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmJ (Real.sqrt (a * b)) ((a + b) / 2) = agmJ a b := by
  set m : ℝ := (a + b) / 2 with hm
  set g : ℝ := Real.sqrt (a * b) with hg
  set F : ℝ → ℝ := fun t => (Real.sqrt ((t ^ 2 + m ^ 2) * (t ^ 2 + g ^ 2)))⁻¹ with hF
  -- `F` is even
  have hFeven : ∀ t : ℝ, F (-t) = F t := by
    intro t
    simp only [hF]
    ring_nf
  -- replace the integral over `ℝ` by twice the integral over `Ioi 0`
  have hhalf : ∫ t : ℝ, F t = 2 * ∫ t in Ioi (0 : ℝ), F t := by
    rw [← integral_comp_abs (f := F)]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with t
    rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_nonpos ht, hFeven t]
  -- change of variables `t = φ x` on `Ioi 0`, whose image is all of `ℝ`
  have hsub : ∫ t : ℝ, F t = 2 * agmJ a b := by
    have hinj : InjOn (fun x : ℝ => (x - a * b / x) / 2) (Ioi (0 : ℝ)) := by
      intro x hx y hy hxy
      have hx0 : x ≠ 0 := ne_of_gt hx
      have hy0 : y ≠ 0 := ne_of_gt hy
      have key : (x - y) * (1 + a * b / (x * y)) = 0 := by
        field_simp at hxy ⊢
        linarith
      have hpos : 0 < 1 + a * b / (x * y) := by
        have h : 0 < a * b / (x * y) := div_pos (mul_pos ha hb) (mul_pos hx hy)
        linarith
      have hxy' : x - y = 0 := by
        rcases mul_eq_zero.1 key with h | h
        · exact h
        · linarith
      linarith
    have hderiv : ∀ x ∈ Ioi (0 : ℝ),
        HasDerivWithinAt (fun x : ℝ => (x - a * b / x) / 2) ((1 + a * b / x ^ 2) / 2)
          (Ioi (0 : ℝ)) x := by
      intro x hx
      exact (agmJ_deriv a b x (ne_of_gt hx)).hasDerivWithinAt
    have h := integral_image_eq_integral_abs_deriv_smul (f := fun x : ℝ => (x - a * b / x) / 2)
      (f' := fun x : ℝ => (1 + a * b / x ^ 2) / 2) (s := Ioi (0 : ℝ)) measurableSet_Ioi
      hderiv hinj F
    rw [agmJ_surj ha hb, setIntegral_univ] at h
    have hcongr : ∫ x in Ioi (0 : ℝ), |(1 + a * b / x ^ 2) / 2| • F ((x - a * b / x) / 2)
        = ∫ x in Ioi (0 : ℝ), 2 * (Real.sqrt ((x ^ 2 + a ^ 2) * (x ^ 2 + b ^ 2)))⁻¹ := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      simp only [hF]
      rw [smul_eq_mul, hm, hg]
      exact agmJ_key ha hb hx
    rw [hcongr, MeasureTheory.integral_const_mul] at h
    simpa [agmJ] using h
  -- halve
  have h2 : ∫ t in Ioi (0 : ℝ), F t = agmJ a b := by
    linarith
  have h3 : agmJ g m = ∫ t in Ioi (0 : ℝ), F t := by
    simp only [agmJ]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t _ => ?_)
    simp only [hF]
    simp [mul_comm]
  rw [h3]
  exact h2

/-- One AGM step leaves `I` unchanged. -/
theorem agmI_gm_am {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    agmI (Real.sqrt (a * b)) ((a + b) / 2) = agmI a b := by
  have hs : 0 < Real.sqrt (a * b) := Real.sqrt_pos.mpr (mul_pos ha hb)
  have hm : 0 < (a + b) / 2 := by positivity
  rw [agmI_eq_agmJ hs hm, agmJ_newman ha hb, ← agmI_eq_agmJ ha hb]

/-! ### Step 4: invariance along `agmSequences` -/

/-- Every entry of `agmSequences x y` is positive when `x, y > 0`. -/
theorem agmSequences_pos {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    0 < (NNReal.agmSequences x y n).1 ∧ 0 < (NNReal.agmSequences x y n).2 := by
  induction n with
  | zero =>
    rw [NNReal.agmSequences_zero]
    change 0 < NNReal.sqrt (x * y) ∧ 0 < (x + y) / 2
    exact ⟨NNReal.sqrt_pos_of_pos (mul_pos hx hy), by positivity⟩
  | succ n ih =>
    rw [NNReal.agmSequences_succ']
    change 0 < NNReal.sqrt ((x.agmSequences y n).1 * (x.agmSequences y n).2) ∧
      0 < ((x.agmSequences y n).1 + (x.agmSequences y n).2) / 2
    exact ⟨NNReal.sqrt_pos_of_pos (mul_pos ih.1 ih.2),
      div_pos (add_pos ih.1 ih.2) (by norm_num)⟩

/-- `I` is invariant along `agmSequences`. -/
theorem agmI_agmSequences {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) (n : ℕ) :
    agmI (x : ℝ) (y : ℝ) =
      agmI ((NNReal.agmSequences x y n).1 : ℝ) ((NNReal.agmSequences x y n).2 : ℝ) := by
  induction n with
  | zero =>
    rw [NNReal.agmSequences_zero]
    change agmI (x : ℝ) (y : ℝ) =
      agmI ((NNReal.sqrt (x * y) : ℝ≥0) : ℝ) (((x + y) / 2 : ℝ≥0) : ℝ)
    push_cast
    exact (agmI_gm_am (by exact_mod_cast hx) (by exact_mod_cast hy)).symm
  | succ n ih =>
    rw [NNReal.agmSequences_succ', ih]
    change agmI ((x.agmSequences y n).1 : ℝ) ((x.agmSequences y n).2 : ℝ) =
      agmI ((NNReal.sqrt ((x.agmSequences y n).1 * (x.agmSequences y n).2) : ℝ≥0) : ℝ)
        ((((x.agmSequences y n).1 + (x.agmSequences y n).2) / 2 : ℝ≥0) : ℝ)
    have h := agmI_gm_am (by exact_mod_cast (agmSequences_pos hx hy n).1)
      (by exact_mod_cast (agmSequences_pos hx hy n).2)
    push_cast
    exact h.symm

/-! ### Step 7: the squeeze -/

/-- `I(x, y) = π / (2 · agm x y)` for positive `x, y`. -/
theorem agmI_eq_pi_div_two_agm {x y : ℝ≥0} (hx : 0 < x) (hy : 0 < y) :
    agmI (x : ℝ) (y : ℝ) = Real.pi / (2 * (NNReal.agm x y : ℝ)) := by
  have hpos := agmSequences_pos hx hy
  have hle : ∀ n, ((NNReal.agmSequences x y n).1 : ℝ) ≤
      ((NNReal.agmSequences x y n).2 : ℝ) := by
    intro n
    exact_mod_cast NNReal.agmSequences_fst_le_snd n n
  have hfst : Tendsto (fun n : ℕ => ((NNReal.agmSequences x y n).1 : ℝ)) atTop
      (𝓝 (NNReal.agm x y : ℝ)) :=
    (NNReal.continuous_coe.tendsto (NNReal.agm x y)).comp
      (NNReal.tendsto_agmSequences_fst_agm (x := x) (y := y))
  have hsnd : Tendsto (fun n : ℕ => ((NNReal.agmSequences x y n).2 : ℝ)) atTop
      (𝓝 (NNReal.agm x y : ℝ)) :=
    (NNReal.continuous_coe.tendsto (NNReal.agm x y)).comp
      (NNReal.tendsto_agmSequences_snd_agm (x := x) (y := y))
  have hagm : 0 < (NNReal.agm x y : ℝ) := by
    exact_mod_cast NNReal.agm_pos hx hy
  have hlim_fst : Tendsto (fun n : ℕ => Real.pi / (2 * ((NNReal.agmSequences x y n).1 : ℝ)))
      atTop (𝓝 (Real.pi / (2 * (NNReal.agm x y : ℝ)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul hfst) (by positivity)
  have hlim_snd : Tendsto (fun n : ℕ => Real.pi / (2 * ((NNReal.agmSequences x y n).2 : ℝ)))
      atTop (𝓝 (Real.pi / (2 * (NNReal.agm x y : ℝ)))) :=
    tendsto_const_nhds.div (tendsto_const_nhds.mul hsnd) (by positivity)
  refine le_antisymm ?_ ?_
  · refine le_of_tendsto_of_tendsto tendsto_const_nhds hlim_fst ?_
    filter_upwards with n
    rw [agmI_agmSequences hx hy n]
    exact (agmI_bounds (hpos n).1 (hle n)).2
  · refine le_of_tendsto_of_tendsto hlim_snd tendsto_const_nhds ?_
    filter_upwards with n
    rw [agmI_agmSequences hx hy n]
    exact (agmI_bounds (hpos n).1 (hle n)).1

/-! ### Step 6: Gauss's theorem -/

/-- **Gauss's theorem**, in the parameter convention `c = k²`. -/
theorem ellipticF_pi_div_two_eq_pi_div_agm {c : ℝ} (hc : c < 1) :
    ellipticF c (Real.pi / 2) =
      Real.pi / (2 * (NNReal.agm 1 ⟨Real.sqrt (1 - c), Real.sqrt_nonneg _⟩ : ℝ)) := by
  rw [ellipticF_pi_div_two_eq_agmI hc]
  have hpos : (0 : ℝ) < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have h := agmI_eq_pi_div_two_agm (x := 1)
    (y := ⟨Real.sqrt (1 - c), Real.sqrt_nonneg _⟩) (by norm_num) (by exact_mod_cast hpos)
  exact h

/-! ### Step 7: P-constructibility -/

/-- The complete integral `F(π/2)` is positive. -/
theorem ellipticF_pi_div_two_pos {c : ℝ} (hc : c < 1) :
    0 < ellipticF c (Real.pi / 2) := by
  have h := intervalIntegral_pos_of_pos_on
    (intervalIntegrable_ellipticFIntegrand hc 0 (Real.pi / 2))
    (fun x _ => ellipticFIntegrand_pos hc x) (by positivity)
  simpa [ellipticF] using h

/-- `agm 1 r = π / (2 F(1 - r², π/2))` for `r > 0`: Gauss's theorem solved for the AGM. -/
theorem agm_one_eq {r : ℝ≥0} (hr : 0 < r) :
    (NNReal.agm 1 r : ℝ) =
      Real.pi / (2 * ellipticF (1 - (r : ℝ) ^ 2) (Real.pi / 2)) := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hc : 1 - (r : ℝ) ^ 2 < 1 := by nlinarith
  have h := ellipticF_pi_div_two_eq_pi_div_agm hc
  have hsub : (⟨Real.sqrt (1 - (1 - (r : ℝ) ^ 2)), Real.sqrt_nonneg _⟩ : ℝ≥0) = r := by
    apply NNReal.eq
    change Real.sqrt (1 - (1 - (r : ℝ) ^ 2)) = (r : ℝ)
    rw [show 1 - (1 - (r : ℝ) ^ 2) = (r : ℝ) ^ 2 by ring]
    exact Real.sqrt_sq r.2
  rw [hsub] at h
  have hA : (0 : ℝ) < (NNReal.agm 1 r : ℝ) := by
    exact_mod_cast NNReal.agm_pos (by norm_num) hr
  have hE : (0 : ℝ) < ellipticF (1 - (r : ℝ) ^ 2) (Real.pi / 2) :=
    ellipticF_pi_div_two_pos hc
  rw [h]
  field_simp

/-- `agm 1 r` is P-constructible for P-constructible positive `r`. -/
theorem agm_one_Pconstructible {r : ℝ≥0} (hrP : PConstructible (r : ℝ)) (hr : 0 < r) :
    PConstructible (NNReal.agm 1 r : ℝ) := by
  rw [agm_one_eq hr]
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hc : 1 - (r : ℝ) ^ 2 < 1 := by nlinarith
  have hr2 : PConstructible ((r : ℝ) ^ 2) := by
    rw [sq]
    exact PConstructible.mul hrP hrP
  have hcP : PConstructible (1 - (r : ℝ) ^ 2) :=
    PConstructible.sub PConstructible.base_one hr2
  exact PConstructible.div pi_Pconstructible
    (PConstructible.mul two_Pconstructible (ellipticF_pi_div_two_Pconstructible hcP hc))

/-- **The AGM of P-constructible inputs is P-constructible.** -/
@[pconstructible]
theorem agm_Pconstructible {x y : ℝ≥0} (hx : PConstructible (x : ℝ))
    (hy : PConstructible (y : ℝ)) : PConstructible (NNReal.agm x y : ℝ) := by
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ x) with hx0 | hx0
  · rw [← hx0, NNReal.agm_zero_left]
    exact zero_Pconstructible
  rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ y) with hy0 | hy0
  · rw [← hy0, NNReal.agm_zero_right]
    exact zero_Pconstructible
  have hrn : 0 < (y / x : ℝ≥0) := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_zero, NNReal.coe_div]
    positivity
  have hrP : PConstructible ((y / x : ℝ≥0) : ℝ) := by
    rw [NNReal.coe_div]
    exact PConstructible.div hy hx
  have hkey : (NNReal.agm x y : ℝ) = (x : ℝ) * (NNReal.agm 1 (y / x) : ℝ) := by
    have hxy : x * (y / x) = y := by
      apply NNReal.eq
      have hx' : (x : ℝ) ≠ 0 := by exact_mod_cast hx0.ne'
      push_cast
      field_simp
    rw [← NNReal.coe_mul, ← NNReal.agm_mul_distrib, mul_one, hxy]
  rw [hkey]
  exact PConstructible.mul hx (agm_one_Pconstructible hrP hrn)

/-- **Gauss's constant** `G = 1/agm(1, √2) = 0.8346268416740731…` is P-constructible. -/
theorem gaussConstant_Pconstructible :
    PConstructible ((NNReal.agm 1 (NNReal.sqrt 2) : ℝ)⁻¹) := by
  have h1 : PConstructible ((1 : ℝ≥0) : ℝ) := by simpa using PConstructible.base_one
  have h2 : PConstructible ((NNReal.sqrt 2 : ℝ≥0) : ℝ) := by
    push_cast
    exact sqrt_Pconstructible two_Pconstructible
  exact inv_Pconstructible (agm_Pconstructible h1 h2)

end Pconstructible
