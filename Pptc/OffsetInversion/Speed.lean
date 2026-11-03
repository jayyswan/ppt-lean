/- Copyright (c) 2024 Lean Community. All rights reserved.

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
import Pptc.BoxOffset

/-! # Pptc.OffsetInversion.Speed — the velocity and speed of a parallel copy

Stream L1 of `PLAN-offset-inversion.md`. The `offset` constructor pushes a traced arc a
fixed signed distance `d` along its unit normal `n = (-y', x')/s`, where `s = speed γ`.
This file computes what that does to the velocity, to the speed, and to the arc length.

## The geometry

Write `x t = (γ t).1`, `y t = (γ t).2`, `s = √(x'² + y'²)`, and let

    κ = (x'·y'' - y'·x'') / s³

be the signed curvature (counterclockwise positive). Differentiating the offset tracing
`P_d = γ + d·n` and using `s' = (x'x'' + y'y'')/s` gives the key identity

    P_d'(t) = (1 - d·κ(t)) · γ'(t)    (componentwise),

and hence, taking Euclidean norms,

    speed (offsetParam γ d) t = |1 - d·κ(t)| · speed γ t.

The absolute value is genuinely needed: past the radius of curvature `1 - d·κ` is
negative and the offset runs backwards, which is exactly how an offset cusp appears.

## The arc-length identity

If `1 - d·κ > 0` on a window `[a,b]` — i.e. the window is cusp free — then
`|1 - dκ| = 1 - dκ` there, and integrating gives

    arcLengthOf (offsetParam γ d) a b = arcLengthOf γ a b - d·(ψ b - ψ a),

where `ψ` is any tangent angle, i.e. any function with `ψ' = κ·s`. On the parabola
`ψ = arctan (y'/x')` works; `ψ` is the Whewell angle. In the classical presentation the
offset length is the base length minus `d` times the total turning, and this file makes
that literal.

## What this needs beyond the `offset` constructor

`offset` only asks for continuous velocity (`hC1`), because it needs the normal to exist.
Here we differentiate the normal, so the base must be twice differentiable pointwise (the
`hx' hy'` pair of hypotheses); this is the `C²` requirement recorded in
`notes/offset-inversion/R0-foundations.md` §7.4.
-/

namespace Pconstructible

/-- The signed curvature `κ = (x'y'' − y'x'') / speed³`, counterclockwise positive. For
the counterclockwise unit circle it is `1`, for the clockwise one `-1`. At a singular
parameter (`speed γ t = 0`) the division gives the junk value `0`. -/
noncomputable def curvature (γ : ℝ → ℝ × ℝ) (t : ℝ) : ℝ :=
  (deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).2)) t
    - deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).1)) t) / speed γ t ^ 3

/-! ### Differentiating the speed

`speed γ = √(x'² + y'²)` is the composite of `√` with a sum of squares, so its derivative
is `(x'x'' + y'y'')/s` — the classical formula. This is the only place the `C²`
hypothesis is used. -/

-- Theorem: the derivative of the speed of `γ` is `(x'x'' + y'y'')/speed γ`.
theorem hasDerivAt_speed {γ : ℝ → ℝ × ℝ} {t : ℝ}
    (hx' : DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t)
    (hy' : DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hreg : speed γ t ≠ 0) :
    HasDerivAt (speed γ)
      ((deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
        + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
        / speed γ t) t := by
  have h1 : HasDerivAt (fun s => deriv (fun s => (γ s).1) s ^ 2)
      (2 * deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t) t := by
    simpa [Pi.pow_def] using (hx'.hasDerivAt).pow 2
  have h2 : HasDerivAt (fun s => deriv (fun s => (γ s).2) s ^ 2)
      (2 * deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t) t := by
    simpa [Pi.pow_def] using (hy'.hasDerivAt).pow 2
  have hg : HasDerivAt
      (fun s => deriv (fun s => (γ s).1) s ^ 2 + deriv (fun s => (γ s).2) s ^ 2)
      (2 * deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
        + 2 * deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t) t :=
    h1.add h2
  have hne : deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2 ≠ 0 := by
    intro h
    exact hreg (by rw [speed, h, Real.sqrt_zero])
  have hs := hg.sqrt hne
  have hv : (2 * deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
        + 2 * deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
        / (2 * Real.sqrt (deriv (fun s => (γ s).1) t ^ 2
          + deriv (fun s => (γ s).2) t ^ 2))
      = (deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
        + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
        / Real.sqrt (deriv (fun s => (γ s).1) t ^ 2
          + deriv (fun s => (γ s).2) t ^ 2) := by
    field_simp
  have hspeed_eq : speed γ = fun y => Real.sqrt (deriv (fun s => (γ s).1) y ^ 2
      + deriv (fun s => (γ s).2) y ^ 2) := rfl
  rw [hspeed_eq]
  simpa [Pi.pow_def, hv] using hs

-- Theorem: the algebraic core of the velocity identity. Writing `A = x'`, `B = y'`,
-- `C = x''`, `E = y''`, `s = speed γ` and `s² = A² + B²`, the two components of the offset
-- velocity are `(1 - d κ)` times the two components of the base velocity.
theorem offset_coord_deriv_algebra {A B C E s d : ℝ} (hs : s ^ 2 = A ^ 2 + B ^ 2)
    (hsne : s ≠ 0) :
    A + d * (-((E * s - B * ((A * C + B * E) / s)) / s ^ 2))
        = (1 - d * ((A * E - B * C) / s ^ 3)) * A ∧
      B + d * ((C * s - A * ((A * C + B * E) / s)) / s ^ 2)
        = (1 - d * ((A * E - B * C) / s ^ 3)) * B := by
  constructor
  · field_simp
    linear_combination (-(d * E)) * hs
  · field_simp
    linear_combination (d * C) * hs

-- Theorem: the offset velocity is `(1 - d κ)` times the base velocity, componentwise.
theorem deriv_offsetParam {γ : ℝ → ℝ × ℝ} {d t : ℝ}
    (hx : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hy : DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hx' : DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t)
    (hy' : DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hreg : speed γ t ≠ 0) :
    deriv (fun s => (offsetParam γ d s).1) t
        = (1 - d * curvature γ t) * deriv (fun s => (γ s).1) t ∧
      deriv (fun s => (offsetParam γ d s).2) t
        = (1 - d * curvature γ t) * deriv (fun s => (γ s).2) t := by
  have hspeed := hasDerivAt_speed (γ := γ) hx' hy' hreg
  have hs2 : speed γ t ^ 2 =
      deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2 := by
    rw [speed, Real.sq_sqrt (by positivity)]
  have hq1 : HasDerivAt
      (fun s => deriv (fun s => (γ s).2) s / speed γ s)
      ((deriv (deriv (fun s => (γ s).2)) t * speed γ t
          - deriv (fun s => (γ s).2) t
            * ((deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
                + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
              / speed γ t)) / speed γ t ^ 2) t :=
    (hy'.hasDerivAt).div hspeed hreg
  have hq2 : HasDerivAt
      (fun s => deriv (fun s => (γ s).1) s / speed γ s)
      ((deriv (deriv (fun s => (γ s).1)) t * speed γ t
          - deriv (fun s => (γ s).1) t
            * ((deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
                + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
              / speed γ t)) / speed γ t ^ 2) t :=
    (hx'.hasDerivAt).div hspeed hreg
  constructor
  · have h1 : HasDerivAt (fun s => (offsetParam γ d s).1)
        (deriv (fun s => (γ s).1) t
          + d * (-((deriv (deriv (fun s => (γ s).2)) t * speed γ t
              - deriv (fun s => (γ s).2) t
                * ((deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
                    + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
                  / speed γ t))
              / speed γ t ^ 2))) t := by
      have h := (hx.hasDerivAt).add (hq1.neg.const_mul d)
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with s
      simp only [offsetParam, unitNormal, Pi.add_apply, Pi.neg_apply]
      ring
    rw [h1.deriv, curvature]
    exact (offset_coord_deriv_algebra hs2 hreg).1
  · have h2 : HasDerivAt (fun s => (offsetParam γ d s).2)
        (deriv (fun s => (γ s).2) t
          + d * ((deriv (deriv (fun s => (γ s).1)) t * speed γ t
              - deriv (fun s => (γ s).1) t
                * ((deriv (fun s => (γ s).1) t * deriv (deriv (fun s => (γ s).1)) t
                    + deriv (fun s => (γ s).2) t * deriv (deriv (fun s => (γ s).2)) t)
                  / speed γ t))
              / speed γ t ^ 2)) t := by
      have h := (hy.hasDerivAt).add (hq2.const_mul d)
      refine h.congr_of_eventuallyEq ?_
      filter_upwards with s
      simp only [offsetParam, unitNormal, Pi.add_apply]
    rw [h2.deriv, curvature]
    exact (offset_coord_deriv_algebra hs2 hreg).2

-- Theorem: the speed of the offset is `|1 - d κ|` times the speed of the base curve.
theorem speed_offsetParam {γ : ℝ → ℝ × ℝ} {d t : ℝ}
    (hx : DifferentiableAt ℝ (fun s => (γ s).1) t)
    (hy : DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hx' : DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t)
    (hy' : DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hreg : speed γ t ≠ 0) :
    speed (offsetParam γ d) t = |1 - d * curvature γ t| * speed γ t := by
  obtain ⟨h1, h2⟩ := deriv_offsetParam hx hy hx' hy' hreg
  rw [speed, h1, h2]
  rw [show ((1 - d * curvature γ t) * deriv (fun s => (γ s).1) t) ^ 2
        + ((1 - d * curvature γ t) * deriv (fun s => (γ s).2) t) ^ 2
      = (1 - d * curvature γ t) ^ 2
        * (deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2) by ring]
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]
  rfl

/-! ### The arc length of a cusp-free offset window

On a window where `1 - d κ > 0` the factor in front of the velocity never changes sign, so
the absolute value in `speed_offsetParam` may be dropped. Integrating the resulting
identity and applying the fundamental theorem of calculus to the tangent angle `ψ` (whose
derivative is `κ · speed γ`) gives the classical formula for the length of a parallel
curve: the base length minus `d` times the total turning `ψ b - ψ a`. -/

-- Theorem: on a cusp-free window `0 < 1 - d κ` the offset arc length is the base length
-- minus `d` times the total turning `ψ b - ψ a`.
theorem arcLengthOf_offsetParam {γ : ℝ → ℝ × ℝ} {ψ : ℝ → ℝ} {a b d : ℝ}
    (hab : a ≤ b)
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧
      DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC2 : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (deriv (fun s => (γ s).1)) t ∧
      DifferentiableAt ℝ (deriv (fun s => (γ s).2)) t)
    (hpos : ∀ t ∈ Set.Icc a b, 0 < 1 - d * curvature γ t)
    (hψ : ∀ t ∈ Set.Icc a b, HasDerivAt ψ (curvature γ t * speed γ t) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hintψ : IntervalIntegrable (fun t => curvature γ t * speed γ t)
      MeasureTheory.volume a b) :
    arcLengthOf (offsetParam γ d) a b = arcLengthOf γ a b - d * (ψ b - ψ a) := by
  -- The offset speed is `|1 - dκ| · s`, and `|1 - dκ| = 1 - dκ` on a cusp-free window.
  have hcongr : arcLengthOf (offsetParam γ d) a b
      = ∫ t in a..b, (1 - d * curvature γ t) * speed γ t := by
    rw [arcLengthOf]
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    rw [speed_offsetParam (hdiff t ht).1 (hdiff t ht).2 (hC2 t ht).1 (hC2 t ht).2
      (hreg t ht), abs_of_pos (hpos t ht)]
  -- Distribute the integrand and integrate termwise.
  have hdist : (∫ t in a..b, (1 - d * curvature γ t) * speed γ t)
      = ∫ t in a..b, (speed γ t - d * (curvature γ t * speed γ t)) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    ring
  rw [hcongr, hdist, intervalIntegral.integral_sub hint (hintψ.const_mul d),
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := ψ) ?_ hintψ, arcLengthOf]
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  exact hψ t ht

end Pconstructible
