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
import Pptc.Jacobi
import Pptc.Box

/-! # Pptc.BoxSine

A consistency check on the box axiom by a second route.

The project reaches the amplitude `ellipticEAm (1/2)` off the **ellipse** in `Pptc.Jacobi`:
`ellipticE_ellipticEAm` inverts `E`, and `ellipticEAm_Pconstructible_of_mem_Icc` boxes the
far end of an `arc_of_length` stroke laid along `ellipseParam`. The sine constructor
(`PConstructibleCurve.sine`) gives a *second* route. The graph of `y = sin x` is traced by
`t ↦ (t, sin t)` at speed

    √(1 + cos²t) = √(2 - sin²t) = √2 · √(1 - (1/2) sin²t),

so its arc length over `[0, X]` is `√2 · E(X, 1/2)`. Laying a P-constructible length `L`
along it and reading the abscissa of the far end off the box therefore returns exactly
`ellipticEAm (1/2) (L / √2)`.

The two routes agreeing is the point: the box API in `Pptc.Box` (in particular
`arc_xendpoint_Pconstructible`) is exactly what would be wrong if they did not. Note this
is a *cross-check on a known value*, not a new reach of the class — it does not extend what
`ellipticEAm_Pconstructible` already proves.
-/

namespace Pconstructible

/-! ### The speed and arc length of the sine graph -/

-- Theorem: the sine graph, traced as `t ↦ (t, sin t)`, has speed
-- `√2 * ellipticEIntegrand (1/2) t`. The identity is `√(1 + cos²t) = √(2 - sin²t)` pulled
-- apart: `2 - sin²t = 2 (1 - (1/2) sin²t)` and `√(2 x) = √2 √x`.
theorem speed_sineArc (t : ℝ) :
    speed (fun s : ℝ => (s, Real.sin s)) t
      = Real.sqrt 2 * ellipticEIntegrand (1 / 2) t := by
  have hx : HasDerivAt (fun s : ℝ => ((fun s : ℝ => (s, Real.sin s)) s).1) 1 t := by
    simpa using hasDerivAt_id' t
  have hy : HasDerivAt (fun s : ℝ => ((fun s : ℝ => (s, Real.sin s)) s).2) (Real.cos t) t := by
    simpa using Real.hasDerivAt_sin t
  rw [speed, hx.deriv, hy.deriv, ellipticEIntegrand]
  have hsq : (1 : ℝ) ^ 2 + Real.cos t ^ 2 = 2 * (1 - (1 / 2) * Real.sin t ^ 2) := by
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hsq, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]

-- Theorem: the arc length of the sine graph over `[0, X]` is `√2 · E(X, 1/2)`.
-- This is `speed_sineArc` integrated, with the constant `√2` pulled out of the integral.
theorem arcLengthOf_sineArc (X : ℝ) :
    arcLengthOf (fun s : ℝ => (s, Real.sin s)) 0 X
      = Real.sqrt 2 * ellipticE (1 / 2) X := by
  rw [arcLengthOf, ellipticE, ← intervalIntegral.integral_const_mul]
  simp only [speed_sineArc]

/-! ### The cross-check: box-inverting the sine arc reproduces `ellipticEAm (1/2)` -/

-- Theorem: laying a P-constructible length `L` along the sine graph from the origin and
-- boxing the endpoint inverts `√2 · E` at `L`, i.e. returns `ellipticEAm (1/2) (L / √2)`.
--
-- This is `ellipticEAm_Pconstructible_of_mem_Icc` with the ellipse replaced by the sine
-- graph. The `arc_of_length` stroke runs from `(0, 0)` to `(X, sin X)`, and on `[0, X] ⊆
-- [0, π/2]` its abscissa — the identity — is increasing, so the box reads the far end off
-- `arc_xendpoint_Pconstructible`.
theorem ellipticEAm_Pconstructible_via_sine {L : ℝ} (hL : PConstructible L)
    (hL0 : 0 ≤ L) (hLub : L ≤ Real.sqrt 2 * ellipticE (1 / 2) (Real.pi / 2)) :
    PConstructible (ellipticEAm (1 / 2) (L / Real.sqrt 2)) := by
  have hc : (1 / 2 : ℝ) < 1 := by norm_num
  have hs2pos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hLdiv0 : 0 ≤ L / Real.sqrt 2 := div_nonneg hL0 hs2pos.le
  have hLdivK : L / Real.sqrt 2 ≤ ellipticE (1 / 2) (Real.pi / 2) := by
    rw [div_le_iff₀ hs2pos]
    linarith [hLub]
  set X := ellipticEAm (1 / 2) (L / Real.sqrt 2) with hXdef
  have hEφ : ellipticE (1 / 2) X = L / Real.sqrt 2 :=
    ellipticE_ellipticEAm hc (L / Real.sqrt 2)
  have hmono := strictMono_ellipticE hc
  have hX0 : 0 ≤ X := by
    refine hmono.le_iff_le.mp ?_
    rw [ellipticE_zero_right, hEφ]
    exact hLdiv0
  have hXpi : X ≤ Real.pi / 2 := by
    refine hmono.le_iff_le.mp ?_
    rw [hEφ]
    exact hLdivK
  -- The stroke's length is `L`, by the arc-length identity and `E(X) = L / √2`.
  have hlen : arcLengthOf (fun s : ℝ => (s, Real.sin s)) 0 X = L := by
    rw [arcLengthOf_sineArc, hEφ]
    field_simp
  have hsub : (fun s : ℝ => (s, Real.sin s)) '' Set.Icc 0 X
      ⊆ {p : ℝ × ℝ | p.2 = Real.sin p.1} := by
    rintro p ⟨s, _, rfl⟩
    simp
  have hinj : Set.InjOn (fun s : ℝ => (s, Real.sin s)) (Set.Icc 0 X) := by
    intro a _ b _ h
    simpa using congrArg Prod.fst h
  have hdiff : ∀ t ∈ Set.Icc 0 X,
      DifferentiableAt ℝ (fun s => ((fun s : ℝ => (s, Real.sin s)) s).1) t ∧
      DifferentiableAt ℝ (fun s => ((fun s : ℝ => (s, Real.sin s)) s).2) t := by
    intro t _
    exact ⟨differentiableAt_id, Real.differentiableAt_sin⟩
  have hint : IntervalIntegrable (speed (fun s : ℝ => (s, Real.sin s)))
      MeasureTheory.volume 0 X := by
    have hcont : Continuous (fun t => Real.sqrt 2 * ellipticEIntegrand (1 / 2) t) :=
      continuous_const.mul (continuous_ellipticEIntegrand (1 / 2))
    rw [show speed (fun s : ℝ => (s, Real.sin s))
        = fun t => Real.sqrt 2 * ellipticEIntegrand (1 / 2) t from funext speed_sineArc]
    exact hcont.intervalIntegrable 0 X
  have hA : PConstructibleCurve ((fun s : ℝ => (s, Real.sin s)) '' Set.Icc 0 X) :=
    PConstructibleCurve.arc_of_length PConstructibleCurve.sine
      (fun s : ℝ => (s, Real.sin s)) hX0 hsub hinj hdiff hint
      (by simpa using zero_Pconstructible) (by simpa using zero_Pconstructible) hL hlen
  have hcontγ : ContinuousOn (fun s : ℝ => (s, Real.sin s)) (Set.Icc 0 X) :=
    continuousOn_id.prodMk Real.continuous_sin.continuousOn
  have hmono' : MonotoneOn (fun t => ((fun s : ℝ => (s, Real.sin s)) t).1) (Set.Icc 0 X) :=
    fun a _ b _ hab => hab
  exact arc_xendpoint_Pconstructible (γ := fun s : ℝ => (s, Real.sin s)) hA hX0 hcontγ hmono'

end Pconstructible
