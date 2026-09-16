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
-- `Pptc.Offset` pulls in `Pptc.Basic`, hence `Pptc.Box`, which is where the four box edges
-- and the compactness toolkit live.
import Pptc.Offset

/-! # Pptc.BoxOffset — the box applied to an offset arc

`Pptc.Box` gives the box on any compact `PConstructibleCurve`, and `isCompact_traced_arc`
turns the `hdiff` bundle of `arc_of_length` / `offset` into the compactness that the box
wants. What was missing is the very first step for the `offset` constructor: the offset
tracing `offsetParam γ d` need not be continuous on `Icc u v` merely because its *velocity*
is, so the `hdiff` bundle of `offset` alone does not give `IsCompact` of the offset arc.

## What the offset needs beyond `hdiff`

`offsetParam γ d = γ + d • unitNormal γ` and `unitNormal` divides the velocity by
`speed γ = √(x'² + y'²)`. Its continuity therefore needs three things, exactly the three
regularity hypotheses the `offset` constructor carries:

* `hdiff` — the two coordinates of `γ` differentiable on the window, hence `γ` continuous;
* `hreg` — `speed γ` nonzero there, so the divisions in `unitNormal` are honest;
* `hC1` — the two velocity components continuous, so `speed` is, and hence `unitNormal`.

`continuousOn_offsetParam` assembles those into `ContinuousOn (offsetParam γ d) (Set.Icc u v)`.
The four `offsetArc_box_*_Pconstructible` wrappers then feed it and a `PConstructibleCurve`
of the offset arc to the corresponding edge of `Box`, so an offset arc boxes exactly like
any other traced arc.

## Why this matters: the offset cusp

Pushed further than the radius of curvature an offset folds over and grows cusps. The
abscissa of such a cusp is a critical value of the offset tracing, and it is the *global*
maximum of the abscissa on the drawn stroke, so `box_xmax` reads it off with no root
isolation and no high-degree algebra at all. `offsetCuspAbscissa` below is the instance
for the cubic pair `(0,0),(0,2),(2,0),(3,0)` at distance `1`, over the regular window
`[1/2, 1]`; it is P-constructible by `offsetArc_box_xmax_Pconstructible`.

Numerically this number agrees with the degree-`12` cusp abscissa of the notes
(`Pptc/NOTES-offset-cusps-lean.md`, B7/B12), but identifying the two formally — proving the
sup is the specific root of the cusp equation — is the large obligation those notes
describe and is **not** done here. What is done is the reachability half: the box reaches
this number, with no root isolation anywhere.
-/

namespace Pconstructible

/-! ### Continuity of the offset tracing -/

-- Theorem: the offset tracing is continuous on a window on which the base tracing is
-- differentiable, regular, and has continuous velocity components — the `hdiff`, `hreg`
-- and `hC1` bundle of the `offset` constructor.
theorem continuousOn_offsetParam {γ : ℝ → ℝ × ℝ} {d u v : ℝ}
    (hdiff : ∀ t ∈ Set.Icc u v,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hreg : ∀ t ∈ Set.Icc u v, speed γ t ≠ 0)
    (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc u v) ∧
      ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc u v)) :
    ContinuousOn (offsetParam γ d) (Set.Icc u v) := by
  -- `hdiff` makes each coordinate of `γ` continuous on the window, hence `γ` itself.
  have hx : ContinuousOn (fun t => (γ t).1) (Set.Icc u v) :=
    fun t ht => (hdiff t ht).1.continuousAt.continuousWithinAt
  have hy : ContinuousOn (fun t => (γ t).2) (Set.Icc u v) :=
    fun t ht => (hdiff t ht).2.continuousAt.continuousWithinAt
  have hγ : ContinuousOn γ (Set.Icc u v) := hx.prodMk hy
  -- `speed γ = √(x'² + y'²)` inherits continuity from the velocity components.
  have hspeed : ContinuousOn (speed γ) (Set.Icc u v) :=
    ((hC1.1.pow 2).add (hC1.2.pow 2)).sqrt
  -- Both divisions in `unitNormal` are by the continuous nonvanishing `speed γ`.
  have hunit : ContinuousOn (unitNormal γ) (Set.Icc u v) :=
    (hC1.2.neg.div hspeed hreg).prodMk (hC1.1.div hspeed hreg)
  exact (hγ.fst.add (continuousOn_const.mul hunit.fst)).prodMk
    (hγ.snd.add (continuousOn_const.mul hunit.snd))

/-! ### The four edges of an offset arc -/

-- Theorem: the right edge of an offset arc that is a constructible curve with a continuous
-- tracing is P-constructible. This is `box_xmax` with both side goals met by the tracing.
@[pconstructible_cond]
theorem offsetArc_box_xmax_Pconstructible {γ : ℝ → ℝ × ℝ} {d u v : ℝ}
    (hP : PConstructibleCurve (offsetParam γ d '' Set.Icc u v)) (huv : u ≤ v)
    (hcont : ContinuousOn (offsetParam γ d) (Set.Icc u v)) :
    PConstructible (sSup (Prod.fst '' (offsetParam γ d '' Set.Icc u v))) :=
  PConstructible.box_xmax hP (isCompact_Icc.image_of_continuousOn hcont)
    (nonempty_traced_arc huv)

-- Theorem: the left edge of such an offset arc is P-constructible, by reflecting in the
-- `y` axis and reading the right edge.
@[pconstructible_cond]
theorem offsetArc_box_xmin_Pconstructible {γ : ℝ → ℝ × ℝ} {d u v : ℝ}
    (hP : PConstructibleCurve (offsetParam γ d '' Set.Icc u v)) (huv : u ≤ v)
    (hcont : ContinuousOn (offsetParam γ d) (Set.Icc u v)) :
    PConstructible (sInf (Prod.fst '' (offsetParam γ d '' Set.Icc u v))) :=
  box_xmin_Pconstructible hP (isCompact_Icc.image_of_continuousOn hcont)
    (nonempty_traced_arc huv)

-- Theorem: the top edge of such an offset arc is P-constructible.
@[pconstructible_cond]
theorem offsetArc_box_ymax_Pconstructible {γ : ℝ → ℝ × ℝ} {d u v : ℝ}
    (hP : PConstructibleCurve (offsetParam γ d '' Set.Icc u v)) (huv : u ≤ v)
    (hcont : ContinuousOn (offsetParam γ d) (Set.Icc u v)) :
    PConstructible (sSup (Prod.snd '' (offsetParam γ d '' Set.Icc u v))) :=
  PConstructible.box_ymax hP (isCompact_Icc.image_of_continuousOn hcont)
    (nonempty_traced_arc huv)

-- Theorem: the bottom edge of such an offset arc is P-constructible, by reflecting in the
-- `x` axis and reading the top edge.
@[pconstructible_cond]
theorem offsetArc_box_ymin_Pconstructible {γ : ℝ → ℝ × ℝ} {d u v : ℝ}
    (hP : PConstructibleCurve (offsetParam γ d '' Set.Icc u v)) (huv : u ≤ v)
    (hcont : ContinuousOn (offsetParam γ d) (Set.Icc u v)) :
    PConstructible (sInf (Prod.snd '' (offsetParam γ d '' Set.Icc u v))) :=
  box_ymin_Pconstructible hP (isCompact_Icc.image_of_continuousOn hcont)
    (nonempty_traced_arc huv)

/-! ### The right edge, straight from the `offset` constructor's hypotheses

The four wrappers above take the offset arc's constructibility and continuity as given. The
convenience form below instead takes the `offset` constructor's own hypothesis list, builds
the `PConstructibleCurve` with `PConstructibleCurve.offset` and the continuity with
`continuousOn_offsetParam`, and hands both to `offsetArc_box_xmax_Pconstructible` — so a
caller holding a regular traced arc can read the right edge of its parallel copy in one
step. -/

-- Theorem: the right edge of the offset of a regular traced arc, from the constructor's
-- hypotheses alone.
theorem offsetArc_box_xmax_of_offsetHyp {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b d : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ S) (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc a b) ∧
      ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc a b))
    (hd : PConstructible d) :
    PConstructible (sSup (Prod.fst '' (offsetParam γ d '' Set.Icc a b))) :=
  offsetArc_box_xmax_Pconstructible (PConstructibleCurve.offset hS γ hab hsub hinj hdiff hreg
    hC1 hd) hab (continuousOn_offsetParam hdiff hreg hC1)

/-! ### The offset cusp abscissa of a concrete cubic pair -/

/-- The abscissa of the cusp of the offset at distance `1` of the cubic pair
`(0,0), (0,2), (2,0), (3,0)`, taken as the right edge of the offset arc over the regular
window `[1/2, 1]`. In the coefficient convention of `cubicVal` the pair is
`x t = 6t² - 3t³`, `y t = 6t - 12t² + 6t³`, whose velocity vanishes only at `t = 0`; so
`[1/2, 1]` is regular and the abscissa is strictly increasing there.

The value is produced by the box, with no root isolation: it is the supremum of the offset
arc's abscissae, attained at the cusp. Numerically it agrees with the degree-`12` cusp
abscissa of `Pptc/NOTES-offset-cusps-lean.md` (B7/B12), but that identification — proving
this `sSup` is the specific root of the cusp equation — is the large obligation the notes
describe and is deliberately not attempted here. This definition records the reachability
half only: the box reaches the number. -/
noncomputable def offsetCuspAbscissa : ℝ :=
  sSup (Prod.fst '' (offsetParam (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6) 1
    '' Set.Icc (1 / 2 : ℝ) 1))

-- Theorem: the offset cusp abscissa is P-constructible. The cubic pair is regular and its
-- abscissa strictly increasing on `[1/2, 1]` (its velocity is `3t(4 - 3t)` there, positive),
-- so the offset arc is a constructible curve by `offsetCubicPairArc_PConstructibleCurve` and
-- has a continuous tracing by `continuousOn_offsetParam`; the right edge `box_xmax` reports
-- is exactly this number. No root isolation and no degree-`12` algebra are involved.
theorem offsetCuspAbscissa_Pconstructible : PConstructible offsetCuspAbscissa := by
  -- The base velocity is `3t(4 - 3t)`, nonzero on `[1/2, 1]`.
  have hder : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1, cubicDer 0 6 (-3) t ≠ 0 := by
    intro t ht
    have ht1 : 0 < t := by linarith [ht.1]
    have ht2 : 0 < 4 - 3 * t := by linarith [ht.2]
    have heq : cubicDer 0 6 (-3) t = 3 * t * (4 - 3 * t) := by
      simp only [cubicDer]
      ring
    rw [heq]
    positivity
  have hreg : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      speed (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6) t ≠ 0 :=
    fun t ht => speed_cubicPairParam_ne_zero (Or.inl (hder t ht))
  -- The velocity components are the quadratics `cubicDer`, hence continuous.
  have hcontd : ∀ a b c : ℝ, Continuous (cubicDer a b c) := by
    intro a b c
    unfold cubicDer
    fun_prop
  have hdx : deriv (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).1)
      = cubicDer 0 6 (-3) :=
    funext (deriv_cubicPairParam_fst 0 0 6 (-3) 0 6 (-12) 6)
  have hdy : deriv (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).2)
      = cubicDer 6 (-12) 6 :=
    funext (deriv_cubicPairParam_snd 0 0 6 (-3) 0 6 (-12) 6)
  have hC1 : ContinuousOn (deriv (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).1))
        (Set.Icc (1 / 2 : ℝ) 1) ∧
      ContinuousOn (deriv (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).2))
        (Set.Icc (1 / 2 : ℝ) 1) :=
    ⟨by rw [hdx]; exact (hcontd 0 6 (-3)).continuousOn,
      by rw [hdy]; exact (hcontd 6 (-12) 6).continuousOn⟩
  have hdiff : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      DifferentiableAt ℝ (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).1) t ∧
        DifferentiableAt ℝ (fun s => (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6 s).2) t :=
    fun t _ => ⟨(hasDerivAt_cubicVal 0 0 6 (-3) t).differentiableAt,
      (hasDerivAt_cubicVal 0 6 (-12) 6 t).differentiableAt⟩
  -- The abscissa `6t² - 3t³` is strictly increasing on `[1/2, 1]`, so the pair is injective.
  have hmono : StrictMonoOn (fun t => cubicVal 0 0 6 (-3) t) (Set.Icc (1 / 2 : ℝ) 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _) (fun t _ => ?_) (fun t ht => ?_)
    · exact (hasDerivAt_cubicVal 0 0 6 (-3) t).continuousAt.continuousWithinAt
    · rw [(hasDerivAt_cubicVal 0 0 6 (-3) t).deriv]
      have ht' := interior_subset ht
      have h1 : 0 < t := by linarith [ht'.1]
      have h2 : 0 < 4 - 3 * t := by linarith [ht'.2]
      have heq : cubicDer 0 6 (-3) t = 3 * t * (4 - 3 * t) := by
        simp only [cubicDer]
        ring
      rw [heq]
      positivity
  have hinj : Set.InjOn (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6) (Set.Icc (1 / 2 : ℝ) 1) :=
    fun a ha b hb hab => hmono.injOn ha hb (congrArg Prod.fst hab)
  have hP : PConstructibleCurve
      (offsetParam (cubicPairParam 0 0 6 (-3) 0 6 (-12) 6) 1 '' Set.Icc (1 / 2 : ℝ) 1) :=
    offsetCubicPairArc_PConstructibleCurve (by pconstructible) (by pconstructible)
      (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
      (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
      (by pconstructible) (by norm_num) hreg hinj
  exact offsetArc_box_xmax_Pconstructible hP (by norm_num)
    (continuousOn_offsetParam hdiff hreg hC1)

end Pconstructible
