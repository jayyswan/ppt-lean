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
import Pptc.Basic

/-! # Pptc.Offset — the parallel-copy constructor put to work

`PConstructibleCurve.offset` is the drawing program's parallel copy: every point of a
traced arc is pushed a fixed signed distance `d` along its unit normal. It is the only
constructor that *leaves* the curve it is given — `restrict` shrinks, `arc_of_length`
stays inside, and translate / scale / rotate are affine — and it is the only one that
raises the degree of the implicit equation without bound. Until this file it had no uses.

## What an offset buys

Offsetting a rational curve makes it irrational: the displacement is divided by
`speed γ t = √(x'² + y'²)`, and that square root is not a rational function of `t`. The
gain is in degree. Crossing the offset of a *cubic pair* `γ t = (x t, y t)` with a line
`A·X + B·Y = C` gives, after clearing the square root,

    (A·x + B·y - C)² · (x'² + y'²)  =  d² · (B·x' - A·y')²

which is degree `10` in `t` — against degree `9`, the Bézout ceiling of two cubic Béziers,
which `nonicVal_root_Pconstructible` reaches only on a codimension-1 hypersurface. On a naive
count there are `12` P-constructible parameters (`8` from the two cubics, `3` from the line,
`1` from `d`) against `10` coefficients, which looks like slack. The count is misleading, and
`offsetCrossPoly_normalForm` at the end of this file says exactly how: the twelve enter
through only eight combinations, and the image is codimension `3`, not dense.

## The two things that make the construction work

**Squaring is only ever used to bound a zero set.** The displayed equation above is what
you get by squaring `g·w = -d·h`, and squaring forgets a sign, so its root set is strictly
larger than the set of parameters at which the offset really meets the line. That costs
nothing here. `crossing_Pconstructible` asks for the crossings to be *finite*, and a
subset of a finite set is finite; the spurious roots enlarge the bound and do nothing
else. The offset is used as the *first* curve of the crossing, the one presented by a
parametrization, so its implicit equation is never needed — only this bound on how often
the composite can vanish. See `offsetCrossPoly_eq_zero_of_offsetCrossVal` and
`offsetCubicPair_cross_point_Pconstructible`.

**The parameter comes back off the offset for free.** Reading a crossing gives the point
`(X, Y)` of the offset, not the parameter `β` that produced it, and there is no reason a
degree-10 construction should hand `β` back cheaply. It does, because of what an offset
*is*: the displacement from `γ β` to `(X, Y)` is along the normal, hence orthogonal to the
velocity, so

    (X - x β) · x' β + (Y - y β) · y' β = 0.

With `x`, `y` cubic that is a **quintic** in `β` with P-constructible coefficients — degree
`5`, comfortably inside `root_Pconstructible_le_six_coeffs`. So the recovery step is
cheaper than the construction, which is the opposite of the usual situation — and, since
it is a statement about the *first* curve alone, it does not care what the offset was
crossed with. That is why `offsetCubicPair_cross_root_Pconstructible` leaves the second
curve open: a harder one raises the degree of what is solved without raising the degree of
anything that has to be undone. See `offsetParam_normal_eq_zero`.

## The conjecture this is aimed at

> **`PConstructible` is a real closed field.**

Already in hand: it is a subfield; it is closed under square roots of positives
(`sqrt_Pconstructible`); it contains every real root of every polynomial of degree at most
`6` with P-constructible coefficients (`root_Pconstructible_le_six_coeffs`) and every real
root of the special nonics `M³ + λM² + v²` (`nonicVal_root_Pconstructible`). What is
missing is *degree, uniformly*, and offset is the untapped degree engine. This file builds
the engine and drives it once. It also settles, in the negative, the question of whether
this particular drive reaches all of degree `10`: see the closing section.
-/

namespace Pconstructible

open Polynomial

/-! ### Generic facts about `offsetParam`

Three facts, all independent of which curve is being offset, and all consequences of the
single geometric statement that `unitNormal` is a unit vector orthogonal to the velocity.

Only `offsetParam_normal_eq_zero` is used below, but it is the one that matters: it is the
recovery step of the whole construction, and it holds for *any* `γ`, with no regularity
hypothesis at all — at a singular parameter `unitNormal` is the junk value `(0, 0)` and the
identity degenerates to `0 = 0`. -/

-- Theorem: offsetting by zero distance reproduces the curve.
@[simp]
theorem offsetParam_zero (γ : ℝ → ℝ × ℝ) : offsetParam γ 0 = γ := by
  funext t
  simp [offsetParam]

-- Theorem: the unit normal is orthogonal to the velocity. (At a singular parameter both
-- sides are still zero, the normal being `(0, 0)` there.)
theorem unitNormal_orthogonal (γ : ℝ → ℝ × ℝ) (t : ℝ) :
    (unitNormal γ t).1 * deriv (fun s => (γ s).1) t
      + (unitNormal γ t).2 * deriv (fun s => (γ s).2) t = 0 := by
  simp only [unitNormal]
  ring

-- Theorem: the displacement from a point of the curve to the corresponding point of the
-- offset is orthogonal to the velocity there. This is what lets the parameter `β` be
-- recovered from the offset point `(X, Y)`: it is one polynomial equation in `β` whose
-- coefficients are built from `X`, `Y` and the coefficients of `γ`.
theorem offsetParam_normal_eq_zero (γ : ℝ → ℝ × ℝ) (d t : ℝ) :
    ((offsetParam γ d t).1 - (γ t).1) * deriv (fun s => (γ s).1) t
      + ((offsetParam γ d t).2 - (γ t).2) * deriv (fun s => (γ s).2) t = 0 := by
  simp only [offsetParam, add_sub_cancel_left]
  linear_combination d * unitNormal_orthogonal γ t

-- Theorem: at a regular parameter the offset really does sit at distance `|d|` from the
-- curve — the clearance is the same everywhere, which is what distinguishes a parallel
-- copy from a scaled one.
theorem offsetParam_dist_sq (γ : ℝ → ℝ × ℝ) (d t : ℝ) (hreg : speed γ t ≠ 0) :
    ((offsetParam γ d t).1 - (γ t).1) ^ 2 + ((offsetParam γ d t).2 - (γ t).2) ^ 2 = d ^ 2 := by
  have hsq : speed γ t ^ 2 =
      deriv (fun s => (γ s).1) t ^ 2 + deriv (fun s => (γ s).2) t ^ 2 := by
    rw [speed, Real.sq_sqrt]
    positivity
  simp only [offsetParam, unitNormal, add_sub_cancel_left]
  field_simp
  nlinarith [hsq]


/-! ### Derivative, speed and normal of a cubic pair

`cubicPairParam` is the curve the Bézier draws (`cubicPairArc_PConstructibleCurve`), and
everything the `offset` constructor asks about a tracing is a statement about its velocity.
For a cubic pair that velocity is the pair of quadratics `cubicDer`, so all four side
conditions reduce to elementary facts about polynomials. -/

-- Theorem: the derivative of a cubic is the quadratic `cubicDer`.
theorem hasDerivAt_cubicVal (c₀ c₁ c₂ c₃ t : ℝ) :
    HasDerivAt (cubicVal c₀ c₁ c₂ c₃) (cubicDer c₁ c₂ c₃ t) t := by
  have h3 : HasDerivAt (fun s : ℝ => c₃ * s ^ 3) (3 * c₃ * t ^ 2) t := by
    have h : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by simpa using hasDerivAt_pow 3 t
    have h' := h.const_mul c₃
    rwa [show c₃ * (3 * t ^ 2) = 3 * c₃ * t ^ 2 from by ring] at h'
  have h2 : HasDerivAt (fun s : ℝ => c₂ * s ^ 2) (2 * c₂ * t) t := by
    have h : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
    have h' := h.const_mul c₂
    rwa [show c₂ * (2 * t) = 2 * c₂ * t from by ring] at h'
  have h1 : HasDerivAt (fun s : ℝ => c₁ * s) c₁ t := by
    simpa using (hasDerivAt_id t).const_mul c₁
  exact ((h3.add h2).add h1).add_const c₀

-- Theorem: the derivative of a cubic, as a `deriv`.
@[simp]
theorem deriv_cubicVal (c₀ c₁ c₂ c₃ t : ℝ) :
    deriv (fun s : ℝ => cubicVal c₀ c₁ c₂ c₃ s) t = cubicDer c₁ c₂ c₃ t :=
  (hasDerivAt_cubicVal c₀ c₁ c₂ c₃ t).deriv

-- Theorem: the two coordinates of a cubic pair differentiate to the two `cubicDer`s.
@[simp]
theorem deriv_cubicPairParam_fst (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ t : ℝ) :
    deriv (fun s => (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ s).1) t = cubicDer c₁ c₂ c₃ t :=
  (hasDerivAt_cubicVal c₀ c₁ c₂ c₃ t).deriv

@[simp]
theorem deriv_cubicPairParam_snd (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ t : ℝ) :
    deriv (fun s => (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ s).2) t = cubicDer e₁ e₂ e₃ t :=
  (hasDerivAt_cubicVal e₀ e₁ e₂ e₃ t).deriv

-- Theorem: the speed of a cubic pair is the Euclidean norm of the pair of quadratics.
theorem speed_cubicPairParam (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ t : ℝ) :
    speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t =
      Real.sqrt (cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2) := by
  rw [speed, deriv_cubicPairParam_fst, deriv_cubicPairParam_snd]

-- Theorem: the speed vanishes exactly where both quadratics do — the cusps of the traced
-- curve, which are where `offset` refuses to work and the unit normal has no meaning.
theorem speed_cubicPairParam_ne_zero {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ t : ℝ}
    (h : cubicDer c₁ c₂ c₃ t ≠ 0 ∨ cubicDer e₁ e₂ e₃ t ≠ 0) :
    speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t ≠ 0 := by
  rw [speed_cubicPairParam]
  have hpos : 0 < cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2 := by
    rcases h with h | h <;> positivity
  exact ne_of_gt (Real.sqrt_pos.mpr hpos)

/-! ### A regular window around a parameter

`offset` needs an arc that is traced injectively, at nowhere-vanishing speed, with
continuous velocity. None of that holds of a cubic pair globally: it may have a cusp, and
it may cross itself. All three hold on a short enough window around any *regular*
parameter, and shortening the window is free, since the crossing argument downstream only
ever needs the arc near the one point it is isolating.

The window is produced by the sign of whichever velocity component is nonzero: that
component keeps its sign nearby, so its coordinate is strictly monotone there, which gives
injectivity, and the speed is bounded away from zero for the same reason. -/

-- Theorem: around a point where a differentiable function has nonvanishing derivative
-- there is a rational window on which the derivative does not vanish and the function is
-- injective.
theorem exists_rat_window_injOn {f f' : ℝ → ℝ} {β : ℝ}
    (hderiv : ∀ t, HasDerivAt f (f' t) t) (hcont : Continuous f') (hne : f' β ≠ 0) :
    ∃ u v : ℚ, (u : ℝ) < β ∧ β < (v : ℝ) ∧
      (∀ t ∈ Set.Icc (u : ℝ) (v : ℝ), f' t ≠ 0) ∧
      Set.InjOn f (Set.Icc (u : ℝ) (v : ℝ)) := by
  -- The positive case, from which the negative one follows by negating `f`.
  have key : ∀ g g' : ℝ → ℝ, (∀ t, HasDerivAt g (g' t) t) → Continuous g' → 0 < g' β →
      ∃ u v : ℚ, (u : ℝ) < β ∧ β < (v : ℝ) ∧
        (∀ t ∈ Set.Icc (u : ℝ) (v : ℝ), 0 < g' t) ∧
        Set.InjOn g (Set.Icc (u : ℝ) (v : ℝ)) := by
    intro g g' hg hgc hpos
    obtain ⟨ε, hε, hball⟩ :=
      Metric.isOpen_iff.mp (isOpen_lt continuous_const hgc) β hpos
    obtain ⟨u, hu1, hu2⟩ := exists_rat_btwn (show β - ε < β by linarith)
    obtain ⟨v, hv1, hv2⟩ := exists_rat_btwn (show β < β + ε by linarith)
    have hwin : ∀ t ∈ Set.Icc (u : ℝ) (v : ℝ), 0 < g' t := by
      intro t ht
      refine hball ?_
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨u, v, hu2, hv1, hwin, StrictMonoOn.injOn ?_⟩
    refine strictMonoOn_of_deriv_pos (convex_Icc _ _)
      (fun t _ => (hg t).continuousAt.continuousWithinAt) fun t ht => ?_
    rw [(hg t).deriv]
    exact hwin t (interior_subset ht)
  rcases hne.lt_or_gt with hlt | hgt
  · obtain ⟨u, v, hu, hv, hwin, hinj⟩ :=
      key (fun t => -f t) (fun t => -f' t) (fun t => (hderiv t).neg) hcont.neg (by linarith)
    exact ⟨u, v, hu, hv, fun t ht => by have := hwin t ht; linarith,
      fun a ha b hb hab => hinj ha hb (by simp [hab])⟩
  · obtain ⟨u, v, hu, hv, hwin, hinj⟩ := key f f' hderiv hcont hgt
    exact ⟨u, v, hu, hv, fun t ht => ne_of_gt (hwin t ht), hinj⟩

-- Theorem: a regular parameter of a cubic pair has a rational window on which the whole
-- package of `offset`'s side conditions holds.
theorem exists_rat_window_cubicPair {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ β : ℝ}
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0) :
    ∃ u v : ℚ, (u : ℝ) < β ∧ β < (v : ℝ) ∧
      (∀ t ∈ Set.Icc (u : ℝ) (v : ℝ),
        speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t ≠ 0) ∧
      Set.InjOn (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) (Set.Icc (u : ℝ) (v : ℝ)) := by
  have hcont : ∀ a b c : ℝ, Continuous (cubicDer a b c) := by
    intro a b c
    unfold cubicDer
    fun_prop
  rcases hreg with h | h
  · obtain ⟨u, v, hu, hv, hwin, hinj⟩ :=
      exists_rat_window_injOn (f := cubicVal c₀ c₁ c₂ c₃)
        (hasDerivAt_cubicVal c₀ c₁ c₂ c₃) (hcont c₁ c₂ c₃) h
    exact ⟨u, v, hu, hv, fun t ht => speed_cubicPairParam_ne_zero (Or.inl (hwin t ht)),
      fun a ha b hb hab => hinj ha hb (congrArg Prod.fst hab)⟩
  · obtain ⟨u, v, hu, hv, hwin, hinj⟩ :=
      exists_rat_window_injOn (f := cubicVal e₀ e₁ e₂ e₃)
        (hasDerivAt_cubicVal e₀ e₁ e₂ e₃) (hcont e₁ e₂ e₃) h
    exact ⟨u, v, hu, hv, fun t ht => speed_cubicPairParam_ne_zero (Or.inr (hwin t ht)),
      fun a ha b hb hab => hinj ha hb (congrArg Prod.snd hab)⟩


/-! ### The first use of the `offset` constructor

Everything the constructor asks for is now in hand, so the parallel copy of a regular arc
of a cubic pair is a constructible curve. This is the point at which `offset` stops being
a constructor with a doc comment and no uses. -/

-- Theorem: the parallel copy, at any P-constructible signed distance, of a regular
-- injectively-traced arc of a cubic pair with P-constructible coefficients is a
-- constructible curve.
theorem offsetCubicPairArc_PConstructibleCurve {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d u v : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hu : PConstructible u) (hv : PConstructible v) (huv : u < v)
    (hreg : ∀ t ∈ Set.Icc u v,
      speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t ≠ 0)
    (hinj : Set.InjOn (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) (Set.Icc u v)) :
    PConstructibleCurve
      (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d '' Set.Icc u v) := by
  have harc := cubicPairArc_PConstructibleCurve hc₀ hc₁ hc₂ hc₃ he₀ he₁ he₂ he₃ hu hv huv
  have hdx : deriv (fun s => (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ s).1)
      = cubicDer c₁ c₂ c₃ := funext (deriv_cubicPairParam_fst c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃)
  have hdy : deriv (fun s => (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ s).2)
      = cubicDer e₁ e₂ e₃ := funext (deriv_cubicPairParam_snd c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃)
  have hcont : ∀ a b c : ℝ, Continuous (cubicDer a b c) := by
    intro a b c
    unfold cubicDer
    fun_prop
  exact PConstructibleCurve.offset harc _ huv.le Set.Subset.rfl hinj
    (fun t _ => ⟨(hasDerivAt_cubicVal c₀ c₁ c₂ c₃ t).differentiableAt,
      (hasDerivAt_cubicVal e₀ e₁ e₂ e₃ t).differentiableAt⟩)
    hreg
    ⟨by rw [hdx]; exact (hcont c₁ c₂ c₃).continuousOn,
      by rw [hdy]; exact (hcont e₁ e₂ e₃).continuousOn⟩
    hd

/-! ### The line `A·X + B·Y = C` as a drawn arc

The second curve of the crossing, and nothing new: `segment_PConstructibleCurve` already
draws the segment between any two P-constructible points, vertical ones included, and the
two endpoints needed here are P-constructible expressions in `A`, `B`, `C` and a pair of
rationals. This is a repackaging, not an addition.

What it buys is shape. `crossing_Pconstructible` wants the second curve given by a
*parametrization* whose parameter locates the crossing, and a cubic pair with both
coordinates affine in the parameter is exactly that; `lineParam_surj` then names the
parameter of a given point outright. Running from the foot of the perpendicular from the
origin in the direction `(-B, A)` also avoids a case split on which of `A`, `B` is
nonzero, which a slope form would force. -/

/-- The line `A·X + B·Y = C`, parametrized from the foot of the perpendicular dropped on it
from the origin, running in the direction `(-B, A)`. Degenerate (a single point) when
`A = B = 0`, which every use below excludes. -/
noncomputable def lineParam (A B C : ℝ) : ℝ → ℝ × ℝ :=
  cubicPairParam (A * C / (A ^ 2 + B ^ 2)) (-B) 0 0 (B * C / (A ^ 2 + B ^ 2)) A 0 0

-- Theorem: every point of `lineParam A B C` satisfies the equation it is named for.
theorem lineParam_implicit {A B C : ℝ} (hAB : A ^ 2 + B ^ 2 ≠ 0) (s : ℝ) :
    A * (lineParam A B C s).1 + B * (lineParam A B C s).2 - C = 0 := by
  simp only [lineParam, cubicPairParam, cubicVal]
  field_simp
  ring

-- Theorem: conversely every point of the plane satisfying that equation is traced, at the
-- parameter `(A·Y - B·X) / (A² + B²)`.
theorem lineParam_surj {A B C X Y : ℝ} (hAB : A ^ 2 + B ^ 2 ≠ 0)
    (hXY : A * X + B * Y - C = 0) :
    lineParam A B C ((A * Y - B * X) / (A ^ 2 + B ^ 2)) = (X, Y) := by
  have hC : C = A * X + B * Y := by linarith
  simp only [lineParam, cubicPairParam, cubicVal, hC, Prod.mk.injEq]
  constructor <;> · field_simp; ring

-- Theorem: an arc of that line, over any interval with P-constructible endpoints, is a
-- constructible curve.
theorem lineArc_PConstructibleCurve {A B C u v : ℝ}
    (hA : PConstructible A) (hB : PConstructible B) (hC : PConstructible C)
    (hu : PConstructible u) (hv : PConstructible v) (huv : u < v) :
    PConstructibleCurve (lineParam A B C '' Set.Icc u v) := by
  have hAB : PConstructible (A ^ 2 + B ^ 2) :=
    PConstructible.add (sq_Pconstructible hA) (sq_Pconstructible hB)
  exact cubicPairArc_PConstructibleCurve
    (PConstructible.div (PConstructible.mul hA hC) hAB) (neg_Pconstructible hB)
    zero_Pconstructible zero_Pconstructible
    (PConstructible.div (PConstructible.mul hB hC) hAB) hA
    zero_Pconstructible zero_Pconstructible hu hv huv


/-! ### The crossing equation, and its rationalization

Write `γ t = (x t, y t)` for the cubic pair, `w = √(x'² + y'²)` for its speed, and

    g = A·x + B·y - C,     h = B·x' - A·y'.

The offset point at parameter `t` is `(x - d·y'/w, y + d·x'/w)`, so substituting it into
the line's equation gives `g + d·h/w`, and clearing the denominator gives `offsetCrossVal`,
the honest crossing condition: it is `w` times the value of the line's implicit equation at
the offset point, so at a regular parameter the two vanish together.

`offsetCrossPoly` is what squaring that condition leaves, and it is an honest polynomial in
`t` of degree `10`: `g` is a cubic, `x'² + y'²` a quartic, `h` a quadratic. It is *not*
equivalent to the crossing condition — squaring forgets the sign of `g·w`, so it has
spurious roots — and it is not used as if it were. Its only job is
`offsetCross_finite_roots`, a finite superset of the crossings, which is all
`crossing_Pconstructible` asks for. -/

/-- The crossing condition: the offset of the cubic pair at parameter `t`, displaced by
`d`, lies on the line `A·X + B·Y = C` exactly when this vanishes (at a regular `t`). -/
noncomputable def offsetCrossVal (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t : ℝ) : ℝ :=
  (A * cubicVal c₀ c₁ c₂ c₃ t + B * cubicVal e₀ e₁ e₂ e₃ t - C)
      * Real.sqrt (cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2)
    + d * (B * cubicDer c₁ c₂ c₃ t - A * cubicDer e₁ e₂ e₃ t)

/-- The degree-`10` polynomial left by squaring the crossing condition. -/
def offsetCrossPoly (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t : ℝ) : ℝ :=
  (A * cubicVal c₀ c₁ c₂ c₃ t + B * cubicVal e₀ e₁ e₂ e₃ t - C) ^ 2
      * (cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2)
    - d ^ 2 * (B * cubicDer c₁ c₂ c₃ t - A * cubicDer e₁ e₂ e₃ t) ^ 2

-- Theorem: squaring the crossing condition. The converse fails — that is the sign the
-- square root forgets — and nothing below needs it.
theorem offsetCrossPoly_eq_zero_of_offsetCrossVal {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t : ℝ}
    (h : offsetCrossVal c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t = 0) :
    offsetCrossPoly c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t = 0 := by
  set g : ℝ := A * cubicVal c₀ c₁ c₂ c₃ t + B * cubicVal e₀ e₁ e₂ e₃ t - C with hg
  set q : ℝ := cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2 with hq
  set k : ℝ := B * cubicDer c₁ c₂ c₃ t - A * cubicDer e₁ e₂ e₃ t with hk
  have hqn : 0 ≤ q := by rw [hq]; positivity
  have hw : Real.sqrt q ^ 2 = q := Real.sq_sqrt hqn
  rw [offsetCrossVal, ← hg, ← hq, ← hk] at h
  rw [offsetCrossPoly, ← hg, ← hq, ← hk]
  linear_combination (g * Real.sqrt q - d * k) * h - g ^ 2 * hw

-- Theorem: the rationalized equation has finitely many roots. Its degree-`10` coefficient
-- is `9·(c₃² + e₃²)·(A·c₃ + B·e₃)²`, so the condition that makes it nonzero is that the
-- line is not parallel to the leading direction of the cubic pair — and the proof does not
-- need the coefficient itself, only that the leading term outranks the subtracted one.
theorem offsetCross_finite_roots {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C : ℝ}
    (hlead : A * c₃ + B * e₃ ≠ 0)
    (hreg : ∃ s : ℝ, cubicDer c₁ c₂ c₃ s ≠ 0 ∨ cubicDer e₁ e₂ e₃ s ≠ 0) :
    {t : ℝ | offsetCrossPoly c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t = 0}.Finite := by
  classical
  set Xc : Polynomial ℝ :=
    Polynomial.C c₃ * X ^ 3 + Polynomial.C c₂ * X ^ 2 + Polynomial.C c₁ * X
      + Polynomial.C c₀ with hXc
  set Xe : Polynomial ℝ :=
    Polynomial.C e₃ * X ^ 3 + Polynomial.C e₂ * X ^ 2 + Polynomial.C e₁ * X
      + Polynomial.C e₀ with hXe
  set Dc : Polynomial ℝ :=
    Polynomial.C (3 * c₃) * X ^ 2 + Polynomial.C (2 * c₂) * X + Polynomial.C c₁ with hDc
  set De : Polynomial ℝ :=
    Polynomial.C (3 * e₃) * X ^ 2 + Polynomial.C (2 * e₂) * X + Polynomial.C e₁ with hDe
  set G : Polynomial ℝ :=
    Polynomial.C A * Xc + Polynomial.C B * Xe - Polynomial.C C with hG
  set H : Polynomial ℝ := Polynomial.C B * Dc - Polynomial.C A * De with hH
  set P : Polynomial ℝ := G ^ 2 * (Dc ^ 2 + De ^ 2) - Polynomial.C (d ^ 2) * H ^ 2 with hP
  have hevalDc : ∀ t : ℝ, Dc.eval t = cubicDer c₁ c₂ c₃ t := by
    intro t; simp [hDc, cubicDer]
  have hevalDe : ∀ t : ℝ, De.eval t = cubicDer e₁ e₂ e₃ t := by
    intro t; simp [hDe, cubicDer]
  have hevalP : ∀ t : ℝ,
      P.eval t = offsetCrossPoly c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t := by
    intro t
    simp only [hP, hG, hH, hXc, hXe, hDc, hDe, offsetCrossPoly, cubicVal, cubicDer,
      Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
  -- The sum of the two squared velocity components is a nonzero polynomial: it is nonzero
  -- at the regular parameter supplied.
  have hDsq : Dc ^ 2 + De ^ 2 ≠ 0 := by
    obtain ⟨s, hs⟩ := hreg
    intro hzero
    have := congrArg (Polynomial.eval s) hzero
    simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_zero,
      hevalDc, hevalDe] at this
    have hnc := sq_nonneg (cubicDer c₁ c₂ c₃ s)
    have hne := sq_nonneg (cubicDer e₁ e₂ e₃ s)
    rcases hs with hs | hs
    · exact hs (sq_eq_zero_iff.mp (by linarith))
    · exact hs (sq_eq_zero_iff.mp (by linarith))
  -- `G` is a genuine cubic, its leading coefficient being the one the hypothesis excludes.
  have hGcoeff : G.coeff 3 = A * c₃ + B * e₃ := by
    simp [hG, hXc, hXe, Polynomial.coeff_X_pow]
  have hG3 : 3 ≤ G.natDegree :=
    Polynomial.le_natDegree_of_ne_zero (by rw [hGcoeff]; exact hlead)
  have hGne : G ≠ 0 := fun hc => hlead (by rw [← hGcoeff, hc, Polynomial.coeff_zero])
  have hHdeg : H.natDegree ≤ 2 := by
    rw [hH, hDc, hDe]
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    simp only [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> first | omega | ring
  -- Degree `10` against degree at most `4`: the difference cannot vanish.
  have hPne : P ≠ 0 := by
    intro hzero
    have heq : G ^ 2 * (Dc ^ 2 + De ^ 2) = Polynomial.C (d ^ 2) * H ^ 2 := by
      rw [hP] at hzero
      exact sub_eq_zero.mp hzero
    have hlhs : 6 ≤ (G ^ 2 * (Dc ^ 2 + De ^ 2)).natDegree := by
      rw [Polynomial.natDegree_mul (pow_ne_zero 2 hGne) hDsq, Polynomial.natDegree_pow]
      omega
    have hrhs : (Polynomial.C (d ^ 2) * H ^ 2).natDegree ≤ 4 := by
      refine le_trans (Polynomial.natDegree_C_mul_le _ _) ?_
      refine le_trans (Polynomial.natDegree_pow_le) ?_
      omega
    rw [heq] at hlhs
    omega
  exact (Polynomial.finite_setOfPred_isRoot hPne).subset
    (fun t ht => by change P.eval t = 0; rw [hevalP]; exact ht)


/-! ### Quintics in value form

The recovery step below produces its polynomial as an expression in `β`, not as an element
of `ℝ[X]`, so this is the bridge: a quintic written out coefficient by coefficient, fed to
`root_Pconstructible_le_six_coeffs`. Nothing here is specific to offsets. -/

/-- The quintic `r₅X⁵ + r₄X⁴ + r₃X³ + r₂X² + r₁X + r₀` as an element of `ℝ[X]`. -/
noncomputable def quinticPoly (r₀ r₁ r₂ r₃ r₄ r₅ : ℝ) : Polynomial ℝ :=
  Polynomial.C r₅ * X ^ 5 + Polynomial.C r₄ * X ^ 4 + Polynomial.C r₃ * X ^ 3
    + Polynomial.C r₂ * X ^ 2 + Polynomial.C r₁ * X + Polynomial.C r₀

-- Theorem: every real root of a quintic with P-constructible coefficients and nonzero
-- leading coefficient is P-constructible. This is `root_Pconstructible_le_six_coeffs` with
-- the polynomial presented by its coefficients rather than as an element of `ℝ[X]`.
theorem quinticVal_root_Pconstructible {r₀ r₁ r₂ r₃ r₄ r₅ β : ℝ}
    (h₀ : PConstructible r₀) (h₁ : PConstructible r₁) (h₂ : PConstructible r₂)
    (h₃ : PConstructible r₃) (h₄ : PConstructible r₄) (h₅ : PConstructible r₅)
    (h5ne : r₅ ≠ 0)
    (hroot : r₅ * β ^ 5 + r₄ * β ^ 4 + r₃ * β ^ 3 + r₂ * β ^ 2 + r₁ * β + r₀ = 0) :
    PConstructible β := by
  have hdeg : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).natDegree ≤ 5 := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    simp only [quinticPoly, Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow, Polynomial.coeff_X, Polynomial.coeff_C]
    split_ifs <;> first | omega | ring
  have hc5 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 5 = r₅ := by
    simp [quinticPoly, Polynomial.coeff_X_pow]
  have hne : quinticPoly r₀ r₁ r₂ r₃ r₄ r₅ ≠ 0 := fun hz => h5ne (by rw [← hc5, hz]; simp)
  refine root_Pconstructible_le_six_coeffs hne (by omega) (fun i => ?_) ?_
  · by_cases hi : 5 < i
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
      exact zero_Pconstructible
    · have e0 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 0 = r₀ := by
        simp [quinticPoly, Polynomial.coeff_X_pow]
      have e1 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 1 = r₁ := by
        simp [quinticPoly, Polynomial.coeff_X_pow]
      have e2 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 2 = r₂ := by
        simp [quinticPoly, Polynomial.coeff_X_pow]
      have e3 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 3 = r₃ := by
        simp [quinticPoly, Polynomial.coeff_X_pow]
      have e4 : (quinticPoly r₀ r₁ r₂ r₃ r₄ r₅).coeff 4 = r₄ := by
        simp [quinticPoly, Polynomial.coeff_X_pow]
      interval_cases i
      · rw [e0]; exact h₀
      · rw [e1]; exact h₁
      · rw [e2]; exact h₂
      · rw [e3]; exact h₃
      · rw [e4]; exact h₄
      · rw [hc5]; exact h₅
  · simp only [quinticPoly, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X]
    linarith [hroot]

/-! ### The degree engine, with the second curve left open

The two theorems here are the reusable core, and they are deliberately silent about what
the offset is crossed with. `crossing_Pconstructible` asks the second curve only for an
implicit equation `F` vanishing on it and for the composite `F ∘ Γ` to have finitely many
zeros, so those are exactly the hypotheses taken; a line, a conic, a polynomial graph and
a sine curve are all instances, differing only in the finiteness bound each needs.

The recovery of the parameter is likewise indifferent to the second curve.
`offsetParam_normal_eq_zero` is a statement about the *first* curve alone — the
displacement to the offset is along the normal, so it kills the velocity, whatever else
happens to pass through that point. With the cubic pair that is a quintic, and a quintic
is two degrees inside `root_Pconstructible_le_six_coeffs` no matter how high the degree of
the crossing equation climbs. That asymmetry is what makes the engine worth having: adding
a harder second curve raises the degree of what is *solved* without raising the degree of
anything that has to be *undone*. -/

-- Theorem: both coordinates of a point where the offset of a cubic pair meets any
-- constructible curve are P-constructible.
theorem offsetCubicPair_cross_point_Pconstructible {T : Set (ℝ × ℝ)}
    (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    -- `F` vanishes on the second curve ...
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    -- ... and vanishes only finitely often along the offset.
    (hfin : {t : ℝ | F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).2 = 0}.Finite)
    -- The arc is regular at `β`, and the offset really does meet the second curve there.
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β ∈ T) :
    PConstructible (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β).1 ∧
      PConstructible (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β).2 := by
  set γ : ℝ → ℝ × ℝ := cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ with hγ
  set Γ : ℝ → ℝ × ℝ := offsetParam γ d with hΓ
  obtain ⟨u, v, hu, hv, hwin, hinj⟩ :=
    exists_rat_window_cubicPair (c₀ := c₀) (e₀ := e₀) hreg
  have huv : (u : ℝ) < (v : ℝ) := lt_trans hu hv
  have hmemβ : β ∈ Set.Icc (u : ℝ) (v : ℝ) := ⟨hu.le, hv.le⟩
  have hS := offsetCubicPairArc_PConstructibleCurve hc₀ hc₁ hc₂ hc₃ he₀ he₁ he₂ he₃ hd
    (rat_Pconstructible u) (rat_Pconstructible v) huv hwin hinj
  rw [← hγ, ← hΓ] at hS
  exact crossing_Pconstructible hS hT (Set.image_subset_range Γ _) hTzero
    (fun t => rfl) hfin ⟨β, hmemβ, rfl⟩ hβT

-- Theorem: the expansion of the orthogonality relation between the offset displacement and
-- the velocity. It is a quintic in the parameter, with coefficients built from the crossing
-- point and the coefficients of the cubic pair by `+ - *` alone.
theorem normalEq_eq_quinticVal (X Y c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ t : ℝ) :
    (X - cubicVal c₀ c₁ c₂ c₃ t) * cubicDer c₁ c₂ c₃ t
        + (Y - cubicVal e₀ e₁ e₂ e₃ t) * cubicDer e₁ e₂ e₃ t
      = -3 * (c₃ ^ 2 + e₃ ^ 2) * t ^ 5
        + -5 * (c₂ * c₃ + e₂ * e₃) * t ^ 4
        + -(4 * c₁ * c₃ + 2 * c₂ ^ 2 + 4 * e₁ * e₃ + 2 * e₂ ^ 2) * t ^ 3
        + (3 * X * c₃ + 3 * Y * e₃ - 3 * c₁ * c₂ - 3 * c₀ * c₃ - 3 * e₁ * e₂
            - 3 * e₀ * e₃) * t ^ 2
        + (2 * X * c₂ + 2 * Y * e₂ - c₁ ^ 2 - 2 * c₀ * c₂ - e₁ ^ 2 - 2 * e₀ * e₂) * t
        + (X * c₁ + Y * e₁ - c₀ * c₁ - e₀ * e₁) := by
  simp only [cubicVal, cubicDer]
  ring

-- Theorem: and the parameter behind such a crossing is P-constructible too, whatever the
-- second curve was. This is the engine: the degree of the equation actually solved is set
-- by `F`, and can be as high as one likes, while the step that undoes the construction
-- stays a quintic.
theorem offsetCubicPair_cross_root_Pconstructible {T : Set (ℝ × ℝ)}
    (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    (hfin : {t : ℝ | F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).2 = 0}.Finite)
    -- The cubic pair has a genuine cubic term, so the recovery quintic is not degenerate.
    (hcubic : c₃ ≠ 0 ∨ e₃ ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β ∈ T) :
    PConstructible β := by
  obtain ⟨hX, hY⟩ := offsetCubicPair_cross_point_Pconstructible hT hc₀ hc₁ hc₂ hc₃ he₀ he₁
    he₂ he₃ hd hTzero hfin hreg hβT
  set X : ℝ := (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β).1 with hXdef
  set Y : ℝ := (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β).2 with hYdef
  have h5ne : -3 * (c₃ ^ 2 + e₃ ^ 2) ≠ 0 := by
    have hpos : 0 < c₃ ^ 2 + e₃ ^ 2 := by rcases hcubic with h | h <;> positivity
    intro hz
    nlinarith
  -- The displacement to the crossing point is along the normal, hence kills the velocity:
  -- one polynomial equation in `β`, of degree `5`.
  have hnormal : (X - cubicVal c₀ c₁ c₂ c₃ β) * cubicDer c₁ c₂ c₃ β
      + (Y - cubicVal e₀ e₁ e₂ e₃ β) * cubicDer e₁ e₂ e₃ β = 0 := by
    have h := offsetParam_normal_eq_zero (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β
    rwa [deriv_cubicPairParam_fst, deriv_cubicPairParam_snd] at h
  rw [normalEq_eq_quinticVal] at hnormal
  exact quinticVal_root_Pconstructible (by pconstructible) (by pconstructible)
    (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
    h5ne hnormal

/-! ### The line as the first instance

With the engine in place a second curve costs only its finiteness bound. For a line that
bound is the degree-10 rationalization, and `line_offset_mul_speed` is what connects the
two: the line's implicit equation at the offset point, times the speed, is exactly
`offsetCrossVal`, whose vanishing forces `offsetCrossPoly` to vanish. -/

-- Theorem: the line's implicit equation, evaluated at the offset point and cleared of its
-- denominator, is exactly `offsetCrossVal`. At a singular parameter both sides vanish, the
-- unit normal and the factor `B·x' - A·y'` being zero together, so this needs no
-- regularity hypothesis.
theorem line_offset_mul_speed (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t : ℝ) :
    (A * (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).1
        + B * (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d t).2 - C)
      * speed (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) t
      = offsetCrossVal c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t := by
  have hq : (0 : ℝ) ≤ cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2 := by positivity
  simp only [offsetParam, unitNormal, offsetCrossVal, speed_cubicPairParam, cubicPairParam,
    deriv_cubicVal]
  by_cases h0 : Real.sqrt (cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2) = 0
  · have hsum : cubicDer c₁ c₂ c₃ t ^ 2 + cubicDer e₁ e₂ e₃ t ^ 2 = 0 := by
      rw [← Real.sqrt_eq_zero hq]
      exact h0
    have hnc := sq_nonneg (cubicDer c₁ c₂ c₃ t)
    have hne := sq_nonneg (cubicDer e₁ e₂ e₃ t)
    have hc : cubicDer c₁ c₂ c₃ t = 0 := sq_eq_zero_iff.mp (by linarith)
    have he : cubicDer e₁ e₂ e₃ t = 0 := sq_eq_zero_iff.mp (by linarith)
    rw [h0, hc, he]
    ring
  · field_simp
    ring

-- Theorem: the parameter of a crossing of the offset cubic pair against a line is
-- P-constructible. `hcross` is the geometric statement that the offset really is on the
-- line at `β`, and `hlead` says the line is not parallel to the leading direction of the
-- cubic pair, which is what keeps the rationalized equation from collapsing below
-- degree `10`.
theorem offsetCubicPairCross_root_Pconstructible {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hA : PConstructible A) (hB : PConstructible B) (hC : PConstructible C)
    (hlead : A * c₃ + B * e₃ ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hcross : offsetCrossVal c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C β = 0) :
    PConstructible β := by
  set γ : ℝ → ℝ × ℝ := cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ with hγ
  set Γ : ℝ → ℝ × ℝ := offsetParam γ d with hΓ
  -- A line needs a direction: `A` and `B` cannot both vanish, or `hlead` would fail.
  have hAB : A ^ 2 + B ^ 2 ≠ 0 := by
    intro hz
    have hA0 : A = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
    have hB0 : B = 0 := by nlinarith [sq_nonneg A, sq_nonneg B]
    exact hlead (by rw [hA0, hB0]; ring)
  have hcubic : c₃ ≠ 0 ∨ e₃ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hlead (by rw [hcon.1, hcon.2]; ring)
  -- The offset is on the line at `β`: the speed there is nonzero, so `hcross` transfers.
  have honline : A * (Γ β).1 + B * (Γ β).2 - C = 0 := by
    obtain ⟨u, v, hu, hv, hwin, -⟩ :=
      exists_rat_window_cubicPair (c₀ := c₀) (e₀ := e₀) hreg
    have hmul := line_offset_mul_speed c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C β
    rw [← hγ, ← hΓ, hcross] at hmul
    exact (mul_eq_zero.mp hmul).resolve_right (hwin β ⟨hu.le, hv.le⟩)
  -- The line arc through that point, cut to a rational window in its own parameter.
  set s₀ : ℝ := (A * (Γ β).2 - B * (Γ β).1) / (A ^ 2 + B ^ 2) with hs₀
  obtain ⟨w, hw1, hw2⟩ := exists_rat_btwn (show s₀ - 1 < s₀ by linarith)
  obtain ⟨z, hz1, hz2⟩ := exists_rat_btwn (show s₀ < s₀ + 1 by linarith)
  have hT := lineArc_PConstructibleCurve hA hB hC (rat_Pconstructible w)
    (rat_Pconstructible z) (show ((w : ℝ)) < (z : ℝ) by linarith)
  -- Every crossing is a root of the rationalized degree-10 equation, so there are finitely
  -- many; the spurious roots that squaring adds only enlarge the bound.
  have hfin : {t : ℝ | A * (Γ t).1 + B * (Γ t).2 - C = 0}.Finite := by
    refine (offsetCross_finite_roots (c₀ := c₀) (e₀ := e₀) (d := d) (C := C) hlead
      ⟨β, hreg⟩).subset fun t ht => ?_
    refine offsetCrossPoly_eq_zero_of_offsetCrossVal ?_
    have hmul := line_offset_mul_speed c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t
    rw [← hγ, ← hΓ] at hmul
    rw [← hmul, show A * (Γ t).1 + B * (Γ t).2 - C = 0 from ht, zero_mul]
  exact offsetCubicPair_cross_root_Pconstructible hT hc₀ hc₁ hc₂ hc₃ he₀ he₁ he₂ he₃ hd
    (F := fun P Q => A * P + B * Q - C)
    (fun q hq => by obtain ⟨s, -, rfl⟩ := hq; exact lineParam_implicit hAB s) hfin hcubic
    hreg ⟨s₀, ⟨hw2.le, hz1.le⟩, by rw [hs₀]; exact lineParam_surj hAB honline⟩

-- Theorem: the same statement with the line taken to be the `y`-axis, which is the shape
-- the construction actually has once the plane is put in the line's frame. Every real
-- solution of
--
--   `x(β) · √(x'(β)² + y'(β)²)  =  d · y'(β)`
--
-- with `x`, `y` cubics with P-constructible coefficients, `x` a genuine cubic, and `d`
-- P-constructible, is P-constructible. Generic such equations have irreducible degree-`10`
-- rationalizations, which is where the numbers this file adds come from.
theorem offsetCubicPair_axisCross_root_Pconstructible {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    (hlead : c₃ ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hcross : cubicVal c₀ c₁ c₂ c₃ β
        * Real.sqrt (cubicDer c₁ c₂ c₃ β ^ 2 + cubicDer e₁ e₂ e₃ β ^ 2)
      = d * cubicDer e₁ e₂ e₃ β) :
    PConstructible β := by
  refine offsetCubicPairCross_root_Pconstructible hc₀ hc₁ hc₂ hc₃ he₀ he₁ he₂ he₃ hd
    PConstructible.base_one zero_Pconstructible zero_Pconstructible (by simpa using hlead)
    hreg ?_
  simp only [offsetCrossVal, one_mul, zero_mul, add_zero, sub_zero, zero_sub]
  linarith [hcross]

/-! ### A number that was out of reach before

Worth recording concretely, because "reaches degree 10" is only interesting if degree 10
was not already reachable. Take

    x t = t³ - t² + 2t + 1,   y t = -(t³/3 + t²/2 + t),   d = √7

in `offsetCubicPair_axisCross_root_Pconstructible`. Then `y' t = -(t² + t + 1)`, the
crossing equation `x·√(x'² + y'²) = d·y'` rationalizes to

    10t¹⁰ - 30t⁹ + 89t⁸ - 114t⁷ + 152t⁶ - 58t⁵ + 38t⁴ + 30t³ - 16t² - 2 = 0,

and its two real roots are near `-0.5322430792` and `0.4965475424`. Both satisfy the
crossing equation itself, not merely its square — one with `d = +√7` and one with
`d = -√7`, the sign of `d` being the choice of which side to offset — and the arc is
regular at both, so the theorem applies to each. Every coefficient in sight is rational
except `d`, which `sqrt_Pconstructible` supplies.

That polynomial is irreducible over `ℚ` (irreducible modulo several primes), and its
Galois group contains `A₁₀`: it is transitive, and the factorisation type `1 + 2 + 7`
at `p = 29` gives an element whose square is a `7`-cycle, so Jordan's theorem applies
once primitivity is checked — a block system of size `2` or `5` cannot admit a `7`-cycle.

That places the roots outside everything the project could previously reach:

* `root_Pconstructible_le_eight` stops at degree `8` over `ℚ`, and these have degree `10`;
* `nonicVal_root_Pconstructible` is a degree-`9` family;
* iterating `root_Pconstructible_le_six_coeffs` builds exactly the numbers lying in towers
  whose steps have degree at most `6`, and no such tower contains these. A tower gives a
  chain of subgroups with all indices at most `6` descending from the Galois group into a
  point stabiliser, while the smallest index of a proper subgroup of `A₁₀` is `10`, so the
  chain cannot take a single step below `A₁₀` — and `A₁₀` is transitive, hence in no point
  stabiliser.

The irreducibility and the cycle type are computations, run outside Lean and not
formalized here; the P-constructibility of the roots is the theorem above and is. -/

/-! ### How much of degree 10 this reaches

The construction above is driven by `12` P-constructible parameters — `8` from the cubic
pair, `3` from the line, `1` from the offset distance — against the `10` coefficients of a
monic degree-`10` polynomial. That count has slack, and the natural hope is that the family
surjects onto the monic degree-`10` polynomials, which would put every degree-`10` real
algebraic number with P-constructible coefficients inside `PConstructible`.

It does not, and `offsetCrossPoly_normalForm` says why. Write the cubic pair in the frame of
the line rather than the frame of the page:

    u = A·x + B·y - C     (the signed distance to the line, up to scale)
    v = B·x - A·y         (the coordinate along it, up to scale)

Then, up to the harmless overall factor `A² + B²`,

    offsetCrossPoly  =  u² · (u'² + v'²)  -  d²(A² + B²) · v'².

The `12` parameters enter only through `u` (a cubic: `4`), `v'` (a quadratic: `3`) and the
single number `d²(A² + B²)` — eight numbers, not twelve. `v₀` is inert because `v` appears
only differentiated, and the line's own three parameters have been absorbed into `u` and
`v`. One further redundancy remains, since scaling `(u, v, d√(A² + B²))` by a common factor
scales the whole expression, and that is invisible after dividing by the leading
coefficient.

So the image is at most `8 - 1 = 7`-dimensional inside the `10`-dimensional space of monic
degree-`10` polynomials, and a numerical rank computation on the Jacobian confirms it is
exactly `7`. The construction reaches a **codimension-3** subvariety, not all of degree `10`.

That is the same shape of obstruction that stopped the two-Bézier program at codimension
`1`, arrived at from a different direction, and it is a sharper statement than a parameter
count: the deficiency is not a shortage of parameters but a degeneracy of the map, so no
cleverer choice of line or of cubic pair repairs it. Breaking it needs a construction whose
polynomial is not of the shape `u²·(u'² + v'²) - D²·v'²` — offsetting something that is not
a cubic pair, crossing the offset against something that is not a line, or offsetting twice.
-/

-- Theorem: the rationalized crossing equation sees its `12` parameters only through `8`
-- combinations — the cubic `u = A·x + B·y - C`, the quadratic `v' = (B·x - A·y)'`, and the
-- number `d²(A² + B²)`. This is the obstruction described above, in one identity.
theorem offsetCrossPoly_normalForm (c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t : ℝ)
    (hAB : A ^ 2 + B ^ 2 ≠ 0) :
    offsetCrossPoly c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d A B C t
      = (cubicVal (A * c₀ + B * e₀ - C) (A * c₁ + B * e₁) (A * c₂ + B * e₂)
              (A * c₃ + B * e₃) t ^ 2
            * (cubicDer (A * c₁ + B * e₁) (A * c₂ + B * e₂) (A * c₃ + B * e₃) t ^ 2
              + cubicDer (B * c₁ - A * e₁) (B * c₂ - A * e₂) (B * c₃ - A * e₃) t ^ 2)
          - d ^ 2 * (A ^ 2 + B ^ 2)
              * cubicDer (B * c₁ - A * e₁) (B * c₂ - A * e₂) (B * c₃ - A * e₃) t ^ 2)
        / (A ^ 2 + B ^ 2) := by
  simp only [offsetCrossPoly, cubicVal, cubicDer]
  field_simp
  ring

end Pconstructible
