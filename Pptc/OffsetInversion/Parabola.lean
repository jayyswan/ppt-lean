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
import Pptc.OffsetInversion.Speed

/-! # Pptc.OffsetInversion.Parabola — the parabola offset inversion

Stream L2 of `PLAN-offset-inversion.md`, the headline theorem. Push the parabola
`y = x ^ 2 / 2` sideways by a signed distance `d`; the offset is again a drawable stroke, so
the right edge of its box is a constructible number. That edge is the abscissa

    e(w) = w - d · w / √(1 + w ^ 2)                                                (L2.1)

of the offset point at parameter `w`, and eliminating the square root from (L2.1) leaves the
quartic

    w ^ 4 - 2 e w ^ 3 + (1 + e ^ 2 - d ^ 2) w ^ 2 - 2 e w + e ^ 2 = 0.             (L2.2)

Both `e` and `d` are constructible, so every coefficient of (L2.2) is. Read as
`w ^ 4 = (cubic in w)` it is the hypothesis of the power-curve root lemma
`powerLaw_cubic_root_Pconstructible` (the degree-4 branch of
`root_Pconstructible_le_five_coeffs`), which makes `w` constructible.

## The geometry

Write `γ t = (t, t ^ 2 / 2)`, so `γ' = (1, t)` and `s = speed γ t = √(1 + t ^ 2)`. The unit
normal is `(-t, 1)/s`, and the offset tracing is

    P_d t = (t - d t / s, t ^ 2 / 2 + d / s).

Its abscissa is `t(1 - d/s)`, whose derivative is `1 - d/s ^ 3 ≥ 1 - d > 0` on `t ≥ 0`
because `s ≥ 1`. So the abscissa is nondecreasing on `[0, w]`, the box reads its largest
value off the drawing, and that value is the far endpoint `e(w)` — the box is what turns the
offset stroke into the number `e`. Squaring `s (w - e) = d w` — legitimate as an implication
for every sign of `d`, since both sides are `d`-signed — gives (L2.2).

## The arc-length equation

The arc length of `γ` from the vertex is `(w √(1 + w ^ 2) + arsinh w)/2`, the antiderivative
of `s`; `arcLengthOf_halfParabolaParam_zero` records this, so the hypothesis

    `(w √(1+w^2) + arsinh w)/2 - d · arctan w = x`

of the headline is exactly "the offset arc from the vertex image has length `x`" — the
`arcLengthOf_offsetParam` readout of `Pptc.OffsetInversion.Speed` with the tangent angle
`ψ = arctan`. The hypothesis is now used essentially: the P-constructible length `x` lays
the arc on the offset curve with `arc_of_length`, and the box reads its endpoint. The
window that contains the arc is built from `x` and `d` alone, so the earlier proof that
offset an arbitrary sub-arc `[0, w]` is gone.

## What is not here

Uniqueness of the root (`ψ` is a strictly increasing bijection `[0, ∞) → [0, ∞)` for
`d < 1`) is the separate, non-constructive half of the headline and is not proved here; the
quartic only records an implication, and the extraneous roots introduced by squaring sit on
the other side of `e`.
-/

namespace Pconstructible

/-! ### The half-parabola, its speed, and its arc length

`Basic.parabolaParam` draws `y = x ^ 2`, whose speed is `√(1 + 4t ^ 2)`. Halving the
ordinate quarters the curvature, so everything below carries `√(1 + t ^ 2)` and the
antiderivative `(t √(1+t^2) + arsinh t)/2` in place of the `Basic` formula. The proofs
mirror `speed_parabolaParam` / `hasDerivAt_parabolaAntideriv` /
`arcLengthOf_parabolaParam` term by term. -/

/-- The parabola `y = x ^ 2 / 2`, parametrized by its abscissa. Its offset is the one the
headline inverts; the `1/2` is what makes the offset abscissa `w - d w/√(1+w²)` rather than
the `w - 2 d w/√(1+4w²)` of the standard parabola. -/
noncomputable def halfParabolaParam (t : ℝ) : ℝ × ℝ := (t, t ^ 2 / 2)

-- Theorem: the first coordinate of the half-parabola has derivative `1`.
theorem deriv_halfParabolaParam_fst (t : ℝ) :
    deriv (fun s => (halfParabolaParam s).1) t = 1 := by
  change deriv (fun s : ℝ => s) t = 1
  simp

-- Theorem: the second coordinate of the half-parabola has derivative `t`.
theorem deriv_halfParabolaParam_snd (t : ℝ) :
    deriv (fun s => (halfParabolaParam s).2) t = t := by
  change deriv (fun s : ℝ => s ^ 2 / 2) t = t
  have h : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
    have h1 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
      simpa using hasDerivAt_pow 2 t
    have h2 := h1.div_const 2
    simpa using h2
  exact h.deriv

-- Theorem: the speed of the half-parabola is `√(1 + t²)`.
theorem speed_halfParabolaParam (t : ℝ) :
    speed halfParabolaParam t = Real.sqrt (1 + t ^ 2) := by
  rw [speed, deriv_halfParabolaParam_fst, deriv_halfParabolaParam_snd]
  congr 1
  ring

-- Theorem: the half-parabola is differentiable in both coordinates everywhere.
theorem differentiableAt_halfParabolaParam (t : ℝ) :
    DifferentiableAt ℝ (fun s => (halfParabolaParam s).1) t ∧
      DifferentiableAt ℝ (fun s => (halfParabolaParam s).2) t := by
  constructor
  · change DifferentiableAt ℝ (fun s : ℝ => s) t
    exact differentiableAt_id
  · change DifferentiableAt ℝ (fun s : ℝ => s ^ 2 / 2) t
    exact differentiableAt_id.pow 2 |>.div_const 2

-- Theorem: the half-parabola is regular: its speed never vanishes.
theorem speed_halfParabolaParam_ne_zero (t : ℝ) : speed halfParabolaParam t ≠ 0 := by
  rw [speed_halfParabolaParam]
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

-- Theorem: the two velocity components of the half-parabola are continuous (indeed
-- constant and the identity), which is the `hC1` hypothesis of the `offset` constructor.
theorem continuous_deriv_halfParabolaParam :
    Continuous (deriv (fun s => (halfParabolaParam s).1)) ∧
      Continuous (deriv (fun s => (halfParabolaParam s).2)) := by
  have h1 : deriv (fun s => (halfParabolaParam s).1) = fun _ => (1 : ℝ) :=
    funext deriv_halfParabolaParam_fst
  have h2 : deriv (fun s => (halfParabolaParam s).2) = fun s => s :=
    funext deriv_halfParabolaParam_snd
  constructor
  · rw [h1]; exact continuous_const
  · rw [h2]; exact continuous_id

/-- An antiderivative of the half-parabola's speed `√(1 + t²)`, namely
`(t √(1+t²) + arsinh t)/2`. -/
noncomputable def halfParabolaAntideriv (t : ℝ) : ℝ :=
  (t * Real.sqrt (1 + t ^ 2) + Real.arsinh t) / 2

-- Theorem: `halfParabolaAntideriv` differentiates to the speed `√(1 + t²)`. This is the
-- `Basic.hasDerivAt_parabolaAntideriv` computation with `1 + 4t²` replaced by `1 + t²`.
theorem hasDerivAt_halfParabolaAntideriv (t : ℝ) :
    HasDerivAt halfParabolaAntideriv (Real.sqrt (1 + t ^ 2)) t := by
  have hu : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hu.le
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hsq : HasDerivAt (fun s : ℝ => 1 + s ^ 2) (2 * t) t := by
    have h := hp.const_add (1 : ℝ)
    simpa using h
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s ^ 2))
      (2 * t / (2 * Real.sqrt (1 + t ^ 2))) t := hsq.sqrt hu.ne'
  have hterm1 : HasDerivAt (fun s : ℝ => s * Real.sqrt (1 + s ^ 2))
      (1 * Real.sqrt (1 + t ^ 2) + t * (2 * t / (2 * Real.sqrt (1 + t ^ 2)))) t :=
    (hasDerivAt_id t).mul hsqrt
  have hterm2 : HasDerivAt (fun s : ℝ => Real.arsinh s)
      ((Real.sqrt (1 + t ^ 2))⁻¹) t := Real.hasDerivAt_arsinh t
  have hsum := hterm1.add hterm2
  have hval : (1 * Real.sqrt (1 + t ^ 2)
        + t * (2 * t / (2 * Real.sqrt (1 + t ^ 2)))
        + (Real.sqrt (1 + t ^ 2))⁻¹) / 2 = Real.sqrt (1 + t ^ 2) := by
    field_simp
    nlinarith [hs2, hspos]
  have hfin := hsum.div_const 2
  rw [hval] at hfin
  exact hfin

-- Theorem: the arc length of the half-parabola over `[u, v]` is the difference of its
-- antiderivative, exactly as in `Basic.arcLengthOf_parabolaParam`.
theorem arcLengthOf_halfParabolaParam (u v : ℝ) :
    arcLengthOf halfParabolaParam u v = halfParabolaAntideriv v - halfParabolaAntideriv u := by
  rw [arcLengthOf]
  simp only [speed_halfParabolaParam]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_halfParabolaAntideriv x) ?_
  apply Continuous.intervalIntegrable
  fun_prop

-- Theorem: the arc length of the half-parabola from the vertex is
-- `(w √(1+w²) + arsinh w)/2`, the expression appearing in the headline equation.
theorem arcLengthOf_halfParabolaParam_zero (w : ℝ) :
    arcLengthOf halfParabolaParam 0 w
      = (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2 := by
  rw [arcLengthOf_halfParabolaParam]
  simp [halfParabolaAntideriv]

/-! ### The half-parabola as a graph

`y = x ^ 2 / 2` is the graph of the rational polynomial `X ^ 2 / 2`, so `poly_graph` draws
the whole unbounded curve. The bounded arcs used below are cut as cubic-pair arcs, which
also makes them curves in their own right before they are offset. -/

-- Theorem: the rational polynomial `X²/2` evaluates to `t²/2`.
theorem aeval_halfX2 (t : ℝ) :
    Polynomial.aeval t ((Polynomial.C (1 / 2 : ℚ)) * Polynomial.X ^ 2) = t ^ 2 / 2 := by
  simp
  ring

-- Theorem: the half-parabola is the graph of the rational polynomial `X²/2`.
theorem halfParabola_PConstructibleCurve :
    PConstructibleCurve {pt : ℝ × ℝ | pt.2 = pt.1 ^ 2 / 2} := by
  have hset : {pt : ℝ × ℝ | pt.2 = pt.1 ^ 2 / 2}
      = {pt : ℝ × ℝ |
          pt.2 = Polynomial.aeval pt.1 ((Polynomial.C (1 / 2 : ℚ)) * Polynomial.X ^ 2)} := by
    ext pt
    simp only [Set.mem_ofPred_eq]
    rw [aeval_halfX2]
  rw [hset]
  exact PConstructibleCurve.poly_graph _ (by compute_degree!)

/-! ### The half-parabola as a cubic pair

`halfParabolaParam` is the cubic pair with `x t = t` and `y t = t²/2`, so the whole arc
over a P-constructible window is a constructible curve by
`cubicPairArc_PConstructibleCurve`, and its offset is a whole-curve use of the `offset`
constructor. This is the legitimate route: the window is chosen from constructible data
only, never from the parameter `w` being inverted. -/

-- Theorem: the half-parabola is the cubic pair `(t, t²/2)`.
theorem cubicPairParam_halfParabola :
    cubicPairParam 0 1 0 0 0 0 (1 / 2) 0 = halfParabolaParam := by
  funext t
  simp [halfParabolaParam, cubicPairParam, cubicVal]
  ring

-- Theorem: the half-parabola over any positive P-constructible window is a constructible
-- curve.
theorem halfParabolaArc_PConstructibleCurve {W : ℝ} (hW : PConstructible W) (hW0 : 0 < W) :
    PConstructibleCurve (halfParabolaParam '' Set.Icc 0 W) := by
  have h := cubicPairArc_PConstructibleCurve (c₀ := 0) (c₁ := 1) (c₂ := 0) (c₃ := 0)
    (d₀ := 0) (d₁ := 0) (d₂ := 1 / 2) (d₃ := 0)
    (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
    (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
    zero_Pconstructible hW hW0
  rw [cubicPairParam_halfParabola] at h
  exact h

-- Theorem: the second coordinate of the offset of the half-parabola is
-- `t²/2 + d/√(1+t²)`.
theorem offsetParam_halfParabola_snd (d t : ℝ) :
    (offsetParam halfParabolaParam d t).2 = t ^ 2 / 2 + d / Real.sqrt (1 + t ^ 2) := by
  unfold offsetParam unitNormal
  rw [deriv_halfParabolaParam_fst, deriv_halfParabolaParam_snd, speed_halfParabolaParam]
  simp only [halfParabolaParam]
  ring

-- Theorem: the first coordinate of the offset of the half-parabola is
-- `t - d t/√(1+t²)`, straight from `unitNormal`.
theorem offsetParam_halfParabola_fst (d t : ℝ) :
    (offsetParam halfParabolaParam d t).1 = t - d * (t / Real.sqrt (1 + t ^ 2)) := by
  unfold offsetParam unitNormal
  rw [deriv_halfParabolaParam_fst, deriv_halfParabolaParam_snd, speed_halfParabolaParam]
  simp only [halfParabolaParam]
  ring

-- Theorem: both coordinates of the offset of the half-parabola are differentiable
-- everywhere, from their explicit formulas.
theorem differentiableAt_offsetParam_halfParabola (d t : ℝ) :
    DifferentiableAt ℝ (fun s => (offsetParam halfParabolaParam d s).1) t ∧
      DifferentiableAt ℝ (fun s => (offsetParam halfParabolaParam d s).2) t := by
  constructor
  · have h : (fun s => (offsetParam halfParabolaParam d s).1)
        = fun s : ℝ => s - d * (s / Real.sqrt (1 + s ^ 2)) :=
      funext (offsetParam_halfParabola_fst d)
    rw [h]
    fun_prop (disch := positivity)
  · have h : (fun s => (offsetParam halfParabolaParam d s).2)
        = fun s : ℝ => s ^ 2 / 2 + d / Real.sqrt (1 + s ^ 2) :=
      funext (offsetParam_halfParabola_snd d)
    rw [h]
    fun_prop (disch := positivity)

-- Theorem: the curvature of the half-parabola is `1/(1+t²)^{3/2}`.
theorem curvature_halfParabolaParam (t : ℝ) :
    curvature halfParabolaParam t = 1 / Real.sqrt (1 + t ^ 2) ^ 3 := by
  have hdx : deriv (fun s => (halfParabolaParam s).1) = fun _ => (1 : ℝ) :=
    funext deriv_halfParabolaParam_fst
  have hdy : deriv (fun s => (halfParabolaParam s).2) = fun s => s :=
    funext deriv_halfParabolaParam_snd
  unfold curvature
  rw [hdx, hdy, speed_halfParabolaParam]
  simp

-- Theorem: the curvature times the speed is `1/(1+t²)`, the derivative of `arctan`.
theorem curvature_halfParabola_mul_speed (t : ℝ) :
    curvature halfParabolaParam t * speed halfParabolaParam t = 1 / (1 + t ^ 2) := by
  rw [curvature_halfParabolaParam, speed_halfParabolaParam]
  have hpos : (0 : ℝ) < 1 + t ^ 2 := by positivity
  have hs : Real.sqrt (1 + t ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hs2 : Real.sqrt (1 + t ^ 2) ^ 2 = 1 + t ^ 2 := Real.sq_sqrt hpos.le
  have h3 : Real.sqrt (1 + t ^ 2) ^ 3 = Real.sqrt (1 + t ^ 2) * (1 + t ^ 2) := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs2]
    ring
  rw [h3]
  field_simp

-- Theorem: the offset is cusp-free for `d < 1`: the factor `1 - d κ` is positive.
theorem one_sub_mul_curvature_halfParabola_pos {d t : ℝ} (hd1 : d < 1) :
    0 < 1 - d * curvature halfParabolaParam t := by
  have hspos : (0 : ℝ) < Real.sqrt (1 + t ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 2) ^ 3 := by
    have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + t ^ 2) := by
      rw [Real.one_le_sqrt]
      nlinarith [sq_nonneg t]
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ Real.sqrt (1 + t ^ 2) ^ 3 := by gcongr
  have hkpos : (0 : ℝ) < 1 / Real.sqrt (1 + t ^ 2) ^ 3 := by positivity
  have hkle : 1 / Real.sqrt (1 + t ^ 2) ^ 3 ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact hs3
  rw [curvature_halfParabolaParam]
  rcases le_total d 0 with hd0 | hd0
  · have hnonpos : d * (1 / Real.sqrt (1 + t ^ 2) ^ 3) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hd0 (by positivity)
    linarith
  · have hlt : d * (1 / Real.sqrt (1 + t ^ 2) ^ 3) < 1 := by
      calc d * (1 / Real.sqrt (1 + t ^ 2) ^ 3) ≤ d * 1 :=
            mul_le_mul_of_nonneg_left hkle hd0
        _ = d := mul_one d
        _ < 1 := hd1
    linarith

-- Theorem: the speed of the offset is `|1 - d κ|` times the speed of the half-parabola.
theorem speed_offsetParam_halfParabola (d t : ℝ) :
    speed (offsetParam halfParabolaParam d) t
      = |1 - d * curvature halfParabolaParam t| * speed halfParabolaParam t :=
  speed_offsetParam (differentiableAt_halfParabolaParam t).1
    (differentiableAt_halfParabolaParam t).2
    (by
      have h : deriv (fun s => (halfParabolaParam s).1) = fun _ => (1 : ℝ) :=
        funext deriv_halfParabolaParam_fst
      rw [h]
      exact differentiableAt_const 1)
    (by
      have h : deriv (fun s => (halfParabolaParam s).2) = fun s => s :=
        funext deriv_halfParabolaParam_snd
      rw [h]
      exact differentiableAt_id)
    (speed_halfParabolaParam_ne_zero t)

-- Theorem: the speed of the offset is continuous everywhere, so it is interval
-- integrable on any window.
theorem continuous_speed_offsetParam_halfParabola (d : ℝ) :
    Continuous (speed (offsetParam halfParabolaParam d)) := by
  have hfun : speed (offsetParam halfParabolaParam d)
      = fun t => |1 - d * curvature halfParabolaParam t| * speed halfParabolaParam t :=
    funext (speed_offsetParam_halfParabola d)
  rw [hfun]
  have hκ : (fun t => |1 - d * curvature halfParabolaParam t|
        * speed halfParabolaParam t)
      = fun t => |1 - d * (1 / Real.sqrt (1 + t ^ 2) ^ 3)| * Real.sqrt (1 + t ^ 2) := by
    funext t
    rw [curvature_halfParabolaParam, speed_halfParabolaParam]
  rw [hκ]
  have hsqrt : Continuous (fun t : ℝ => Real.sqrt (1 + t ^ 2)) := by fun_prop
  have hpow : Continuous (fun t : ℝ => Real.sqrt (1 + t ^ 2) ^ 3) := hsqrt.pow 3
  have hne : ∀ t : ℝ, Real.sqrt (1 + t ^ 2) ^ 3 ≠ 0 :=
    fun t => (pow_pos (Real.sqrt_pos.mpr (by positivity)) 3).ne'
  have hdiv : Continuous (fun t : ℝ => 1 / Real.sqrt (1 + t ^ 2) ^ 3) :=
    continuous_const.div hpow hne
  have hinner : Continuous (fun t : ℝ => 1 - d * (1 / Real.sqrt (1 + t ^ 2) ^ 3)) :=
    continuous_const.sub (continuous_const.mul hdiv)
  exact hinner.abs.mul hsqrt

-- Theorem: the offset of the half-parabola over a positive P-constructible window is a
-- constructible curve. This is the whole-curve use: the window is chosen before the
-- offset, from constructible data, and the offset acts on all of it at once.
theorem halfParabolaOffsetArc_PConstructibleCurve {d W : ℝ} (hd : PConstructible d)
    (hW : PConstructible W) (hW0 : 0 < W) :
    PConstructibleCurve (offsetParam halfParabolaParam d '' Set.Icc 0 W) := by
  have hreg : ∀ t ∈ Set.Icc 0 W,
      speed (cubicPairParam 0 1 0 0 0 0 (1 / 2) 0) t ≠ 0 := by
    intro t _
    rw [cubicPairParam_halfParabola]
    exact speed_halfParabolaParam_ne_zero t
  have hinj : Set.InjOn (cubicPairParam 0 1 0 0 0 0 (1 / 2) 0) (Set.Icc 0 W) := by
    intro a _ b _ hab
    simpa [cubicPairParam, cubicVal] using congrArg Prod.fst hab
  have h := offsetCubicPairArc_PConstructibleCurve (c₀ := 0) (c₁ := 1) (c₂ := 0) (c₃ := 0)
    (e₀ := 0) (e₁ := 0) (e₂ := 1 / 2) (e₃ := 0) (d := d) (u := 0) (v := W)
    (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
    (by pconstructible) (by pconstructible) (by pconstructible) (by pconstructible)
    hd zero_Pconstructible hW hW0 hreg hinj
  rw [cubicPairParam_halfParabola] at h
  exact h

/-! ### The offset abscissa and its monotonicity

The abscissa of `P_d t` is `t - d t/√(1+t²)`. Its derivative is `1 - d/(1+t²)^{3/2}`, which
is positive for `d < 1` because `(1+t²)^{3/2} ≥ 1`: for `d ≤ 0` it exceeds `1`, and for
`0 < d < 1` it exceeds `1 - d`. So the abscissa is nondecreasing on `[0, w]`, which is
exactly the monotonicity `arc_xendpoint_Pconstructible` asks of the far endpoint. -/

-- Theorem: the abscissa of the offset of the half-parabola at parameter `t` is
-- `t - d t/√(1+t²)`, straight from `unitNormal`. (Defined above, before the
-- differentiability lemmas that use it.)

-- Theorem: the derivative of the offset abscissa `t ↦ t - d t/√(1+t²)` is
-- `1 - d/√(1+t²)³`.
theorem hasDerivAt_offsetAbscissa (d x : ℝ) :
    HasDerivAt (fun t : ℝ => t - d * (t / Real.sqrt (1 + t ^ 2)))
      (1 - d / Real.sqrt (1 + x ^ 2) ^ 3) x := by
  have hu : (0 : ℝ) < 1 + x ^ 2 := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1 + x ^ 2) ^ 2 = 1 + x ^ 2 := Real.sq_sqrt hu.le
  have hs : HasDerivAt (fun t : ℝ => Real.sqrt (1 + t ^ 2))
      (x / Real.sqrt (1 + x ^ 2)) x := by
    have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have hsq : HasDerivAt (fun t : ℝ => 1 + t ^ 2) (2 * x) x := by
      have h := hp.const_add (1 : ℝ)
      simpa using h
    have h := hsq.sqrt hu.ne'
    have hv : 2 * x / (2 * Real.sqrt (1 + x ^ 2)) = x / Real.sqrt (1 + x ^ 2) := by
      field_simp
    rwa [hv] at h
  have hdiv : HasDerivAt (fun t : ℝ => t / Real.sqrt (1 + t ^ 2))
      ((1 * Real.sqrt (1 + x ^ 2) - x * (x / Real.sqrt (1 + x ^ 2)))
        / Real.sqrt (1 + x ^ 2) ^ 2) x :=
    (hasDerivAt_id x).div hs hspos.ne'
  have h := (hasDerivAt_id x).sub (hdiv.const_mul d)
  have hval : (1 - d * ((1 * Real.sqrt (1 + x ^ 2)
        - x * (x / Real.sqrt (1 + x ^ 2))) / Real.sqrt (1 + x ^ 2) ^ 2))
      = 1 - d / Real.sqrt (1 + x ^ 2) ^ 3 := by
    have hs3 : Real.sqrt (1 + x ^ 2) ^ 3
        = Real.sqrt (1 + x ^ 2) * (1 + x ^ 2) := by
      rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hs2]
      ring
    field_simp
    rw [hs3]
    have hx2 : Real.sqrt (1 + x ^ 2) ^ 2 - x ^ 2 = 1 := by linarith [hs2]
    rw [hx2]
    ring
  rw [hval] at h
  exact h

-- Theorem: the derivative of the offset abscissa is positive for `d < 1`.
theorem offsetAbscissa_deriv_pos {d x : ℝ} (hd1 : d < 1) :
    0 < 1 - d / Real.sqrt (1 + x ^ 2) ^ 3 := by
  have hspos : (0 : ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  have hs3 : (1 : ℝ) ≤ Real.sqrt (1 + x ^ 2) ^ 3 := by
    have hs1 : (1 : ℝ) ≤ Real.sqrt (1 + x ^ 2) := by
      rw [Real.one_le_sqrt]
      nlinarith [sq_nonneg x]
    calc (1 : ℝ) = 1 ^ 3 := by norm_num
      _ ≤ Real.sqrt (1 + x ^ 2) ^ 3 := by gcongr
  rcases le_total d 0 with hd0 | hd0
  · have hle : d / Real.sqrt (1 + x ^ 2) ^ 3 ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hd0 (by positivity)
    linarith
  · have hlt : d / Real.sqrt (1 + x ^ 2) ^ 3 < 1 := by
      rw [div_lt_one (by positivity)]
      exact lt_of_lt_of_le hd1 hs3
    linarith

-- Theorem: the offset abscissa is strictly increasing on `[0, w]` when `d < 1`.
theorem strictMonoOn_offsetParam_halfParabola_fst {d w : ℝ} (hd1 : d < 1) :
    StrictMonoOn (fun t => (offsetParam halfParabolaParam d t).1) (Set.Icc 0 w) := by
  have hfun : (fun t => (offsetParam halfParabolaParam d t).1)
      = fun t : ℝ => t - d * (t / Real.sqrt (1 + t ^ 2)) :=
    funext (offsetParam_halfParabola_fst d)
  rw [hfun]
  refine strictMonoOn_of_deriv_pos (convex_Icc _ _) ?_ ?_
  · -- continuity of the offset abscissa
    have hcont : Continuous (fun t : ℝ => t - d * (t / Real.sqrt (1 + t ^ 2))) := by
      have hden : ∀ t : ℝ, Real.sqrt (1 + t ^ 2) ≠ 0 :=
        fun t => (Real.sqrt_pos.mpr (by positivity)).ne'
      exact continuous_id.sub
        (continuous_const.mul (continuous_id.div (by fun_prop) hden))
    exact hcont.continuousOn
  · -- the derivative is positive off the endpoints
    intro x _
    rw [(hasDerivAt_offsetAbscissa d x).deriv]
    exact offsetAbscissa_deriv_pos hd1

-- Theorem: the offset abscissa is nondecreasing on `[0, w]` when `d < 1`.
theorem monotoneOn_offsetParam_halfParabola_fst {d w : ℝ} (hd1 : d < 1) :
    MonotoneOn (fun t => (offsetParam halfParabolaParam d t).1) (Set.Icc 0 w) :=
  (strictMonoOn_offsetParam_halfParabola_fst (d := d) (w := w) hd1).monotoneOn

/-! ### Bounding the inversion parameter

To lay an arc of length `x` along the *offset* curve we first need an offset arc long
enough to contain it: a P-constructible window `[0, W]` with `w ≤ W`. The bound comes from
the length identity and the elementary inequalities `arctan w ≤ w ≤ antiderivative w`, so
it uses only `x` and `d` — never `w` itself. -/

-- Theorem: `arctan w ≤ w` for `w ≥ 0`.
theorem arctan_le_self {w : ℝ} (hw : 0 ≤ w) : Real.arctan w ≤ w := by
  have hmono : MonotoneOn (fun t : ℝ => t - Real.arctan t) (Set.Icc 0 w) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (continuous_id.sub Real.continuous_arctan).continuousOn
    · intro x _
      exact (differentiableAt_id.sub (Real.differentiableAt_arctan x)).differentiableWithinAt
    · intro x _
      have hderiv : HasDerivAt (fun t : ℝ => t - Real.arctan t)
          (1 - 1 / (1 + x ^ 2)) x :=
        (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x)
      rw [hderiv.deriv]
      have hle : 1 / (1 + x ^ 2) ≤ 1 := by
        rw [div_le_one (by positivity)]
        nlinarith [sq_nonneg x]
      linarith
  have h0 : (0 : ℝ) - Real.arctan 0 ≤ w - Real.arctan w :=
    hmono ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw
  simpa using h0

-- Theorem: `w` is at most the half-parabola's arc-length antiderivative at `w`.
theorem self_le_halfParabolaAntideriv {w : ℝ} (hw : 0 ≤ w) :
    w ≤ halfParabolaAntideriv w := by
  have hmono : MonotoneOn (fun t : ℝ => halfParabolaAntideriv t - t) (Set.Icc 0 w) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · have hcont : Continuous halfParabolaAntideriv :=
        continuous_iff_continuousAt.mpr
          fun x => (hasDerivAt_halfParabolaAntideriv x).continuousAt
      exact (hcont.sub continuous_id).continuousOn
    · intro x _
      exact ((hasDerivAt_halfParabolaAntideriv x).differentiableAt.sub
        differentiableAt_id).differentiableWithinAt
    · intro x _
      have hderiv : HasDerivAt (fun t : ℝ => halfParabolaAntideriv t - t)
          (Real.sqrt (1 + x ^ 2) - 1) x :=
        (hasDerivAt_halfParabolaAntideriv x).sub (hasDerivAt_id x)
      rw [hderiv.deriv]
      have h1 : (1 : ℝ) ≤ Real.sqrt (1 + x ^ 2) := by
        rw [Real.one_le_sqrt]
        nlinarith [sq_nonneg x]
      linarith
  have h0 : halfParabolaAntideriv 0 - 0 ≤ halfParabolaAntideriv w - w :=
    hmono ⟨le_rfl, hw⟩ ⟨hw, le_rfl⟩ hw
  have hz : halfParabolaAntideriv 0 = 0 := by
    unfold halfParabolaAntideriv
    simp
  linarith

-- Theorem: the arc length of the offset of the half-parabola over `[0, w]` is
-- `(w√(1+w²) + arsinh w)/2 - d·arctan w`. This is `arcLengthOf_offsetParam` with the
-- tangent angle `ψ = arctan`, which is legitimate on the cusp-free window `d < 1`.
theorem arcLengthOf_offsetParam_halfParabola {d w : ℝ} (hd1 : d < 1) (hw : 0 ≤ w) :
    arcLengthOf (offsetParam halfParabolaParam d) 0 w
      = (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2 - d * Real.arctan w := by
  have hC2 : ∀ t ∈ Set.Icc 0 w,
      DifferentiableAt ℝ (deriv (fun s => (halfParabolaParam s).1)) t ∧
        DifferentiableAt ℝ (deriv (fun s => (halfParabolaParam s).2)) t := by
    intro t _
    have h1 : deriv (fun s => (halfParabolaParam s).1) = fun _ => (1 : ℝ) :=
      funext deriv_halfParabolaParam_fst
    have h2 : deriv (fun s => (halfParabolaParam s).2) = fun s => s :=
      funext deriv_halfParabolaParam_snd
    constructor
    · rw [h1]
      exact differentiableAt_const 1
    · rw [h2]
      exact differentiableAt_id
  have hψ : ∀ t ∈ Set.Icc 0 w,
      HasDerivAt Real.arctan (curvature halfParabolaParam t
        * speed halfParabolaParam t) t := by
    intro t _
    simpa [curvature_halfParabola_mul_speed] using Real.hasDerivAt_arctan t
  have hint : IntervalIntegrable (speed halfParabolaParam) MeasureTheory.volume 0 w := by
    have hcont : Continuous (speed halfParabolaParam) := by
      have h : speed halfParabolaParam = fun t => Real.sqrt (1 + t ^ 2) :=
        funext speed_halfParabolaParam
      rw [h]
      fun_prop
    exact hcont.intervalIntegrable 0 w
  have hintψ : IntervalIntegrable
      (fun t => curvature halfParabolaParam t * speed halfParabolaParam t)
      MeasureTheory.volume 0 w := by
    have hcont : Continuous
        (fun t => curvature halfParabolaParam t * speed halfParabolaParam t) := by
      have h : (fun t => curvature halfParabolaParam t * speed halfParabolaParam t)
          = fun t => 1 / (1 + t ^ 2) := funext curvature_halfParabola_mul_speed
      rw [h]
      exact continuous_const.div (by fun_prop) (fun t => by positivity)
    exact hcont.intervalIntegrable 0 w
  have h := arcLengthOf_offsetParam (γ := halfParabolaParam) (ψ := Real.arctan)
    (a := 0) (b := w) (d := d) hw
    (fun t _ => differentiableAt_halfParabolaParam t)
    (fun t _ => speed_halfParabolaParam_ne_zero t)
    hC2
    (fun t _ => one_sub_mul_curvature_halfParabola_pos hd1)
    hψ hint hintψ
  rw [h, arcLengthOf_halfParabolaParam_zero]
  simp

-- Theorem: a P-constructible upper bound for the inversion parameter `w`, built from
-- `x` and `d` alone.
theorem halfParabolaOffsetWindow_exists {d x w : ℝ} (hd : PConstructible d)
    (hx : PConstructible x) (hd1 : d < 1) (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) :
    ∃ W : ℝ, PConstructible W ∧ 0 < W ∧ w ≤ W := by
  have hlen := arcLengthOf_offsetParam_halfParabola (d := d) (w := w) hd1 hw
  have hbase : w ≤ (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2 := by
    have h := self_le_halfParabolaAntideriv hw
    simpa [halfParabolaAntideriv] using h
  have harctan : Real.arctan w ≤ w := arctan_le_self hw
  have harctan0 : 0 ≤ Real.arctan w := Real.arctan_nonneg.mpr hw
  rcases le_total d 0 with hd0 | hd0
  · have hx_ge : w ≤ x := by
      rw [← hweq, ← hlen]
      have hnonneg : 0 ≤ -d * Real.arctan w := by
        have hnonpos : d * Real.arctan w ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg hd0 harctan0
        linarith
      nlinarith [hbase, hnonneg]
    refine ⟨x + 1, ?_, by linarith, by linarith⟩
    exact PConstructible.add hx PConstructible.base_one
  · have h1d : 0 < 1 - d := by linarith
    have hlow : (1 - d) * w ≤ x := by
      rw [← hweq, ← hlen]
      have hdarc : d * Real.arctan w ≤ d * w :=
        mul_le_mul_of_nonneg_left harctan hd0
      nlinarith [hbase, hdarc]
    refine ⟨x / (1 - d) + 1, ?_, ?_, ?_⟩
    · exact (by pconstructible : PConstructible (x / (1 - d) + 1))
    · have hx_nonneg : 0 ≤ x := by
        have : 0 ≤ (1 - d) * w := mul_nonneg h1d.le hw
        linarith
      have : 0 ≤ x / (1 - d) := div_nonneg hx_nonneg h1d.le
      linarith
    · have hwx : w ≤ x / (1 - d) := by
        rw [le_div_iff₀ h1d]
        linarith
      linarith

-- Theorem: the far endpoint of the offset of the half-parabola is P-constructible,
-- provided the offset arc over `[0, w]` is contained in a P-constructible one.
theorem halfParabolaOffsetEndpoint_of_le {d x w W : ℝ}
    (hd : PConstructible d) (hx : PConstructible x) (hd1 : d < 1) (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x)
    (hwW : w ≤ W) (hW : PConstructible W) (hW0 : 0 < W) :
    PConstructible (offsetParam halfParabolaParam d w).1 := by
  have hlen : arcLengthOf (offsetParam halfParabolaParam d) 0 w = x := by
    rw [arcLengthOf_offsetParam_halfParabola hd1 hw, ← hweq]
  have hS := halfParabolaOffsetArc_PConstructibleCurve (d := d) (W := W) hd hW hW0
  have hsub : offsetParam halfParabolaParam d '' Set.Icc 0 w ⊆
      offsetParam halfParabolaParam d '' Set.Icc 0 W :=
    Set.image_mono (Set.Icc_subset_Icc le_rfl hwW)
  have hinj : Set.InjOn (offsetParam halfParabolaParam d) (Set.Icc 0 w) := by
    intro a ha b hb hab
    exact (strictMonoOn_offsetParam_halfParabola_fst (d := d) (w := w) hd1).injOn ha hb
      (congrArg Prod.fst hab)
  have hdiff : ∀ t ∈ Set.Icc 0 w,
      DifferentiableAt ℝ (fun s => (offsetParam halfParabolaParam d s).1) t ∧
        DifferentiableAt ℝ (fun s => (offsetParam halfParabolaParam d s).2) t :=
    fun t _ => differentiableAt_offsetParam_halfParabola d t
  have hx₀ : PConstructible (offsetParam halfParabolaParam d 0).1 := by
    have h : (offsetParam halfParabolaParam d 0).1 = 0 := by
      rw [offsetParam_halfParabola_fst]
      norm_num
    rw [h]
    exact zero_Pconstructible
  have hy₀ : PConstructible (offsetParam halfParabolaParam d 0).2 := by
    have h : (offsetParam halfParabolaParam d 0).2 = d := by
      rw [offsetParam_halfParabola_snd]
      norm_num
    rw [h]
    exact hd
  exact arcLength_xendpoint_Pconstructible hS (offsetParam halfParabolaParam d) hw hsub hinj
    hdiff ((continuous_speed_offsetParam_halfParabola d).intervalIntegrable 0 w) hx₀ hy₀ hx hlen
    (Or.inl (strictMonoOn_offsetParam_halfParabola_fst (d := d) (w := w) hd1).monotoneOn)

-- Theorem: the far endpoint's abscissa of the offset of the half-parabola over `[0, w]`
-- is P-constructible. The arc of length `x` is laid *on the offset curve* by
-- `arc_of_length` (through `arcLength_xendpoint_Pconstructible`), and the box reads its
-- endpoint. The window `[0, W]` that contains it is built from `x` and `d` alone.
theorem halfParabolaOffsetEndpoint_Pconstructible {d x w : ℝ}
    (hd : PConstructible d) (hx : PConstructible x) (hd1 : d < 1) (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) :
    PConstructible (offsetParam halfParabolaParam d w).1 := by
  obtain ⟨W, hW, hW0, hwW⟩ := halfParabolaOffsetWindow_exists hd hx hd1 hw hweq
  exact halfParabolaOffsetEndpoint_of_le hd hx hd1 hw hweq hwW hW hW0

/-! ### The quartic

Squaring the defining relation `e = w - d w/s` (equivalently `s (w - e) = d w`, whose two
sides always share the sign of `d`) and using `s ^ 2 = 1 + w ^ 2` gives

    `(w - e) ^ 2 (1 + w ^ 2) = d ^ 2 w ^ 2`,

which expands to (L2.2). With `e` and `d` constructible, every coefficient is, and the
leading coefficient is `1`, so `powerLaw_cubic_root_Pconstructible` closes. -/

-- Theorem: the offset parameter and the offset abscissa satisfy the squared relation
-- `(w - e)² (1 + w²) = d² w²`.
theorem halfParabola_offset_identity {d w : ℝ} :
    (w - (offsetParam halfParabolaParam d w).1) ^ 2 * (1 + w ^ 2) = d ^ 2 * w ^ 2 := by
  have hu : (0 : ℝ) < 1 + w ^ 2 := by positivity
  have hs : Real.sqrt (1 + w ^ 2) ≠ 0 := (Real.sqrt_pos.mpr hu).ne'
  have hs2 : Real.sqrt (1 + w ^ 2) ^ 2 = 1 + w ^ 2 := Real.sq_sqrt hu.le
  have hdiff : w - (offsetParam halfParabolaParam d w).1
      = d * (w / Real.sqrt (1 + w ^ 2)) := by
    rw [offsetParam_halfParabola_fst]
    ring
  have hcancel : (w / Real.sqrt (1 + w ^ 2)) ^ 2 * Real.sqrt (1 + w ^ 2) ^ 2 = w ^ 2 := by
    field_simp
  rw [hdiff]
  calc (d * (w / Real.sqrt (1 + w ^ 2))) ^ 2 * (1 + w ^ 2)
      = (d * (w / Real.sqrt (1 + w ^ 2))) ^ 2 * Real.sqrt (1 + w ^ 2) ^ 2 := by
        rw [hs2]
    _ = d ^ 2 * ((w / Real.sqrt (1 + w ^ 2)) ^ 2 * Real.sqrt (1 + w ^ 2) ^ 2) := by
        ring
    _ = d ^ 2 * w ^ 2 := by rw [hcancel]

-- Theorem: the offset parameter `w ≥ 0` satisfies the quartic (L2.2), so it is
-- P-constructible when `d < 1` is. The quartic is read as `w ^ 4 = (cubic in w)` and
-- closed by the power curve `y = x ^ 4` meeting that cubic graph.
theorem halfParabolaOffset_w_Pconstructible {d x w : ℝ} (hd : PConstructible d)
    (hx : PConstructible x) (hd1 : d < 1) (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) : PConstructible w := by
  set e : ℝ := (offsetParam halfParabolaParam d w).1 with hedef
  have he : PConstructible e :=
    halfParabolaOffsetEndpoint_Pconstructible hd hx hd1 hw hweq
  -- The quartic in the form taken by `quartic_eq_cubicVal`.
  have hval : e ^ 2 + (-2 * e) * w + (1 + e ^ 2 - d ^ 2) * w ^ 2 + (-2 * e) * w ^ 3
      + 1 * w ^ 4 = 0 := by
    have h : (w - e) ^ 2 * (1 + w ^ 2) = d ^ 2 * w ^ 2 := by
      simpa [hedef] using halfParabola_offset_identity (d := d) (w := w)
    nlinarith [h]
  refine powerLaw_cubic_root_Pconstructible (n := 4) (by norm_num) ?_ ?_ ?_ ?_
    (quartic_eq_cubicVal (a₄ := 1) (by norm_num) hval)
  · -- `-e²`
    exact (by pconstructible : PConstructible ((-(e ^ 2)) / 1))
  · -- `2e`
    exact (by pconstructible : PConstructible ((-(-2 * e)) / 1))
  · -- `-(1 + e² - d²)`
    exact (by pconstructible : PConstructible ((-(1 + e ^ 2 - d ^ 2)) / 1))
  · -- `2e`
    exact (by pconstructible : PConstructible ((-(-2 * e)) / 1))

-- Theorem: (parabola offset inversion) For P-constructible `d < 1` and `x ≥ 0`, any
-- `w ≥ 0` with `(w√(1+w²) + arsinh w)/2 - d·arctan w = x` is P-constructible.
--
-- The equation is the arc-length readout of the offset stroke: `(w√(1+w²) + arsinh w)/2`
-- is the arc length of the half-parabola from its vertex (`arcLengthOf_halfParabolaParam_zero`)
-- and `d·arctan w` is the `d`-multiple of its total turning, so the left side is
-- `arcLengthOf (offsetParam γ d) 0 w` by `arcLengthOf_offsetParam`. The proof uses exactly
-- that: the P-constructible length `x` is laid on the offset curve with `arc_of_length`, the
-- box reads the endpoint, and the quartic gives `w`.
theorem parabola_offset_root_Pconstructible {d x w : ℝ}
    (hd : PConstructible d) (hx : PConstructible x) (hd1 : d < 1)
    (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) :
    PConstructible w :=
  halfParabolaOffset_w_Pconstructible hd hx hd1 hw hweq

/-! ### The arc-length corollary

`arsinh` has no closure rule of its own in `Basic` because it is `log (w + √(1 + w²))`, and
`log` is already reachable from the arc length of the standard parabola
(`Basic.log_Pconstructible`). Under the headline's hypotheses the turning term of the offset
stroke is therefore constructible too, since its parameter is. -/

-- Theorem: `arsinh` of a P-constructible number is P-constructible, via
-- `arsinh w = log (w + √(1 + w²))` and the logarithm closure.
theorem arsinh_Pconstructible {w : ℝ} (hw : PConstructible w) :
    PConstructible (Real.arsinh w) := by
  have hpos : (0 : ℝ) < w + Real.sqrt (1 + w ^ 2) := by
    rw [← neg_lt_iff_pos_add']
    exact Real.lt_sqrt_of_sq_lt (by nlinarith [sq_nonneg w])
  unfold Real.arsinh
  exact log_Pconstructible (by pconstructible) hpos

-- Theorem: under the hypotheses of the parabola offset inversion, the turning term
-- `arsinh w` of the offset stroke is P-constructible as well.
theorem parabola_offset_arsinh_Pconstructible {d x w : ℝ}
    (hd : PConstructible d) (hx : PConstructible x) (hd1 : d < 1)
    (hw : 0 ≤ w)
    (hweq : (w * Real.sqrt (1 + w ^ 2) + Real.arsinh w) / 2
      - d * Real.arctan w = x) :
    PConstructible (Real.arsinh w) :=
  arsinh_Pconstructible (parabola_offset_root_Pconstructible hd hx hd1 hw hweq)

end Pconstructible
