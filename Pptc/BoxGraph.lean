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
-- `Pptc.Basic` pulls in `Pptc.Box` (the box endpoints) and `Pptc.Defs`, and carries the
-- interval-integral calculus used here.
import Pptc.Basic

/-! # Pptc.BoxGraph

Graph tracings have speed at least `1`, so arc length is a surjection onto `[0, ∞)`; the far
endpoint of an `arc_of_length` stroke is recovered by the box, so every drawable graph can be
inverted at constructible lengths.

The graph tracing `t ↦ (t, f t)` has `speed = √(1 + f'(t)²) ≥ 1`, so its arc-length
function

    F X = arcLengthOf γ a (a + X)

is `C¹` with derivative at least `1` and `F 0 = 0`; by `surjective_of_hasDerivAt_ge` it is a
surjection of the line onto `[0, ∞)`. Hence every P-constructible length `L ≥ 0` is the
length of a graph arc from `a` to some `b ≥ a`. Feeding that arc to the bounding-box endpoint
extractor (`arc_xendpoint_Pconstructible`) recovers `b` as P-constructible — so every
drawable graph can be inverted at constructible lengths, with no monotonicity hypothesis on
`f` at all. -/

open MeasureTheory

namespace Pconstructible

-- Theorem: the speed of a graph tracing `t ↦ (t, f t)` is `√(1 + f'(t)²)`: its abscissa
-- has derivative `1` and its ordinate has derivative `f'(t)`.
theorem speed_graph (f : ℝ → ℝ) (t : ℝ) :
    speed (fun s : ℝ => (s, f s)) t = Real.sqrt (1 + deriv f t ^ 2) := by
  simp [speed]

/-! ### Inverting the arc length of a graph tracing

Graph tracings have speed at least `1`, so arc length is a surjection onto `[0, ∞)`; the far
endpoint of an `arc_of_length` stroke is recovered by the box, so every drawable graph can be
inverted at constructible lengths. -/

-- Theorem: if a graph tracing of a constructible curve runs from P-constructible `(a, f a)`
-- for a P-constructible length `L`, its far abscissa `b ≥ a` is P-constructible. This is the
-- `arc_of_length` + box step, with the monotonicity side condition free because the tracing's
-- abscissa is the identity.
private lemma graph_xendpoint_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (f : ℝ → ℝ) (hmem : ∀ t : ℝ, (t, f t) ∈ S)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ f t) (hC1 : Continuous (deriv f))
    {a : ℝ} (ha : PConstructible a) (hfa : PConstructible (f a))
    {L : ℝ} (hL : PConstructible L) {b : ℝ} (hab : a ≤ b)
    (hlen : arcLengthOf (fun t : ℝ => (t, f t)) a b = L) :
    PConstructible b := by
  let γ : ℝ → ℝ × ℝ := fun t => (t, f t)
  have hγ_fst : ∀ t : ℝ, (γ t).1 = t := fun _ => rfl
  have hγ_snd : ∀ t : ℝ, (γ t).2 = f t := fun _ => rfl
  -- The tracing is continuous, hence so is its speed.
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hdiff t).continuousAt
  have hγcont : Continuous γ := continuous_id.prodMk hfcont
  have hspeed_eq : speed γ = fun t => Real.sqrt (1 + deriv f t ^ 2) := by
    funext t
    exact speed_graph f t
  have hscont : Continuous (speed γ) := by
    rw [hspeed_eq]
    exact Real.continuous_sqrt.comp (continuous_const.add (hC1.pow 2))
  -- The arc from `a` to `b` is an `arc_of_length` stroke; its far endpoint is a box edge.
  have hsub : γ '' Set.Icc a b ⊆ S := by
    rintro _ ⟨t, -, rfl⟩
    exact hmem t
  have hinj : Set.InjOn γ (Set.Icc a b) := by
    intro t₁ _ t₂ _ h
    simpa only [hγ_fst] using congrArg Prod.fst h
  have hdiffb : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t :=
    fun t _ => ⟨differentiableAt_id, hdiff t⟩
  have hInt : IntervalIntegrable (speed γ) volume a b := hscont.intervalIntegrable a b
  have hx₀ : PConstructible (γ a).1 := by rw [hγ_fst]; exact ha
  have hy₀ : PConstructible (γ a).2 := by rw [hγ_snd]; exact hfa
  have hA : PConstructibleCurve (γ '' Set.Icc a b) :=
    PConstructibleCurve.arc_of_length hS γ hab hsub hinj hdiffb hInt hx₀ hy₀ hL hlen
  have hcontOn : ContinuousOn γ (Set.Icc a b) := hγcont.continuousOn
  have hmono : MonotoneOn (fun t => (γ t).1) (Set.Icc a b) :=
    fun _ _ _ _ h => by simpa only [hγ_fst] using h
  simpa only [hγ_fst] using arc_xendpoint_Pconstructible hA hab hcontOn hmono

-- Theorem: supplied-`b` form of `graphArcLength_inverse_Pconstructible`: if the graph arc
-- from `a` to `b` has the P-constructible length `L`, then `b` is P-constructible.
theorem graphArcLength_endpoint_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (f : ℝ → ℝ) (hmem : ∀ t : ℝ, (t, f t) ∈ S)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ f t) (hC1 : Continuous (deriv f))
    {a : ℝ} (ha : PConstructible a) (hfa : PConstructible (f a))
    {L : ℝ} (hL : PConstructible L) {b : ℝ} (hab : a ≤ b)
    (hlen : arcLengthOf (fun t : ℝ => (t, f t)) a b = L) :
    PConstructible b :=
  graph_xendpoint_Pconstructible hS f hmem hdiff hC1 ha hfa hL hab hlen

-- Theorem: for a tracing `t ↦ (t, f t)` of a constructible curve whose speed is at least 1,
-- any P-constructible length `L ≥ 0` is laid from a P-constructible start `(a, f a)` at a
-- P-constructible abscissa `b ≥ a`.
theorem graphArcLength_inverse_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (f : ℝ → ℝ) (hmem : ∀ t : ℝ, (t, f t) ∈ S)
    (hdiff : ∀ t : ℝ, DifferentiableAt ℝ f t) (hC1 : Continuous (deriv f))
    {a : ℝ} (ha : PConstructible a) (hfa : PConstructible (f a))
    {L : ℝ} (hL : PConstructible L) (hL0 : 0 ≤ L) :
    ∃ b : ℝ, a ≤ b ∧ arcLengthOf (fun t : ℝ => (t, f t)) a b = L ∧ PConstructible b := by
  let γ : ℝ → ℝ × ℝ := fun t => (t, f t)
  have hγ_fst : ∀ t : ℝ, (γ t).1 = t := fun _ => rfl
  -- The tracing's speed is continuous ...
  have hfcont : Continuous f := continuous_iff_continuousAt.mpr fun t => (hdiff t).continuousAt
  have hspeed_eq : speed γ = fun t => Real.sqrt (1 + deriv f t ^ 2) := by
    funext t
    exact speed_graph f t
  have hscont : Continuous (speed γ) := by
    rw [hspeed_eq]
    exact Real.continuous_sqrt.comp (continuous_const.add (hC1.pow 2))
  -- ... and at least `1`, so `F X = arcLengthOf γ a (a + X)` has derivative `≥ 1` and `F 0 = 0`.
  have hF : ∀ X : ℝ, HasDerivAt (fun X => arcLengthOf γ a (a + X)) (speed γ (a + X)) X := by
    intro X
    have hbase : HasDerivAt (fun u => ∫ t in a..u, speed γ t) (speed γ (a + X)) (a + X) :=
      intervalIntegral.integral_hasDerivAt_right (hscont.intervalIntegrable a (a + X))
        (hscont.stronglyMeasurableAtFilter volume (nhds (a + X))) hscont.continuousAt
    have hinner : HasDerivAt (fun X : ℝ => a + X) 1 X :=
      HasDerivAt.comp_const_add a X (hasDerivAt_id (a + X))
    simpa only [arcLengthOf, Function.comp_def, mul_one] using hbase.comp X hinner
  have hF0 : (fun X => arcLengthOf γ a (a + X)) 0 = 0 := by
    simp [arcLengthOf]
  have hspeed1 : ∀ X : ℝ, 1 ≤ speed γ (a + X) := by
    intro X
    rw [hspeed_eq]
    exact Real.le_sqrt_of_sq_le (by nlinarith [sq_nonneg (deriv f (a + X))])
  -- Surjectivity onto the line, then `X ≥ 0` because `F` is strictly increasing.
  have hsurj : Function.Surjective (fun X => arcLengthOf γ a (a + X)) :=
    surjective_of_hasDerivAt_ge one_pos hF hspeed1 hF0
  obtain ⟨X, hX⟩ := hsurj L
  have hmonoF : StrictMono (fun X => arcLengthOf γ a (a + X)) :=
    strictMono_of_hasDerivAt_pos hF fun θ => lt_of_lt_of_le one_pos (hspeed1 θ)
  have hX0 : 0 ≤ X := hmonoF.le_iff_le.mp (by simpa only [hF0, hX] using hL0)
  have hab : a ≤ a + X := by linarith
  exact ⟨a + X, hab, hX, graph_xendpoint_Pconstructible hS f hmem hdiff hC1 ha hfa hL hab hX⟩

/-! ### N2 and N4: inverting the parabola, cubic and quartic arc lengths

`PConstructible.arc_length` evaluated the parabola's arc-length function forward, which is
how the drawing program reaches `log` (see `Basic.lean`). B8 runs that same function
backwards at new constructible lengths: `1/2` on `y = x²` (N2), and `1` on each of `y = x³`
and `y = x⁴` (N4). For `y = x⁴` the inverse of arc length is hyperelliptic — a genus-2
problem, outside everything the elliptic machinery of `ThirdKind` and `Jacobi` covers — yet
the box still recovers it, which is precisely the point of N4. -/

-- Lemma: for each monomial `t ^ n` whose graph `poly_graph` draws, B8 inverts its arc length
-- from the origin at any P-constructible length `L ≥ 0`. This discharges the graph hypotheses
-- once, so the three witnesses below stay a few lines each.
private lemma monomialArc_exists (n : ℕ)
    (hdeg : (Polynomial.X ^ n : Polynomial ℚ).natDegree ≤ 6)
    (L : ℝ) (hL : PConstructible L) (hL0 : 0 ≤ L) :
    ∃ b : ℝ, 0 ≤ b ∧ arcLengthOf (fun t : ℝ => (t, t ^ n)) 0 b = L ∧ PConstructible b := by
  have hmem : ∀ t : ℝ, (t, t ^ n) ∈
      {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 ((Polynomial.X : Polynomial ℚ) ^ n)} :=
    fun _ => by simp [Polynomial.aeval_X_pow]
  have hdiff : ∀ t : ℝ, DifferentiableAt ℝ (fun t : ℝ => t ^ n) t := fun _ =>
    differentiableAt_id.pow n
  have hC1 : Continuous (deriv fun t : ℝ => t ^ n) := by
    have hd : deriv (fun t : ℝ => t ^ n) = fun t => (n : ℝ) * t ^ (n - 1) :=
      funext fun t => deriv_pow_field n
    rw [hd]
    fun_prop
  have hfa : PConstructible ((fun t : ℝ => t ^ n) 0) := by
    by_cases hn : n = 0
    · subst hn
      simpa using PConstructible.base_one
    · simpa [zero_pow hn] using zero_Pconstructible
  exact graphArcLength_inverse_Pconstructible
    (PConstructibleCurve.poly_graph (Polynomial.X ^ n) hdeg)
    (fun t : ℝ => t ^ n) hmem hdiff hC1 zero_Pconstructible hfa hL hL0

-- Theorem: the abscissa `b` with `arcLengthOf (fun t => (t, t²)) 0 b = 1/2` (N2). Its value
-- is `0.44633388551759072893813142528262481720135752704286437386727212215…` `[NC 50]`.
noncomputable def parabolaHalfArcAbscissa : ℝ :=
  (monomialArc_exists 2 (by simp) (1 / 2) (by pconstructible) (by norm_num)).choose

-- Theorem: `parabolaHalfArcAbscissa` is `≥ 0`, satisfies the half-arc-length equation, and
-- is P-constructible.
theorem parabolaHalfArcAbscissa_spec :
    0 ≤ parabolaHalfArcAbscissa ∧
      arcLengthOf (fun t : ℝ => (t, t ^ 2)) 0 parabolaHalfArcAbscissa = 1 / 2 ∧
      PConstructible parabolaHalfArcAbscissa :=
  (monomialArc_exists 2 (by simp) (1 / 2) (by pconstructible) (by norm_num)).choose_spec

-- Theorem: the half-unit parabola arc abscissa is P-constructible.
theorem parabolaHalfArcAbscissa_Pconstructible : PConstructible parabolaHalfArcAbscissa :=
  parabolaHalfArcAbscissa_spec.2.2

-- Theorem: the abscissa `b` with `arcLengthOf (fun t => (t, t³)) 0 b = 1` (N4). Its value is
-- `0.790706893627604843078476035616…` `[NC 45]`.
noncomputable def cubicUnitArcAbscissa : ℝ :=
  (monomialArc_exists 3 (by simp) 1 PConstructible.base_one (by norm_num)).choose

-- Theorem: `cubicUnitArcAbscissa` is `≥ 0`, satisfies the unit-arc-length equation, and is
-- P-constructible.
theorem cubicUnitArcAbscissa_spec :
    0 ≤ cubicUnitArcAbscissa ∧
      arcLengthOf (fun t : ℝ => (t, t ^ 3)) 0 cubicUnitArcAbscissa = 1 ∧
      PConstructible cubicUnitArcAbscissa :=
  (monomialArc_exists 3 (by simp) 1 PConstructible.base_one (by norm_num)).choose_spec

-- Theorem: the unit cubic arc abscissa is P-constructible.
theorem cubicUnitArcAbscissa_Pconstructible : PConstructible cubicUnitArcAbscissa :=
  cubicUnitArcAbscissa_spec.2.2

-- Theorem: the abscissa `b` with `arcLengthOf (fun t => (t, t⁴)) 0 b = 1` (N4). Its value is
-- `0.810451620058442235121609068479…` `[NC 45]`; this inverse is genus 2.
noncomputable def quarticUnitArcAbscissa : ℝ :=
  (monomialArc_exists 4 (by simp) 1 PConstructible.base_one (by norm_num)).choose

-- Theorem: `quarticUnitArcAbscissa` is `≥ 0`, satisfies the unit-arc-length equation, and is
-- P-constructible.
theorem quarticUnitArcAbscissa_spec :
    0 ≤ quarticUnitArcAbscissa ∧
      arcLengthOf (fun t : ℝ => (t, t ^ 4)) 0 quarticUnitArcAbscissa = 1 ∧
      PConstructible quarticUnitArcAbscissa :=
  (monomialArc_exists 4 (by simp) 1 PConstructible.base_one (by norm_num)).choose_spec

-- Theorem: the unit quartic arc abscissa (the genus-2 inversion) is P-constructible.
theorem quarticUnitArcAbscissa_Pconstructible : PConstructible quarticUnitArcAbscissa :=
  quarticUnitArcAbscissa_spec.2.2

end Pconstructible
