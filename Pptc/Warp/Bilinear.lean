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

/-! # Pptc.Warp.Bilinear

Text warps (Shape Format ▸ Text Effects ▸ Transform) and what they do to glyph outlines,
for the presets whose guides are straight.

## The warp law

Every Transform preset is defined in ECMA-376 (`presetTextWarpDefinitions.xml`) by a pair of
*guide paths*, a top one `T` and a bottom one `B`. PowerPoint normalizes each glyph point by
the ink box of the whole text, `u` left to right and `v` top to bottom, and sends it to

  `F (u, v) = (1 - v) • T (u) + v • B (u)`,

where **each guide is traced at constant speed** (by arc length) over `u ∈ [0, 1]`. The probes
in `notes/warp/probes/` establish this for all 36 presets that bend glyphs: corners agree to
≤ 0.5 pt on a 288 pt box (most to 0.00–0.1 pt), and the Bézier-parameter alternative is off by
up to 20 pt wherever the two differ. The four "Follow Path" presets are not warps at all:
they move each glyph rigidly (0.000 pt residual), so they add nothing.

This file is `ruledWarp` and its straight-guide case. When both guides are single segments,
the map is the **bilinear cell** `P + u A + v B + u v C`. The polygonal presets (Plain, Stop,
Triangle, Chevron, Fade, Slant, Cascade) are finitely many such cells side by side.

## What a bilinear cell does to glyph primitives

* A straight glyph edge becomes a quadratic arc, which is a cubic Bézier with
  degree-elevated control points (`bilinearCell_segment_PConstructibleCurve`). **Nothing new**:
  the straight half of a polygonal warp is already in the class.
* An idealized glyph circle becomes a rational quartic, the "egg" `eggCurve`
  (`heightCell_image_glyphCircle`). When the cell is pinched to zero height at the circle's
  tangent line (Triangle with its handle at the stop), the egg degenerates to a sheared
  **piriform** (pear curve) `a² y² = x³ (2a − x)` (`piriform_eq_image`).

Constructibility of the curved images is not claimed outright: the warp is not a constructor
of `PConstructibleCurve`. It is stated as a hypothesis `TriangleCircleRule`, the proposed
rule restricted to one preset and to circle glyphs, and the consequences are derived from it
(`eggCurve_PConstructibleCurve_of_rule`, `piriform_PConstructibleCurve_of_rule`).
-/

namespace Pconstructible
namespace Warp

/-! ### The ruled warp and the bilinear cell -/

/-- The ruled warp with guides `T` (top) and `B` (bottom): the glyph point with normalized
coordinates `p = (u, v)` goes to the point a fraction `v` of the way from `T u` to `B u`.
The guides are taken already parametrized as PowerPoint traces them (by arc length over
`[0, 1]`); that reparametrization is part of the data, not of this definition. -/
def ruledWarp (T B : ℝ → ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  ((1 - p.2) * (T p.1).1 + p.2 * (B p.1).1, (1 - p.2) * (T p.1).2 + p.2 * (B p.1).2)

/-- The bilinear map `(u, v) ↦ P + u A + v B + u v C`, written out in coordinates. -/
def bilinearCell (P A B C : ℝ × ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (P.1 + p.1 * A.1 + p.2 * B.1 + p.1 * p.2 * C.1,
   P.2 + p.1 * A.2 + p.2 * B.2 + p.1 * p.2 * C.2)

-- Theorem: with two straight guides traced at constant speed, the ruled warp is a bilinear
-- cell. Its constant term is the top guide's start, its `u` and `v` terms the top guide's
-- direction and the left side, and its twist `C` the failure of the cell to be a
-- parallelogram (zero exactly when the guides are parallel and equally long).
theorem ruledWarp_segment (p₀ p₁ q₀ q₁ : ℝ × ℝ) :
    ruledWarp (segmentParam p₀ p₁) (segmentParam q₀ q₁) =
      bilinearCell p₀ (p₁.1 - p₀.1, p₁.2 - p₀.2) (q₀.1 - p₀.1, q₀.2 - p₀.2)
        (q₁.1 - q₀.1 - (p₁.1 - p₀.1), q₁.2 - q₀.2 - (p₁.2 - p₀.2)) := by
  funext p
  simp only [ruledWarp, segmentParam, bilinearCell, Prod.mk.injEq]
  constructor <;> ring

/-! ### Straight glyph edges: nothing new

Along a glyph edge `t ↦ p + t (q - p)` both `u` and `v` are affine in `t`, so the bilinear
cell makes the image quadratic in `t`: a parabolic arc (a segment if the cell is affine
along it). A quadratic is a cubic Bézier whose control points are the degree-elevated
quadratic ones, so `cubic_bezier` draws the image directly. -/

/-- Coefficients of the image of a glyph edge, `F (p + t (q - p)) = Q₀ + t Q₁ + t² Q₂`, one
coordinate at a time (`P A B C` are that coordinate of the cell's vectors). -/
def edgeQuad (P A B C pu pv qu qv : ℝ) : ℝ × ℝ × ℝ :=
  (P + pu * A + pv * B + pu * pv * C,
   (qu - pu) * A + (qv - pv) * B + (pu * (qv - pv) + pv * (qu - pu)) * C,
   (qu - pu) * (qv - pv) * C)

/-- The cubic-Bézier control points of the quadratic `Q₀ + t Q₁ + t² Q₂` (degree elevation):
`Q₀`, `Q₀ + Q₁/3`, `Q₀ + 2Q₁/3 + Q₂/3`, `Q₀ + Q₁ + Q₂`. -/
noncomputable def elevate (Q : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ × ℝ :=
  (Q.1, Q.1 + Q.2.1 / 3, Q.1 + 2 * Q.2.1 / 3 + Q.2.2 / 3, Q.1 + Q.2.1 + Q.2.2)

-- Theorem: the bilinear image of a straight glyph edge is the cubic Bézier with the
-- degree-elevated control points of its quadratic coefficients.
theorem bilinearCell_segmentParam (P A B C p q : ℝ × ℝ) (t : ℝ) :
    bilinearCell P A B C (segmentParam p q t) =
      bezierParam
        ((elevate (edgeQuad P.1 A.1 B.1 C.1 p.1 p.2 q.1 q.2)).1,
          (elevate (edgeQuad P.2 A.2 B.2 C.2 p.1 p.2 q.1 q.2)).1)
        ((elevate (edgeQuad P.1 A.1 B.1 C.1 p.1 p.2 q.1 q.2)).2.1,
          (elevate (edgeQuad P.2 A.2 B.2 C.2 p.1 p.2 q.1 q.2)).2.1)
        ((elevate (edgeQuad P.1 A.1 B.1 C.1 p.1 p.2 q.1 q.2)).2.2.1,
          (elevate (edgeQuad P.2 A.2 B.2 C.2 p.1 p.2 q.1 q.2)).2.2.1)
        ((elevate (edgeQuad P.1 A.1 B.1 C.1 p.1 p.2 q.1 q.2)).2.2.2,
          (elevate (edgeQuad P.2 A.2 B.2 C.2 p.1 p.2 q.1 q.2)).2.2.2) t := by
  simp only [bilinearCell, segmentParam, bezierParam, elevate, edgeQuad, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: under a bilinear cell with P-constructible data, the image of a glyph edge
-- between P-constructible points is a constructible curve. So for the polygonal presets
-- every straight glyph edge, and hence every polygon glyph, warps to curves the class
-- already has; whatever the warp adds must come from curved glyphs.
theorem bilinearCell_segment_PConstructibleCurve {P A B C p q : ℝ × ℝ}
    (hP1 : PConstructible P.1) (hP2 : PConstructible P.2)
    (hA1 : PConstructible A.1) (hA2 : PConstructible A.2)
    (hB1 : PConstructible B.1) (hB2 : PConstructible B.2)
    (hC1 : PConstructible C.1) (hC2 : PConstructible C.2)
    (hp1 : PConstructible p.1) (hp2 : PConstructible p.2)
    (hq1 : PConstructible q.1) (hq2 : PConstructible q.2) :
    PConstructibleCurve (bilinearCell P A B C '' (segmentParam p q '' Set.Icc 0 1)) := by
  rw [Set.image_image]
  simp_rw [bilinearCell_segmentParam]
  refine PConstructibleCurve.cubic_bezier _ _ _ _ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp only [elevate, edgeQuad] <;> pconstructible

/-! ### Glyph circles: eggs and the piriform

Take a cell whose two sides are vertical and whose bottom guide is horizontal, normalized so
that `x = u` and the height above the bottom guide is `D (u) (1 - v)` with `D` affine,
`D (u) = d₀ + d₁ u` (`heightCell`). Fade, Cascade and each half of Triangle are of this form
after an affine change of coordinates.

A glyph circle that touches the cell's left side, with centre `(a, 1/2)` and radii `a` and
`1/2` in `(u, v)` (`glyphCircle`: the circle of a lone round glyph, in a row twice its width or
more), then maps to the quartic

  `a² (D (x) − 2y)² = D (x)² · x (2a − x)`,

an egg: the circle's `v`-profile `±√(x (2a − x))/a`, rescaled by the height `D (x)`. With
`d₁ = 0` it is an ellipse (the cell is affine). With `d₀ = 0` the cell is pinched to a point at
the tangent line, the egg acquires a cusp there, and the shear `y ↦ D (x)/2 − y` turns it
into the piriform. -/

/-- The cell `(u, v) ↦ (u, (d₀ + d₁ u)(1 - v))`: abscissa `u`, height `d₀ + d₁ u` above the
bottom guide at `v = 0`, shrinking linearly to the bottom guide at `v = 1`. -/
def heightCell (d₀ d₁ : ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, (d₀ + d₁ * p.1) * (1 - p.2))

/-- The idealized round glyph in normalized coordinates: centre `(a, 1/2)`, radius `a` along
`u` and `1/2` along `v`, i.e. `((u − a)/a)² + (2v − 1)² = 1` cleared of denominators. -/
def glyphCircle (a : ℝ) : Set (ℝ × ℝ) :=
  {p | (p.1 - a) ^ 2 + a ^ 2 * (2 * p.2 - 1) ^ 2 = a ^ 2}

/-- The egg quartic `a² (d₀ + d₁ x − 2y)² = (d₀ + d₁ x)² x (2a − x)` on `x ≥ 0`. The side
condition removes the acnode `(-d₀/d₁, 0)`, an isolated real point of the quartic that no
glyph point reaches. -/
def eggCurve (a d₀ d₁ : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ a ^ 2 * (d₀ + d₁ * p.1 - 2 * p.2) ^ 2 = (d₀ + d₁ * p.1) ^ 2 * p.1 * (2 * a - p.1)}

/-- The piriform (pear curve) `a² y² = x³ (2a − x)`, i.e. `a⁴ y² = b² x³ (2a − x)` with `b = a`. -/
def piriform (a : ℝ) : Set (ℝ × ℝ) :=
  {p | a ^ 2 * p.2 ^ 2 = p.1 ^ 3 * (2 * a - p.1)}

-- Theorem: a glyph circle lies in the strip `0 ≤ u ≤ 2a`.
theorem glyphCircle_mem_Icc {a : ℝ} (ha : 0 ≤ a) {p : ℝ × ℝ} (h : p ∈ glyphCircle a) :
    0 ≤ p.1 ∧ p.1 ≤ 2 * a := by
  simp only [glyphCircle, Set.mem_ofPred_eq] at h
  have h2 : p.1 * (p.1 - 2 * a) ≤ 0 := by nlinarith [sq_nonneg (a * (2 * p.2 - 1))]
  constructor
  · by_contra hn
    push Not at hn
    nlinarith
  · by_contra hn
    push Not at hn
    nlinarith

-- Theorem: under a cell whose height `d₀ + d₁ u` is non-negative and not identically zero,
-- the glyph circle maps exactly onto the egg quartic. Forward, the circle equation times
-- `D²` is the quartic. Backward, `v` is recovered as `1 - y / D (x)` where `D (x) ≠ 0`; the only
-- place `D` can vanish on `x ≥ 0` is a pinch at `x = 0`, where the quartic forces `y = 0` and
-- the circle's tangency point `(0, 1/2)` is the preimage.
theorem heightCell_image_glyphCircle {a d₀ d₁ : ℝ} (ha : 0 < a) (hd₀ : 0 ≤ d₀) (hd₁ : 0 ≤ d₁)
    (hd : 0 < d₀ + d₁) :
    heightCell d₀ d₁ '' glyphCircle a = eggCurve a d₀ d₁ := by
  ext ⟨x, y⟩
  simp only [Set.mem_image, heightCell, glyphCircle, eggCurve, Set.mem_ofPred_eq, Prod.mk.injEq,
    Prod.exists]
  constructor
  · rintro ⟨u, v, hc, rfl, rfl⟩
    have hu := glyphCircle_mem_Icc ha.le (p := (u, v)) hc
    refine ⟨hu.1, ?_⟩
    linear_combination (d₀ + d₁ * u) ^ 2 * hc
  · rintro ⟨hx, he⟩
    by_cases hD : d₀ + d₁ * x = 0
    · -- the pinch: `x = 0`, `d₀ = 0`, hence `y = 0`
      have hx0 : x = 0 := by
        rcases hx.lt_or_eq with hxp | hxe
        · exfalso
          have : d₁ * x = 0 := by nlinarith [mul_nonneg hd₁ hx]
          rcases mul_eq_zero.mp this with h1 | h1
          · linarith
          · linarith
        · exact hxe.symm
      subst hx0
      have hy : y = 0 := by
        rw [hD] at he
        have : a ^ 2 * (2 * y) ^ 2 = 0 := by linear_combination he
        have ha2 : a ^ 2 ≠ 0 := by positivity
        have := (mul_eq_zero.mp this).resolve_left ha2
        nlinarith [sq_nonneg y]
      refine ⟨0, 1 / 2, by ring, rfl, ?_⟩
      rw [hy]; simp only [mul_zero, add_zero] at hD; rw [hD]; ring
    · refine ⟨x, 1 - y / (d₀ + d₁ * x), ?_, rfl, ?_⟩
      · have hk : 2 * (1 - y / (d₀ + d₁ * x)) - 1 = (d₀ + d₁ * x - 2 * y) / (d₀ + d₁ * x) := by
          field_simp; ring
        rw [hk, div_pow, ← mul_div_assoc, he, mul_assoc,
          mul_div_cancel_left₀ _ (pow_ne_zero 2 hD)]
        ring
      · field_simp
        ring

-- Theorem: pinching the cell at the circle's tangent line turns the glyph circle into a
-- sheared piriform: after `y ↦ x − 2y`, which undoes the height `x`, the image is exactly the
-- pear curve `a² y² = x³ (2a − x)`. The cusp of the pear is the pinch point.
theorem piriform_eq_image {a : ℝ} (ha : 0 < a) :
    piriform a = (fun p : ℝ × ℝ => (p.1, p.1 - 2 * p.2)) '' (heightCell 0 1 '' glyphCircle a) := by
  rw [heightCell_image_glyphCircle ha le_rfl zero_le_one (by norm_num)]
  ext ⟨x, y⟩
  simp only [piriform, eggCurve, Set.mem_image, Set.mem_ofPred_eq, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    have hx : 0 ≤ x := by
      by_contra hneg
      push Not at hneg
      have : x ^ 3 * (2 * a - x) < 0 :=
        mul_neg_of_neg_of_pos (Odd.pow_neg (by decide) hneg) (by linarith)
      nlinarith [sq_nonneg (a * y)]
    refine ⟨x, (x - y) / 2, ⟨hx, ?_⟩, rfl, by ring⟩
    linear_combination h
  · rintro ⟨u, w, ⟨hu, he⟩, rfl, rfl⟩
    linear_combination he

/-! ### The Triangle preset

`textTriangle` with handle fraction `α = adj / 100000 ∈ [0, 1]` on the box `(l, t, w, h)`
(slide coordinates, `y` down): the top guide runs `(l, t + α h) → (l + w/2, t) → (l + w, t + α h)`,
the bottom guide `(l, t + h) → (l + w, t + h)`. The two top segments are equally long, so arc
length splits them at `u = 1/2`, and the top guide is `u ↦ (l + u w, t + α h |2u − 1|)`. At the
default `α = 1/2` the left half is an egg cell; at the stop `α = 1` it is pinched at both ends. -/

/-- The Triangle warp, `ruledWarp` of its two guides traced by arc length. -/
noncomputable def triangleWarp (l t w h α : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  ruledWarp (fun u => (l + u * w, t + α * h * |2 * u - 1|)) (fun u => (l + u * w, t + h))

-- Theorem: on the left half of the text (`u ≤ 1/2`) the Triangle warp is the egg cell with
-- `d₀ = (1 − α) h` and `d₁ = 2 α h`, followed by the affine map `(x, y) ↦ (l + w x, t + h − y)`.
theorem triangleWarp_eq_left {l t w h α : ℝ} {p : ℝ × ℝ} (hp : p.1 ≤ 1 / 2) :
    triangleWarp l t w h α p =
      affineMap w 0 0 (-1) l (t + h) (heightCell ((1 - α) * h) (2 * α * h) p) := by
  have habs : |2 * p.1 - 1| = 1 - 2 * p.1 := by
    rw [abs_of_nonpos (by linarith)]; ring
  simp only [triangleWarp, ruledWarp, affineMap, heightCell, habs, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: a glyph circle in the left quarter-width (`a ≤ 1/4`) is carried by the Triangle
-- warp onto an affine image of an egg; at the stop `α = 1` the egg is the pinched one.
theorem triangleWarp_image_glyphCircle {l t w h α a : ℝ} (ha₀ : 0 ≤ a) (ha : a ≤ 1 / 4) :
    triangleWarp l t w h α '' glyphCircle a =
      affineMap w 0 0 (-1) l (t + h) ''
        (heightCell ((1 - α) * h) (2 * α * h) '' glyphCircle a) := by
  rw [Set.image_image]
  refine Set.image_congr fun p hp => ?_
  exact triangleWarp_eq_left (by linarith [(glyphCircle_mem_Icc ha₀ hp).2])

/-! ### The proposed rule, and what it would give

`TriangleCircleRule` is the text-warp rule cut down to what the theorems below use: the
Triangle preset on a box with P-constructible position and positive P-constructible size, its
handle at a rational fraction `α ∈ [0, 1]` (stored as an integer in 1/100000 units, so every
reachable handle value is rational), and one idealized round glyph `glyphCircle a`, `a`
rational (its normalized size comes from integer font units and the text layout). The glyph
is idealized because a `●` is drawn as a circle; the probes find the warped `●` within
0.33–0.40 pt of the exact image of a true circle.

Whether the stop value `α = 1` is reachable in the UI without typing (by dragging the handle
past its end) is an open probe: see `notes/warp/probes/probe_handle.py`. The egg family at the
default `α = 1/2` needs no such assumption. -/

/-- The proposed text-warp rule for the Triangle preset and round glyphs. -/
def TriangleCircleRule : Prop :=
  ∀ (l t w h : ℝ) (α a : ℚ), PConstructible l → PConstructible t → PConstructible w →
    PConstructible h → 0 < w → 0 < h → 0 ≤ α → α ≤ 1 → 0 < a → a ≤ 1 / 4 →
      PConstructibleCurve (triangleWarp l t w h α '' glyphCircle a)

-- Theorem: under the rule, every egg with rational shape data is constructible. Take the unit
-- box at the origin; the affine map `(x, y) ↦ (x, 1 − y)` relating the Triangle image to the
-- egg is its own inverse.
theorem eggCurve_PConstructibleCurve_of_rule (hR : TriangleCircleRule) {α a : ℚ}
    (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (ha₀ : 0 < a) (ha : a ≤ 1 / 4) :
    PConstructibleCurve (eggCurve a (1 - α) (2 * α)) := by
  have h := hR 0 0 1 1 α a zero_Pconstructible zero_Pconstructible PConstructible.base_one
    PConstructible.base_one one_pos one_pos hα₀ hα₁ ha₀ ha
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha₀
  have ha4 : (a : ℝ) ≤ 1 / 4 := by
    rw [show (1 / 4 : ℝ) = ((1 / 4 : ℚ) : ℝ) by norm_num]; exact_mod_cast ha
  rw [triangleWarp_image_glyphCircle ha'.le ha4] at h
  have h' := affineMap_PConstructibleCurve h (a := 1) (b := 0) (c := 0) (d := -1) (u := 0)
    (v := 1) PConstructible.base_one zero_Pconstructible zero_Pconstructible
    (by pconstructible) zero_Pconstructible PConstructible.base_one
  rw [Set.image_image, Set.image_image] at h'
  have hα0' : (0 : ℝ) ≤ α := by exact_mod_cast hα₀
  have hα1' : (α : ℝ) ≤ 1 := by exact_mod_cast hα₁
  have hid : ∀ p : ℝ × ℝ, affineMap 1 0 0 (-1) 0 1 (affineMap 1 0 0 (-1) 0 (0 + 1)
      (heightCell ((1 - α) * 1) (2 * α * 1) p)) = heightCell (1 - α) (2 * α) p := by
    intro p; simp only [affineMap, heightCell, Prod.mk.injEq]; constructor <;> ring
  simp_rw [hid] at h'
  rwa [heightCell_image_glyphCircle ha' (by linarith) (by linarith) (by linarith)] at h'

-- Theorem: under the rule, the piriform `y² = x³ (2 − x)` is constructible. Pinch the Triangle
-- (`α = 1`), take the egg `eggCurve a 0 2`, undo the height by the shear `y ↦ x − y`, and
-- rescale by `1/a`.
theorem piriform_PConstructibleCurve_of_rule (hR : TriangleCircleRule) :
    PConstructibleCurve (piriform 1) := by
  have hegg := eggCurve_PConstructibleCurve_of_rule hR (α := 1) (a := 1 / 4)
    (by norm_num) le_rfl (by norm_num) le_rfl
  -- shear `(x, y) ↦ (x, x − y)` takes `eggCurve (1/4) 0 2` to `piriform (1/4)`
  have h1 := linearMap_PConstructibleCurve hegg (a := 1) (b := 0) (c := 1) (d := -1)
    PConstructible.base_one zero_Pconstructible PConstructible.base_one (by pconstructible)
  have hset : linearMap 1 0 1 (-1) '' eggCurve ((1 / 4 : ℚ) : ℝ) (1 - ((1 : ℚ) : ℝ))
      (2 * ((1 : ℚ) : ℝ)) = piriform (1 / 4) := by
    ext ⟨x, y⟩
    simp only [eggCurve, piriform, linearMap, Set.mem_image, Set.mem_ofPred_eq, Prod.mk.injEq,
      Prod.exists]
    push_cast
    constructor
    · rintro ⟨u, w, ⟨hu, he⟩, rfl, rfl⟩
      linear_combination he / 4
    · intro h
      have hx : 0 ≤ x := by
        by_contra hneg
        push Not at hneg
        have : x ^ 3 * (2 * (1 / 4) - x) < 0 :=
          mul_neg_of_neg_of_pos (Odd.pow_neg (by decide) hneg) (by linarith)
        nlinarith [sq_nonneg y]
      refine ⟨x, x - y, ⟨hx, ?_⟩, by ring, by ring⟩
      linear_combination 4 * h
  rw [hset] at h1
  -- rescale by 4: `(1/4)² y² = x³ (1/2 − x)` becomes `Y² = X³ (2 − X)` with `X = 4x`, `Y = 4y`
  have h2 := stretch_PConstructibleCurve h1 (s := 4) (by pconstructible)
  have hset2 : (fun p : ℝ × ℝ => (4 * p.1, 4 * p.2)) '' piriform (1 / 4) = piriform 1 := by
    ext ⟨x, y⟩
    simp only [piriform, Set.mem_image, Set.mem_ofPred_eq, Prod.mk.injEq, Prod.exists]
    constructor
    · rintro ⟨u, w, h, rfl, rfl⟩
      linear_combination 256 * h
    · intro h
      exact ⟨x / 4, y / 4, by linear_combination h / 256, by ring, by ring⟩
  rwa [hset2] at h2

end Warp
end Pconstructible
