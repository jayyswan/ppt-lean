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
-- Deliberately does *not* import `Pptc.Basic`: `Pptc.Basic` imports this file (it uses the
-- box to rewrite `cos_sin_Pconstructible`), so the dependency `Defs -> Tactic -> Box ->
-- Basic` is what keeps the two apart. `Mathlib.Topology.Order.Compact` supplies
-- `isCompact_Icc` and `IsCompact.image_of_continuousOn` for §W2.
import Pptc.Defs
import Pptc.Tactic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Pptc.Box

The bounding-box API for `PConstructibleCurve`: the left, right, top and bottom edges of a
compact constructible curve, and the width and height the drawing program reports for it.

## W1 — the four-edge API

`Pptc.Defs` takes the two *maxima* as axioms (`box_xmax`, `box_ymax`). The two *minima* are
not assumed: they are recovered by reflection. The closure operation `scale_x` carries no
positivity hypothesis on its factor, so scaling the `x` axis by `-1` is legal, and

    PConstructibleCurve.scale_x A (-1) = (fun p => (-1 * p.1, p.2)) '' A.

Projecting that reflected curve to the first coordinate gives exactly the negated
abscissae of `A`. The supremum of a set and the infimum of its reflection are one and the
same measurement — `sSup (-S) = -sInf S` (`Real.sSup_neg`) — so `box_xmax` applied to the
reflection returns the *left* edge of the original curve. `scale_y` does the same for the
bottom edge, and subtracting the two edges gives the width and the height. Only the
reflection is new; the extremal reading is the axiom.

## W2 — the compactness toolkit

`box_xmax` / `box_ymax` each demand `IsCompact A`. Compactness is what makes the reported
edge a *measurement* rather than the value of a limiting process: on a compact set the
supremum is attained (`IsCompact.sSup_mem`), so some point of the curve really sits at the
reported edge. The obligation is almost always discharged from a tracing `γ` whose `hdiff`
hypothesis — the very bundle carried by `arc_of_length` and `offset` — already says each
coordinate is differentiable, hence continuous, on `Icc a b`.
`isCompact_traced_arc` packages `isCompact_Icc.image_of_continuousOn` into exactly that
hypothesis bundle, and `nonempty_traced_arc` supplies the companion `Nonempty` goal, so
callers discharge both side conditions by `exact`.
-/

open scoped Pointwise

namespace Pconstructible

/-! ### Projecting a coordinate through an axis scaling

`scale_x A c` is `(fun p => (c * p.1, p.2)) '' A`; projecting it to the `x` coordinate is
the same as scaling the projected set by `c`. Stated for each axis separately because the
projection has to commute past the untouched product component each time. -/

-- Lemma: `Prod.fst` of `scale_x A c` is `c` times `Prod.fst` of `A`.
private lemma fst_image_scale (c : ℝ) (A : Set (ℝ × ℝ)) :
    Prod.fst '' ((fun p : ℝ × ℝ => (c * p.1, p.2)) '' A)
      = (fun x : ℝ => c * x) '' (Prod.fst '' A) := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, hq⟩, hx⟩
    rw [← hq] at hx
    exact ⟨p.1, ⟨p, hp, rfl⟩, hx⟩
  · rintro ⟨y, ⟨p, hp, hy⟩, hx⟩
    refine ⟨(c * p.1, p.2), ⟨p, hp, rfl⟩, ?_⟩
    rw [← hy] at hx
    exact hx

-- Lemma: `Prod.snd` of `scale_y A c` is `c` times `Prod.snd` of `A`.
private lemma snd_image_scale (c : ℝ) (A : Set (ℝ × ℝ)) :
    Prod.snd '' ((fun p : ℝ × ℝ => (p.1, c * p.2)) '' A)
      = (fun y : ℝ => c * y) '' (Prod.snd '' A) := by
  ext x
  constructor
  · rintro ⟨q, ⟨p, hp, hq⟩, hx⟩
    rw [← hq] at hx
    exact ⟨p.2, ⟨p, hp, rfl⟩, hx⟩
  · rintro ⟨y, ⟨p, hp, hy⟩, hx⟩
    refine ⟨(p.1, c * p.2), ⟨p, hp, rfl⟩, ?_⟩
    rw [← hy] at hx
    exact hx

-- Lemma: `-1` is P-constructible. `Defs` has no `neg` constructor, so it is
-- `1 - (1 + 1)`, converted to the literal `-1` by `norm_num`.
private lemma neg_one_Pconstructible : PConstructible (-1 : ℝ) := by
  have h : PConstructible ((1 : ℝ) - (1 + 1)) :=
    PConstructible.base_one.sub (PConstructible.base_one.add PConstructible.base_one)
  simpa only [show ((1 : ℝ) - (1 + 1)) = -1 by norm_num] using h

/-! ### W1 — the four edges -/

-- Theorem: the left edge `sInf (Prod.fst '' A)` of a compact nonempty constructible
-- curve is P-constructible, by reflecting the curve in the `y` axis and reading its
-- right edge with `box_xmax`.
@[pconstructible_cond]
theorem box_xmin_Pconstructible {A : Set (ℝ × ℝ)} (hA : PConstructibleCurve A)
    (hcomp : IsCompact A) (hne : A.Nonempty) : PConstructible (sInf (Prod.fst '' A)) := by
  -- `-1` is P-constructible; reflecting is a legal curve operation.
  have hneg1 := neg_one_Pconstructible
  -- The reflected curve is constructible; reflecting is a continuous map, so compactness
  -- and nonemptiness transfer.
  have hA' : PConstructibleCurve ((fun p : ℝ × ℝ => (-1 * p.1, p.2)) '' A) :=
    PConstructibleCurve.scale_x hA hneg1
  have hcont : Continuous (fun p : ℝ × ℝ => (-1 * p.1, p.2)) :=
    (continuous_const.mul continuous_fst).prodMk continuous_snd
  have hcomp' : IsCompact ((fun p : ℝ × ℝ => (-1 * p.1, p.2)) '' A) :=
    hcomp.image hcont
  have hne' : ((fun p : ℝ × ℝ => (-1 * p.1, p.2)) '' A).Nonempty :=
    Set.Nonempty.image (fun p : ℝ × ℝ => (-1 * p.1, p.2)) hne
  -- The axiom reads the reflected curve's right edge ...
  have hmax := PConstructible.box_xmax hA' hcomp' hne'
  -- ... which is the original curve's left edge.
  have hsSup : sSup (Prod.fst '' ((fun p : ℝ × ℝ => (-1 * p.1, p.2)) '' A))
      = -sInf (Prod.fst '' A) := by
    rw [fst_image_scale (-1) A]
    have hneg : (fun x : ℝ => -1 * x) = (fun x : ℝ => -x) := by funext x; ring
    rw [hneg, Set.image_neg_eq_neg, Real.sSup_neg]
  rw [hsSup] at hmax
  -- `hmax : PConstructible (-sInf ...)`; multiplying by `-1` returns `sInf ...`.
  simpa using hneg1.mul hmax

-- Theorem: the bottom edge `sInf (Prod.snd '' A)` of a compact nonempty constructible
-- curve is P-constructible, by reflecting the curve in the `x` axis and reading its top
-- edge with `box_ymax`.
@[pconstructible_cond]
theorem box_ymin_Pconstructible {A : Set (ℝ × ℝ)} (hA : PConstructibleCurve A)
    (hcomp : IsCompact A) (hne : A.Nonempty) : PConstructible (sInf (Prod.snd '' A)) := by
  have hneg1 := neg_one_Pconstructible
  have hA' : PConstructibleCurve ((fun p : ℝ × ℝ => (p.1, -1 * p.2)) '' A) :=
    PConstructibleCurve.scale_y hA hneg1
  have hcont : Continuous (fun p : ℝ × ℝ => (p.1, -1 * p.2)) :=
    continuous_fst.prodMk (continuous_const.mul continuous_snd)
  have hcomp' : IsCompact ((fun p : ℝ × ℝ => (p.1, -1 * p.2)) '' A) :=
    hcomp.image hcont
  have hne' : ((fun p : ℝ × ℝ => (p.1, -1 * p.2)) '' A).Nonempty :=
    Set.Nonempty.image (fun p : ℝ × ℝ => (p.1, -1 * p.2)) hne
  have hmax := PConstructible.box_ymax hA' hcomp' hne'
  have hsSup : sSup (Prod.snd '' ((fun p : ℝ × ℝ => (p.1, -1 * p.2)) '' A))
      = -sInf (Prod.snd '' A) := by
    rw [snd_image_scale (-1) A]
    have hneg : (fun y : ℝ => -1 * y) = (fun y : ℝ => -y) := by funext y; ring
    rw [hneg, Set.image_neg_eq_neg, Real.sSup_neg]
  rw [hsSup] at hmax
  simpa using hneg1.mul hmax

-- Theorem: the width `sSup (Prod.fst '' A) - sInf (Prod.fst '' A)` of a compact nonempty
-- constructible curve is P-constructible, being the difference of its two vertical edges.
@[pconstructible_cond]
theorem box_width_Pconstructible {A : Set (ℝ × ℝ)} (hA : PConstructibleCurve A)
    (hcomp : IsCompact A) (hne : A.Nonempty) :
    PConstructible (sSup (Prod.fst '' A) - sInf (Prod.fst '' A)) :=
  (PConstructible.box_xmax hA hcomp hne).sub (box_xmin_Pconstructible hA hcomp hne)

-- Theorem: the height `sSup (Prod.snd '' A) - sInf (Prod.snd '' A)` of a compact
-- nonempty constructible curve is P-constructible, being the difference of its two
-- horizontal edges.
@[pconstructible_cond]
theorem box_height_Pconstructible {A : Set (ℝ × ℝ)} (hA : PConstructibleCurve A)
    (hcomp : IsCompact A) (hne : A.Nonempty) :
    PConstructible (sSup (Prod.snd '' A) - sInf (Prod.snd '' A)) :=
  (PConstructible.box_ymax hA hcomp hne).sub (box_ymin_Pconstructible hA hcomp hne)

/-! ### W2 — the compactness toolkit -/

-- Theorem: the image of a closed parameter interval under a tracing whose two coordinate
-- functions are differentiable on it is compact. This is precisely the `hdiff` bundle of
-- `PConstructibleCurve.arc_of_length` and `.offset`, so their callers can discharge the
-- `IsCompact` side goal of the box by `exact`.
theorem isCompact_traced_arc {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t) :
    IsCompact (γ '' Set.Icc a b) := by
  -- Differentiability at each point gives continuity there, hence continuity on the
  -- interval for each coordinate; `ContinuousOn.prodMk` reassembles them into `γ`.
  have hx : ContinuousOn (fun t => (γ t).1) (Set.Icc a b) :=
    fun t ht => (hdiff t ht).1.continuousAt.continuousWithinAt
  have hy : ContinuousOn (fun t => (γ t).2) (Set.Icc a b) :=
    fun t ht => (hdiff t ht).2.continuousAt.continuousWithinAt
  exact isCompact_Icc.image_of_continuousOn (hx.prodMk hy)

-- Theorem: the image of a nonempty closed interval under any tracing is nonempty. This is
-- the companion `Nonempty` side goal of the box for curves presented by a tracing.
theorem nonempty_traced_arc {γ : ℝ → ℝ × ℝ} {a b : ℝ} (hab : a ≤ b) :
    (γ '' Set.Icc a b).Nonempty :=
  (Set.nonempty_Icc.mpr hab).image γ

/-! ### W2b — compactness of restricted curves

`box_xmax` / `box_ymax` need `IsCompact A`, and `restrict` crops a curve to an axis-aligned
window. For a *closed* source curve the cropped curve is again compact, and
`isCompact_restrict_of_isClosed` records exactly that: the window is a product of two closed
intervals, hence compact, and intersecting it with a closed set preserves compactness.

The base curve families are then classified one by one. `poly_graph`, `exp_two` and `sine`
are graphs of continuous functions, `ellipse` and `rectangle` are level sets / finite unions
of closed edges, and `cubic_bezier` is the continuous image of the compact parameter interval
`Icc 0 1`. All six are closed, so the general lemma applies to any cropped instance.

`power_law` is deliberately **not** on that list, and cropping cannot repair it. Its locus
`{(x, a x ^ b) : 0 < x}` omits `x = 0`, so for `b > 0` it has the limit point `(0, 0)`
outside itself and is not closed; even cut to the closed window `[0, 1] × [0, 1]` the result
`{0 < x ≤ 1}` is still not closed in `ℝ × ℝ`, because a closed window contributes closed
edges but cannot add the missing curve point. This is the same subtlety recorded at
`Defs.lean:190-196` for `sSup` / `sInf`: the abscissae have infimum `0`, a limit no point of
the curve attains, and box-taking such a curve would assert that an infinite limiting process
is a finite construction. So a `power_law` restrict must supply `IsCompact` from elsewhere
(e.g. from a tracing by `isCompact_traced_arc`), not from this classification. -/

-- Theorem: a closed set cropped to a closed axis-aligned window is compact. The window is
-- exactly the one `PConstructibleCurve.restrict` produces, so this discharges the
-- `IsCompact` side goal for any `restrict` whose source curve is closed. `ℝ × ℝ` carries
-- only the product partial order, so `isCompact_Icc` is applied in each factor and the two
-- halves are joined by `IsCompact.prod` rather than on the product directly.
theorem isCompact_restrict_of_isClosed {S : Set (ℝ × ℝ)} (hS : IsClosed S)
    (xmin xmax ymin ymax : ℝ) :
    IsCompact (S ∩ {p : ℝ × ℝ | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax}) := by
  have hwin : {p : ℝ × ℝ | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax}
      = Set.Icc xmin xmax ×ˢ Set.Icc ymin ymax := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc]
    tauto
  rw [hwin]
  exact (isCompact_Icc.prod isCompact_Icc).inter_left hS

-- Theorem: the graph of a rational polynomial is a closed subset of the plane: it is the
-- zero set of the continuous function `pt ↦ pt.2 - p(pt.1)`.
theorem isClosed_poly_graph (p : Polynomial ℚ) :
    IsClosed {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 p} :=
  isClosed_eq continuous_snd ((Polynomial.continuous_aeval p).comp continuous_fst)

-- Theorem: the axis-aligned ellipse locus is closed: it is the level set at `1` of a
-- continuous function of the plane.
theorem isClosed_ellipse (cx cy width height : ℝ) :
    IsClosed {p : ℝ × ℝ |
      ((p.1 - cx) / (width / 2)) ^ 2 + ((p.2 - cy) / (height / 2)) ^ 2 = 1} :=
  isClosed_eq (by fun_prop) continuous_const

-- Theorem: the boundary of an axis-aligned rectangle is closed: it is the union of its four
-- closed edges, each a product of a closed interval with a singleton.
theorem isClosed_rectangle (cx cy width height : ℝ) :
    IsClosed {p : ℝ × ℝ |
        (cx - width / 2 ≤ p.1 ∧ p.1 ≤ cx + width / 2 ∧
          (p.2 = cy - height / 2 ∨ p.2 = cy + height / 2)) ∨
        (cy - height / 2 ≤ p.2 ∧ p.2 ≤ cy + height / 2 ∧
          (p.1 = cx - width / 2 ∨ p.1 = cx + width / 2))} := by
  have hset : {p : ℝ × ℝ |
        (cx - width / 2 ≤ p.1 ∧ p.1 ≤ cx + width / 2 ∧
          (p.2 = cy - height / 2 ∨ p.2 = cy + height / 2)) ∨
        (cy - height / 2 ≤ p.2 ∧ p.2 ≤ cy + height / 2 ∧
          (p.1 = cx - width / 2 ∨ p.1 = cx + width / 2))}
      = ((Set.Icc (cx - width / 2) (cx + width / 2) ×ˢ {cy - height / 2})
          ∪ (Set.Icc (cx - width / 2) (cx + width / 2) ×ˢ {cy + height / 2}))
        ∪ (({cx - width / 2} ×ˢ Set.Icc (cy - height / 2) (cy + height / 2))
          ∪ ({cx + width / 2} ×ˢ Set.Icc (cy - height / 2) (cy + height / 2))) := by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_prod, Set.mem_Icc,
      Set.mem_singleton_iff]
    tauto
  rw [hset]
  exact ((isClosed_Icc.prod isClosed_singleton).union
    (isClosed_Icc.prod isClosed_singleton)).union
      ((isClosed_singleton.prod isClosed_Icc).union
        (isClosed_singleton.prod isClosed_Icc))

-- Theorem: the graph `y = 2 ^ x` is closed: a graph of the continuous function `2 ^ ·`.
theorem isClosed_exp_two :
    IsClosed {p : ℝ × ℝ | p.2 = (2 : ℝ) ^ p.1} :=
  isClosed_eq continuous_snd
    ((Real.continuous_const_rpow (by norm_num : (2 : ℝ) ≠ 0)).comp continuous_fst)

-- Theorem: the sine graph `y = sin x` is closed: a graph of a continuous function.
theorem isClosed_sine :
    IsClosed {p : ℝ × ℝ | p.2 = Real.sin p.1} :=
  isClosed_eq continuous_snd (Real.continuous_sin.comp continuous_fst)

-- Theorem: a cubic Bézier curve drawn over `Icc 0 1` is closed: it is the continuous image
-- of a compact interval, hence compact, and `ℝ × ℝ` is Hausdorff.
theorem isClosed_cubic_bezier (p₁ p₂ p₃ p₄ : ℝ × ℝ) :
    IsClosed (bezierParam p₁ p₂ p₃ p₄ '' Set.Icc 0 1) := by
  have hcont : Continuous (bezierParam p₁ p₂ p₃ p₄) := by
    unfold bezierParam
    fun_prop
  exact (isCompact_Icc.image_of_continuousOn hcont.continuousOn).isClosed

-- Corollary: the compactness side goal of the box for a `poly_graph` cropped by `restrict`,
-- read off the general lemma and the closedness of the polynomial graph.
theorem isCompact_restrict_poly_graph (p : Polynomial ℚ) (xmin xmax ymin ymax : ℝ) :
    IsCompact ({pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 p} ∩
      {p : ℝ × ℝ | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax}) :=
  isCompact_restrict_of_isClosed (isClosed_poly_graph p) xmin xmax ymin ymax

/-! ### W3 — endpoint extraction for monotone arcs

A coordinate-monotone tracing reaches its box edge at an endpoint. If `(γ t).1` is
nondecreasing on `Icc a b`, its largest value is `(γ b).1`, and that value *is* the
supremum `box_xmax` reads off the traced curve — so the box returns an endpoint coordinate
directly, with no other-crossings argument. The antitone versions are the same idea against
`box_xmin` / `box_ymin`: then the coordinate is smallest at the right endpoint. Together
these turn the box into an extractor for the far end of an `arc_of_length` or `offset`
stroke, whose coordinate is monotone precisely on the stretch being laid. -/

-- Theorem: if the abscissa of a tracing is nondecreasing on `Icc a b`, the abscissa
-- `(γ b).1` of the right endpoint is P-constructible.
theorem arc_xendpoint_Pconstructible {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : MonotoneOn (fun t => (γ t).1) (Set.Icc a b)) :
    PConstructible (γ b).1 := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hcomp : IsCompact (γ '' Set.Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hne : (γ '' Set.Icc a b).Nonempty := nonempty_traced_arc hab
  -- `(γ b).1` lies in the abscissa set and dominates every other abscissa on the arc.
  have hgreat : IsGreatest (Prod.fst '' (γ '' Set.Icc a b)) (γ b).1 := by
    refine ⟨⟨γ b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact hmono ht hb ht.2
  have hbox := PConstructible.box_xmax hA hcomp hne
  rw [hgreat.csSup_eq] at hbox
  exact hbox

-- Theorem: if the ordinate of a tracing is nondecreasing on `Icc a b`, the ordinate
-- `(γ b).2` of the right endpoint is P-constructible.
theorem arc_yendpoint_Pconstructible {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : MonotoneOn (fun t => (γ t).2) (Set.Icc a b)) :
    PConstructible (γ b).2 := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hcomp : IsCompact (γ '' Set.Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hne : (γ '' Set.Icc a b).Nonempty := nonempty_traced_arc hab
  have hgreat : IsGreatest (Prod.snd '' (γ '' Set.Icc a b)) (γ b).2 := by
    refine ⟨⟨γ b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact hmono ht hb ht.2
  have hbox := PConstructible.box_ymax hA hcomp hne
  rw [hgreat.csSup_eq] at hbox
  exact hbox

-- Theorem: if the abscissa of a tracing is nonincreasing on `Icc a b`, the abscissa
-- `(γ b).1` of the right endpoint is P-constructible.
theorem arc_xendpoint_antitone_Pconstructible {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : AntitoneOn (fun t => (γ t).1) (Set.Icc a b)) :
    PConstructible (γ b).1 := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hcomp : IsCompact (γ '' Set.Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hne : (γ '' Set.Icc a b).Nonempty := nonempty_traced_arc hab
  -- Now `(γ b).1` lies in the abscissa set and is dominated by every other abscissa.
  have hleast : IsLeast (Prod.fst '' (γ '' Set.Icc a b)) (γ b).1 := by
    refine ⟨⟨γ b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact hmono ht hb ht.2
  have hbox := box_xmin_Pconstructible hA hcomp hne
  rw [hleast.csInf_eq] at hbox
  exact hbox

-- Theorem: if the ordinate of a tracing is nonincreasing on `Icc a b`, the ordinate
-- `(γ b).2` of the right endpoint is P-constructible.
theorem arc_yendpoint_antitone_Pconstructible {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : AntitoneOn (fun t => (γ t).2) (Set.Icc a b)) :
    PConstructible (γ b).2 := by
  have hb : b ∈ Set.Icc a b := ⟨hab, le_rfl⟩
  have hcomp : IsCompact (γ '' Set.Icc a b) := isCompact_Icc.image_of_continuousOn hcont
  have hne : (γ '' Set.Icc a b).Nonempty := nonempty_traced_arc hab
  have hleast : IsLeast (Prod.snd '' (γ '' Set.Icc a b)) (γ b).2 := by
    refine ⟨⟨γ b, ⟨b, hb, rfl⟩, rfl⟩, ?_⟩
    rintro _ ⟨q, ⟨t, ht, rfl⟩, rfl⟩
    exact hmono ht hb ht.2
  have hbox := box_ymin_Pconstructible hA hcomp hne
  rw [hleast.csInf_eq] at hbox
  exact hbox

/-! ### W4 — inverse arc length

`arc_of_length` lays an arc of prescribed P-constructible length `x` along a curve,
producing the arc as a curve but *not* its far endpoint. Feeding that arc to W3 extracts the
endpoint whenever the tracing is coordinate-monotone: the length `x = arcLengthOf γ a b` is
the datum pinning `b` through the integral, and at that `b` the monotone coordinate is a box
edge. So both coordinates of the far endpoint are P-constructible — informally, the
arc-length function `G(s) = arcLengthOf γ a s` has been inverted at the constructible value
`x`. The hypothesis list below is exactly `arc_of_length`'s, so callers that have just
applied that constructor can hand every hypothesis straight to this theorem.

Read with `x` as the independent variable, this is the uniform statement of plan §3.N1: for
any drawable curve admitting a coordinate-monotone tracing, the arc-length parametrization
`s ↦ γ (G⁻¹ s)` is P-constructible at every P-constructible `s`. That is *this* theorem
rather than a strengthening of it — `b` is precisely the parameter at which `G` takes the
value `s`. A `Function.invFun` formulation would add only a range/strict-monotonicity side
condition asserting that this `b` is the element `invFun` returns, while the mathematical
content stays here, so no separate N1 theorem is stated. -/

-- Lemma: the `hdiff` bundle of `arc_of_length` / `offset` makes the tracing continuous on
-- `Icc a b`.
private lemma continuousOn_of_hdiff {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t) :
    ContinuousOn γ (Set.Icc a b) :=
  ContinuousOn.prodMk (fun t ht => (hdiff t ht).1.continuousAt.continuousWithinAt)
    (fun t ht => (hdiff t ht).2.continuousAt.continuousWithinAt)

-- Lemma: the far endpoint's abscissa is P-constructible from the traced arc alone when the
-- tracing's abscissa is monotone in either direction.
private lemma xendpoint_of_monotone_or_antitone {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : MonotoneOn (fun t => (γ t).1) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).1) (Set.Icc a b)) :
    PConstructible (γ b).1 := by
  rcases hmono with h | h
  · exact arc_xendpoint_Pconstructible hA hab hcont h
  · exact arc_xendpoint_antitone_Pconstructible hA hab hcont h

-- Lemma: the far endpoint's ordinate is P-constructible from the traced arc alone when the
-- tracing's ordinate is monotone in either direction.
private lemma yendpoint_of_monotone_or_antitone {γ : ℝ → ℝ × ℝ} {a b : ℝ}
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : MonotoneOn (fun t => (γ t).2) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).2) (Set.Icc a b)) :
    PConstructible (γ b).2 := by
  rcases hmono with h | h
  · exact arc_yendpoint_Pconstructible hA hab hcont h
  · exact arc_yendpoint_antitone_Pconstructible hA hab hcont h

-- Theorem: if a tracing of a constructible curve has P-constructible arc length `x` from
-- `a` to `b` and each coordinate is monotone (in either direction) on `Icc a b`, then both
-- coordinates of the far endpoint `γ b` are P-constructible.
theorem arcLength_inverse_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ S)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
    {x : ℝ} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x)
    (hmono₁ : MonotoneOn (fun t => (γ t).1) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).1) (Set.Icc a b))
    (hmono₂ : MonotoneOn (fun t => (γ t).2) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).2) (Set.Icc a b)) :
    PConstructible (γ b).1 ∧ PConstructible (γ b).2 := by
  -- The prescribed length makes the traced arc a constructible curve in its own right;
  -- W3 then reads its far endpoint off the box.
  have hA := PConstructibleCurve.arc_of_length hS γ hab hsub hinj hdiff hint hx₀ hy₀ hx hlen
  have hcont := continuousOn_of_hdiff hdiff
  exact ⟨xendpoint_of_monotone_or_antitone hA hab hcont hmono₁,
    yendpoint_of_monotone_or_antitone hA hab hcont hmono₂⟩

-- Theorem: single-coordinate form of `arcLength_inverse_Pconstructible`, extracting only
-- the abscissa of the far endpoint. Takes every `arc_of_length` hypothesis, so it can be
-- applied immediately after that constructor.
theorem arcLength_xendpoint_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ S)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
    {x : ℝ} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x)
    (hmono : MonotoneOn (fun t => (γ t).1) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).1) (Set.Icc a b)) :
    PConstructible (γ b).1 := by
  have hA := PConstructibleCurve.arc_of_length hS γ hab hsub hinj hdiff hint hx₀ hy₀ hx hlen
  exact xendpoint_of_monotone_or_antitone hA hab (continuousOn_of_hdiff hdiff) hmono

-- Theorem: single-coordinate form of `arcLength_inverse_Pconstructible`, extracting only
-- the ordinate of the far endpoint.
theorem arcLength_yendpoint_Pconstructible
    {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ S)
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ∀ t ∈ Set.Icc a b,
      DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
    (hint : IntervalIntegrable (speed γ) MeasureTheory.volume a b)
    (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2)
    {x : ℝ} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x)
    (hmono : MonotoneOn (fun t => (γ t).2) (Set.Icc a b) ∨
      AntitoneOn (fun t => (γ t).2) (Set.Icc a b)) :
    PConstructible (γ b).2 := by
  have hA := PConstructibleCurve.arc_of_length hS γ hab hsub hinj hdiff hint hx₀ hy₀ hx hlen
  exact yendpoint_of_monotone_or_antitone hA hab (continuousOn_of_hdiff hdiff) hmono

/-! ### Inverting an increasing antiderivative

Both Legendre integrals are `∫₀^φ` of a continuous integrand bounded away from `0` and
`∞`, so both are strictly increasing bijections of the line onto itself. Proved once here
in terms of the derivative and used below in `Pptc.Jacobi` and by the graph inverse-arc-length
theorem in `Pptc.BoxGraph`. -/

-- Theorem: a function whose derivative is everywhere positive is strictly monotone.
theorem strictMono_of_hasDerivAt_pos {f g : ℝ → ℝ}
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hpos : ∀ θ, 0 < g θ) : StrictMono f :=
  strictMono_of_deriv_pos fun x => by rw [(hf x).deriv]; exact hpos x

-- Theorem: a derivative bounded below by `d` forces the function away from `0` at least
-- as fast as the line of slope `d` does, on both sides of the origin.
theorem mul_le_of_hasDerivAt_ge {f g : ℝ → ℝ} {d : ℝ}
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hg : ∀ θ, d ≤ g θ) (hf0 : f 0 = 0) (φ : ℝ) :
    (0 ≤ φ → d * φ ≤ f φ) ∧ (φ ≤ 0 → f φ ≤ d * φ) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun φ => f φ - d * φ) (g x - d) x := fun x =>
    (hf x).sub (by simpa using (hasDerivAt_id x).const_mul d)
  have hmono : Monotone fun φ => f φ - d * φ := by
    refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) fun x => ?_
    rw [(hd x).deriv]
    linarith [hg x]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := hmono h
    simp only [hf0, mul_zero, sub_zero] at this
    linarith
  · have := hmono h
    simp only [hf0, mul_zero, sub_zero] at this
    linarith

-- Theorem: such a function is onto, by the intermediate value theorem between the two
-- points where the line of slope `d` has already passed the target.
theorem surjective_of_hasDerivAt_ge {f g : ℝ → ℝ} {d : ℝ} (hd : 0 < d)
    (hf : ∀ φ, HasDerivAt f (g φ) φ) (hg : ∀ θ, d ≤ g θ) (hf0 : f 0 = 0) :
    Function.Surjective f := by
  have hcont : Continuous f := by
    have : Differentiable ℝ f := fun x => (hf x).differentiableAt
    exact this.continuous
  intro u
  have key := mul_le_of_hasDerivAt_ge hf hg hf0
  rcases le_total 0 u with hu | hu
  · have hb : 0 ≤ u / d := by positivity
    have h₁ : u ≤ f (u / d) := by
      have := (key (u / d)).1 hb
      rwa [mul_div_cancel₀ _ hd.ne'] at this
    have := intermediate_value_Icc hb (hcont.continuousOn)
    obtain ⟨φ, -, hφ⟩ := this (Set.mem_Icc.mpr ⟨by rw [hf0]; exact hu, h₁⟩)
    exact ⟨φ, hφ⟩
  · have hb : u / d ≤ 0 := div_nonpos_of_nonpos_of_nonneg hu hd.le
    have h₁ : f (u / d) ≤ u := by
      have := (key (u / d)).2 hb
      rwa [mul_div_cancel₀ _ hd.ne'] at this
    have := intermediate_value_Icc hb (hcont.continuousOn)
    obtain ⟨φ, -, hφ⟩ := this (Set.mem_Icc.mpr ⟨h₁, by rw [hf0]; exact hu⟩)
    exact ⟨φ, hφ⟩

end Pconstructible
