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
-- Most of the mathematical content arrives transitively through `Pptc.Defs`.
import Pptc.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.FieldTheory.Minpoly.Basic
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

/-! # Pptc.Basic

Basic theorems about P-constructible numbers.

`PConstructible` itself (and the mutually-inductive `PConstructibleCurve`) are
defined in `Pptc.Defs`; this module proves various facts about P-constructible numbers.
-/

namespace Pconstructible

-- Theorem: All natural numbers are P-constructible.
theorem nat_Pconstructible (n : ℕ) : PConstructible (n : ℝ) := by
  induction n with
  | zero =>
    -- 0 = 1 - 1
    convert PConstructible.sub PConstructible.base_one PConstructible.base_one
    simp
  | succ n ih =>
    -- n + 1 = (n : ℝ) + 1
    convert PConstructible.add ih PConstructible.base_one
    push_cast
    rfl

-- Theorem: All integers are P-constructible.
theorem int_Pconstructible (z : ℤ) : PConstructible (z : ℝ) := by
  cases z with
  | ofNat n =>
    exact nat_Pconstructible n
  | negSucc n =>
    have h1 : PConstructible ((n + 1 : ℕ) : ℝ) := nat_Pconstructible (n + 1)
    have h0 : PConstructible (0 : ℝ) := by
      convert PConstructible.sub PConstructible.base_one PConstructible.base_one
      simp
    -- z = 0 - (n + 1)
    convert PConstructible.sub h0 h1
    push_cast
    ring

-- Theorem: All rational numbers are P-constructible.
theorem rat_Pconstructible (q : ℚ) : PConstructible (q : ℝ) := by
  -- Use q.num and q.den directly instead of structural 'cases q' to
  -- match Mathlib's cast definitions
  have h1 : PConstructible (q.num : ℝ) := int_Pconstructible q.num
  have h2 : PConstructible (q.den : ℝ) := nat_Pconstructible q.den
  convert PConstructible.div h1 h2
  exact Rat.cast_def q

-- Theorem: 420/69 is P-constructible.
theorem example_420_69_Pconstructible : PConstructible (420 / 69 : ℝ) := by
  have := rat_Pconstructible ((420 : ℚ) / 69)
  simp only [Rat.cast_div, Rat.cast_ofNat] at this
  convert this

-- Theorem: 0 is P-constructible.
theorem zero_Pconstructible : PConstructible (0 : ℝ) := by
  convert PConstructible.sub PConstructible.base_one PConstructible.base_one
  simp

-- Theorem: the negation of a P-constructible number is P-constructible. `PConstructible`
-- has no negation constructor, but `0 - x` serves and this saves spelling that out.
theorem neg_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (-x) := by
  simpa using PConstructible.sub zero_Pconstructible hx

-- Theorem: the reciprocal of a P-constructible number is P-constructible. As for
-- `neg_Pconstructible`, this is just the corresponding closure constructor with `1` on
-- the left, restated in the form Mathlib's lemmas produce.
theorem inv_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible x⁻¹ := by
  simpa [one_div] using PConstructible.div PConstructible.base_one hx

-- Theorem: 2 is P-constructible.
theorem two_Pconstructible : PConstructible (2 : ℝ) := by
  convert PConstructible.add PConstructible.base_one PConstructible.base_one
  norm_num

/-! ### Reading a coordinate off a curve

The two workhorses. If a vertical line at a P-constructible abscissa meets a
constructible curve in a single point, that point's ordinate is P-constructible — and
symmetrically for horizontal lines.

No bound on the coordinate is needed. Cutting the curve requires a segment long enough
to reach it, but by the Archimedean property some natural number exceeds the coordinate
in absolute value, and every natural number is P-constructible, so a big enough
rectangle always exists. Geometrically: "draw a rectangle large enough". This is what
frees the results below from having to supply explicit bounds. -/

-- Theorem: the ordinate of a single crossing with a vertical line is P-constructible.
theorem ordinate_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {c y : ℝ} (hc : PConstructible c)
    (h : S ∩ {p : ℝ × ℝ | p.1 = c} = {(c, y)}) :
    PConstructible y := by
  obtain ⟨n, hn⟩ := exists_nat_gt |y|
  obtain ⟨hylo, hyhi⟩ := abs_lt.mp hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg y) hn
  have hnP : PConstructible ((n : ℝ)) := nat_Pconstructible n
  have hnegn : PConstructible (-(n : ℝ)) := neg_Pconstructible hnP
  have hmem : ((c, y) : ℝ × ℝ) ∈ S := (h.ge rfl).1
  -- Rectangle of centre `(c + 1, 0)`, width `2`, height `2n`; its left edge is the
  -- segment `{c} × [-n, n]`, isolated by cropping to abscissae at most `c`.
  have hRect := PConstructibleCurve.rectangle (c + 1) 0 2 (2 * (n : ℝ))
    (PConstructible.add hc PConstructible.base_one) zero_Pconstructible
    two_Pconstructible (PConstructible.mul two_Pconstructible hnP)
    (by norm_num) (by linarith)
  have hT := PConstructibleCurve.restrict hRect (c - 1) c (-(n : ℝ)) (n : ℝ)
    (PConstructible.sub hc PConstructible.base_one) hc hnegn hnP
  refine PConstructible.inter_y (x := c) hS hT ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hSmem, hR, hb1, hb2, hb3, hb4⟩
    have hu : u = c := by
      rcases hR with ⟨h1, _, _⟩ | ⟨_, _, h3⟩
      · linarith
      · rcases h3 with h3 | h3 <;> linarith
    have hpt : ((u, v) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.1 = c} := ⟨hSmem, hu⟩
    rw [h] at hpt
    simpa using hpt
  · rintro ⟨rfl, rfl⟩
    exact ⟨hmem, Or.inr ⟨by linarith, by linarith, Or.inl (by ring)⟩,
      by linarith, le_rfl, by linarith, by linarith⟩

-- Theorem: the abscissa of a single crossing with a horizontal line is P-constructible.
theorem abscissa_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {x c : ℝ} (hc : PConstructible c)
    (h : S ∩ {p : ℝ × ℝ | p.2 = c} = {(x, c)}) :
    PConstructible x := by
  obtain ⟨n, hn⟩ := exists_nat_gt |x|
  obtain ⟨hxlo, hxhi⟩ := abs_lt.mp hn
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_le_of_lt (abs_nonneg x) hn
  have hnP : PConstructible ((n : ℝ)) := nat_Pconstructible n
  have hnegn : PConstructible (-(n : ℝ)) := neg_Pconstructible hnP
  have hmem : ((x, c) : ℝ × ℝ) ∈ S := (h.ge rfl).1
  -- Rectangle of centre `(0, c + 1)`, width `2n`, height `2`; its bottom edge is the
  -- segment `[-n, n] × {c}`, isolated by cropping to ordinates at most `c`.
  have hRect := PConstructibleCurve.rectangle 0 (c + 1) (2 * (n : ℝ)) 2
    zero_Pconstructible (PConstructible.add hc PConstructible.base_one)
    (PConstructible.mul two_Pconstructible hnP) two_Pconstructible
    (by linarith) (by norm_num)
  have hT := PConstructibleCurve.restrict hRect (-(n : ℝ)) (n : ℝ) (c - 1) c
    hnegn hnP (PConstructible.sub hc PConstructible.base_one) hc
  refine PConstructible.inter_x (y := c) hS hT ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hSmem, hR, hb1, hb2, hb3, hb4⟩
    have hv : v = c := by
      rcases hR with ⟨_, _, h3⟩ | ⟨h1, _, _⟩
      · rcases h3 with h3 | h3 <;> linarith
      · linarith
    have hpt : ((u, v) : ℝ × ℝ) ∈ S ∩ {p : ℝ × ℝ | p.2 = c} := ⟨hSmem, hv⟩
    rw [h] at hpt
    simpa using hpt
  · rintro ⟨rfl, rfl⟩
    exact ⟨hmem, Or.inl ⟨by linarith, by linarith, Or.inl (by ring)⟩,
      by linarith, by linarith, by linarith, le_rfl⟩

-- Theorem: the square root of a P-constructible number is P-constructible.
theorem sqrt_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.sqrt x) := by
  by_cases h : x ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos h]
    exact zero_Pconstructible
  · push Not at h
    -- `√x` is just the ordinate of the curve `y = t ^ (1/2)` above `t = x`. No bound on
    -- `√x` is needed; `ordinate_Pconstructible` supplies a large enough rectangle.
    refine ordinate_Pconstructible (PConstructibleCurve.power_law 1 (1 / 2)) hx ?_
    ext ⟨a, b⟩
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
    push_cast
    constructor
    · rintro ⟨⟨ha, hb⟩, hline⟩
      subst hline
      exact ⟨rfl, by rw [hb, one_mul, Real.sqrt_eq_rpow]⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨h, by rw [one_mul, Real.sqrt_eq_rpow]⟩, rfl⟩

-- Theorem: the square of a P-constructible number is P-constructible.
theorem sq_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (x ^ 2) := by
  have := PConstructible.mul hx hx
  rwa [← sq] at this

-- Theorem: the distance between two P-constructible points is P-constructible.
-- This needs no appeal to `PConstructible.arc_length`; it is just the distance formula
-- fed through `sqrt_Pconstructible`.
theorem dist_Pconstructible {x₀ y₀ x₁ y₁ : ℝ}
    (hx₀ : PConstructible x₀) (hy₀ : PConstructible y₀)
    (hx₁ : PConstructible x₁) (hy₁ : PConstructible y₁) :
    PConstructible (Real.sqrt ((x₁ - x₀) ^ 2 + (y₁ - y₀) ^ 2)) :=
  sqrt_Pconstructible
    (PConstructible.add (sq_Pconstructible (PConstructible.sub hx₁ hx₀))
      (sq_Pconstructible (PConstructible.sub hy₁ hy₀)))

/-! ### Algebraic numbers of degree at most 6

The drawing program can plot the graph of any rational polynomial of degree at most `6`,
and that one curve family already reaches every real algebraic number of degree at
most `6`. The construction is the obvious one: plot a polynomial that kills `x` and read
off where its graph crosses the horizontal axis.

All of the work is in making that crossing *unique*, since `abscissa_Pconstructible`
(and behind it `PConstructible.inter_x`) demands that the two curves meet in a single
point, while a degree-`6` polynomial may cross the axis six times. A nonzero
polynomial has only finitely many roots, so the roots other than `x` form a finite —
hence closed — set that `x` avoids, and some ball of radius `ε` around `x` misses all of
them. Cropping the graph to a window `[q₁, q₂] × [-1, 1]` whose abscissa bounds are
rationals drawn from inside that gap therefore leaves exactly one crossing, the wanted
one. Rationals are used for the bounds only because `PConstructibleCurve.restrict` needs
`PConstructible` ones and `rat_Pconstructible` is the cheapest supply; any
P-constructible pair inside the gap would serve equally well.

The degree bound is inherited verbatim from `PConstructibleCurve.poly_graph`; nothing
else in the argument is sensitive to it — and the next section lifts it to `8` by bringing
a second curve family to the crossing. -/

-- Theorem: a root of a nonzero rational polynomial of degree at most 6 is
-- P-constructible.
theorem root_Pconstructible_le_six {x : ℝ} {p : Polynomial ℚ} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ 6) (hroot : Polynomial.aeval x p = 0) :
    PConstructible x := by
  -- Move to `ℝ[X]`, where Mathlib's finiteness of the root set is stated.
  set P : Polynomial ℝ := p.map (algebraMap ℚ ℝ) with hPdef
  have hPne : P ≠ 0 := by
    rw [hPdef]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℚ ℝ).injective).mpr hp
  have heval : ∀ t : ℝ, Polynomial.aeval t p = P.eval t := by
    intro t
    simp [hPdef, Polynomial.eval_map, Polynomial.aeval_def]
  -- The roots other than `x` form a finite, hence closed, set avoiding `x`, so some
  -- ball around `x` contains no other root.
  have hAfin : {t : ℝ | P.IsRoot t ∧ t ≠ x}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset (fun t ht => ht.1)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hAfin.isClosed.isOpen_compl x (fun h => h.2 rfl)
  -- Rational abscissa bounds strictly inside that ball, straddling `x`.
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show x - ε < x by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show x < x + ε by linarith)
  have huniq : ∀ t : ℝ, Polynomial.aeval t p = 0 → (q₁ : ℝ) ≤ t → t ≤ (q₂ : ℝ) → t = x := by
    intro t ht hlo hhi
    have hmem : t ∈ Metric.ball x ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hnot := hball hmem
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not] at hnot
    exact hnot (by rw [Polynomial.IsRoot, ← heval]; exact ht)
  -- The graph of `p`, cropped to that window, meets the horizontal axis exactly once.
  have hS := PConstructibleCurve.restrict (PConstructibleCurve.poly_graph p hdeg)
    (q₁ : ℝ) (q₂ : ℝ) (-1) 1 (rat_Pconstructible q₁) (rat_Pconstructible q₂)
    (neg_Pconstructible PConstructible.base_one) PConstructible.base_one
  refine abscissa_Pconstructible hS zero_Pconstructible ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hgraph, hb1, hb2, -, -⟩, hline⟩
    exact ⟨huniq u (by rw [← hgraph]; exact hline) hb1 hb2, hline⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨hroot.symm, hq₁b.le, hq₂a.le, by norm_num, by norm_num⟩, rfl⟩

-- Theorem: every real algebraic number of degree at most 6 over ℚ is P-constructible.
-- Its minimal polynomial is a nonzero rational polynomial of degree at most 6 that
-- kills it, so `root_Pconstructible_le_six` applies directly.
theorem algebraic_Pconstructible_le_six {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hdeg : (minpoly ℚ x).natDegree ≤ 6) :
    PConstructible x :=
  root_Pconstructible_le_six (minpoly.ne_zero hx.isIntegral) hdeg (minpoly.aeval ℚ x)

/-! ### Algebraic numbers of degree at most 8

The degree-6 ceiling above belongs to `poly_graph`, not to the drawing program.
`power_law` will plot `y = x ^ n` for any `n`, and that one extra curve family lifts the
ceiling by two.

Cross `y = x ^ 7` with the graph of a rational `p` of degree at most 6: the crossings are
the roots of `x ^ 7 - p x`, and as `p` ranges over the rational polynomials of degree at
most 6 that is *every* monic rational septic. The power curve supplies the leading term and
the graph supplies everything below it, so nothing is asked of `poly_graph` beyond what it
draws. A leading coefficient other than `1` costs nothing either, since `power_law` carries
its own factor `a`.

Degree 8 needs one more idea. Crossing `y = x ^ 8` with a degree-6 graph reaches the octics
whose `X ^ 7` coefficient vanishes — but that coefficient can always be removed first.
Substituting `X = Z - c₇ / (8 c₈)` shifts every root by a rational and kills the second
coefficient, and a rational shift costs nothing in P-constructibility. That substitution is
`Polynomial.taylor`, and `taylor_coeff_seven` below is the computation that it works.

Degree 9 is where this stops. Crossing `y = x ^ 9` with a degree-6 graph would need the
`X ^ 8` *and* `X ^ 7` coefficients to vanish, and one shift kills only one of them. Getting
past it needs a graph of degree 7 or more, which is exactly what `poly_graph` will not draw.

One wrinkle throughout: `power_law` draws only the branch `x > 0`. A negative root is
reached by reflecting the whole picture in the `y` axis, which replaces `p` by `p (-X)` and
leaves the degree bound intact. -/

section PowerLaw

open Polynomial

-- Theorem: the power curve `y = a * x ^ n` meets the graph of a rational polynomial `p` of
-- degree at most 6 exactly where `a * x ^ n = p x`. A *positive* root is P-constructible.
theorem powerLaw_root_pos_Pconstructible {n : ℕ} (hn : 6 < n) {a : ℚ} (ha : a ≠ 0)
    {p : Polynomial ℚ} (hdeg : p.natDegree ≤ 6) {β : ℝ} (hβ : 0 < β)
    (heq : (a : ℝ) * β ^ n = aeval β p) :
    PConstructible β := by
  -- `a * X ^ n - p` is nonzero, because `n` exceeds the degree of `p`.
  set P : Polynomial ℝ := C (a : ℝ) * X ^ n - p.map (algebraMap ℚ ℝ) with hPdef
  have hane : (a : ℝ) ≠ 0 := by exact_mod_cast ha
  have hmapdeg : (p.map (algebraMap ℚ ℝ)).natDegree ≤ 6 := by
    rw [Polynomial.natDegree_map]; exact hdeg
  have hPne : P ≠ 0 := by
    intro h
    have hEq : (C (a : ℝ) * X ^ n : Polynomial ℝ) = p.map (algebraMap ℚ ℝ) := by
      rwa [hPdef, sub_eq_zero] at h
    have h1 : (C (a : ℝ) * X ^ n : Polynomial ℝ).natDegree = n := by
      rw [Polynomial.natDegree_C_mul hane, Polynomial.natDegree_X_pow]
    rw [hEq] at h1
    omega
  have hevalP : ∀ t : ℝ, P.eval t = (a : ℝ) * t ^ n - aeval t p := by
    intro t
    simp [hPdef, Polynomial.eval_map, ← Polynomial.aeval_def]
  have hroot : P.IsRoot β := by
    rw [Polynomial.IsRoot, hevalP, heq, sub_self]
  -- Isolate `β` from the finitely many other roots, keeping the window inside `x > 0`.
  have hAfin : {t : ℝ | P.IsRoot t ∧ t ≠ β}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset (fun t ht => ht.1)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hAfin.isClosed.isOpen_compl β (fun h => h.2 rfl)
  have hδ : 0 < min ε β := lt_min hε hβ
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show β - min ε β < β by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show β < β + min ε β by linarith)
  have hq₁pos : (0 : ℝ) < q₁ := by
    have : min ε β ≤ β := min_le_right _ _
    linarith
  have huniq : ∀ t : ℝ, P.IsRoot t → (q₁ : ℝ) ≤ t → t ≤ (q₂ : ℝ) → t = β := by
    intro t ht hlo hhi
    have hδε : min ε β ≤ ε := min_le_left _ _
    have hmem : t ∈ Metric.ball β ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hnot := hball hmem
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not] at hnot
    exact hnot ht
  -- A window tall enough to hold the crossing, whichever sign `a` has.
  obtain ⟨M, hM⟩ := exists_nat_gt (|(a : ℝ)| * (q₂ : ℝ) ^ n)
  have hS := PConstructibleCurve.restrict (PConstructibleCurve.power_law a (n : ℚ))
    (q₁ : ℝ) (q₂ : ℝ) (-(M : ℝ)) (M : ℝ) (rat_Pconstructible q₁) (rat_Pconstructible q₂)
    (neg_Pconstructible (nat_Pconstructible M)) (nat_Pconstructible M)
  refine PConstructible.inter_x hS (PConstructibleCurve.poly_graph p hdeg)
    (x := β) (y := (a : ℝ) * β ^ n) ?_
  have hpow : ∀ u : ℝ, 0 < u → u ^ (((n : ℚ) : ℝ)) = u ^ n := by
    intro u hu
    push_cast
    exact Real.rpow_natCast u n
  have hbound : |(a : ℝ) * β ^ n| < (M : ℝ) := by
    have h1 : β ^ n ≤ (q₂ : ℝ) ^ n := pow_le_pow_left₀ hβ.le hq₂a.le n
    have h2 : (0 : ℝ) < β ^ n := pow_pos hβ n
    calc |(a : ℝ) * β ^ n| = |(a : ℝ)| * β ^ n := by rw [abs_mul, abs_of_pos h2]
      _ ≤ |(a : ℝ)| * (q₂ : ℝ) ^ n := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ < (M : ℝ) := hM
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hbound
  have hmem : ((β, (a : ℝ) * β ^ n) : ℝ × ℝ) ∈
      ({pt : ℝ × ℝ | 0 < pt.1 ∧ pt.2 = (a : ℝ) * pt.1 ^ (((n : ℚ)) : ℝ)} ∩
        {pt : ℝ × ℝ | (q₁ : ℝ) ≤ pt.1 ∧ pt.1 ≤ (q₂ : ℝ) ∧
          -(M : ℝ) ≤ pt.2 ∧ pt.2 ≤ (M : ℝ)}) ∩
      {pt : ℝ × ℝ | pt.2 = aeval pt.1 p} :=
    ⟨⟨⟨hβ, by rw [hpow β hβ]⟩, hq₁b.le, hq₂a.le, hlo.le, hhi.le⟩, heq⟩
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨⟨hupos, hv⟩, hb1, hb2, -, -⟩, hgraph⟩
    rw [hpow u hupos] at hv
    have hru : P.IsRoot u := by
      rw [Polynomial.IsRoot, hevalP, ← hgraph, ← hv, sub_self]
    have hu : u = β := huniq u hru hb1 hb2
    exact ⟨hu, by rw [hv, hu]⟩
  · rintro ⟨rfl, rfl⟩
    exact hmem

-- Theorem: the same for a negative root. `power_law` only ever draws `x > 0`, so the
-- left-hand crossing is found by reflecting the picture in the `y` axis, which replaces
-- `p` by `p (-X)`.
theorem powerLaw_root_Pconstructible {n : ℕ} (hn : 6 < n) {a : ℚ} (ha : a ≠ 0)
    {p : Polynomial ℚ} (hdeg : p.natDegree ≤ 6) {β : ℝ} (hβ : β ≠ 0)
    (heq : (a : ℝ) * β ^ n = aeval β p) :
    PConstructible β := by
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · have hγ : 0 < -β := by linarith
    have hdeg' : (p.comp (-X)).natDegree ≤ 6 := by
      rw [Polynomial.natDegree_comp]
      simpa using hdeg
    have hane : a * (-1) ^ n ≠ 0 := mul_ne_zero ha (pow_ne_zero n (by norm_num))
    have heq' : ((a * (-1) ^ n : ℚ) : ℝ) * (-β) ^ n = aeval (-β) (p.comp (-X)) := by
      rw [Polynomial.aeval_comp]
      simp only [map_neg, Polynomial.aeval_X, neg_neg]
      rw [neg_pow, ← heq]
      push_cast
      have hsq : ((-1 : ℝ)) ^ n * ((-1 : ℝ)) ^ n = 1 := by
        rw [← pow_add, ← two_mul, pow_mul]; norm_num
      linear_combination ((a : ℝ) * β ^ n) * hsq
    have h := powerLaw_root_pos_Pconstructible hn hane hdeg' hγ heq'
    simpa using neg_Pconstructible h
  · exact powerLaw_root_pos_Pconstructible hn ha hdeg hpos heq

-- Theorem: every real root of a nonzero rational polynomial of degree at most 7 is
-- P-constructible. The power curve `y = a * x ^ 7` supplies the leading term, so the
-- degree-6 graph carries the whole tail and no depression is needed.
theorem root_Pconstructible_le_seven {x : ℝ} {q : Polynomial ℚ} (hq : q ≠ 0)
    (hdeg : q.natDegree ≤ 7) (hroot : aeval x q = 0) :
    PConstructible x := by
  by_cases h6 : q.natDegree ≤ 6
  · exact root_Pconstructible_le_six hq h6 hroot
  · have h7' : q.natDegree = 7 := by omega
    rcases eq_or_ne x 0 with rfl | hx0
    · exact zero_Pconstructible
    · set a : ℚ := q.leadingCoeff with hadef
      have ha : a ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      have hq7 : q.coeff 7 = a := by rw [hadef, Polynomial.leadingCoeff, h7']
      set p : Polynomial ℚ := C a * X ^ 7 - q with hpdef
      have hpdeg : p.natDegree ≤ 6 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h | h
        · simp [hpdef, ← h, hq7]
        · have hqN : q.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
          simp [hpdef, hqN, Polynomial.coeff_X_pow, show N ≠ 7 by omega]
      have heq : (a : ℝ) * x ^ 7 = aeval x p := by
        rw [hpdef]
        simp [hroot]
      exact powerLaw_root_Pconstructible (by norm_num) ha hpdeg hx0 heq

-- Theorem: the coefficient of `X ^ 7` in the shifted polynomial `q (X + s)`.
theorem taylor_coeff_seven {q : Polynomial ℚ} (h8 : q.natDegree = 8) (s : ℚ) :
    (taylor s q).coeff 7 = q.coeff 7 + 8 * q.coeff 8 * s := by
  rw [Polynomial.taylor_coeff]
  have hd : (Polynomial.hasseDeriv 7 q).natDegree < 2 := by
    have := Polynomial.natDegree_hasseDeriv_le q 7
    omega
  rw [Polynomial.eval_eq_sum_range' hd]
  simp [Finset.sum_range_succ, Polynomial.hasseDeriv_coeff]

-- Theorem: shifting does not disturb the leading coefficient.
theorem taylor_coeff_eight {q : Polynomial ℚ} (h8 : q.natDegree = 8) (s : ℚ) :
    (taylor s q).coeff 8 = q.coeff 8 := by
  rw [Polynomial.taylor_coeff]
  have hd : (Polynomial.hasseDeriv 8 q).natDegree < 1 := by
    have := Polynomial.natDegree_hasseDeriv_le q 8
    omega
  rw [Polynomial.eval_eq_sum_range' hd]
  simp [Polynomial.hasseDeriv_coeff]

-- Theorem: every real root of a nonzero rational polynomial of degree at most 8 is
-- P-constructible.
theorem root_Pconstructible_le_eight {x : ℝ} {q : Polynomial ℚ} (hq : q ≠ 0)
    (hdeg : q.natDegree ≤ 8) (hroot : aeval x q = 0) :
    PConstructible x := by
  by_cases h7 : q.natDegree ≤ 7
  · exact root_Pconstructible_le_seven hq h7 hroot
  · have h8 : q.natDegree = 8 := by omega
    have ha : q.coeff 8 ≠ 0 := by
      rw [← h8]
      exact Polynomial.leadingCoeff_ne_zero.mpr hq
    set s : ℚ := -(q.coeff 7) / (8 * q.coeff 8) with hsdef
    set r : Polynomial ℚ := taylor s q with hrdef
    have hr8 : r.coeff 8 = q.coeff 8 := taylor_coeff_eight h8 s
    have hr7 : r.coeff 7 = 0 := by
      rw [hrdef, taylor_coeff_seven h8 s, hsdef]
      field_simp
      ring
    have hrdeg : r.natDegree = 8 := by rw [hrdef, Polynomial.natDegree_taylor]; exact h8
    -- `z = x - s` is a root of `r`, and `r` has no `X ^ 7` term.
    have hrz : aeval (x - s) r = 0 := by
      rw [hrdef, Polynomial.taylor_apply, Polynomial.aeval_comp]
      simp only [map_add, Polynomial.aeval_X, Polynomial.aeval_C, eq_ratCast]
      rw [show x - (s : ℝ) + (s : ℝ) = x by ring]
      exact hroot
    rcases eq_or_ne (x - s) 0 with hz | hz
    · have : x = (s : ℝ) := by linarith [hz]
      rw [this]
      exact rat_Pconstructible s
    · set p : Polynomial ℚ := C (q.coeff 8) * X ^ 8 - r with hpdef
      have hpdeg : p.natDegree ≤ 6 := by
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro N hN
        rcases eq_or_lt_of_le (Nat.succ_le_of_lt hN) with h | h
        · simp [hpdef, ← h, hr7]
        · rcases eq_or_lt_of_le (Nat.succ_le_of_lt h) with h' | h'
          · simp [hpdef, ← h', hr8]
          · have hrN : r.coeff N = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
            simp [hpdef, hrN, Polynomial.coeff_X_pow, show N ≠ 8 by omega]
      have heq : ((q.coeff 8 : ℚ) : ℝ) * (x - s) ^ 8 = aeval (x - s) p := by
        rw [hpdef]
        simp [hrz]
      have hzP := powerLaw_root_Pconstructible (by norm_num) ha hpdeg hz heq
      have : x = (x - (s : ℝ)) + (s : ℝ) := by ring
      rw [this]
      exact PConstructible.add hzP (rat_Pconstructible s)

-- Theorem: every real algebraic number of degree at most 8 over ℚ is P-constructible.
theorem algebraic_Pconstructible_le_eight {x : ℝ} (hx : IsAlgebraic ℚ x)
    (hdeg : (minpoly ℚ x).natDegree ≤ 8) :
    PConstructible x :=
  root_Pconstructible_le_eight (minpoly.ne_zero hx.isIntegral) hdeg (minpoly.aeval ℚ x)

end PowerLaw


/-- The linear parametrization of the segment from `p` to `q`, traced over `[0, 1]`. -/
def segmentParam (p q : ℝ × ℝ) : ℝ → ℝ × ℝ :=
  fun t => (p.1 + t * (q.1 - p.1), p.2 + t * (q.2 - p.2))

-- Theorem: a segment is traced at constant speed, namely the distance between its
-- endpoints.
theorem speed_segmentParam (p q : ℝ × ℝ) :
    speed (segmentParam p q) = fun _ => Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
  have hd : ∀ (c d : ℝ) (t : ℝ), HasDerivAt (fun s : ℝ => c + s * d) d t := by
    intro c d t
    simpa using ((hasDerivAt_id t).mul_const d).const_add c
  ext t
  change Real.sqrt (deriv (fun s : ℝ => p.1 + s * (q.1 - p.1)) t ^ 2 +
      deriv (fun s : ℝ => p.2 + s * (q.2 - p.2)) t ^ 2) = _
  rw [(hd p.1 (q.1 - p.1) t).deriv, (hd p.2 (q.2 - p.2) t).deriv]

-- Theorem: `arcLengthOf` really does compute length — on a straight segment it returns
-- exactly the distance formula. This is the sanity check that `speed` / `arcLengthOf`
-- were written correctly.
theorem arcLengthOf_segmentParam (p q : ℝ × ℝ) :
    arcLengthOf (segmentParam p q) 0 1 =
      Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2) := by
  rw [arcLengthOf, speed_segmentParam]
  simp

-- Theorem: a straight segment lying inside a constructible curve, with `PConstructible`
-- endpoints, has `PConstructible` arc length.
--
-- Note the conclusion is *identical* to that of `dist_Pconstructible` above, which is
-- proved without `PConstructible.arc_length`. That is the intended sanity check on the
-- new constructor: on straight segments it grants no number that was not already
-- constructible. It also exercises every side condition of the constructor, confirming
-- they are dischargeable in practice.
theorem arcLength_segment_Pconstructible {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (p q : ℝ × ℝ) (hne : p ≠ q)
    (hsub : segmentParam p q '' Set.Icc 0 1 ⊆ S)
    (hp1 : PConstructible p.1) (hp2 : PConstructible p.2)
    (hq1 : PConstructible q.1) (hq2 : PConstructible q.2) :
    PConstructible (Real.sqrt ((q.1 - p.1) ^ 2 + (q.2 - p.2) ^ 2)) := by
  rw [← arcLengthOf_segmentParam p q]
  -- `p ≠ q` means the segment is nondegenerate in at least one coordinate, which is what
  -- makes the parametrization injective.
  have hkey : q.1 - p.1 ≠ 0 ∨ q.2 - p.2 ≠ 0 := by
    simpa [sub_ne_zero, ne_comm, Prod.ext_iff, not_and_or, or_iff_not_imp_left] using hne
  refine PConstructible.arc_length hS _ zero_le_one hsub ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- injective on `[0, 1]`
    intro t₁ _ t₂ _ h
    have h1 : p.1 + t₁ * (q.1 - p.1) = p.1 + t₂ * (q.1 - p.1) := congrArg Prod.fst h
    have h2 : p.2 + t₁ * (q.2 - p.2) = p.2 + t₂ * (q.2 - p.2) := congrArg Prod.snd h
    rcases hkey with hk | hk
    · exact mul_right_cancel₀ hk (by linarith : t₁ * (q.1 - p.1) = t₂ * (q.1 - p.1))
    · exact mul_right_cancel₀ hk (by linarith : t₁ * (q.2 - p.2) = t₂ * (q.2 - p.2))
  · -- differentiable in each coordinate
    intro t _
    exact ⟨by fun_prop, by fun_prop⟩
  · -- the speed is constant, hence integrable
    rw [speed_segmentParam]
    exact intervalIntegrable_const
  · simpa [segmentParam] using hp1
  · simpa [segmentParam] using hp2
  · simpa [segmentParam] using hq1
  · simpa [segmentParam] using hq2

/-! ### Cubic Bézier curves

Sanity checks on the `cubic_bezier` primitive. The drawn arc really does run from the
first control point to the last, and spacing the four control points evenly along a line
collapses the Bernstein cubic to the straight parametrization `segmentParam`.

The latter is what makes the primitive earn its place: it turns every segment between
P-constructible endpoints into a constructible curve. That was not available before —
`poly_graph` is a graph over `x`, so it cannot produce a vertical segment, and its
coefficients are rational rather than merely P-constructible. -/

-- Theorem: a cubic Bézier starts at its first control point.
theorem bezierParam_zero (p₁ p₂ p₃ p₄ : ℝ × ℝ) : bezierParam p₁ p₂ p₃ p₄ 0 = p₁ := by
  simp [bezierParam]

-- Theorem: ... and ends at its last.
theorem bezierParam_one (p₁ p₂ p₃ p₄ : ℝ × ℝ) : bezierParam p₁ p₂ p₃ p₄ 1 = p₄ := by
  simp [bezierParam]

-- Theorem: control points spaced evenly along the segment from `p` to `q` make the
-- Bézier the linear parametrization of that segment (the Bernstein weights reproduce
-- the identity, so the cubic terms cancel exactly).
theorem bezierParam_eq_segmentParam (p q : ℝ × ℝ) :
    bezierParam p (p.1 + (q.1 - p.1) / 3, p.2 + (q.2 - p.2) / 3)
        (p.1 + 2 * (q.1 - p.1) / 3, p.2 + 2 * (q.2 - p.2) / 3) q =
      segmentParam p q := by
  funext t
  simp only [bezierParam, segmentParam, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: 3 is P-constructible.
theorem three_Pconstructible : PConstructible (3 : ℝ) := by
  convert PConstructible.add two_Pconstructible PConstructible.base_one
  norm_num

-- Theorem: the straight segment joining two P-constructible points is a constructible
-- curve.
theorem segment_PConstructibleCurve (p q : ℝ × ℝ)
    (hp1 : PConstructible p.1) (hp2 : PConstructible p.2)
    (hq1 : PConstructible q.1) (hq2 : PConstructible q.2) :
    PConstructibleCurve (segmentParam p q '' Set.Icc 0 1) := by
  rw [← bezierParam_eq_segmentParam]
  -- The interior control points are P-constructible, being built from the endpoints by
  -- `+ - * /` alone.
  have hmid : ∀ c : ℝ, PConstructible c → ∀ a b : ℝ, PConstructible a → PConstructible b →
      PConstructible (a + c * (b - a) / 3) := fun c hc a b ha hb =>
    PConstructible.add ha
      (PConstructible.div (PConstructible.mul hc (PConstructible.sub hb ha))
        three_Pconstructible)
  refine PConstructibleCurve.cubic_bezier _ _ _ _ hp1 hp2 ?_ ?_ ?_ ?_ hq1 hq2
  · simpa using hmid 1 PConstructible.base_one _ _ hp1 hq1
  · simpa using hmid 1 PConstructible.base_one _ _ hp2 hq2
  · exact hmid 2 two_Pconstructible _ _ hp1 hq1
  · exact hmid 2 two_Pconstructible _ _ hp2 hq2

/-! ### Polynomials with P-constructible coefficients

Everything above solves polynomials with *rational* coefficients, because that is all
`poly_graph` will draw. `cubic_bezier` will draw more: its control points are
P-constructible, and the Bernstein basis is an invertible rational change of basis, so
choosing the four abscissae in arithmetic progression makes the curve the graph of an
*arbitrary* cubic with P-constructible coefficients, over any interval with P-constructible
endpoints. That is `cubicGraph_PConstructibleCurve`, and it is what lets the coefficients
leave ℚ.

Two constructions come out of it. Crossing that graph with the horizontal axis solves any
cubic; crossing it with the power curve `y = x ^ n` solves `x ^ n = c x` for any `n > 3`.
The second is the useful one, because of the Bring–Jerrard reduction: a Tschirnhaus
substitution `z = x³ + a x² + b x + c` kills the three coefficients below the leading one,
and the three conditions are the first three elementary symmetric functions of the new
roots — degrees `1`, `2`, `3` in `(a, b, c)` — so they are solved by a linear equation, a
square root and a cubic, all P-constructible. A polynomial of degree `n` is thereby reduced
to `z ^ n = (tail of degree n - 4)`, and a cubic tail covers `n ≤ 7`.

The pattern behind both this section and the last is the same. Solving `x ^ n = p x` needs
the coefficients between the tail and the leading term to vanish, so with a graph of degree
`d` and `r` coefficients removable by a change of variable,

  `n ≤ d + r + 1`.

Over ℚ that reads `6 + 1 + 1 = 8`: `poly_graph` gives `d = 6`, and only the depression is
rational. Here it reads `3 + 3 + 1 = 7`: the Bézier gives `d = 3`, and Bring–Jerrard gives
`r = 3`. Degree 8 over the P-constructible field would need a fourth coefficient removed,
which is where the classical theory stops — the fourth condition is quartic and the system
ceases to be triangular — or a P-constructible *quartic* graph, which `cubic_bezier` does
not draw.

Unlike the degree-8 theorem this one takes P-constructible coefficients, so it iterates:
the P-constructible reals are closed under solving any polynomial of degree at most 7 over
themselves. -/

section BezierGraph

open Polynomial

theorem pow_Pconstructible {x : ℝ} (hx : PConstructible x) :
    ∀ n : ℕ, PConstructible (x ^ n)
  | 0 => by simpa using PConstructible.base_one
  | n + 1 => by rw [pow_succ]; exact PConstructible.mul (pow_Pconstructible hx n) hx

/-- The cubic `c₃ x³ + c₂ x² + c₁ x + c₀`. -/
def cubicVal (c₀ c₁ c₂ c₃ x : ℝ) : ℝ := c₃ * x ^ 3 + c₂ * x ^ 2 + c₁ * x + c₀

/-- Its derivative, which is where the Bézier handles go. -/
def cubicDer (c₁ c₂ c₃ x : ℝ) : ℝ := 3 * c₃ * x ^ 2 + 2 * c₂ * x + c₁

/-- The graph of that cubic over the interval `[u, v]`. -/
def cubicGraph (c₀ c₁ c₂ c₃ u v : ℝ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | u ≤ p.1 ∧ p.1 ≤ v ∧ p.2 = cubicVal c₀ c₁ c₂ c₃ p.1}

theorem cubicVal_Pconstructible {c₀ c₁ c₂ c₃ x : ℝ} (h₀ : PConstructible c₀)
    (h₁ : PConstructible c₁) (h₂ : PConstructible c₂) (h₃ : PConstructible c₃)
    (hx : PConstructible x) : PConstructible (cubicVal c₀ c₁ c₂ c₃ x) :=
  PConstructible.add (PConstructible.add (PConstructible.add
    (PConstructible.mul h₃ (pow_Pconstructible hx 3))
    (PConstructible.mul h₂ (pow_Pconstructible hx 2)))
    (PConstructible.mul h₁ hx)) h₀

theorem cubicDer_Pconstructible {c₁ c₂ c₃ x : ℝ} (h₁ : PConstructible c₁)
    (h₂ : PConstructible c₂) (h₃ : PConstructible c₃) (hx : PConstructible x) :
    PConstructible (cubicDer c₁ c₂ c₃ x) :=
  PConstructible.add (PConstructible.add
    (PConstructible.mul (PConstructible.mul three_Pconstructible h₃)
      (pow_Pconstructible hx 2))
    (PConstructible.mul (PConstructible.mul two_Pconstructible h₂) hx)) h₁

-- Theorem: the graph of a cubic with P-constructible coefficients, over any interval with
-- P-constructible endpoints, is a constructible curve. The control points are the two
-- endpoints of the arc together with the two handles at a third of the tangent.
theorem cubicGraph_PConstructibleCurve {c₀ c₁ c₂ c₃ u v : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (hu : PConstructible u) (hv : PConstructible v)
    (huv : u < v) :
    PConstructibleCurve (cubicGraph c₀ c₁ c₂ c₃ u v) := by
  have hvu : v - u ≠ 0 := by linarith
  have hh : PConstructible (v - u) := PConstructible.sub hv hu
  have hthree : PConstructible (3 : ℝ) := three_Pconstructible
  set P₁ : ℝ × ℝ := (u, cubicVal c₀ c₁ c₂ c₃ u) with hP₁
  set P₂ : ℝ × ℝ :=
    (u + (v - u) / 3, cubicVal c₀ c₁ c₂ c₃ u + (v - u) * cubicDer c₁ c₂ c₃ u / 3) with hP₂
  set P₃ : ℝ × ℝ :=
    (v - (v - u) / 3, cubicVal c₀ c₁ c₂ c₃ v - (v - u) * cubicDer c₁ c₂ c₃ v / 3) with hP₃
  set P₄ : ℝ × ℝ := (v, cubicVal c₀ c₁ c₂ c₃ v) with hP₄
  have hbez := PConstructibleCurve.cubic_bezier P₁ P₂ P₃ P₄
    hu (cubicVal_Pconstructible h₀ h₁ h₂ h₃ hu)
    (PConstructible.add hu (PConstructible.div hh hthree))
    (PConstructible.add (cubicVal_Pconstructible h₀ h₁ h₂ h₃ hu)
      (PConstructible.div (PConstructible.mul hh (cubicDer_Pconstructible h₁ h₂ h₃ hu))
        hthree))
    (PConstructible.sub hv (PConstructible.div hh hthree))
    (PConstructible.sub (cubicVal_Pconstructible h₀ h₁ h₂ h₃ hv)
      (PConstructible.div (PConstructible.mul hh (cubicDer_Pconstructible h₁ h₂ h₃ hv))
        hthree))
    hv (cubicVal_Pconstructible h₀ h₁ h₂ h₃ hv)
  -- The Bézier traces exactly the graph: its abscissa is affine in `t` and its ordinate is
  -- the cubic of that abscissa.
  have hparam : ∀ t : ℝ, bezierParam P₁ P₂ P₃ P₄ t =
      (u + (v - u) * t, cubicVal c₀ c₁ c₂ c₃ (u + (v - u) * t)) := by
    intro t
    simp only [bezierParam, hP₁, hP₂, hP₃, hP₄, cubicVal, cubicDer, Prod.mk.injEq]
    constructor <;> ring
  convert hbez using 1
  ext ⟨a, b⟩
  simp only [cubicGraph, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · rintro ⟨hle, hge, hb⟩
    refine ⟨(a - u) / (v - u), ⟨div_nonneg (by linarith) (by linarith), ?_⟩, ?_⟩
    · rw [div_le_one (by linarith)]; linarith
    · rw [hparam]
      have hx : u + (v - u) * ((a - u) / (v - u)) = a := by field_simp; ring
      rw [hx, ← hb]
  · rintro ⟨t, ⟨ht0, ht1⟩, hpt⟩
    rw [hparam t, Prod.mk.injEq] at hpt
    obtain ⟨ha, hb⟩ := hpt
    subst ha
    subst hb
    exact ⟨by nlinarith, by nlinarith, rfl⟩

-- Theorem: crossing the power curve `y = x ^ n` with the graph of a cubic whose
-- coefficients are P-constructible solves `x ^ n = c x`, for a positive root.
theorem powerLaw_cubic_root_pos_Pconstructible {n : ℕ} (hn : 3 < n) {c₀ c₁ c₂ c₃ β : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (hβ : 0 < β) (heq : β ^ n = cubicVal c₀ c₁ c₂ c₃ β) :
    PConstructible β := by
  set P : Polynomial ℝ :=
    X ^ n - (C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀) with hPdef
  have hevalP : ∀ t : ℝ, P.eval t = t ^ n - cubicVal c₀ c₁ c₂ c₃ t := by
    intro t
    simp [hPdef, cubicVal]
  have hPne : P ≠ 0 := by
    intro hc
    have hcn : P.coeff n = 1 := by
      simp [hPdef, Polynomial.coeff_X_pow, Polynomial.coeff_C, Polynomial.coeff_X,
        show n ≠ 3 by omega, show n ≠ 2 by omega, show n ≠ 0 by omega,
        show (1 : ℕ) ≠ n by omega]
    rw [hc] at hcn
    simp at hcn
  have hroot : P.IsRoot β := by
    rw [Polynomial.IsRoot, hevalP, heq, sub_self]
  have hAfin : {t : ℝ | P.IsRoot t ∧ t ≠ β}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset (fun t ht => ht.1)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hAfin.isClosed.isOpen_compl β (fun h => h.2 rfl)
  have hδ : 0 < min ε β := lt_min hε hβ
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show β - min ε β < β by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show β < β + min ε β by linarith)
  have hq₁pos : (0 : ℝ) < q₁ := by
    have : min ε β ≤ β := min_le_right _ _
    linarith
  have huniq : ∀ t : ℝ, P.IsRoot t → (q₁ : ℝ) ≤ t → t ≤ (q₂ : ℝ) → t = β := by
    intro t ht hlo hhi
    have hδε : min ε β ≤ ε := min_le_left _ _
    have hmem : t ∈ Metric.ball β ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hnot := hball hmem
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not] at hnot
    exact hnot ht
  have hT := cubicGraph_PConstructibleCurve h₀ h₁ h₂ h₃
    (rat_Pconstructible q₁) (rat_Pconstructible q₂) (by linarith : (q₁ : ℝ) < q₂)
  refine PConstructible.inter_x (PConstructibleCurve.power_law 1 (n : ℚ)) hT
    (x := β) (y := β ^ n) ?_
  have hpow : ∀ t : ℝ, 0 < t → t ^ (((n : ℚ) : ℝ)) = t ^ n := by
    intro t ht
    push_cast
    exact Real.rpow_natCast t n
  have hmem : ((β, β ^ n) : ℝ × ℝ) ∈
      {pt : ℝ × ℝ | 0 < pt.1 ∧ pt.2 = ((1 : ℚ) : ℝ) * pt.1 ^ (((n : ℚ)) : ℝ)} ∩
        cubicGraph c₀ c₁ c₂ c₃ (q₁ : ℝ) (q₂ : ℝ) := by
    refine ⟨⟨hβ, ?_⟩, hq₁b.le, hq₂a.le, heq⟩
    rw [hpow β hβ]
    push_cast
    ring
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, cubicGraph, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hapos, hb⟩, hlo, hhi, hgraph⟩
    rw [hpow a hapos] at hb
    norm_num at hb
    have hra : P.IsRoot a := by
      rw [Polynomial.IsRoot, hevalP, ← hgraph, ← hb, sub_self]
    have ha : a = β := huniq a hra hlo hhi
    exact ⟨ha, by rw [hb, ha]⟩
  · rintro ⟨rfl, rfl⟩
    exact hmem

-- Theorem: the same for any root, positive, negative or zero. Reflecting in the `y` axis
-- turns the cubic `c` into `x ↦ (-1) ^ n * c (-x)`, whose coefficients are again
-- P-constructible.
theorem powerLaw_cubic_root_Pconstructible {n : ℕ} (hn : 3 < n) {c₀ c₁ c₂ c₃ β : ℝ}
    (h₀ : PConstructible c₀) (h₁ : PConstructible c₁) (h₂ : PConstructible c₂)
    (h₃ : PConstructible c₃) (heq : β ^ n = cubicVal c₀ c₁ c₂ c₃ β) :
    PConstructible β := by
  rcases lt_trichotomy β 0 with hneg | rfl | hpos
  · have hsign : PConstructible (((-1 : ℝ)) ^ n) :=
      pow_Pconstructible (neg_Pconstructible PConstructible.base_one) n
    have heq' : (-β) ^ n =
        cubicVal ((-1) ^ n * c₀) ((-1) ^ n * (-c₁)) ((-1) ^ n * c₂) ((-1) ^ n * (-c₃)) (-β) := by
      simp only [cubicVal] at heq ⊢
      have hb : (-β) ^ n = (-1 : ℝ) ^ n * β ^ n := by
        rw [← neg_one_mul, mul_pow]
      rw [hb, heq]
      ring
    have := powerLaw_cubic_root_pos_Pconstructible hn
      (PConstructible.mul hsign h₀) (PConstructible.mul hsign (neg_Pconstructible h₁))
      (PConstructible.mul hsign h₂) (PConstructible.mul hsign (neg_Pconstructible h₃))
      (by linarith : (0 : ℝ) < -β) heq'
    simpa using neg_Pconstructible this
  · exact zero_Pconstructible
  · exact powerLaw_cubic_root_pos_Pconstructible hn h₀ h₁ h₂ h₃ hpos heq

-- Theorem: a cubic with P-constructible coefficients has P-constructible real roots — its
-- graph is a constructible curve, and the roots are where that curve crosses the axis.
theorem cubicVal_root_Pconstructible {c₀ c₁ c₂ c₃ β : ℝ} (h₀ : PConstructible c₀)
    (h₁ : PConstructible c₁) (h₂ : PConstructible c₂) (h₃ : PConstructible c₃)
    (hne : c₃ ≠ 0 ∨ c₂ ≠ 0 ∨ c₁ ≠ 0 ∨ c₀ ≠ 0)
    (hroot : cubicVal c₀ c₁ c₂ c₃ β = 0) :
    PConstructible β := by
  set P : Polynomial ℝ := C c₃ * X ^ 3 + C c₂ * X ^ 2 + C c₁ * X + C c₀ with hPdef
  have hevalP : ∀ t : ℝ, P.eval t = cubicVal c₀ c₁ c₂ c₃ t := by
    intro t
    simp [hPdef, cubicVal]
  have hPne : P ≠ 0 := by
    intro hc
    have e3 : P.coeff 3 = c₃ := by simp [hPdef]
    have e2 : P.coeff 2 = c₂ := by simp [hPdef]
    have e1 : P.coeff 1 = c₁ := by simp [hPdef]
    have e0 : P.coeff 0 = c₀ := by simp [hPdef]
    rw [hc] at e3 e2 e1 e0
    simp only [Polynomial.coeff_zero] at e3 e2 e1 e0
    rcases hne with h | h | h | h
    exacts [h e3.symm, h e2.symm, h e1.symm, h e0.symm]
  have hrootP : P.IsRoot β := by rw [Polynomial.IsRoot, hevalP, hroot]
  have hAfin : {t : ℝ | P.IsRoot t ∧ t ≠ β}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hPne).subset (fun t ht => ht.1)
  obtain ⟨ε, hε, hball⟩ :=
    Metric.isOpen_iff.mp hAfin.isClosed.isOpen_compl β (fun h => h.2 rfl)
  obtain ⟨q₁, hq₁a, hq₁b⟩ := exists_rat_btwn (show β - ε < β by linarith)
  obtain ⟨q₂, hq₂a, hq₂b⟩ := exists_rat_btwn (show β < β + ε by linarith)
  have huniq : ∀ t : ℝ, P.IsRoot t → (q₁ : ℝ) ≤ t → t ≤ (q₂ : ℝ) → t = β := by
    intro t ht hlo hhi
    have hmem : t ∈ Metric.ball β ε := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hnot := hball hmem
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_and, not_not] at hnot
    exact hnot ht
  have hS := cubicGraph_PConstructibleCurve h₀ h₁ h₂ h₃
    (rat_Pconstructible q₁) (rat_Pconstructible q₂) (by linarith : (q₁ : ℝ) < q₂)
  refine abscissa_Pconstructible hS zero_Pconstructible ?_
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, cubicGraph, Set.mem_singleton_iff,
    Prod.mk.injEq]
  constructor
  · rintro ⟨⟨hlo, hhi, hgraph⟩, hzero⟩
    have hra : P.IsRoot a := by
      rw [Polynomial.IsRoot, hevalP, ← hgraph, hzero]
    exact ⟨huniq a hra hlo hhi, hzero⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨⟨hq₁b.le, hq₂a.le, hroot.symm⟩, rfl⟩

/-- **The Bring–Jerrard reduction.** A Tschirnhaus substitution `z = x³ + a x² + b x + c`
carries a polynomial of degree `n ≥ 4` to one whose coefficients in degrees `n-1`, `n-2`
and `n-3` all vanish, so that the surviving tail has degree at most `n - 4`. The three
conditions are the first three elementary symmetric functions of the transformed roots,
hence of degrees `1`, `2` and `3` in `(a, b, c)`, so they are solved in turn by a linear
equation, a square root and a cubic — every step P-constructible, as is the recovery of `x`
from `z`, which is one more cubic.

Classical (Bring 1786, Jerrard 1834) and not in Mathlib; taken on trust here. -/
theorem bringJerrard {n : ℕ} (hn : 4 ≤ n) {p : Polynomial ℝ} (hp : p ≠ 0)
    (hdeg : p.natDegree = n) (hcoeff : ∀ i, PConstructible (p.coeff i)) {β : ℝ}
    (hroot : p.eval β = 0) :
    ∃ z c₀ c₁ c₂ c₃ : ℝ,
      PConstructible c₀ ∧ PConstructible c₁ ∧ PConstructible c₂ ∧ PConstructible c₃ ∧
      z ^ n = cubicVal c₀ c₁ c₂ c₃ z ∧ (PConstructible z → PConstructible β) := by
  sorry

-- Theorem: every real root of every polynomial of degree at most 7 whose coefficients are
-- P-constructible is itself P-constructible. Degrees up to 3 are read straight off the
-- cubic graph; from 4 to 7 the Bring–Jerrard reduction shortens the tail to a cubic, and
-- the power curve `y = x ^ n` supplies the leading term.
theorem root_Pconstructible_le_seven_coeffs {p : Polynomial ℝ} (hp : p ≠ 0)
    (hdeg : p.natDegree ≤ 7) (hcoeff : ∀ i, PConstructible (p.coeff i)) {β : ℝ}
    (hroot : p.eval β = 0) :
    PConstructible β := by
  by_cases h3 : p.natDegree ≤ 3
  · -- Degree at most 3: the graph of `p` is a Bézier, and `β` is where it meets the axis.
    have hval : cubicVal (p.coeff 0) (p.coeff 1) (p.coeff 2) (p.coeff 3) β = 0 := by
      rw [← hroot, Polynomial.eval_eq_sum_range' (n := 4) (by omega)]
      simp [cubicVal, Finset.sum_range_succ]
      ring
    have hne : p.coeff 3 ≠ 0 ∨ p.coeff 2 ≠ 0 ∨ p.coeff 1 ≠ 0 ∨ p.coeff 0 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨e3, e2, e1, e0⟩ := hcon
      refine hp (Polynomial.ext fun i => ?_)
      rcases lt_or_ge i 4 with hi | hi
      · interval_cases i <;> simp [e0, e1, e2, e3]
      · exact Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    exact cubicVal_root_Pconstructible (hcoeff 0) (hcoeff 1) (hcoeff 2) (hcoeff 3) hne hval
  · -- Degree 4 to 7: reduce and cross.
    obtain ⟨z, c₀, c₁, c₂, c₃, h₀, h₁, h₂, h₃, hz, hrec⟩ :=
      bringJerrard (n := p.natDegree) (by omega) hp rfl hcoeff hroot
    exact hrec (powerLaw_cubic_root_Pconstructible (by omega) h₀ h₁ h₂ h₃ hz)

end BezierGraph


/-! ### π is P-constructible

Measuring half of the unit circle. A *full* circle cannot be used directly: `θ ↦ (cos θ,
sin θ)` on `[0, 2π]` has `γ 0 = γ (2π)`, so it fails the injectivity side condition of
`PConstructible.arc_length`. The upper half circle avoids that, and its two endpoints
`(1, 0)` and `(-1, 0)` are P-constructible points, as required. Its length is `π`. -/

-- Theorem: -1 is P-constructible.
theorem neg_one_Pconstructible : PConstructible (-1 : ℝ) :=
  neg_Pconstructible PConstructible.base_one

/-- The unit circle, obtained from the `ellipse` constructor with centre `(0, 0)` and
bounding box `2 × 2`. -/
theorem unitCircle_PConstructibleCurve :
    PConstructibleCurve
      {p : ℝ × ℝ | ((p.1 - 0) / (2 / 2)) ^ 2 + ((p.2 - 0) / (2 / 2)) ^ 2 = 1} :=
  PConstructibleCurve.ellipse 0 0 2 2 zero_Pconstructible zero_Pconstructible
    two_Pconstructible two_Pconstructible (by norm_num) (by norm_num)

/-- The unit circle parametrized by angle. Restricted to `[0, π]` this traces the upper
half circle injectively. -/
noncomputable def circleParam : ℝ → ℝ × ℝ := fun θ => (Real.cos θ, Real.sin θ)

-- Theorem: the circle is traced at unit speed, so arc length agrees with angle.
theorem speed_circleParam (θ : ℝ) : speed circleParam θ = 1 := by
  have hc : HasDerivAt (fun s : ℝ => (circleParam s).1) (-Real.sin θ) θ := Real.hasDerivAt_cos θ
  have hs : HasDerivAt (fun s : ℝ => (circleParam s).2) (Real.cos θ) θ := Real.hasDerivAt_sin θ
  rw [speed, hc.deriv, hs.deriv, neg_sq, Real.sin_sq_add_cos_sq, Real.sqrt_one]

-- Theorem: `circleParam` traces the circle at unit speed, so the arc swept from angle `0`
-- to angle `L` has length exactly `L`; the upper half circle (`L = π`) is the case used
-- for `pi_Pconstructible`.
theorem arcLengthOf_circleParam (L : ℝ) : arcLengthOf circleParam 0 L = L := by
  rw [arcLengthOf]
  simp [speed_circleParam]

/-! ### The circular arc: `arccos` and `π`

The arc of the unit circle running from `(1, 0)` to `(x, √(1 - x²))` has length exactly
`arccos x`, and both of those endpoints are P-constructible as soon as `x` is — so
`PConstructible.arc_length` can measure it with no auxiliary curve. Taking `x = -1`
sweeps the entire upper half circle and so produces `π`. -/

-- Theorem: `arccos x` is P-constructible for P-constructible `x` in `[-1, 1]`.
--
-- The angle `arccos x` is at most `π`, which is exactly the range on which `cos` is
-- injective, so the arc traced over `[0, arccos x]` never doubles back and its integral
-- is a genuine length.
theorem arccos_Pconstructible_of_mem_Icc {x : ℝ} (hx : PConstructible x)
    (h₁ : -1 ≤ x) (h₂ : x ≤ 1) : PConstructible (Real.arccos x) := by
  rw [← arcLengthOf_circleParam (Real.arccos x)]
  refine PConstructible.arc_length unitCircle_PConstructibleCurve circleParam
    (Real.arccos_nonneg x) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the unit circle
    rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, circleParam, sub_zero]
    norm_num
  · -- injective on `[0, arccos x] ⊆ [0, π]`, because `cos` is
    intro t₁ ht₁ t₂ ht₂ h
    exact Real.injOn_cos.mono (Set.Icc_subset_Icc le_rfl (Real.arccos_le_pi x))
      ht₁ ht₂ (congrArg Prod.fst h)
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(Real.hasDerivAt_cos t).differentiableAt, (Real.hasDerivAt_sin t).differentiableAt⟩
  · -- unit speed, hence integrable
    rw [show speed circleParam = fun _ => (1 : ℝ) from funext speed_circleParam]
    exact intervalIntegrable_const
  · simpa [circleParam] using PConstructible.base_one
  · simpa [circleParam] using zero_Pconstructible
  · -- the far endpoint is `(x, √(1 - x²))`
    simpa [circleParam, Real.cos_arccos h₁ h₂] using hx
  · simpa [circleParam, Real.sin_arccos, pow_two] using
      sqrt_Pconstructible (PConstructible.sub PConstructible.base_one (PConstructible.mul hx hx))

-- Theorem: π is P-constructible.
--
-- Note this is a genuinely new number: unlike `arcLength_segment_Pconstructible`, whose
-- conclusion was already reachable via `dist_Pconstructible`, π is transcendental and so
-- is *not* obtainable from the arithmetic closure or from `sqrt_Pconstructible`. It
-- enters only through `PConstructible.arc_length`.
--
-- It is the case `x = -1` of the lemma above: the arc from `(1, 0)` round to `(-1, 0)`
-- is the whole upper half circle, so its length is `arccos (-1) = π`.
theorem pi_Pconstructible : PConstructible Real.pi := by
  rw [← Real.arccos_neg_one]
  exact arccos_Pconstructible_of_mem_Icc neg_one_Pconstructible (by norm_num) (by norm_num)

/-! ### `logb 2` is P-constructible

Reading off the *other* coordinate of the exponential curve. The point of `y = 2 ^ x`
lying at height `a` sits at abscissa `logb 2 a`, so a horizontal line at height `a` cuts
the curve exactly there — which is precisely what `abscissa_Pconstructible` consumes. -/

-- Theorem: `logb 2 x` is P-constructible for positive P-constructible `x`.
theorem logb_two_Pconstructible {x : ℝ} (hx : PConstructible x) (hxpos : 0 < x) :
    PConstructible (Real.logb 2 x) := by
  refine abscissa_Pconstructible PConstructibleCurve.exp_two hx ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hE, hline⟩
    subst hline
    exact ⟨((Real.logb_eq_iff_rpow_eq (by norm_num) (by norm_num) hxpos).mpr hE.symm).symm, rfl⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨(Real.rpow_logb (by norm_num) (by norm_num) hxpos).symm, rfl⟩

/-! ### Exponentials and general powers

`rpow_two_Pconstructible` reads off the `y`-coordinate of `y = 2 ^ x` above a given
abscissa, and `rpow_Pconstructible` then gets every positive base from
`a ^ b = 2 ^ (b * logb 2 a)`. -/

-- Theorem: `2 ^ x` is P-constructible.
--
-- `2 ^ x` outgrows every polynomial in `x`, so there is no algebraic bound on it to
-- supply. None is needed: `ordinate_Pconstructible` gets its segment from the
-- Archimedean property rather than from a formula.
theorem rpow_two_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible ((2 : ℝ) ^ x) := by
  refine ordinate_Pconstructible PConstructibleCurve.exp_two hx ?_
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hE, hline⟩
    subst hline
    exact ⟨rfl, hE⟩
  · rintro ⟨rfl, rfl⟩
    exact ⟨rfl, rfl⟩

-- Theorem: `a ^ b` is P-constructible for positive P-constructible `a` and
-- P-constructible `b`, since `a ^ b = 2 ^ (b * logb 2 a)`.
theorem rpow_Pconstructible {a b : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hapos : 0 < a) : PConstructible (a ^ b) := by
  have key : (2 : ℝ) ^ (b * Real.logb 2 a) = a ^ b := by
    rw [mul_comm, Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_logb (by norm_num) (by norm_num) hapos]
  rw [← key]
  exact rpow_two_Pconstructible (PConstructible.mul hb (logb_two_Pconstructible ha hapos))


/-! ### The natural logarithm

`ln a` comes out of the *arc length of a parabola*, which is the one place the geometry
supplies a logarithm. Arc length of `y = x ^ 2` over `[0, m]` is `∫₀^m √(1 + 4t²) dt`,
whose antiderivative carries an `arsinh`, and `arsinh` is a logarithm.

Choosing `m = (a² - 1) / (4a)` makes that logarithm exactly `ln a`, because

  `√(1 + 4m²) = (a² + 1) / (2a)`  and so  `2m + √(1 + 4m²) = a`.

The standard parabola is used rather than a scaled one, so `poly_graph` applies directly
and no `stretch` is needed; the scaling is absorbed into the endpoint `m` instead. -/

/-- The standard parabola `y = x ^ 2`, parametrized by abscissa. -/
def parabolaParam : ℝ → ℝ × ℝ := fun t => (t, t ^ 2)

theorem speed_parabolaParam (t : ℝ) :
    speed parabolaParam t = Real.sqrt (1 + 4 * t ^ 2) := by
  have h1 : deriv (fun s : ℝ => (parabolaParam s).1) t = 1 := by
    change deriv (fun s : ℝ => s) t = 1
    simp
  have h2 : deriv (fun s : ℝ => (parabolaParam s).2) t = 2 * t := by
    change deriv (fun s : ℝ => s ^ 2) t = 2 * t
    simp
  rw [speed, h1, h2]
  congr 1
  ring

/-- An antiderivative of `√(1 + 4t²)`. -/
noncomputable def parabolaAntideriv (t : ℝ) : ℝ :=
  t * Real.sqrt (1 + 4 * t ^ 2) / 2 + Real.arsinh (2 * t) / 4

theorem hasDerivAt_parabolaAntideriv (t : ℝ) :
    HasDerivAt parabolaAntideriv (Real.sqrt (1 + 4 * t ^ 2)) t := by
  have hu : (0 : ℝ) < 1 + 4 * t ^ 2 := by positivity
  have hspos : (0 : ℝ) < Real.sqrt (1 + 4 * t ^ 2) := Real.sqrt_pos.mpr hu
  have hs2 : Real.sqrt (1 + 4 * t ^ 2) ^ 2 = 1 + 4 * t ^ 2 := Real.sq_sqrt hu.le
  have hp : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by simpa using hasDerivAt_pow 2 t
  have hsq : HasDerivAt (fun s : ℝ => 1 + 4 * s ^ 2) (8 * t) t := by
    have h2 := (hp.const_mul (4 : ℝ)).const_add (1 : ℝ)
    rwa [show (4 : ℝ) * (2 * t) = 8 * t from by ring] at h2
  have hsqrt : HasDerivAt (fun s : ℝ => Real.sqrt (1 + 4 * s ^ 2))
      (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2))) t := hsq.sqrt hu.ne'
  have hterm1 : HasDerivAt (fun s : ℝ => s * Real.sqrt (1 + 4 * s ^ 2) / 2)
      ((1 * Real.sqrt (1 + 4 * t ^ 2) + t * (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2)))) / 2) t :=
    ((hasDerivAt_id t).mul hsqrt).div_const 2
  have h2t : (1 : ℝ) + (2 * t) ^ 2 = 1 + 4 * t ^ 2 := by ring
  have hterm2 : HasDerivAt (fun s : ℝ => Real.arsinh (2 * s) / 4)
      ((Real.sqrt (1 + 4 * t ^ 2))⁻¹ * (2 * 1) / 4) t := by
    have hc := (Real.hasDerivAt_arsinh (2 * t)).comp t ((hasDerivAt_id t).const_mul 2)
    rw [h2t] at hc
    exact hc.div_const 4
  have hval : (1 * Real.sqrt (1 + 4 * t ^ 2)
        + t * (8 * t / (2 * Real.sqrt (1 + 4 * t ^ 2)))) / 2
      + (Real.sqrt (1 + 4 * t ^ 2))⁻¹ * (2 * 1) / 4 = Real.sqrt (1 + 4 * t ^ 2) := by
    field_simp
    nlinarith [hs2, hspos]
  rw [← hval]
  exact hterm1.add hterm2

theorem arcLengthOf_parabolaParam (u v : ℝ) :
    arcLengthOf parabolaParam u v = parabolaAntideriv v - parabolaAntideriv u := by
  rw [arcLengthOf]
  simp only [speed_parabolaParam]
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => hasDerivAt_parabolaAntideriv x) ?_
  apply Continuous.intervalIntegrable
  fun_prop

/-- The standard parabola `y = x ^ 2`, as the graph of `X ^ 2` over `ℚ`. -/
theorem parabola_PConstructibleCurve :
    PConstructibleCurve
      {pt : ℝ × ℝ | pt.2 = Polynomial.aeval pt.1 ((Polynomial.X : Polynomial ℚ) ^ 2)} :=
  PConstructibleCurve.poly_graph (Polynomial.X ^ 2) (by simp)

theorem parabolaArc_Pconstructible {u v : ℝ} (hu : PConstructible u) (hv : PConstructible v)
    (huv : u ≤ v) : PConstructible (arcLengthOf parabolaParam u v) := by
  refine PConstructible.arc_length parabola_PConstructibleCurve parabolaParam huv
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rintro p ⟨t, _, rfl⟩
    simp [parabolaParam]
  · intro t₁ _ t₂ _ h
    exact congrArg Prod.fst h
  · intro t _
    refine ⟨?_, ?_⟩
    · change DifferentiableAt ℝ (fun s : ℝ => s) t
      exact differentiableAt_id
    · change DifferentiableAt ℝ (fun s : ℝ => s ^ 2) t
      exact differentiableAt_id.pow 2
  · rw [show speed parabolaParam = fun t => Real.sqrt (1 + 4 * t ^ 2) from
      funext speed_parabolaParam]
    apply Continuous.intervalIntegrable
    fun_prop
  · simpa [parabolaParam] using hu
  · simpa [parabolaParam] using sq_Pconstructible hu
  · simpa [parabolaParam] using hv
  · simpa [parabolaParam] using sq_Pconstructible hv

theorem parabolaAntideriv_Pconstructible {m : ℝ} (hm : PConstructible m) :
    PConstructible (parabolaAntideriv m) := by
  have h0 : parabolaAntideriv 0 = 0 := by simp [parabolaAntideriv]
  rcases le_total 0 m with hmm | hmm
  · have h := parabolaArc_Pconstructible zero_Pconstructible hm hmm
    rwa [arcLengthOf_parabolaParam, h0, sub_zero] at h
  · have h := parabolaArc_Pconstructible hm zero_Pconstructible hmm
    rw [arcLengthOf_parabolaParam, h0, zero_sub] at h
    simpa using neg_Pconstructible h

theorem parabolaAntideriv_val {a : ℝ} (hapos : 0 < a) :
    parabolaAntideriv ((a ^ 2 - 1) / (4 * a))
      = (a ^ 4 - 1) / (16 * a ^ 2) + Real.log a / 4 := by
  have ha : a ≠ 0 := hapos.ne'
  set m := (a ^ 2 - 1) / (4 * a) with hmdef
  have hsv : Real.sqrt (1 + 4 * m ^ 2) = (a ^ 2 + 1) / (2 * a) := by
    rw [show (1 : ℝ) + 4 * m ^ 2 = ((a ^ 2 + 1) / (2 * a)) ^ 2 from by
      rw [hmdef]; field_simp; ring]
    exact Real.sqrt_sq (by positivity)
  have hars : Real.arsinh (2 * m) = Real.log a := by
    unfold Real.arsinh
    rw [show (1 : ℝ) + (2 * m) ^ 2 = 1 + 4 * m ^ 2 from by ring, hsv]
    congr 1
    rw [hmdef]
    field_simp
    ring
  rw [parabolaAntideriv, hsv, hars, hmdef]
  field_simp
  ring

-- Theorem: the natural logarithm of a positive P-constructible number is P-constructible.
theorem log_Pconstructible {a : ℝ} (ha : PConstructible a) (hapos : 0 < a) :
    PConstructible (Real.log a) := by
  have ha0 : a ≠ 0 := hapos.ne'
  have h4 : PConstructible (4 : ℝ) := by
    convert PConstructible.mul two_Pconstructible two_Pconstructible
    norm_num
  have ha2 : PConstructible (a ^ 2) := sq_Pconstructible ha
  have ha4 : PConstructible (a ^ 4) := by
    convert sq_Pconstructible ha2 using 1
    ring
  have hm : PConstructible ((a ^ 2 - 1) / (4 * a)) :=
    PConstructible.div (PConstructible.sub ha2 PConstructible.base_one)
      (PConstructible.mul h4 ha)
  have hG := parabolaAntideriv_Pconstructible hm
  rw [parabolaAntideriv_val hapos] at hG
  have hq : PConstructible ((a ^ 4 - 1) / (4 * a ^ 2)) :=
    PConstructible.div (PConstructible.sub ha4 PConstructible.base_one)
      (PConstructible.mul h4 ha2)
  have hkey : Real.log a
      = 4 * ((a ^ 4 - 1) / (16 * a ^ 2) + Real.log a / 4) - (a ^ 4 - 1) / (4 * a ^ 2) := by
    field_simp
    ring
  rw [hkey]
  exact PConstructible.sub (PConstructible.mul h4 hG) hq

-- e is P-constructible: ln is now available, so `e = 2 ^ (1 / ln 2)`.
theorem exp_one_Pconstructible : PConstructible (Real.exp 1) := by
  have hln2 : PConstructible (Real.log 2) := log_Pconstructible two_Pconstructible (by norm_num)
  have h : Real.exp 1 = (2 : ℝ) ^ (1 / Real.log 2) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    rw [mul_one_div, div_self (Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num))]
  rw [h]
  exact rpow_Pconstructible two_Pconstructible
    (PConstructible.div PConstructible.base_one hln2) (by norm_num)


/-! ### The Lambert W function

`W x` is pinned down by `W x * exp (W x) = x`, and unlike everything above it is not a
composite of operations already available: it has no closed form in terms of `exp`, `log`
and arithmetic. That is exactly the situation `PConstructible.inter_x` exists for. An
implicit equation is the statement that two curves cross, and here the drawing program
can draw both of them.

Write the defining equation as `exp u = x / u`. The left-hand side is the exponential
curve, which `PConstructibleCurve.exp_two` supplies once the `x`-axis is scaled by
`log 2`, since `2 ^ (u / log 2) = e ^ u`. The right-hand side is a rectangular hyperbola,
which `PConstructibleCurve.power_law` supplies as `y = u ^ (-1)` with the `y`-axis scaled
by `x`. So `W x` is the abscissa at which an exponential curve meets a hyperbola: one
drawing each, and one intersection.

Isolating that intersection takes different work on the two halves of the principal
branch. For `x > 0` there is nothing to do — `power_law` draws only the `u > 0` branch of
the hyperbola, and `u * exp u` is injective there, so the curves already meet exactly
once. For `-1/e ≤ x < 0` the equation `u * exp u = x` has two roots, one in `[-1, 0)` and
one below `-1`, so the exponential curve is cropped to `[-1, 0] × [0, 1]` to discard the
second. The lower branch `W₋₁` is not reachable this way and is not defined here.

Everything rests on `mulExp`, the function being inverted. Its strict monotonicity on
`[-1, ∞)` — from `(u * e ^ u)' = (1 + u) e ^ u` — is what makes the intersections
singletons, and its minimum value `mulExp (-1) = -1/e` is what bounds the domain. Outside
that domain `lambertW` takes the junk value `0`, in the manner of `Real.sqrt` and
`Real.log`, so `lambertW_Pconstructible` needs no domain hypothesis. -/

/-- `mulExp u = u * exp u`, the function that the Lambert W function inverts. -/
noncomputable def mulExp (u : ℝ) : ℝ := u * Real.exp u

theorem hasDerivAt_mulExp (u : ℝ) : HasDerivAt mulExp ((1 + u) * Real.exp u) u := by
  have h : HasDerivAt (fun s : ℝ => s * Real.exp s) (1 * Real.exp u + u * Real.exp u) u :=
    (hasDerivAt_id u).mul (Real.hasDerivAt_exp u)
  have he : (1 + u) * Real.exp u = 1 * Real.exp u + u * Real.exp u := by ring
  rw [he]
  exact h

-- Theorem: `u * exp u` is strictly increasing on `[-1, ∞)`, because its derivative
-- `(1 + u) * exp u` is positive there. This is what makes the principal branch of `W`
-- single-valued, and below it is what turns the curve crossings into singletons.
theorem strictMonoOn_mulExp : StrictMonoOn mulExp (Set.Ici (-1)) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici _) ?_ ?_
  · exact (continuous_id.mul Real.continuous_exp).continuousOn
  · intro u hu
    rw [interior_Ici, Set.mem_Ioi] at hu
    rw [(hasDerivAt_mulExp u).deriv]
    have h1 : (0 : ℝ) < 1 + u := by linarith
    positivity

-- Theorem: `u * exp u = x` is solvable with `u ≥ -1` exactly when `x ≥ -1/e`. The
-- solution is found by the intermediate value theorem between `-1`, where `mulExp` takes
-- the value `-1/e`, and `max x 0`, where it is at least `max x 0 ≥ x`.
theorem exists_mulExp_eq {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    ∃ w : ℝ, -1 ≤ w ∧ mulExp w = x := by
  have hb0 : (0 : ℝ) ≤ max x 0 := le_max_right _ _
  have hlo : mulExp (-1) ≤ x := by simpa [mulExp] using hx
  have hhi : x ≤ mulExp (max x 0) := by
    have h1 : (1 : ℝ) ≤ Real.exp (max x 0) := Real.one_le_exp hb0
    have h2 : max x 0 ≤ mulExp (max x 0) := by
      rw [mulExp]
      nlinarith
    exact le_trans (le_max_left _ _) h2
  obtain ⟨w, hw, hwx⟩ :=
    intermediate_value_Icc (by linarith : (-1 : ℝ) ≤ max x 0)
      (continuous_id.mul Real.continuous_exp).continuousOn ⟨hlo, hhi⟩
  exact ⟨w, hw.1, hwx⟩

open Classical in
/-- The principal branch of the Lambert W function: the unique `w ≥ -1` with
`w * exp w = x`. For `x < -1/e` there is no such `w` and this takes the junk value `0`,
as `Real.sqrt` and `Real.log` do outside their domains. -/
noncomputable def lambertW (x : ℝ) : ℝ :=
  if h : ∃ w : ℝ, -1 ≤ w ∧ mulExp w = x then h.choose else 0

-- Theorem: `lambertW` is characterised by its defining equation. Any `w ≥ -1` solving
-- `w * exp w = x` *is* `lambertW x`, since `strictMonoOn_mulExp` leaves room for only one.
theorem lambertW_eq {x w : ℝ} (hw : -1 ≤ w) (hwx : mulExp w = x) : lambertW x = w := by
  have hex : ∃ w : ℝ, -1 ≤ w ∧ mulExp w = x := ⟨w, hw, hwx⟩
  rw [lambertW, dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  exact strictMonoOn_mulExp.injOn h1 hw (h2.trans hwx.symm)

-- Theorem: the defining equation itself, on the domain `[-1/e, ∞)`.
theorem lambertW_mul_exp {x : ℝ} (hx : -Real.exp (-1) ≤ x) :
    lambertW x * Real.exp (lambertW x) = x := by
  obtain ⟨w, hw, hwx⟩ := exists_mulExp_eq hx
  rw [lambertW_eq hw hwx, ← mulExp, hwx]

-- Theorem: below `-1/e` there is no solution at all, so `lambertW` is its junk value.
-- `mulExp` is increasing on `[-1, ∞)`, so `-1/e = mulExp (-1)` is the least value it
-- takes there.
theorem lambertW_of_lt {x : ℝ} (hx : x < -Real.exp (-1)) : lambertW x = 0 := by
  have hex : ¬ ∃ w : ℝ, -1 ≤ w ∧ mulExp w = x := by
    rintro ⟨w, hw, rfl⟩
    have h := strictMonoOn_mulExp.monotoneOn (Set.mem_Ici.mpr le_rfl) hw hw
    simp only [mulExp] at h hx
    linarith
  rw [lambertW, dif_neg hex]

/-! #### The two curves -/

-- Theorem: the natural exponential curve `y = e ^ x` is constructible. The drawing
-- program only offers base `2`, but scaling the `x`-axis by `log 2` changes the base:
-- `2 ^ (u / log 2) = e ^ u`.
theorem exp_PConstructibleCurve :
    PConstructibleCurve {p : ℝ × ℝ | p.2 = Real.exp p.1} := by
  have hlog2 : PConstructible (Real.log 2) := log_Pconstructible two_Pconstructible (by norm_num)
  have hne : Real.log 2 ≠ 0 := Real.log_ne_zero_of_pos_of_ne_one (by norm_num) (by norm_num)
  have h := PConstructibleCurve.scale_x PConstructibleCurve.exp_two hlog2
  convert h using 1
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · intro hv
    refine ⟨u / Real.log 2, v, ?_, by field_simp, rfl⟩
    rw [hv, Real.rpow_def_of_pos (by norm_num)]
    congr 1
    field_simp
  · rintro ⟨a, b, hb, hua, rfl⟩
    rw [hb, Real.rpow_def_of_pos (by norm_num), hua]

-- Theorem: the right-hand branch of the rectangular hyperbola `y = c / x` is
-- constructible, as the power law `y = x ^ (-1)` with the `y`-axis scaled by `c`.
theorem hyperbola_PConstructibleCurve {c : ℝ} (hc : PConstructible c) :
    PConstructibleCurve {p : ℝ × ℝ | 0 < p.1 ∧ p.2 = c / p.1} := by
  have h := PConstructibleCurve.scale_y (PConstructibleCurve.power_law 1 (-1)) hc
  convert h using 1
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  push_cast
  simp [Real.rpow_neg_one, div_eq_mul_inv, eq_comm]

-- Theorem: so is the left-hand branch, by reflecting the right-hand branch of `y = -c / x`
-- in the `y`-axis. `power_law` only ever draws `x > 0`, so the two branches of a
-- hyperbola have to be obtained separately.
theorem hyperbola_neg_PConstructibleCurve {c : ℝ} (hc : PConstructible c) :
    PConstructibleCurve {p : ℝ × ℝ | p.1 < 0 ∧ p.2 = c / p.1} := by
  have h := PConstructibleCurve.scale_x (hyperbola_PConstructibleCurve (neg_Pconstructible hc))
    (neg_Pconstructible PConstructible.base_one)
  convert h using 1
  ext ⟨u, v⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hu, hv⟩
    refine ⟨-u, v, ⟨by linarith, ?_⟩, by ring, rfl⟩
    rw [hv]
    field_simp
  · rintro ⟨a, b, ⟨ha, hb⟩, hua, rfl⟩
    refine ⟨by linarith, ?_⟩
    rw [hb, ← hua]
    field_simp

/-! #### The construction -/

-- Theorem: `W x` is P-constructible for every P-constructible `x`. Outside `[-1/e, ∞)`
-- this is the junk value `0`; inside it, `W x` is the abscissa where the exponential
-- curve `y = e ^ u` meets the hyperbola `y = x / u`, since that crossing is exactly the
-- equation `u * exp u = x`.
theorem lambertW_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (lambertW x) := by
  by_cases hdom : -Real.exp (-1) ≤ x
  · obtain ⟨w, hw1, hwx⟩ := exists_mulExp_eq hdom
    rw [lambertW_eq hw1 hwx]
    rw [mulExp] at hwx
    have hexp := Real.exp_pos w
    rcases lt_trichotomy x 0 with hneg | hzero | hpos
    · -- `-1 ≤ w < 0`: crop the exponential curve to `[-1, 0] × [0, 1]` first, so that only
      -- the principal root of `u * exp u = x` survives the intersection.
      have hwneg : w < 0 := by nlinarith
      have hE := PConstructibleCurve.restrict exp_PConstructibleCurve (-1) 0 0 1
        (neg_Pconstructible PConstructible.base_one) zero_Pconstructible
        zero_Pconstructible PConstructible.base_one
      refine PConstructible.inter_x (y := Real.exp w) hE
        (hyperbola_neg_PConstructibleCurve hx) ?_
      ext ⟨u, v⟩
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hEc, hb1, hb2, -, -⟩, hu0, hH⟩
        have hune : u ≠ 0 := hu0.ne
        have hkey : mulExp u = x := by
          rw [mulExp, ← hEc, hH]
          field_simp
        have hu : u = w := strictMonoOn_mulExp.injOn (Set.mem_Ici.mpr hb1)
          (Set.mem_Ici.mpr hw1) (by rw [hkey, mulExp]; linarith)
        exact ⟨hu, by rw [hEc, hu]⟩
      · rintro ⟨rfl, rfl⟩
        refine ⟨⟨rfl, hw1, hwneg.le, hexp.le, Real.exp_le_one_iff.mpr hwneg.le⟩, hwneg, ?_⟩
        rw [eq_div_iff hwneg.ne, ← hwx]
        ring
    · -- `x = 0` forces `w = 0`, since `exp` never vanishes.
      rcases mul_eq_zero.mp (hwx.trans hzero) with h | h
      · rw [h]
        exact zero_Pconstructible
      · exact absurd h hexp.ne'
    · -- `w > 0`: the `u > 0` branch of the hyperbola is the only one `power_law` draws,
      -- and `mulExp` is injective there, so no cropping is needed.
      have hwpos : 0 < w := by nlinarith
      refine PConstructible.inter_x (y := Real.exp w) exp_PConstructibleCurve
        (hyperbola_PConstructibleCurve hx) ?_
      ext ⟨u, v⟩
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
      constructor
      · rintro ⟨hEc, hu0, hH⟩
        have hune : u ≠ 0 := hu0.ne'
        have hkey : mulExp u = x := by
          rw [mulExp, ← hEc, hH]
          field_simp
        have hu : u = w := strictMonoOn_mulExp.injOn (Set.mem_Ici.mpr (by linarith))
          (Set.mem_Ici.mpr hw1) (by rw [hkey, mulExp]; linarith)
        exact ⟨hu, by rw [hEc, hu]⟩
      · rintro ⟨rfl, rfl⟩
        refine ⟨rfl, hwpos, ?_⟩
        rw [eq_div_iff hwpos.ne', ← hwx]
        ring
  · push Not at hdom
    rw [lambertW_of_lt hdom]
    exact zero_Pconstructible

-- Sanity checks that `lambertW` really is the Lambert W function and not merely some
-- function that the construction above happens to reach: it takes the expected values at
-- the three points where `W` is elementary, namely `W 0 = 0`, `W e = 1` and the branch
-- point `W (-1/e) = -1`.
example : lambertW 0 = 0 := lambertW_eq (by norm_num) (by simp [mulExp])

example : lambertW (Real.exp 1) = 1 := lambertW_eq (by norm_num) (by simp [mulExp])

example : lambertW (-Real.exp (-1)) = -1 := lambertW_eq le_rfl (by simp [mulExp])


/-! ### Translating a curve

`PConstructibleCurve.translate_x` and `translate_y` slide a curve along one axis; used
together they move it anywhere. They are the only operations here that do not fix the
origin, and what they buy is not new *pictures* — a translated ellipse was always
available, since `ellipse` carries its own centre — but the curves that were pinned to
the axes. `power_law` draws `y = c / x` and nothing else, so until now both branches of
every hyperbola straddled the origin. Together with `linearMap_PConstructibleCurve` below
they also close the class under every *affine* map of the plane, not merely the linear
ones. -/

-- Theorem: a curve may be translated by any P-constructible vector, by translating along
-- each axis in turn.
theorem translate_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {u v : ℝ} (hu : PConstructible u) (hv : PConstructible v) :
    PConstructibleCurve ((fun p : ℝ × ℝ => (p.1 + u, p.2 + v)) '' S) := by
  simpa [Set.image_image] using
    PConstructibleCurve.translate_y (PConstructibleCurve.translate_x hS hu) hv

-- Theorem: the right-hand branch of a hyperbola with an arbitrary P-constructible centre
-- `(u, v)` is constructible.
theorem hyperbola_shift_PConstructibleCurve {c u v : ℝ} (hc : PConstructible c)
    (hu : PConstructible u) (hv : PConstructible v) :
    PConstructibleCurve {p : ℝ × ℝ | u < p.1 ∧ p.2 = c / (p.1 - u) + v} := by
  have h := translate_PConstructibleCurve (hyperbola_PConstructibleCurve hc) hu hv
  convert h using 1
  ext ⟨a, b⟩
  simp only [Set.mem_ofPred_eq, Set.mem_image, Prod.exists, Prod.mk.injEq]
  constructor
  · rintro ⟨hlt, hb⟩
    exact ⟨a - u, c / (a - u), ⟨by linarith, rfl⟩, by ring, by rw [hb]⟩
  · rintro ⟨x, y, ⟨hx, rfl⟩, rfl, rfl⟩
    refine ⟨by linarith, ?_⟩
    rw [show x + u - u = x by ring]

/-! ### The Laplace limit

Kepler's equation `M = E - e · sin E` ties the mean anomaly `M` of a body on an elliptic
orbit to its eccentric anomaly `E`. Lagrange inverted it as a power series in the
eccentricity `e`, and that series converges precisely for `e` below the *Laplace limit*
`λ = 0.66274…`, the unique positive root of

  `λ · exp √(1 + λ²) = 1 + √(1 + λ²)`.

That root is P-constructible, and what makes it so is `PConstructibleCurve.translate_y`.
Substituting `m = 2(√(1 + λ²) - 1)` turns the defining equation into

  `m · eᵐ = (m + 4) / e²`,

a *generalized* Lambert equation: `lambertW` above solves `w · eʷ = x` for a right-hand
side that stays constant, whereas here it moves with `m`. That construction read its root
off a crossing of the exponential curve with a hyperbola, and this one does the same,
crossing `y = eˣ` with

  `y = (x + 4) / (e² x) = (4 / e²) / x + 1 / e²`.

The second curve is that hyperbola lifted `1 / e²` off the axis, and lifting is precisely
what was missing: `power_law` draws `y = c / x`, whose asymptote *is* the axis. The whole
distance between `W` and the generalization needed here is the height of that asymptote.

The crossing is unique for `x > 0`, since `eˣ` climbs where the hyperbola falls. There is
a second crossing near `x = -4.3`, and cropping to `[1/10, 1]` — the interval across which
`laplaceAux` changes sign — leaves only the wanted one. Turning `m` back into `λ` is then
algebra: `√(1 + λ²)` works out to `(m + 2)/2`, and squaring the defining equation makes
both of its sides `(m + 4)/2`. -/

/-- `e² · x · eˣ - (x + 4)`, whose unique positive root carries the Laplace limit. -/
noncomputable def laplaceAux (x : ℝ) : ℝ := Real.exp 2 * (x * Real.exp x) - (x + 4)

-- Theorem: `laplaceAux` is continuous, so the intermediate value theorem applies to it.
theorem continuous_laplaceAux : Continuous laplaceAux :=
  (continuous_const.mul (continuous_id.mul Real.continuous_exp)).sub
    (continuous_id.add continuous_const)

-- Theorem: 4 is P-constructible.
theorem four_Pconstructible : PConstructible (4 : ℝ) := by
  convert PConstructible.add three_Pconstructible PConstructible.base_one
  norm_num

-- Theorem: `2 < e`, straight from `x + 1 < eˣ` at `x = 1`.
theorem two_lt_exp_one : (2 : ℝ) < Real.exp 1 := by
  have := Real.add_one_lt_exp (x := 1) (by norm_num)
  linarith

-- Theorem: `e < 16/5`. The same inequality at `x = -1/4` gives `3/4 < e^(-1/4)`, which
-- inverts to `e^(1/4) < 4/3`; a fourth power turns that into `e < 256/81 < 16/5`. Mathlib's
-- sharp decimal bounds live in `Mathlib.Analysis.Complex.ExponentialBounds`, which this file
-- does not import; these two crude bounds are all the construction needs.
theorem exp_one_lt : Real.exp 1 < 16 / 5 := by
  have h : (-(1 / 4) : ℝ) + 1 < Real.exp (-(1 / 4)) := Real.add_one_lt_exp (by norm_num)
  have hmul : Real.exp (-(1 / 4)) * Real.exp (1 / 4) = 1 := by
    rw [← Real.exp_add]; norm_num
  have hq : Real.exp (1 / 4) < 4 / 3 := by
    nlinarith [Real.exp_pos ((1 : ℝ) / 4), Real.exp_pos (-((1 : ℝ) / 4))]
  have he : Real.exp 1 = Real.exp (1 / 4) ^ 4 := by
    have h : Real.exp (1 / 4) ^ 4 = Real.exp (1 / 4 + 1 / 4 + 1 / 4 + 1 / 4) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add]; ring
    rw [h]; norm_num
  have h2 : Real.exp (1 / 4) ^ 2 < 16 / 9 := by
    nlinarith [Real.exp_pos ((1 : ℝ) / 4)]
  have h4 : Real.exp (1 / 4) ^ 4 < 256 / 81 := by
    nlinarith [sq_nonneg (Real.exp (1 / 4)), Real.exp_pos ((1 : ℝ) / 4)]
  rw [he]
  linarith

-- Theorem: `e³ < 41`, with room to spare, from `e < 16/5`.
theorem exp_three_lt : Real.exp 3 < 41 := by
  have he : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
  have h2 : Real.exp 1 * Real.exp 1 < 256 / 25 := by
    nlinarith [exp_one_lt, Real.exp_pos (1 : ℝ)]
  rw [he]
  nlinarith [exp_one_lt, Real.exp_pos (1 : ℝ)]

-- Theorem: `e³ > 8`, from `e > 2`.
theorem exp_three_gt : (8 : ℝ) < Real.exp 3 := by
  have he : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
    rw [show (3 : ℝ) = 1 + 1 + 1 by norm_num, Real.exp_add, Real.exp_add]
  rw [he]
  nlinarith [two_lt_exp_one, Real.exp_pos (1 : ℝ)]

-- Theorem: `laplaceAux` is negative at `1/10`, because `e^2.1 ≤ e³ < 41` leaves the first
-- term below `4.1`.
theorem laplaceAux_neg : laplaceAux (1 / 10) < 0 := by
  have h1 : Real.exp 2 * ((1 / 10) * Real.exp (1 / 10)) = (1 / 10) * Real.exp (2 + 1 / 10) := by
    rw [Real.exp_add]; ring
  have h2 : Real.exp (2 + 1 / 10) < 41 :=
    lt_of_le_of_lt (Real.exp_le_exp.mpr (by norm_num)) exp_three_lt
  rw [laplaceAux, h1]
  linarith

-- Theorem: and positive at `1`, where the first term is `e³ > 8 > 5`.
theorem laplaceAux_pos : 0 < laplaceAux 1 := by
  have h1 : Real.exp 2 * (1 * Real.exp 1) = Real.exp 3 := by
    rw [show (3 : ℝ) = 2 + 1 by norm_num, Real.exp_add]; ring
  rw [laplaceAux, h1]
  linarith [exp_three_gt]

-- Theorem: so it vanishes somewhere in `[1/10, 1]`, by the intermediate value theorem.
theorem exists_laplaceRoot : ∃ x ∈ Set.Icc (1 / 10 : ℝ) 1, laplaceAux x = 0 := by
  have h := intermediate_value_Icc (by norm_num : (1 / 10 : ℝ) ≤ 1)
    continuous_laplaceAux.continuousOn
  have hmem : (0 : ℝ) ∈ Set.Icc (laplaceAux (1 / 10)) (laplaceAux 1) :=
    ⟨laplaceAux_neg.le, laplaceAux_pos.le⟩
  obtain ⟨x, hx, hx0⟩ := h hmem
  exact ⟨x, hx, hx0⟩

-- The crossing is unique because `eˣ` climbs while `4/e²/x + 1/e²` falls: cross-multiply
-- the two equations by the other root and the exponentials cancel, leaving `b < a`.
theorem laplaceAux_cross {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : laplaceAux a = 0) (hB : laplaceAux b = 0) (hab : a < b) : b < a := by
  have hlt : Real.exp a < Real.exp b := Real.exp_lt_exp.mpr hab
  rw [laplaceAux, sub_eq_zero] at hA hB
  have key : Real.exp 2 * (a * b) * Real.exp a < Real.exp 2 * (a * b) * Real.exp b :=
    mul_lt_mul_of_pos_left hlt (by positivity)
  have e1 : Real.exp 2 * (a * b) * Real.exp a = b * (a + 4) := by rw [← hA]; ring
  have e2 : Real.exp 2 * (a * b) * Real.exp b = a * (b + 4) := by rw [← hB]; ring
  rw [e1, e2] at key
  nlinarith [key]

-- Theorem: at most one positive root, by the previous lemma applied both ways round.
theorem laplaceRoot_unique {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hA : laplaceAux a = 0) (hB : laplaceAux b = 0) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact absurd (laplaceAux_cross ha hb hA hB hab) (by linarith)
  · exact hab
  · exact absurd (laplaceAux_cross hb ha hB hA hab) (by linarith)

open Classical in
/-- The unique positive root of `e² · x · eˣ = x + 4`, the generalized Lambert equation
carrying the Laplace limit. Outside that equation there is nothing to choose, so the
junk-value branch never fires; `laplaceRoot_mem` discharges it. -/
noncomputable def laplaceRoot : ℝ :=
  if h : ∃ x : ℝ, 0 < x ∧ laplaceAux x = 0 then h.choose else 0

-- Theorem: `laplaceRoot` is the root just found — uniqueness pins the choice — so it
-- satisfies the equation and lies in `[1/10, 1]`.
theorem laplaceRoot_mem : laplaceRoot ∈ Set.Icc (1 / 10 : ℝ) 1 ∧ laplaceAux laplaceRoot = 0 := by
  obtain ⟨x, hx, hx0⟩ := exists_laplaceRoot
  have hxpos : 0 < x := lt_of_lt_of_le (by norm_num) hx.1
  have hex : ∃ x : ℝ, 0 < x ∧ laplaceAux x = 0 := ⟨x, hxpos, hx0⟩
  have hchoose := hex.choose_spec
  have : laplaceRoot = x := by
    rw [laplaceRoot, dif_pos hex]
    exact laplaceRoot_unique hchoose.1 hxpos hchoose.2 hx0
  rw [this]
  exact ⟨hx, hx0⟩

-- Theorem: in particular it is positive.
theorem laplaceRoot_pos : 0 < laplaceRoot :=
  lt_of_lt_of_le (by norm_num) laplaceRoot_mem.1.1

/-- The Laplace limit `0.66274…`: the eccentricity at which Lagrange's series for the
solution of Kepler's equation stops converging, characterised by `laplaceLimit_spec`. -/
noncomputable def laplaceLimit : ℝ := Real.sqrt (laplaceRoot * (laplaceRoot + 4)) / 2

-- Theorem: the Laplace limit is positive.
theorem laplaceLimit_pos : 0 < laplaceLimit := by
  have h := laplaceRoot_pos
  have hp : 0 < laplaceRoot * (laplaceRoot + 4) := by nlinarith
  rw [laplaceLimit]
  exact div_pos (Real.sqrt_pos.mpr hp) (by norm_num)

-- Theorem: its square is `m(m + 4)/4`.
theorem laplaceLimit_sq : laplaceLimit ^ 2 = laplaceRoot * (laplaceRoot + 4) / 4 := by
  have h := laplaceRoot_pos
  have hnn : 0 ≤ laplaceRoot * (laplaceRoot + 4) := by nlinarith
  rw [laplaceLimit, div_pow, Real.sq_sqrt hnn]
  norm_num

-- Theorem: `√(1 + λ²) = (m + 2)/2`, the substitution `m = 2(√(1 + λ²) - 1)` read backwards.
-- This is what makes the exponential in the defining equation elementary in `m`.
theorem sqrt_one_add_laplaceLimit_sq :
    Real.sqrt (1 + laplaceLimit ^ 2) = (laplaceRoot + 2) / 2 := by
  have h := laplaceRoot_pos
  rw [laplaceLimit_sq, show 1 + laplaceRoot * (laplaceRoot + 4) / 4
    = ((laplaceRoot + 2) / 2) ^ 2 by ring]
  exact Real.sqrt_sq (by linarith)

-- Theorem: the number constructed really is the Laplace limit.
theorem laplaceLimit_spec :
    laplaceLimit * Real.exp (Real.sqrt (1 + laplaceLimit ^ 2))
      = 1 + Real.sqrt (1 + laplaceLimit ^ 2) := by
  have hm := laplaceRoot_mem.2
  have hpos := laplaceRoot_pos
  rw [laplaceAux, sub_eq_zero] at hm
  rw [sqrt_one_add_laplaceLimit_sq]
  have hE : Real.exp ((laplaceRoot + 2) / 2) ^ 2 = Real.exp 2 * Real.exp laplaceRoot := by
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  have hsq : (laplaceLimit * Real.exp ((laplaceRoot + 2) / 2)) ^ 2
      = ((laplaceRoot + 4) / 2) ^ 2 := by
    rw [mul_pow, laplaceLimit_sq, hE]
    linear_combination ((laplaceRoot + 4) / 4) * hm
  have h1 : 0 ≤ laplaceLimit * Real.exp ((laplaceRoot + 2) / 2) :=
    mul_nonneg laplaceLimit_pos.le (Real.exp_pos _).le
  have h2 : (0 : ℝ) ≤ (laplaceRoot + 4) / 2 := by linarith
  have := congrArg Real.sqrt hsq
  rw [Real.sqrt_sq h1, Real.sqrt_sq h2] at this
  rw [this]
  ring

-- Theorem: the root is P-constructible.
theorem laplaceRoot_Pconstructible : PConstructible laplaceRoot := by
  have hE : PConstructible (Real.exp 2) := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    exact PConstructible.mul exp_one_Pconstructible exp_one_Pconstructible
  have hEpos : (0 : ℝ) < Real.exp 2 := Real.exp_pos 2
  have h4 : PConstructible (4 : ℝ) := four_Pconstructible
  have hc : PConstructible (4 / Real.exp 2) := PConstructible.div h4 hE
  have hv : PConstructible (1 / Real.exp 2) := PConstructible.div PConstructible.base_one hE
  have h110 : PConstructible (1 / 10 : ℝ) := by
    have := rat_Pconstructible ((1 : ℚ) / 10)
    push_cast at this
    exact this
  have hHyp := hyperbola_shift_PConstructibleCurve hc zero_Pconstructible hv
  simp only [sub_zero] at hHyp
  have hT := PConstructibleCurve.restrict hHyp (1 / 10) 1 0 (Real.exp 2)
    h110 PConstructible.base_one zero_Pconstructible hE
  -- The exponential curve meets that cropped hyperbola exactly at the root.
  have hpos := laplaceRoot_pos
  have hmem := laplaceRoot_mem
  have ha0 : laplaceRoot ≠ 0 := ne_of_gt hpos
  have hE0 : Real.exp 2 ≠ 0 := ne_of_gt hEpos
  have hroot : Real.exp laplaceRoot = 4 / Real.exp 2 / laplaceRoot + 1 / Real.exp 2 := by
    have h := hmem.2
    rw [laplaceAux, sub_eq_zero] at h
    field_simp
    linarith [h]
  refine PConstructible.inter_x exp_PConstructibleCurve hT
    (x := laplaceRoot) (y := Real.exp laplaceRoot) ?_
  ext ⟨a, b⟩
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff, Prod.mk.injEq]
  constructor
  · rintro ⟨hb, ⟨hapos, hhyp⟩, -, -, -, -⟩
    have hane : a ≠ 0 := ne_of_gt hapos
    have hkey : laplaceAux a = 0 := by
      rw [laplaceAux, sub_eq_zero, ← hb, hhyp]
      field_simp
      ring
    have : a = laplaceRoot := laplaceRoot_unique hapos hpos hkey hmem.2
    exact ⟨this, by rw [hb, this]⟩
  · rintro ⟨rfl, rfl⟩
    have hle : Real.exp laplaceRoot ≤ Real.exp 2 :=
      Real.exp_le_exp.mpr (by linarith [hmem.1.2])
    exact ⟨rfl, ⟨hpos, hroot⟩, hmem.1.1, hmem.1.2, (Real.exp_pos _).le, hle⟩

-- Theorem: the Laplace limit is P-constructible.
theorem laplaceLimit_Pconstructible : PConstructible laplaceLimit :=
  PConstructible.div
    (sqrt_Pconstructible (PConstructible.mul laplaceRoot_Pconstructible
      (PConstructible.add laplaceRoot_Pconstructible four_Pconstructible)))
    two_Pconstructible


/-! ### Sine and cosine

`PConstructibleCurve.arc_of_length` used in earnest. Instead of measuring an arc whose
endpoints are already known, lay out an arc of known *length* and ask where it ends. On
the unit circle that question is radian measure: the arc that starts at `(1, 0)` and runs
for length `x` ends at `(cos x, sin x)`.

Reaching that far endpoint takes a second curve, cutting the first there and nowhere else,
and the complementary arc supplies one — the arc that starts at `(-1, 0)` and runs
backwards for length `π - x` covers the remainder of the upper half circle, so the two
abut at the single point `(cos x, sin x)`. Both start at P-constructible points and have
P-constructible lengths, `x` and `π - x`, the latter because `π` is P-constructible.

That settles `0 ≤ x ≤ π`, and reduction mod `2π` removes the restriction. This is what
`arc_of_length` buys: every earlier constructor locates a point of a curve by cutting it
with another curve, never by measuring along it, so none of them can turn a length into
an angle. -/

/-- The unit circle traced from angle `u` at unit speed, in the direction `s = ±1`
(`s = 1` counterclockwise, `s = -1` clockwise). Unit speed is what makes the parameter
`t` double as arc length. -/
noncomputable def circleArcParam (u s : ℝ) : ℝ → ℝ × ℝ := fun t => circleParam (u + s * t)

theorem speed_circleArcParam {s : ℝ} (hs : s ^ 2 = 1) (u t : ℝ) :
    speed (circleArcParam u s) t = 1 := by
  have hlin : HasDerivAt (fun r : ℝ => u + s * r) s t := by
    simpa using ((hasDerivAt_id t).const_mul s).const_add u
  have hc : HasDerivAt (fun r : ℝ => (circleArcParam u s r).1)
      (-Real.sin (u + s * t) * s) t := hlin.cos
  have hsn : HasDerivAt (fun r : ℝ => (circleArcParam u s r).2)
      (Real.cos (u + s * t) * s) t := hlin.sin
  have hpyth : (-Real.sin (u + s * t) * s) ^ 2 + (Real.cos (u + s * t) * s) ^ 2 = 1 :=
    calc (-Real.sin (u + s * t) * s) ^ 2 + (Real.cos (u + s * t) * s) ^ 2
        = (Real.sin (u + s * t) ^ 2 + Real.cos (u + s * t) ^ 2) * s ^ 2 := by ring
      _ = 1 := by rw [Real.sin_sq_add_cos_sq, hs]; ring
  rw [speed, hc.deriv, hsn.deriv, hpyth, Real.sqrt_one]

-- Theorem: the parameter of `circleArcParam` is arc length, so an arc traced over
-- `[0, L]` has length exactly `L`.
theorem arcLengthOf_circleArcParam {s : ℝ} (hs : s ^ 2 = 1) (u L : ℝ) :
    arcLengthOf (circleArcParam u s) 0 L = L := by
  rw [arcLengthOf, show speed (circleArcParam u s) = fun _ => (1 : ℝ) from
    funext (speed_circleArcParam hs u)]
  simp

-- Theorem: two angles landing on the same point of the unit circle and differing by less
-- than a full turn are equal. This is the injectivity behind both the side condition of
-- `arc_of_length` and the "meet in exactly one point" hypothesis of `inter_x`/`inter_y`.
theorem angle_eq_of_cos_eq_of_sin_eq {θ₁ θ₂ : ℝ} (hlt : |θ₁ - θ₂| < 2 * Real.pi)
    (hc : Real.cos θ₁ = Real.cos θ₂) (hs : Real.sin θ₁ = Real.sin θ₂) : θ₁ = θ₂ := by
  have hone : Real.cos (θ₁ - θ₂) = 1 := by
    rw [Real.cos_sub, hc, hs]
    nlinarith [Real.sin_sq_add_cos_sq θ₂]
  obtain ⟨hlo, hhi⟩ := abs_lt.mp hlt
  have := (Real.cos_eq_one_iff_of_lt_of_lt hlo hhi).mp hone
  linarith

-- Theorem: `s = ±1` is the only content of `s ^ 2 = 1`.
theorem eq_one_or_neg_one_of_sq_eq_one {s : ℝ} (hs : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h : (s - 1) * (s + 1) = 0 := by nlinarith [hs]
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inl (by linarith)
  · exact Or.inr (by linarith)

-- Theorem: the arc of the unit circle that starts at a P-constructible point of it and
-- runs for a P-constructible length `L ≤ π` is a P-constructible curve.
--
-- The bound `L ≤ π` is only what the injectivity side condition of `arc_of_length` needs
-- (any `L < 2 * π` would do); it costs nothing below, where the arcs used are shorter
-- than a half turn anyway.
theorem circleArc_PConstructibleCurve {u s L : ℝ} (hs : s ^ 2 = 1)
    (hL : 0 ≤ L) (hLpi : L ≤ Real.pi) (hLc : PConstructible L)
    (hcu : PConstructible (Real.cos u)) (hsu : PConstructible (Real.sin u)) :
    PConstructibleCurve (circleArcParam u s '' Set.Icc 0 L) := by
  have hpi := Real.pi_pos
  have hlin : ∀ t : ℝ, HasDerivAt (fun r : ℝ => u + s * r) s t := fun t => by
    simpa using ((hasDerivAt_id t).const_mul s).const_add u
  refine PConstructibleCurve.arc_of_length unitCircle_PConstructibleCurve (circleArcParam u s)
    hL ?_ ?_ ?_ ?_ ?_ ?_ hLc (arcLengthOf_circleArcParam hs u L)
  · -- the arc lies on the unit circle
    rintro p ⟨t, _, rfl⟩
    simp only [Set.mem_ofPred_eq, circleArcParam, circleParam, sub_zero]
    norm_num
  · -- injective on `[0, L]`: the angles swept differ by at most `L ≤ π < 2 * π`
    intro t₁ ht₁ t₂ ht₂ h
    obtain ⟨ht₁0, ht₁L⟩ := ht₁
    obtain ⟨ht₂0, ht₂L⟩ := ht₂
    have hc : Real.cos (u + s * t₁) = Real.cos (u + s * t₂) := congrArg Prod.fst h
    have hsn : Real.sin (u + s * t₁) = Real.sin (u + s * t₂) := congrArg Prod.snd h
    -- both signs of `s` run the same argument
    rcases eq_one_or_neg_one_of_sq_eq_one hs with rfl | rfl <;>
      have := angle_eq_of_cos_eq_of_sin_eq
        (by rw [abs_lt]; constructor <;> linarith) hc hsn <;>
      linarith
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(hlin t).cos.differentiableAt, (hlin t).sin.differentiableAt⟩
  · -- unit speed, hence integrable
    rw [show speed (circleArcParam u s) = fun _ => (1 : ℝ) from
      funext (speed_circleArcParam hs u)]
    exact intervalIntegrable_const
  · simpa [circleArcParam, circleParam] using hcu
  · simpa [circleArcParam, circleParam] using hsu

-- Theorem: `cos x` and `sin x` are P-constructible for P-constructible `x` in `[0, π]`.
--
-- The two arcs meet only at angle `x`: a point common to both is `(cos θ₁, sin θ₁)` for
-- some `θ₁ ≤ x` and `(cos θ₂, sin θ₂)` for some `θ₂ ≥ x`, and since the two angles differ
-- by less than a full turn they must be equal, which forces both to be `x`.
theorem cos_sin_Pconstructible_of_mem_Icc {x : ℝ} (hx : PConstructible x)
    (h0 : 0 ≤ x) (hpi : x ≤ Real.pi) :
    PConstructible (Real.cos x) ∧ PConstructible (Real.sin x) := by
  have hpipos := Real.pi_pos
  -- The arc from `(1, 0)` of length `x`, sweeping angles `[0, x]`.
  have hA : PConstructibleCurve (circleArcParam 0 1 '' Set.Icc 0 x) :=
    circleArc_PConstructibleCurve (by norm_num) h0 hpi hx
      (by simpa using PConstructible.base_one) (by simpa using zero_Pconstructible)
  -- The arc from `(-1, 0)` of length `π - x`, sweeping angles `[x, π]` backwards.
  have hB : PConstructibleCurve (circleArcParam Real.pi (-1) '' Set.Icc 0 (Real.pi - x)) :=
    circleArc_PConstructibleCurve (by norm_num) (by linarith) (by linarith)
      (PConstructible.sub pi_Pconstructible hx)
      (by simpa using neg_one_Pconstructible) (by simpa using zero_Pconstructible)
  have hinter : circleArcParam 0 1 '' Set.Icc 0 x ∩
      circleArcParam Real.pi (-1) '' Set.Icc 0 (Real.pi - x) = {(Real.cos x, Real.sin x)} := by
    ext p
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_Icc, Set.mem_singleton_iff]
    constructor
    · rintro ⟨⟨t₁, ⟨ht₁0, ht₁x⟩, rfl⟩, t₂, ⟨ht₂0, ht₂x⟩, heq⟩
      have hc : Real.cos (Real.pi + -1 * t₂) = Real.cos (0 + 1 * t₁) := congrArg Prod.fst heq
      have hsn : Real.sin (Real.pi + -1 * t₂) = Real.sin (0 + 1 * t₁) := congrArg Prod.snd heq
      have hang : Real.pi + -1 * t₂ = 0 + 1 * t₁ :=
        angle_eq_of_cos_eq_of_sin_eq (by rw [abs_lt]; constructor <;> linarith) hc hsn
      have ht₁ : t₁ = x := by linarith
      subst ht₁
      simp [circleArcParam, circleParam]
    · rintro rfl
      exact ⟨⟨x, ⟨h0, le_rfl⟩, by simp [circleArcParam, circleParam]⟩,
        Real.pi - x, ⟨by linarith, le_rfl⟩, by simp [circleArcParam, circleParam]⟩
  exact ⟨PConstructible.inter_x hA hB hinter, PConstructible.inter_y hA hB hinter⟩

-- Theorem: every real number sits a whole number of turns away from one in `[0, 2π)`.
theorem exists_int_turns (x : ℝ) :
    ∃ n : ℤ, 0 ≤ x - n * (2 * Real.pi) ∧ x - n * (2 * Real.pi) < 2 * Real.pi := by
  have h2pi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
  refine ⟨⌊x / (2 * Real.pi)⌋, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / (2 * Real.pi))) h2pi.le
    rw [div_mul_cancel₀ _ h2pi.ne'] at h
    linarith
  · have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / (2 * Real.pi))) h2pi
    rw [div_mul_cancel₀ _ h2pi.ne'] at h
    linarith

-- Theorem: `cos x` and `sin x` are P-constructible for every P-constructible `x`.
--
-- Reduction mod `2π`: the residue `r = x - n * (2π)` is P-constructible because `π` is,
-- and if it exceeds `π` the reflection `2π - r` brings it back into `[0, π]` at the cost
-- of a sign on the sine.
theorem cos_sin_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.cos x) ∧ PConstructible (Real.sin x) := by
  obtain ⟨n, hr0, hr2⟩ := exists_int_turns x
  have hrP : PConstructible (x - n * (2 * Real.pi)) :=
    PConstructible.sub hx (PConstructible.mul (int_Pconstructible n)
      (PConstructible.mul two_Pconstructible pi_Pconstructible))
  rw [← Real.cos_sub_int_mul_two_pi x n, ← Real.sin_sub_int_mul_two_pi x n]
  rcases le_total (x - n * (2 * Real.pi)) Real.pi with h | h
  · exact cos_sin_Pconstructible_of_mem_Icc hrP hr0 h
  · obtain ⟨hc, hsn⟩ := cos_sin_Pconstructible_of_mem_Icc
      (PConstructible.sub (PConstructible.mul two_Pconstructible pi_Pconstructible) hrP)
      (by linarith) (by linarith [Real.pi_pos])
    rw [Real.cos_two_pi_sub] at hc
    rw [Real.sin_two_pi_sub] at hsn
    refine ⟨hc, ?_⟩
    simpa using neg_Pconstructible hsn

-- Theorem: the cosine of a P-constructible number is P-constructible.
theorem cos_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.cos x) :=
  (cos_sin_Pconstructible hx).1

-- Theorem: the sine of a P-constructible number is P-constructible.
theorem sin_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.sin x) :=
  (cos_sin_Pconstructible hx).2

-- Theorem: the tangent of a P-constructible number is P-constructible. No hypothesis is
-- needed at the poles: there `cos x = 0`, and Lean's division makes `tan x = 0`, which is
-- P-constructible anyway.
theorem tan_Pconstructible {x : ℝ} (hx : PConstructible x) : PConstructible (Real.tan x) := by
  rw [Real.tan_eq_sin_div_cos]
  exact PConstructible.div (sin_Pconstructible hx) (cos_Pconstructible hx)

/-! ### Inverse trigonometric functions

`arccos_Pconstructible_of_mem_Icc`, proved above alongside `π`, already does all of the
geometry; what is left here is bookkeeping. Note how much cheaper these are than `cos`
and `sin`: those needed `arc_of_length` to *lay out* an arc of known length, and then a
second curve to discover where it landed. Here both endpoints are known from the start
and only their separation along the circle is wanted, so `PConstructible.arc_length`
simply reads it off.

All three statements come out unconditional. Mathlib clamps the inverse functions outside
their natural domain — `arccos x` is `π` for `x ≤ -1` and `0` for `x ≥ 1` — and those
values are P-constructible too, so the bound `-1 ≤ x ≤ 1` is needed only by the geometric
core and not by anything built on it. -/

-- Theorem: the arccosine of a P-constructible number is P-constructible. No bound on `x`
-- is needed: outside `[-1, 1]` Mathlib's `arccos` is constantly `π` or `0`.
theorem arccos_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arccos x) := by
  rcases le_total x (-1) with h | h₁
  · rw [Real.arccos_eq_pi.mpr h]
    exact pi_Pconstructible
  rcases le_total x 1 with h₂ | h₂
  · exact arccos_Pconstructible_of_mem_Icc hx h₁ h₂
  · rw [Real.arccos_eq_zero.mpr h₂]
    exact zero_Pconstructible

-- Theorem: the arcsine of a P-constructible number is P-constructible.
--
-- `arccos` is *defined* in Mathlib as `π / 2 - arcsin`, so this is the previous theorem
-- rearranged; the complementary angle costs only a subtraction and a halving.
theorem arcsin_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arcsin x) := by
  have h := PConstructible.sub (PConstructible.div pi_Pconstructible two_Pconstructible)
    (arccos_Pconstructible hx)
  rwa [Real.arccos_eq_pi_div_two_sub_arcsin, sub_sub_cancel] at h

-- Theorem: the arctangent of a P-constructible number is P-constructible.
--
-- Via `arctan x = arcsin (x / √(1 + x²))`. Unlike `tan_Pconstructible` there are no poles
-- to worry about, and `1 + x²` is positive, so the square root is a genuine one.
theorem arctan_Pconstructible {x : ℝ} (hx : PConstructible x) :
    PConstructible (Real.arctan x) := by
  rw [Real.arctan_eq_arcsin]
  refine arcsin_Pconstructible (PConstructible.div hx (sqrt_Pconstructible ?_))
  simpa [pow_two] using PConstructible.add PConstructible.base_one (PConstructible.mul hx hx)


/-! ### Linear transformations of the plane

`PConstructibleCurve` is closed under every linear map of the plane whose four matrix
entries are P-constructible. Three primitives do the work: `PConstructibleCurve.scale_x`
and `PConstructibleCurve.scale_y`, which stretch the two axes independently, and
`PConstructibleCurve.rotate`, which turns the plane through a whole number of degrees.

Those are not obviously enough. A rotation and a *uniform* scale are both conformal, so no
composite of them can carry a circle to a non-circular ellipse; it is only because
`scale_x` and `scale_y` may be given different factors that anything beyond the
similarities is reachable at all. And the rotations supplied form a discrete set of 360
angles, so even rotation by a general P-constructible angle has to be built rather than
assumed. That is done first, and the general theorem then follows from a singular value
decomposition.

#### Rotation by an angle that is not a whole number of degrees

Write `Rot ψ` for rotation by `ψ` and `diag (u, v)` for the scaling that `scale_x` and
`scale_y` compose to. The claim is that

  `Rot ψ = diag (A, B) ∘ Rot 30° ∘ diag (p, 1) ∘ Rot 60° ∘ diag (1, H)`

for suitable P-constructible `A, B, p, H`, whenever `|ψ| ≤ 30°`. Multiplying the five
matrices out, the composite is

  `[[A X₁, -A H X₂], [B X₃, -B H X₁]]`,  `X₁ = (√3/4)(p - 1)`,
                                          `X₂ = (3p + 1)/4`,  `X₃ = (p + 3)/4`,

so matching it against `[[cos ψ, -sin ψ], [sin ψ, cos ψ]]` fixes `A`, `B` and `H` from the
first three entries and leaves the fourth as a single constraint on `p`, namely
`sin²ψ · X₁² = -cos²ψ · X₂X₃`. Cleared of denominators that is the quadratic

  `3p² + (16 cos²ψ - 6) p + 3 = 0`,

whose discriminant `(16 cos²ψ - 6)² - 36` is non-negative exactly when `cos²ψ ≥ 3/4` —
which is the 30° window quoted above. So the root `p` exists there, and being built from
`cos ψ` by a square root it is P-constructible. Outside the window there is no such `p`,
but none is needed: rounding `ψ` to the nearest whole number of degrees leaves a residue
of at most half a degree, and the whole-degree part is a primitive.

The angles `30°` and `60°` are not arbitrary. Running the same computation with a general
pair `α, β` turns the constraint on `p` into

  `p + 1/p = ((1 + t²u²) sin²ψ - (t² + u²) cos²ψ) / (tu)`,  `t = tan α`, `u = tan β`,

which is solvable only when the right-hand side has absolute value at least `2`. For
`α = β = 45°` that value is `-2 cos 2ψ`, which reaches `2` only at multiples of `90°`: the
obvious choice is exactly the borderline one that fails, and so is `β = -α`. The pair
`30°, 60°` clears the bar with room to spare.

#### The general linear map

With arbitrary rotations available the decomposition is the singular value decomposition,
in the concrete form `M = Rot θ ∘ diag (σ₁, σ₂) ∘ Rot φ`, and it too comes out of algebra
rather than any spectral theory. Split `M` into a rotation-like and a reflection-like
part,

  `[[a, b], [c, d]] = [[E, -G], [G, E]] + [[F, H], [H, -F]]`,

where `E = (a + d)/2`, `F = (a - d)/2`, `G = (c - b)/2`, `H = (c + b)/2`. Put each part in
polar form, `(E, G) = Q · (cos α, sin α)` and `(F, H) = R · (cos β, sin β)`, so the two
summands are `Q · Rot α` and `R · Rot β ∘ diag (1, -1)`. Now set `θ = (α + β)/2` and
`φ = (α - β)/2`, which makes `α = θ + φ` and `β = θ - φ`. Pulling `Rot θ` out on the left
and `Rot φ` out on the right is then legitimate for *both* summands — the sign flip in
`diag (1, -1)` is what turns the reflection's `Rot (-φ)` back into `Rot φ` as it passes
through — and what is left behind is `Q · I + R · diag (1, -1) = diag (Q + R, Q - R)`.

Every number in that decomposition is P-constructible: `Q` and `R` are square roots, the
angles `α` and `β` are arccosines (`exists_polar_Pconstructible`), `θ` and `φ` are halves
of their sum and difference, and `cos_sin_Pconstructible` then supplies the four
trigonometric matrix entries.

`PConstructibleCurve.translate_x` and `translate_y` extend all of this from the linear
maps to the *affine* ones, since an affine map is a linear map followed by a translation
and the two halves are now separately available. -/

/-- The linear map of the plane with matrix `[[a, b], [c, d]]`, acting on the point
`(x, y)` as the column vector it names: `(x, y) ↦ (a * x + b * y, c * x + d * y)`. -/
def linearMap (a b c d : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (a * p.1 + b * p.2, c * p.1 + d * p.2)

-- Theorem: scaling `x` by `sx` and `y` by `sy` is the linear map `[[sx, 0], [0, sy]]`.
theorem scale_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {sx sy : ℝ} (hsx : PConstructible sx) (hsy : PConstructible sy) :
    PConstructibleCurve (linearMap sx 0 0 sy '' S) := by
  have h := (hS.scale_x hsx).scale_y hsy
  rw [← Set.image_comp] at h
  have hfun : ((fun p : ℝ × ℝ => (p.1, sy * p.2)) ∘ fun p : ℝ × ℝ => (sx * p.1, p.2))
      = linearMap sx 0 0 sy := by
    funext p
    simp [linearMap]
  rwa [hfun] at h

-- Theorem: uniform scaling is the two axis scalings sharing a factor. This is the single
-- `stretch` operation the definition used to carry, now derived.
theorem stretch_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {s : ℝ} (hs : PConstructible s) :
    PConstructibleCurve ((fun p : ℝ × ℝ => (s * p.1, s * p.2)) '' S) := by
  have h := scale_PConstructibleCurve hS hs hs
  have hfun : linearMap s 0 0 s = fun p : ℝ × ℝ => (s * p.1, s * p.2) := by
    funext p
    simp [linearMap]
  rwa [hfun] at h

-- Theorem: rotation by a whole number of degrees, restated as a linear map. The angle is
-- taken as a hypothesis rather than computed, so a caller may present it in whichever form
-- is convenient -- `π / 6` rather than `30 * (π / 180)`, say.
theorem rotate_deg_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (n : ℤ) {θ : ℝ} (hθ : θ = (n : ℝ) * (Real.pi / 180)) :
    PConstructibleCurve
      (linearMap (Real.cos θ) (-Real.sin θ) (Real.sin θ) (Real.cos θ) '' S) := by
  subst hθ
  have hfun : (fun p : ℝ × ℝ =>
        let φ := (n : ℝ) * (Real.pi / 180)
        (p.1 * Real.cos φ - p.2 * Real.sin φ, p.1 * Real.sin φ + p.2 * Real.cos φ))
      = linearMap (Real.cos ((n : ℝ) * (Real.pi / 180)))
          (-Real.sin ((n : ℝ) * (Real.pi / 180))) (Real.sin ((n : ℝ) * (Real.pi / 180)))
          (Real.cos ((n : ℝ) * (Real.pi / 180))) := by
    funext p
    simp only [linearMap, Prod.mk.injEq]
    constructor <;> ring
  rw [← hfun]
  exact hS.rotate n

-- Theorem: the matching quadratic `3p² + (16c² - 6)p + 3 = 0` has a P-constructible root
-- whenever `c² ≥ 3/4`, and that root avoids the three values at which the matching would
-- divide by zero.
--
-- The discriminant is `(16c² - 6)² - 36`, non-negative exactly when `16c² - 6 ≥ 6`, which is
-- the hypothesis on `c²`. The three exclusions come out of the equation itself: `p = 1`
-- forces `16c² - 6 = -6`, while `p = -3` and `p = -1/3` both force `16c² - 6 = 10`, that is
-- `c² = 1`, which `s ≠ 0` rules out.
theorem exists_rotation_param {c s : ℝ} (hcP : PConstructible c) (hsc : s ^ 2 + c ^ 2 = 1)
    (hc2 : 3 / 4 ≤ c ^ 2) (hs0 : s ≠ 0) :
    ∃ p : ℝ, PConstructible p ∧ 3 * p ^ 2 + (16 * c ^ 2 - 6) * p + 3 = 0 ∧
      p - 1 ≠ 0 ∧ p + 3 ≠ 0 ∧ 3 * p + 1 ≠ 0 := by
  have h6 : PConstructible (6 : ℝ) := by simpa using nat_Pconstructible 6
  have h16 : PConstructible (16 : ℝ) := by simpa using nat_Pconstructible 16
  have h36 : PConstructible (36 : ℝ) := by simpa using nat_Pconstructible 36
  have hs2 : 0 < s ^ 2 := by positivity
  have hw6 : (6 : ℝ) ≤ 16 * c ^ 2 - 6 := by nlinarith
  have hw10 : 16 * c ^ 2 - 6 < 10 := by nlinarith
  have hDnn : 0 ≤ (16 * c ^ 2 - 6) ^ 2 - 36 := by nlinarith
  have hDsq : Real.sqrt ((16 * c ^ 2 - 6) ^ 2 - 36) ^ 2 = (16 * c ^ 2 - 6) ^ 2 - 36 :=
    Real.sq_sqrt hDnn
  obtain ⟨p, hp_def⟩ :
      ∃ p : ℝ, p = (-(16 * c ^ 2 - 6) + Real.sqrt ((16 * c ^ 2 - 6) ^ 2 - 36)) / 6 := ⟨_, rfl⟩
  have hquad : 3 * p ^ 2 + (16 * c ^ 2 - 6) * p + 3 = 0 := by
    rw [hp_def]
    field_simp
    linear_combination 3 * hDsq
  refine ⟨p, ?_, hquad, ?_, ?_, ?_⟩
  · rw [hp_def]
    exact PConstructible.div
      (PConstructible.add
        (neg_Pconstructible (PConstructible.sub
          (PConstructible.mul h16 (sq_Pconstructible hcP)) h6))
        (sqrt_Pconstructible (PConstructible.sub
          (sq_Pconstructible (PConstructible.sub
            (PConstructible.mul h16 (sq_Pconstructible hcP)) h6)) h36)))
      h6
  · intro h
    have hp1 : p = 1 := by linarith
    rw [hp1] at hquad
    nlinarith
  · intro h
    have hp3 : p = -3 := by linarith
    rw [hp3] at hquad
    nlinarith
  · intro h
    have hp13 : p = -(1 / 3) := by linarith
    rw [hp13] at hquad
    nlinarith

-- Theorem: rotation by a P-constructible angle of at most 30° either way is a constructible
-- transformation. This is the geometric core of the section; the five factors and the
-- quadratic in `p` are explained above.
theorem rotate_small_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {ψ : ℝ} (hψ : PConstructible ψ) (hcos : Real.sqrt 3 / 2 ≤ Real.cos ψ) :
    PConstructibleCurve
      (linearMap (Real.cos ψ) (-Real.sin ψ) (Real.sin ψ) (Real.cos ψ) '' S) := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have h3pos : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hrP : PConstructible (Real.sqrt 3) := sqrt_Pconstructible three_Pconstructible
  have hcP : PConstructible (Real.cos ψ) := cos_Pconstructible hψ
  have hsP : PConstructible (Real.sin ψ) := sin_Pconstructible hψ
  set c := Real.cos ψ with hc_def
  set s := Real.sin ψ with hs_def
  have hsc : s ^ 2 + c ^ 2 = 1 := Real.sin_sq_add_cos_sq ψ
  have hcpos : 0 < c := lt_of_lt_of_le (by positivity) hcos
  have hc2 : 3 / 4 ≤ c ^ 2 := by nlinarith
  rcases eq_or_ne s 0 with hs0 | hs0
  · have hc1 : c = 1 := by nlinarith
    have hid : linearMap c (-s) s c = id := by
      funext z
      simp [linearMap, hc1, hs0]
    rw [hid, Set.image_id]
    exact hS
  obtain ⟨p, hpP, hquad, hX1, hX3, hX2⟩ := exists_rotation_param hcP hsc hc2 hs0
  have hrne : Real.sqrt 3 ≠ 0 := ne_of_gt h3pos
  have hcne : c ≠ 0 := ne_of_gt hcpos
  have h4P : PConstructible (4 : ℝ) := by simpa using nat_Pconstructible 4
  obtain ⟨A, hA_def⟩ : ∃ A : ℝ, A = 4 * c / (Real.sqrt 3 * (p - 1)) := ⟨_, rfl⟩
  obtain ⟨B, hB_def⟩ : ∃ B : ℝ, B = 4 * s / (p + 3) := ⟨_, rfl⟩
  obtain ⟨H, hH_def⟩ : ∃ H : ℝ, H = s * Real.sqrt 3 * (p - 1) / (c * (3 * p + 1)) := ⟨_, rfl⟩
  have hX1' : -1 + p ≠ 0 := fun h => hX1 (by linarith)
  have hX2' : 1 + p * 3 ≠ 0 := fun h => hX2 (by linarith)
  have hX2'' : p * 3 + 1 ≠ 0 := fun h => hX2 (by linarith)
  have hX3' : 3 + p ≠ 0 := fun h => hX3 (by linarith)
  have e1 : A * (Real.sqrt 3 / 4 * (p - 1)) = c := by
    rw [hA_def]; field_simp [hrne, hX1, hX1']
  have e2 : A * H * ((3 * p + 1) / 4) = s := by
    rw [hA_def, hH_def]; field_simp [hrne, hX1, hX1', hX2, hX2', hcne]
  have e3 : B * ((p + 3) / 4) = s := by
    rw [hB_def]; field_simp [hX3, hX3']
  have e4 : B * H * (Real.sqrt 3 / 4 * (p - 1)) = -c := by
    rw [hB_def, hH_def]; field_simp [hX3, hX3', hX2, hX2', hcne]
    linear_combination (s ^ 2 * (p - 1) ^ 2) * h3 + hquad + (3 * (p - 1) ^ 2) * hsc
  have hAP : PConstructible A := by
    rw [hA_def]
    exact PConstructible.div (PConstructible.mul h4P hcP)
      (PConstructible.mul hrP (PConstructible.sub hpP PConstructible.base_one))
  have hBP : PConstructible B := by
    rw [hB_def]
    exact PConstructible.div (PConstructible.mul h4P hsP)
      (PConstructible.add hpP three_Pconstructible)
  have hHP : PConstructible H := by
    rw [hH_def]
    exact PConstructible.div
      (PConstructible.mul (PConstructible.mul hsP hrP)
        (PConstructible.sub hpP PConstructible.base_one))
      (PConstructible.mul hcP
        (PConstructible.add (PConstructible.mul three_Pconstructible hpP)
          PConstructible.base_one))
  have hM : linearMap c (-s) s c =
      linearMap A 0 0 B ∘
        linearMap (Real.sqrt 3 / 2) (-(1 / 2)) (1 / 2) (Real.sqrt 3 / 2) ∘
          linearMap p 0 0 1 ∘
            linearMap (1 / 2) (-(Real.sqrt 3 / 2)) (Real.sqrt 3 / 2) (1 / 2) ∘
              linearMap 1 0 0 H := by
    funext z
    simp only [Function.comp_apply, linearMap, Prod.mk.injEq]
    constructor
    · linear_combination -(z.1 * e1) + z.2 * e2 + (A * p * H * z.2 / 4) * h3
    · linear_combination -(z.1 * e3) + z.2 * e4 - (B * z.1 / 4) * h3
  have hstep1 := scale_PConstructibleCurve hS PConstructible.base_one hHP
  have hstep2 := rotate_deg_PConstructibleCurve hstep1 60 (by push_cast; ring :
    Real.pi / 3 = ((60 : ℤ) : ℝ) * (Real.pi / 180))
  rw [Real.cos_pi_div_three, Real.sin_pi_div_three] at hstep2
  have hstep3 := scale_PConstructibleCurve hstep2 hpP PConstructible.base_one
  have hstep4 := rotate_deg_PConstructibleCurve hstep3 30 (by push_cast; ring :
    Real.pi / 6 = ((30 : ℤ) : ℝ) * (Real.pi / 180))
  rw [Real.cos_pi_div_six, Real.sin_pi_div_six] at hstep4
  have hstep5 := scale_PConstructibleCurve hstep4 hAP hBP
  rw [hM]
  simp only [Set.image_comp]
  exact hstep5

-- Theorem: every real number sits within half a degree of a whole number of degrees.
theorem exists_int_degrees (x : ℝ) :
    ∃ n : ℤ, |x - n * (Real.pi / 180)| ≤ Real.pi / 360 := by
  have hd : (0 : ℝ) < Real.pi / 180 := by positivity
  refine ⟨round (x / (Real.pi / 180)), ?_⟩
  have h := abs_sub_round (x / (Real.pi / 180))
  have hrw : x - (round (x / (Real.pi / 180)) : ℝ) * (Real.pi / 180)
      = Real.pi / 180 * (x / (Real.pi / 180) - (round (x / (Real.pi / 180)) : ℝ)) := by
    field_simp
  rw [hrw, abs_mul, abs_of_pos hd]
  nlinarith [abs_nonneg (x / (Real.pi / 180) - (round (x / (Real.pi / 180)) : ℝ))]

-- Theorem: rotation by *any* P-constructible angle is a constructible transformation,
-- even though only whole-degree rotations are assumed. Rounding to the nearest whole
-- degree leaves a residue of at most half a degree, comfortably inside the 30° window of
-- `rotate_small_PConstructibleCurve`, and the whole-degree part is a primitive.
theorem rotate_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {ψ : ℝ} (hψ : PConstructible ψ) :
    PConstructibleCurve
      (linearMap (Real.cos ψ) (-Real.sin ψ) (Real.sin ψ) (Real.cos ψ) '' S) := by
  have h180 : PConstructible (180 : ℝ) := by simpa using nat_Pconstructible 180
  obtain ⟨n, hn⟩ := exists_int_degrees ψ
  obtain ⟨φ, hφ_def⟩ : ∃ φ : ℝ, φ = ψ - n * (Real.pi / 180) := ⟨_, rfl⟩
  have hφP : PConstructible φ := by
    rw [hφ_def]
    exact PConstructible.sub hψ (PConstructible.mul (int_Pconstructible n)
      (PConstructible.div pi_Pconstructible h180))
  have habs : |φ| ≤ Real.pi / 360 := by rw [hφ_def]; exact hn
  have hcos : Real.sqrt 3 / 2 ≤ Real.cos φ := by
    have hpi := Real.pi_pos
    have h1 : |φ| ≤ Real.pi / 6 := by linarith
    have h2 := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg φ) (by linarith) h1
    rwa [Real.cos_pi_div_six, Real.cos_abs] at h2
  have hdeg := rotate_deg_PConstructibleCurve
    (rotate_small_PConstructibleCurve hS hφP hcos) n rfl
  rw [← Set.image_comp] at hdeg
  have hsum : ψ = (n : ℝ) * (Real.pi / 180) + φ := by rw [hφ_def]; ring
  have hfun :
      (linearMap (Real.cos ((n : ℝ) * (Real.pi / 180)))
          (-Real.sin ((n : ℝ) * (Real.pi / 180))) (Real.sin ((n : ℝ) * (Real.pi / 180)))
          (Real.cos ((n : ℝ) * (Real.pi / 180))) ∘
        linearMap (Real.cos φ) (-Real.sin φ) (Real.sin φ) (Real.cos φ))
      = linearMap (Real.cos ψ) (-Real.sin ψ) (Real.sin ψ) (Real.cos ψ) := by
    rw [hsum, Real.cos_add, Real.sin_add]
    funext z
    simp only [Function.comp_apply, linearMap, Prod.mk.injEq]
    constructor <;> ring
  rwa [hfun] at hdeg

-- Theorem: a point of the plane with P-constructible coordinates has P-constructible polar
-- coordinates -- a radius `r` and an angle `ψ`, both P-constructible, with
-- `(u, v) = r * (cos ψ, sin ψ)`.
--
-- The radius is `√(u² + v²)` and the angle is `± arccos (u / r)`, the sign chosen to match
-- the sign of `v`: `arccos` only ever returns an angle in `[0, π]`, so on its own it can
-- never reach the lower half plane. The degenerate case `r = 0` forces `u = v = 0`, where
-- any angle will do.
theorem exists_polar_Pconstructible {u v : ℝ} (hu : PConstructible u) (hv : PConstructible v) :
    ∃ r ψ : ℝ, PConstructible r ∧ PConstructible ψ ∧
      r * Real.cos ψ = u ∧ r * Real.sin ψ = v := by
  have hrP : PConstructible (Real.sqrt (u ^ 2 + v ^ 2)) :=
    sqrt_Pconstructible (PConstructible.add (sq_Pconstructible hu) (sq_Pconstructible hv))
  set r := Real.sqrt (u ^ 2 + v ^ 2) with hr_def
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r ^ 2 = u ^ 2 + v ^ 2 := Real.sq_sqrt (by positivity)
  rcases hr0.eq_or_lt with hr | hrpos
  · refine ⟨r, 0, hrP, zero_Pconstructible, ?_, ?_⟩
    · have hu0 : u = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      simp [← hr, hu0]
    · have hv0 : v = 0 := by nlinarith [sq_nonneg u, sq_nonneg v]
      simp [← hr, hv0]
  · have habs : |u / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hrpos, div_le_one hrpos, abs_le]
      constructor <;> nlinarith [sq_nonneg v]
    obtain ⟨hc1, hc2⟩ := abs_le.mp habs
    have hcos : Real.cos (Real.arccos (u / r)) = u / r := Real.cos_arccos hc1 hc2
    have hsin : Real.sin (Real.arccos (u / r)) = |v| / r := by
      rw [Real.sin_arccos, show 1 - (u / r) ^ 2 = (v / r) ^ 2 by field_simp; nlinarith,
        Real.sqrt_sq_eq_abs, abs_div, abs_of_pos hrpos]
    have harc : PConstructible (Real.arccos (u / r)) :=
      arccos_Pconstructible (PConstructible.div hu hrP)
    rcases le_or_gt 0 v with hv0 | hv0
    · refine ⟨r, Real.arccos (u / r), hrP, harc, ?_, ?_⟩
      · rw [hcos]; field_simp
      · rw [hsin, abs_of_nonneg hv0]; field_simp
    · refine ⟨r, -Real.arccos (u / r), hrP, neg_Pconstructible harc, ?_, ?_⟩
      · rw [Real.cos_neg, hcos]; field_simp
      · rw [Real.sin_neg, hsin, abs_of_neg hv0]; field_simp

-- Theorem: `PConstructibleCurve` is closed under every linear transformation of the plane
-- whose four matrix entries are P-constructible. Three steps do it: rotate by `φ`, scale
-- the axes by `Q + R` and `Q - R`, then rotate by `θ`.
theorem linearMap_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {a b c d : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hc : PConstructible c) (hd : PConstructible d) :
    PConstructibleCurve (linearMap a b c d '' S) := by
  obtain ⟨Q, α, hQP, hαP, hQc, hQs⟩ :=
    exists_polar_Pconstructible
      (PConstructible.div (PConstructible.add ha hd) two_Pconstructible)
      (PConstructible.div (PConstructible.sub hc hb) two_Pconstructible)
  obtain ⟨R, β, hRP, hβP, hRc, hRs⟩ :=
    exists_polar_Pconstructible
      (PConstructible.div (PConstructible.sub ha hd) two_Pconstructible)
      (PConstructible.div (PConstructible.add hc hb) two_Pconstructible)
  obtain ⟨θ, hθ_def⟩ : ∃ t : ℝ, t = (α + β) / 2 := ⟨_, rfl⟩
  obtain ⟨φ, hφ_def⟩ : ∃ f : ℝ, f = (α - β) / 2 := ⟨_, rfl⟩
  have hθP : PConstructible θ := by
    rw [hθ_def]
    exact PConstructible.div (PConstructible.add hαP hβP) two_Pconstructible
  have hφP : PConstructible φ := by
    rw [hφ_def]
    exact PConstructible.div (PConstructible.sub hαP hβP) two_Pconstructible
  have hα : α = θ + φ := by rw [hθ_def, hφ_def]; ring
  have hβ : β = θ - φ := by rw [hθ_def, hφ_def]; ring
  rw [hα, Real.cos_add] at hQc
  rw [hα, Real.sin_add] at hQs
  rw [hβ, Real.cos_sub] at hRc
  rw [hβ, Real.sin_sub] at hRs
  have hstep := rotate_PConstructibleCurve
    (scale_PConstructibleCurve (rotate_PConstructibleCurve hS hφP)
      (PConstructible.add hQP hRP) (PConstructible.sub hQP hRP)) hθP
  have hfun :
      linearMap a b c d =
        linearMap (Real.cos θ) (-Real.sin θ) (Real.sin θ) (Real.cos θ) ∘
          linearMap (Q + R) 0 0 (Q - R) ∘
            linearMap (Real.cos φ) (-Real.sin φ) (Real.sin φ) (Real.cos φ) := by
    funext z
    simp only [Function.comp_apply, linearMap, Prod.mk.injEq]
    constructor
    · linear_combination -(z.1 * hQc) - z.1 * hRc + z.2 * hQs - z.2 * hRs
    · linear_combination -(z.1 * hQs) - z.1 * hRs - z.2 * hQc + z.2 * hRc
  rw [hfun]
  simp only [Set.image_comp]
  exact hstep

-- Theorem: a shear is a constructible transformation. Not an interesting map in itself,
-- but it is exactly the kind that no composite of rotations and *uniform* scalings can
-- produce, so it is the shortest witness that the theorem above has real content.
theorem shear_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {k : ℝ} (hk : PConstructible k) :
    PConstructibleCurve ((fun p : ℝ × ℝ => (p.1 + k * p.2, p.2)) '' S) := by
  have h := linearMap_PConstructibleCurve hS PConstructible.base_one hk
    zero_Pconstructible PConstructible.base_one
  have hfun : linearMap 1 k 0 1 = fun p : ℝ × ℝ => (p.1 + k * p.2, p.2) := by
    funext p
    simp [linearMap]
  rwa [hfun] at h

/-- The affine map of the plane with linear part `[[a, b], [c, d]]` and translation
`(u, v)`: `(x, y) ↦ (a * x + b * y + u, c * x + d * y + v)`. -/
def affineMap (a b c d u v : ℝ) : ℝ × ℝ → ℝ × ℝ :=
  fun p => (a * p.1 + b * p.2 + u, c * p.1 + d * p.2 + v)

-- Theorem: `PConstructibleCurve` is closed under every affine transformation of the plane
-- with P-constructible coefficients. An affine map is a linear map followed by a
-- translation, and each half is now available on its own: `linearMap_PConstructibleCurve`
-- for the matrix and `translate_PConstructibleCurve` for the shift.
--
-- Together with the linear theorem this says the class is closed under the whole affine
-- group. Where an invertible linear map is pinned down by where it sends two independent
-- vectors, an invertible affine map is pinned down by where it sends three non-collinear
-- points, so any triangle may be carried to any other and any curve dragged along with it.
theorem affineMap_PConstructibleCurve {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    {a b c d u v : ℝ} (ha : PConstructible a) (hb : PConstructible b)
    (hc : PConstructible c) (hd : PConstructible d)
    (hu : PConstructible u) (hv : PConstructible v) :
    PConstructibleCurve (affineMap a b c d u v '' S) := by
  have h := translate_PConstructibleCurve (linearMap_PConstructibleCurve hS ha hb hc hd) hu hv
  have hfun : (fun p : ℝ × ℝ => (p.1 + u, p.2 + v)) ∘ linearMap a b c d
      = affineMap a b c d u v := by
    funext z
    simp [linearMap, affineMap]
  rwa [← Set.image_comp, hfun] at h

-- Theorem: the affine maps really do contain both halves they were assembled from. With
-- the identity linear part `affineMap` is a plain translation, and with no shift it is
-- `linearMap`, so nothing was lost in the packaging.
theorem affineMap_id_left {u v : ℝ} :
    affineMap 1 0 0 1 u v = fun p : ℝ × ℝ => (p.1 + u, p.2 + v) := by
  funext p
  simp [affineMap]

theorem affineMap_zero_right {a b c d : ℝ} : affineMap a b c d 0 0 = linearMap a b c d := by
  funext p
  simp [affineMap, linearMap]


/-! ### The incomplete elliptic integral of the second kind

`E(φ) = ∫₀^φ √(1 - c sin²θ) dθ` *is* an arc length of an ellipse, and at the right size
it is one on the nose. Trace the ellipse with semi-axes `1` and `b = √(1 - c)` by

  `γ θ = (sin θ, b cos θ)`,

so `θ = 0` is the top of the ellipse and `θ` increases towards the right. Its speed is

  `√(cos²θ + b² sin²θ) = √(cos²θ + (1 - c) sin²θ) = √(1 - c sin²θ)`,

which is the integrand, so the arc swept over `[0, φ]` has length exactly `E(φ)`.

Both endpoints of that arc are P-constructible points of the plane: the near one is
`(0, b)` and the far one is `(sin φ, b cos φ)`. That is where `sin_Pconstructible` and
`cos_Pconstructible` are spent, and it is all `PConstructible.arc_length` asks for — so
the integral is read straight off the plane, with no auxiliary curve.

A drawing program cannot name the parameter `φ`, and would instead cut the arc out with a
wedge at the centre of the ellipse of angle `arctan (tan φ / b)`, the polar angle at which
the parameter `φ` sits, after stretching the ellipse by `1 / b` to put a `1` on the other
semi-axis and dividing the measured length by that same factor afterwards. Both steps are
ways of *locating* the far endpoint; `arc_length` only requires that endpoint to be
P-constructible, which the sine and cosine theorems already supply. So the ellipse is used
here at exactly the size at which its arc length is `E(φ)`, and nothing is rescaled.

Mathlib does not define the elliptic integrals, so they are spelled out here.

Throughout, the elliptic integrals are indexed by the **parameter** `c`, the square of the
more familiar modulus `k`; `c < 1` is the standing hypothesis. Legendre's `E(φ, k)` is the
case `c = k²`, recorded as `ellipticE_sq_Pconstructible` at the end of the next section.
Allowing negative `c` is not idle generality: the reflection that carries the first-kind
integral past `φ = π/2` lands on the complementary parameter `-c / (1 - c)`, which is
negative whenever `c` is positive. -/

/-- The integrand of the elliptic integral of the second kind, `√(1 - c sin²θ)`. It is
also the reciprocal of the first-kind integrand, so the two share this definition. -/
noncomputable def ellipticEIntegrand (c θ : ℝ) : ℝ :=
  Real.sqrt (1 - c * Real.sin θ ^ 2)

/-- The incomplete elliptic integral of the second kind,
`E(φ) = ∫₀^φ √(1 - c sin²θ) dθ`, in terms of the parameter `c = k²`. -/
noncomputable def ellipticE (c φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, ellipticEIntegrand c θ

-- Theorem: at `c = 0` the ellipse is the unit circle and `E(φ) = φ`, the arc length of
-- the circle being its angle. A check that the definition is the right one.
theorem ellipticE_zero (φ : ℝ) : ellipticE 0 φ = φ := by
  simp [ellipticE, ellipticEIntegrand]

-- Theorem: for `c < 1` the integrand is strictly positive, so it is safe to invert.
-- Both signs of `c` need saying: `c sin²θ` is at most `c` when `c ≥ 0` and at most `0`
-- when `c ≤ 0`.
theorem one_sub_mul_sin_sq_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < 1 - c * Real.sin θ ^ 2 := by
  rcases le_total c 0 with h | h
  · nlinarith [sq_nonneg (Real.sin θ)]
  · nlinarith [Real.sin_sq_le_one θ]

theorem ellipticEIntegrand_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < ellipticEIntegrand c θ :=
  Real.sqrt_pos.mpr (one_sub_mul_sin_sq_pos hc θ)

theorem ellipticEIntegrand_sq {c : ℝ} (hc : c < 1) (θ : ℝ) :
    ellipticEIntegrand c θ ^ 2 = 1 - c * Real.sin θ ^ 2 :=
  Real.sq_sqrt (one_sub_mul_sin_sq_pos hc θ).le

theorem continuous_ellipticEIntegrand (c : ℝ) : Continuous (ellipticEIntegrand c) := by
  unfold ellipticEIntegrand
  fun_prop

theorem intervalIntegrable_ellipticEIntegrand (c a b : ℝ) :
    IntervalIntegrable (ellipticEIntegrand c) MeasureTheory.volume a b :=
  (continuous_ellipticEIntegrand c).intervalIntegrable a b

/-- The ellipse centred at the origin with horizontal semi-axis `1` and vertical
semi-axis `b`, from the `ellipse` constructor with bounding box `2 × 2b`. -/
theorem ellipse_PConstructibleCurve {b : ℝ} (hb : PConstructible b) (hbpos : 0 < b) :
    PConstructibleCurve
      {p : ℝ × ℝ | ((p.1 - 0) / (2 / 2)) ^ 2 + ((p.2 - 0) / (2 * b / 2)) ^ 2 = 1} :=
  PConstructibleCurve.ellipse 0 0 2 (2 * b) zero_Pconstructible zero_Pconstructible
    two_Pconstructible (PConstructible.mul two_Pconstructible hb) (by norm_num) (by positivity)

/-- The ellipse with semi-axes `1` and `b`, parametrized from the top. On `[0, π]` this
traces the right half of it injectively, since `cos` is injective there. -/
noncomputable def ellipseParam (b : ℝ) : ℝ → ℝ × ℝ := fun θ => (Real.sin θ, b * Real.cos θ)

-- Theorem: the ellipse is traced at speed `√(cos²θ + b² sin²θ)`.
theorem speed_ellipseParam (b θ : ℝ) :
    speed (ellipseParam b) θ = Real.sqrt (Real.cos θ ^ 2 + b ^ 2 * Real.sin θ ^ 2) := by
  have hc : HasDerivAt (fun s : ℝ => (ellipseParam b s).1) (Real.cos θ) θ :=
    Real.hasDerivAt_sin θ
  have hs : HasDerivAt (fun s : ℝ => (ellipseParam b s).2) (b * -Real.sin θ) θ :=
    (Real.hasDerivAt_cos θ).const_mul b
  rw [speed, hc.deriv, hs.deriv]
  congr 1
  ring

-- Theorem: with `b² = 1 - c` that speed is exactly the elliptic integrand.
theorem speed_ellipseParam_eq {c b : ℝ} (hb : b ^ 2 = 1 - c) (θ : ℝ) :
    speed (ellipseParam b) θ = ellipticEIntegrand c θ := by
  rw [speed_ellipseParam, hb, ellipticEIntegrand]
  congr 1
  linear_combination Real.sin_sq_add_cos_sq θ

-- Theorem: so the arc swept over `[0, φ]` has length `E(φ)`.
theorem arcLengthOf_ellipseParam {c b : ℝ} (hb : b ^ 2 = 1 - c) (φ : ℝ) :
    arcLengthOf (ellipseParam b) 0 φ = ellipticE c φ := by
  rw [arcLengthOf, ellipticE]
  simp only [speed_ellipseParam_eq hb]

-- Theorem: `E(φ)` is P-constructible for `0 ≤ φ ≤ π`.
--
-- The bound `φ ≤ π` is exactly what the injectivity side condition of
-- `PConstructible.arc_length` needs: past a half turn the parametrization comes back over
-- ellipse it has already covered, and the integral would stop being a length.
theorem ellipticE_Pconstructible_of_mem_Icc {c b φ : ℝ} (hb : b ^ 2 = 1 - c)
    (hbpos : 0 < b) (hbP : PConstructible b) (hφ : PConstructible φ)
    (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) : PConstructible (ellipticE c φ) := by
  rw [← arcLengthOf_ellipseParam hb φ]
  refine PConstructible.arc_length (ellipse_PConstructibleCurve hbP hbpos) (ellipseParam b)
    h0 ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the ellipse
    rintro p ⟨θ, _, rfl⟩
    simp only [Set.mem_ofPred_eq, ellipseParam, sub_zero]
    field_simp
    linear_combination Real.sin_sq_add_cos_sq θ
  · -- injective on `[0, φ] ⊆ [0, π]`, because `cos` is
    intro t₁ ht₁ t₂ ht₂ h
    have hcos : Real.cos t₁ = Real.cos t₂ :=
      mul_left_cancel₀ hbpos.ne' (congrArg Prod.snd h)
    exact Real.injOn_cos (Set.Icc_subset_Icc le_rfl hpi ht₁)
      (Set.Icc_subset_Icc le_rfl hpi ht₂) hcos
  · -- differentiable in each coordinate
    intro t _
    exact ⟨(Real.hasDerivAt_sin t).differentiableAt,
      ((Real.hasDerivAt_cos t).const_mul b).differentiableAt⟩
  · -- the speed is continuous, hence integrable
    rw [show speed (ellipseParam b) = ellipticEIntegrand c from
      funext (speed_ellipseParam_eq hb)]
    exact intervalIntegrable_ellipticEIntegrand c 0 φ
  · simpa [ellipseParam] using zero_Pconstructible
  · simpa [ellipseParam] using hbP
  · simpa [ellipseParam] using sin_Pconstructible hφ
  · simpa [ellipseParam] using PConstructible.mul hbP (cos_Pconstructible hφ)

/-! Beyond a half turn the ellipse repeats, and so does `E`. Only `sin²θ` occurs in the
integrand, so it has period `π`, and `E(φ + nπ) = E(φ) + n · E(π)`: reducing `φ` modulo
`π` removes the restriction `0 ≤ φ ≤ π` above, exactly as reduction modulo `2π` did for
`cos` and `sin`. The same two facts serve the first-kind integral in the next section,
whose integrand is the reciprocal of this one and so has the same period. -/

-- Theorem: the second-kind integrand has period `π`, since `sin (θ + π) = -sin θ` is
-- squared.
theorem periodic_ellipticEIntegrand (c : ℝ) :
    Function.Periodic (ellipticEIntegrand c) Real.pi := fun θ => by
  simp [ellipticEIntegrand, Real.sin_add_pi]

-- Theorem: `E(φ + nπ) = E(φ) + n · E(π)`.
theorem ellipticE_add_int_mul_pi (c φ : ℝ) (n : ℤ) :
    ellipticE c (φ + n * Real.pi) = ellipticE c φ + n * ellipticE c Real.pi := by
  have hper := periodic_ellipticEIntegrand c
  have hint : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (ellipticEIntegrand c) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => intervalIntegrable_ellipticEIntegrand c t₁ t₂
  -- the whole turns: `n` copies of one period, each of length `E(π)`
  have hA : (∫ θ in (0 : ℝ)..(n : ℝ) * Real.pi, ellipticEIntegrand c θ)
      = n * ellipticE c Real.pi := by
    have h := hper.intervalIntegral_add_zsmul_eq n 0 hint
    simpa [ellipticE, zsmul_eq_mul] using h
  -- the remainder: a translate of `[0, φ]` by a whole number of periods
  have hB : (∫ θ in ((n : ℝ) * Real.pi)..(φ + (n : ℝ) * Real.pi), ellipticEIntegrand c θ)
      = ellipticE c φ := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := φ)
      (ellipticEIntegrand c) ((n : ℝ) * Real.pi)
    have hshift : ∀ x : ℝ,
        ellipticEIntegrand c (x + (n : ℝ) * Real.pi) = ellipticEIntegrand c x :=
      fun x => hper.int_mul n x
    simp only [hshift, zero_add] at h
    rw [ellipticE, h]
  rw [ellipticE, ← intervalIntegral.integral_add_adjacent_intervals
    (b := (n : ℝ) * Real.pi) (hint 0 _) (hint _ _), hA, hB]
  ring

-- Theorem: every real number sits a whole number of half-turns away from one in `[0, π)`.
theorem exists_int_half_turns (x : ℝ) :
    ∃ n : ℤ, 0 ≤ x - n * Real.pi ∧ x - n * Real.pi ≤ Real.pi := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  refine ⟨⌊x / Real.pi⌋, ?_, ?_⟩
  · have h := mul_le_mul_of_nonneg_right (Int.floor_le (x / Real.pi)) hpi.le
    rw [div_mul_cancel₀ _ hpi.ne'] at h
    linarith
  · have h := mul_lt_mul_of_pos_right (Int.lt_floor_add_one (x / Real.pi)) hpi
    rw [div_mul_cancel₀ _ hpi.ne'] at h
    linarith

-- Theorem: `E(φ)` is P-constructible for every P-constructible `φ` and every
-- P-constructible parameter `c < 1`.
--
-- `c < 1` is what makes the ellipse drawable: `b = √(1 - c)` has to be a positive length.
-- It is also exactly the range in which the integrand is real for every `θ`.
theorem ellipticE_Pconstructible {c φ : ℝ} (hc : PConstructible c) (hφ : PConstructible φ)
    (hc1 : c < 1) : PConstructible (ellipticE c φ) := by
  have hb : Real.sqrt (1 - c) ^ 2 = 1 - c := Real.sq_sqrt (by linarith)
  have hbpos : 0 < Real.sqrt (1 - c) := Real.sqrt_pos.mpr (by linarith)
  have hbP : PConstructible (Real.sqrt (1 - c)) :=
    sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hc)
  obtain ⟨n, h0, hpi⟩ := exists_int_half_turns φ
  have hrP : PConstructible (φ - n * Real.pi) :=
    PConstructible.sub hφ (PConstructible.mul (int_Pconstructible n) pi_Pconstructible)
  have hr := ellipticE_Pconstructible_of_mem_Icc hb hbpos hbP hrP h0 hpi
  have hEpi := ellipticE_Pconstructible_of_mem_Icc hb hbpos hbP pi_Pconstructible
    Real.pi_pos.le le_rfl
  have hkey : ellipticE c φ
      = ellipticE c (φ - n * Real.pi) + n * ellipticE c Real.pi := by
    have h := ellipticE_add_int_mul_pi c (φ - n * Real.pi) n
    rwa [sub_add_cancel] at h
  rw [hkey]
  exact PConstructible.add hr (PConstructible.mul (int_Pconstructible n) hEpi)


/-! ### The incomplete elliptic integral of the first kind

`F(φ) = ∫₀^φ dθ/√(1 - c sin²θ)` is not the arc length of an ellipse, or of any other
curve on the list: an arc length is `∫√(x'² + y'²)`, always a square *root* of something,
while `F` carries its radical in the denominator. What produces `F` is one arc length
together with an integration by parts.

Take `t = tan ψ`, which turns the integrand into

  `∫₀^φ dψ/√(1 - c sin²ψ) = ∫₀^{tan φ} dt/√((1 + t²)(1 + m² t²))`,  `m² = 1 - c`.

The point of that substitution is the shape of the new quartic. A cubic Bézier moves with
speed `√(x'(t)² + y'(t)²)` for quadratics `x'`, `y'`, so the quartics it can realise are
exactly the *sums of two squares* — the ones that are non-negative everywhere. Jacobi's
`(1 - t²)(1 - k² t²)` goes negative past `t = 1` and is therefore out of reach, but the
tangent form is positive definite, and Brahmagupta–Fibonacci exhibits the two squares:

  `(1² + t²)(1² + (mt)²) = (1 - m t²)² + (t + m t)²`.

So the cubic `t ↦ (t - m t³/3, (1 + m) t²/2)` — control points `(0,0)`, `(T/3, 0)`,
`(2T/3, (1+m)T²/6)`, `(T - mT³/3, (1+m)T²/2)`, all P-constructible — moves at exactly
speed `√((1+t²)(1+m²t²))`, and its arc length `J` is P-constructible.

Two integrations by parts then turn `J` back into `F`. Differentiating `t √P` gives

  `3√P - ((1 + m²)t² + 2)/√P`,

so `3J - T √P(T) = (1 + m²) I₂ + 2 F` where `I₂ = ∫₀^T t² dt/√P`; and differentiating
`tan ψ · Δ(ψ)`, with `Δ = √(1 - c sin²ψ)`, gives `m² tan²ψ/Δ + Δ`, so
`m² I₂ + E(φ) = tan φ · Δ(φ)`. Eliminating `I₂`:

  `F(φ) = (3J + (1 + m²)/m² · E(φ) - tan φ · Δ(φ) · (1/cos²φ + (1 + m²)/m²)) / 2`.

Everything on the right is P-constructible, so `F` is. At `c = 0` the formula collapses:
`J = T + T³/3`, `Δ = 1`, `E(φ) = φ`, and the right-hand side is `φ`, as it must be.

`tan φ` is what confines the construction to `|φ| < π/2`. Oddness of the integrand covers
negative `φ`, and the reflection `ψ ↦ π/2 + ψ` carries the rest of the line into range at
the cost of moving to the complementary parameter `-c/(1 - c)` — which is why the whole
development is indexed by a parameter allowed to be negative. -/

/-- The integrand of the elliptic integral of the first kind, `1/√(1 - c sin²θ)`. -/
noncomputable def ellipticFIntegrand (c θ : ℝ) : ℝ := (ellipticEIntegrand c θ)⁻¹

/-- The incomplete elliptic integral of the first kind,
`F(φ) = ∫₀^φ dθ/√(1 - c sin²θ)`, in terms of the parameter `c = k²`. -/
noncomputable def ellipticF (c φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ, ellipticFIntegrand c θ

-- Theorem: at `c = 0` the circle again, and `F(φ) = φ`.
theorem ellipticF_zero (φ : ℝ) : ellipticF 0 φ = φ := by
  simp [ellipticF, ellipticFIntegrand, ellipticEIntegrand]

theorem ellipticFIntegrand_pos {c : ℝ} (hc : c < 1) (θ : ℝ) : 0 < ellipticFIntegrand c θ :=
  inv_pos.mpr (ellipticEIntegrand_pos hc θ)

theorem continuous_ellipticFIntegrand {c : ℝ} (hc : c < 1) :
    Continuous (ellipticFIntegrand c) :=
  (continuous_ellipticEIntegrand c).inv₀ fun θ => (ellipticEIntegrand_pos hc θ).ne'

theorem intervalIntegrable_ellipticFIntegrand {c : ℝ} (hc : c < 1) (a b : ℝ) :
    IntervalIntegrable (ellipticFIntegrand c) MeasureTheory.volume a b :=
  (continuous_ellipticFIntegrand hc).intervalIntegrable a b

/-! #### The Bézier cubic and its quartic -/

/-- The quartic `(1 + t²)(1 + m² t²)`, written as the sum of two squares that a cubic
Bézier can realise as its speed. -/
def firstKindQuartic (m t : ℝ) : ℝ := (1 - m * t ^ 2) ^ 2 + ((1 + m) * t) ^ 2

-- Theorem: Brahmagupta–Fibonacci — the two squares really do multiply out to the quartic.
theorem firstKindQuartic_eq (m t : ℝ) :
    firstKindQuartic m t = m ^ 2 * t ^ 4 + (1 + m ^ 2) * t ^ 2 + 1 := by
  unfold firstKindQuartic
  ring

theorem firstKindQuartic_pos (m t : ℝ) : 0 < firstKindQuartic m t := by
  rw [show firstKindQuartic m t = (1 + t ^ 2) * (1 + m ^ 2 * t ^ 2) from by
    rw [firstKindQuartic_eq]; ring]
  positivity

theorem sqrt_firstKindQuartic_pos (m t : ℝ) : 0 < Real.sqrt (firstKindQuartic m t) :=
  Real.sqrt_pos.mpr (firstKindQuartic_pos m t)

theorem sq_sqrt_firstKindQuartic (m t : ℝ) :
    Real.sqrt (firstKindQuartic m t) ^ 2 = firstKindQuartic m t :=
  Real.sq_sqrt (firstKindQuartic_pos m t).le

theorem continuous_sqrt_firstKindQuartic (m : ℝ) :
    Continuous fun t => Real.sqrt (firstKindQuartic m t) := by
  unfold firstKindQuartic
  fun_prop

-- Theorem: at `t = tan ψ` the quartic is `Δ(ψ)² / cos⁴ψ`, so its square root is
-- `Δ(ψ) / cos²ψ`. This is the bridge between the Bézier and the angle.
theorem sqrt_firstKindQuartic_tan {c m ψ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hcos : Real.cos ψ ≠ 0) :
    Real.sqrt (firstKindQuartic m (Real.tan ψ))
      = ellipticEIntegrand c ψ / Real.cos ψ ^ 2 := by
  have hE := ellipticEIntegrand_pos hc ψ
  rw [show firstKindQuartic m (Real.tan ψ)
      = (ellipticEIntegrand c ψ / Real.cos ψ ^ 2) ^ 2 from ?_]
  · exact Real.sqrt_sq (by positivity)
  · rw [div_pow, ellipticEIntegrand_sq hc, firstKindQuartic_eq, Real.tan_eq_sin_div_cos]
    field_simp
    linear_combination (1 + m ^ 2 * Real.sin ψ ^ 2 + Real.cos ψ ^ 2) *
        Real.sin_sq_add_cos_sq ψ + Real.sin ψ ^ 2 * hm

/-- The cubic `t ↦ (t - m t³/3, (1+m) t²/2)`, whose coordinate derivatives `1 - m t²` and
`(1+m) t` are the two quadratics of `firstKindQuartic`. -/
noncomputable def firstKindCurve (m t : ℝ) : ℝ × ℝ := (t - m * t ^ 3 / 3, (1 + m) * t ^ 2 / 2)

-- Theorem: `s ↦ firstKindCurve m (T s)` is a cubic Bézier with these control points.
theorem bezierParam_firstKind (m T s : ℝ) :
    bezierParam (0, 0) (T / 3, 0) (2 * T / 3, (1 + m) * T ^ 2 / 6)
        (T - m * T ^ 3 / 3, (1 + m) * T ^ 2 / 2) s
      = firstKindCurve m (T * s) := by
  simp only [bezierParam, firstKindCurve, Prod.mk.injEq]
  constructor <;> ring

-- Theorem: that Bézier is a constructible curve.
theorem firstKindBezier_PConstructibleCurve {m T : ℝ} (hm : PConstructible m)
    (hT : PConstructible T) :
    PConstructibleCurve (bezierParam (0, 0) (T / 3, 0) (2 * T / 3, (1 + m) * T ^ 2 / 6)
      (T - m * T ^ 3 / 3, (1 + m) * T ^ 2 / 2) '' Set.Icc 0 1) := by
  have h3 : PConstructible (3 : ℝ) := three_Pconstructible
  have h6 : PConstructible (6 : ℝ) := by
    convert PConstructible.mul two_Pconstructible h3 using 1
    norm_num
  have hT2 : PConstructible (T ^ 2) := sq_Pconstructible hT
  have hT3 : PConstructible (T ^ 3) := by
    convert PConstructible.mul hT2 hT using 1
    ring
  have h1m : PConstructible (1 + m) := PConstructible.add PConstructible.base_one hm
  exact PConstructibleCurve.cubic_bezier _ _ _ _
    zero_Pconstructible zero_Pconstructible (PConstructible.div hT h3) zero_Pconstructible
    (PConstructible.div (PConstructible.mul two_Pconstructible hT) h3)
    (PConstructible.div (PConstructible.mul h1m hT2) h6)
    (PConstructible.sub hT (PConstructible.div (PConstructible.mul hm hT3) h3))
    (PConstructible.div (PConstructible.mul h1m hT2) two_Pconstructible)

/-- The same cubic, parametrized by the angle `ψ` through `t = tan ψ`. Its speed is
`Δ(ψ)/cos⁴ψ`, which is what makes its arc length an integral in `ψ`. -/
noncomputable def firstKindTanParam (m : ℝ) : ℝ → ℝ × ℝ :=
  fun ψ => firstKindCurve m (Real.tan ψ)

theorem hasDerivAt_firstKindTanParam_fst {m ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (firstKindTanParam m s).1)
      ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ψ := by
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have h : HasDerivAt (fun s : ℝ => Real.tan s - m * Real.tan s ^ 3 / 3)
      ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ψ :=
    (ht.sub (((ht.pow 3).const_mul m).div_const 3)).congr_deriv (by push_cast; ring)
  exact h

theorem hasDerivAt_firstKindTanParam_snd {m ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => (firstKindTanParam m s).2)
      ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ψ := by
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have h : HasDerivAt (fun s : ℝ => (1 + m) * Real.tan s ^ 2 / 2)
      ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ψ :=
    (((ht.pow 2).const_mul (1 + m)).div_const 2).congr_deriv (by push_cast; ring)
  exact h

-- Theorem: the cubic, read in the angle `ψ`, moves at speed `Δ(ψ)/cos⁴ψ`.
theorem speed_firstKindTanParam {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {ψ : ℝ}
    (hcos : Real.cos ψ ≠ 0) :
    speed (firstKindTanParam m) ψ = ellipticEIntegrand c ψ / Real.cos ψ ^ 4 := by
  have hE := ellipticEIntegrand_pos hc ψ
  rw [speed, (hasDerivAt_firstKindTanParam_fst (m := m) hcos).deriv,
    (hasDerivAt_firstKindTanParam_snd (m := m) hcos).deriv]
  rw [show ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ^ 2
        + ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ^ 2
      = (ellipticEIntegrand c ψ / Real.cos ψ ^ 4) ^ 2 from ?_]
  · exact Real.sqrt_sq (by positivity)
  · have h2 : firstKindQuartic m (Real.tan ψ)
        = (ellipticEIntegrand c ψ / Real.cos ψ ^ 2) ^ 2 := by
      rw [← sqrt_firstKindQuartic_tan hm hc hcos, sq_sqrt_firstKindQuartic]
    have hexp : ((1 - m * Real.tan ψ ^ 2) * (1 / Real.cos ψ ^ 2)) ^ 2
        + ((1 + m) * Real.tan ψ * (1 / Real.cos ψ ^ 2)) ^ 2
        = firstKindQuartic m (Real.tan ψ) * (1 / Real.cos ψ ^ 2) ^ 2 := by
      unfold firstKindQuartic
      ring
    rw [hexp, h2]
    field_simp

/-! #### The change of variables `t = tan ψ` -/

-- Theorem: on the interval between `0` and any `φ` with `|φ| < π/2`, the cosine is
-- positive — so `tan` is smooth there and the substitution below is legitimate.
theorem cos_pos_of_mem_uIcc {φ ψ : ℝ} (hφ : |φ| < Real.pi / 2)
    (hψ : ψ ∈ Set.uIcc (0 : ℝ) φ) : 0 < Real.cos ψ := by
  have hpi := Real.pi_pos
  rw [abs_lt] at hφ
  refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩ <;>
    rcases Set.mem_uIcc.mp hψ with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> linarith

-- Theorem: `t = tan ψ` carries an integral over `[0, tan φ]` back to one over `[0, φ]`.
theorem integral_comp_tan {φ : ℝ} (hφ : |φ| < Real.pi / 2) {g : ℝ → ℝ} (hg : Continuous g) :
    (∫ ψ in (0 : ℝ)..φ, (1 / Real.cos ψ ^ 2) * g (Real.tan ψ))
      = ∫ t in (0 : ℝ)..Real.tan φ, g t := by
  have hd : ∀ ψ ∈ Set.uIcc (0 : ℝ) φ, HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ :=
    fun ψ hψ => Real.hasDerivAt_tan (cos_pos_of_mem_uIcc hφ hψ).ne'
  have hc' : ContinuousOn (fun ψ => 1 / Real.cos ψ ^ 2) (Set.uIcc (0 : ℝ) φ) := by
    refine ContinuousOn.div continuousOn_const (Continuous.continuousOn (by fun_prop))
      fun ψ hψ => pow_ne_zero 2 (cos_pos_of_mem_uIcc hφ hψ).ne'
  simpa [Real.tan_zero] using intervalIntegral.integral_deriv_smul_comp hd hc' hg

/-! #### The two integrations by parts -/

-- Theorem: differentiating `t √P` gives `3√P - ((1+m²)t² + 2)/√P`. This is the
-- integration by parts that converts the Bézier's arc length into first-kind integrals.
theorem hasDerivAt_mul_sqrt_firstKindQuartic (m t : ℝ) :
    HasDerivAt (fun s : ℝ => s * Real.sqrt (firstKindQuartic m s))
      (3 * Real.sqrt (firstKindQuartic m t)
        - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t)) t := by
  have hpos := sqrt_firstKindQuartic_pos m t
  have hsq := sq_sqrt_firstKindQuartic m t
  have hP : HasDerivAt (firstKindQuartic m) (4 * m ^ 2 * t ^ 3 + 2 * (1 + m ^ 2) * t) t := by
    rw [show firstKindQuartic m = fun s : ℝ => m ^ 2 * s ^ 4 + (1 + m ^ 2) * s ^ 2 + 1 from
      funext (firstKindQuartic_eq m)]
    exact ((((hasDerivAt_pow 4 t).const_mul (m ^ 2)).add
      ((hasDerivAt_pow 2 t).const_mul (1 + m ^ 2))).add_const 1).congr_deriv (by push_cast; ring)
  have hs := hP.sqrt (firstKindQuartic_pos m t).ne'
  have hsq' : Real.sqrt (firstKindQuartic m t) ^ 2
      = m ^ 2 * t ^ 4 + (1 + m ^ 2) * t ^ 2 + 1 := by
    rw [hsq, firstKindQuartic_eq]
  refine ((hasDerivAt_id t).mul hs).congr_deriv ?_
  simp only [id_eq]
  field_simp
  linear_combination (-4 : ℝ) * hsq'

-- Theorem: differentiating `tan ψ · Δ(ψ)` gives `m² tan²ψ/Δ + Δ`. This is the
-- integration by parts that brings in the second-kind integral.
theorem hasDerivAt_tan_mul_ellipticEIntegrand {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {ψ : ℝ} (hcos : Real.cos ψ ≠ 0) :
    HasDerivAt (fun s : ℝ => Real.tan s * ellipticEIntegrand c s)
      (m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ) ψ := by
  have hE := ellipticEIntegrand_pos hc ψ
  have hEsq := ellipticEIntegrand_sq hc ψ
  have ht : HasDerivAt Real.tan (1 / Real.cos ψ ^ 2) ψ := Real.hasDerivAt_tan hcos
  have hu : HasDerivAt (fun s : ℝ => 1 - c * Real.sin s ^ 2)
      (-(2 * c * Real.sin ψ * Real.cos ψ)) ψ :=
    ((((Real.hasDerivAt_sin ψ).pow 2).const_mul c).const_sub 1).congr_deriv
      (by push_cast; ring)
  have hD : HasDerivAt (ellipticEIntegrand c)
      (-(2 * c * Real.sin ψ * Real.cos ψ) / (2 * ellipticEIntegrand c ψ)) ψ :=
    hu.sqrt (one_sub_mul_sin_sq_pos hc ψ).ne'
  refine (ht.mul hD).congr_deriv ?_
  simp only [ellipticFIntegrand]
  rw [Real.tan_eq_sin_div_cos]
  field_simp
  linear_combination (2 - 2 * Real.cos ψ ^ 2 - Real.sin ψ ^ 2) * hEsq
    - Real.sin ψ ^ 2 * hm
    + (ellipticEIntegrand c ψ ^ 2 + c * Real.sin ψ ^ 2 - 2) * Real.sin_sq_add_cos_sq ψ


/-! #### The arc length of the Bézier -/

-- Theorem: read in the angle, the Bézier's arc length is `∫₀^{tan φ} √P`.
theorem arcLengthOf_firstKindTanParam {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {φ : ℝ}
    (hφ : |φ| < Real.pi / 2) :
    arcLengthOf (firstKindTanParam m) 0 φ
      = ∫ t in (0 : ℝ)..Real.tan φ, Real.sqrt (firstKindQuartic m t) := by
  rw [arcLengthOf, ← integral_comp_tan hφ (continuous_sqrt_firstKindQuartic m)]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  rw [speed_firstKindTanParam hm hc hcos.ne', sqrt_firstKindQuartic_tan hm hc hcos.ne']
  field_simp

-- Theorem: that arc length is P-constructible. This is the one place the geometry is
-- used; everything after it is calculus.
theorem arcLength_firstKind_Pconstructible {c m φ : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    (hmpos : 0 < m) (hmP : PConstructible m) (hφP : PConstructible φ)
    (h0 : 0 < φ) (hlt : φ < Real.pi / 2) :
    PConstructible (arcLengthOf (firstKindTanParam m) 0 φ) := by
  have hpi := Real.pi_pos
  have habs : |φ| < Real.pi / 2 := by rw [abs_lt]; constructor <;> linarith
  have hTpos : 0 < Real.tan φ := by
    have := Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two le_rfl hlt h0
    rwa [Real.tan_zero] at this
  have hTP : PConstructible (Real.tan φ) := tan_Pconstructible hφP
  have hmemI : ∀ ψ ∈ Set.Icc (0 : ℝ) φ, 0 < Real.cos ψ := fun ψ hψ =>
    cos_pos_of_mem_uIcc habs (by rwa [Set.uIcc_of_le h0.le])
  have htan_nonneg : ∀ ψ ∈ Set.Icc (0 : ℝ) φ, 0 ≤ Real.tan ψ := fun ψ hψ => by
    rw [Real.tan_eq_sin_div_cos]
    exact div_nonneg (Real.sin_nonneg_of_nonneg_of_le_pi hψ.1 (by linarith [hψ.2]))
      (hmemI ψ hψ).le
  refine PConstructible.arc_length (firstKindBezier_PConstructibleCurve hmP hTP)
    (firstKindTanParam m) h0.le ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- the arc lies on the Bézier: the parameter `tan ψ / tan φ` lands in `[0, 1]`
    rintro p ⟨ψ, hψ, rfl⟩
    have htanle : Real.tan ψ ≤ Real.tan φ := by
      rcases eq_or_lt_of_le hψ.2 with rfl | h
      · exact le_rfl
      · exact (Real.tan_lt_tan_of_nonneg_of_lt_pi_div_two hψ.1 hlt h).le
    refine ⟨Real.tan ψ / Real.tan φ,
      ⟨div_nonneg (htan_nonneg ψ hψ) hTpos.le, (div_le_one hTpos).mpr htanle⟩, ?_⟩
    rw [bezierParam_firstKind]
    simp only [firstKindTanParam]
    congr 1
    field_simp
  · -- injective: the second coordinate is increasing in `tan ψ`, and `tan` is injective
    intro ψ₁ h₁ ψ₂ h₂ heq
    have h1m : (1 : ℝ) + m ≠ 0 := by linarith
    have hsq : Real.tan ψ₁ ^ 2 = Real.tan ψ₂ ^ 2 := by
      have h : (1 + m) * Real.tan ψ₁ ^ 2 / 2 = (1 + m) * Real.tan ψ₂ ^ 2 / 2 :=
        congrArg Prod.snd heq
      have hz : (1 + m) * (Real.tan ψ₁ ^ 2 - Real.tan ψ₂ ^ 2) = 0 := by
        linear_combination 2 * h
      rcases mul_eq_zero.mp hz with h' | h'
      · exact absurd h' h1m
      · linarith
    have htan : Real.tan ψ₁ = Real.tan ψ₂ := by
      have hz : (Real.tan ψ₁ - Real.tan ψ₂) * (Real.tan ψ₁ + Real.tan ψ₂) = 0 := by
        linear_combination hsq
      have hn₁ := htan_nonneg ψ₁ h₁
      have hn₂ := htan_nonneg ψ₂ h₂
      rcases mul_eq_zero.mp hz with h | h
      · linarith
      · have e₁ : Real.tan ψ₁ = 0 := by linarith
        have e₂ : Real.tan ψ₂ = 0 := by linarith
        rw [e₁, e₂]
    exact Real.injOn_tan ⟨by linarith [h₁.1], by linarith [h₁.2]⟩
      ⟨by linarith [h₂.1], by linarith [h₂.2]⟩ htan
  · -- differentiable in each coordinate
    intro ψ hψ
    exact ⟨(hasDerivAt_firstKindTanParam_fst (hmemI ψ hψ).ne').differentiableAt,
      (hasDerivAt_firstKindTanParam_snd (hmemI ψ hψ).ne').differentiableAt⟩
  · -- the speed agrees on `[0, φ]` with a continuous function, hence is integrable
    refine ContinuousOn.intervalIntegrable (ContinuousOn.congr
      (f := fun ψ => ellipticEIntegrand c ψ / Real.cos ψ ^ 4) ?_ ?_)
    · exact ContinuousOn.div (continuous_ellipticEIntegrand c).continuousOn
        (Continuous.continuousOn (by fun_prop))
        fun ψ hψ => pow_ne_zero 4 (cos_pos_of_mem_uIcc habs hψ).ne'
    · exact fun ψ hψ => speed_firstKindTanParam hm hc (cos_pos_of_mem_uIcc habs hψ).ne'
  · simpa [firstKindTanParam, firstKindCurve] using zero_Pconstructible
  · simpa [firstKindTanParam, firstKindCurve] using zero_Pconstructible
  · have hT3 : PConstructible (Real.tan φ ^ 3) := by
      convert PConstructible.mul (sq_Pconstructible hTP) hTP using 1
      ring
    simpa [firstKindTanParam, firstKindCurve] using
      PConstructible.sub hTP (PConstructible.div (PConstructible.mul hmP hT3)
        three_Pconstructible)
  · simpa [firstKindTanParam, firstKindCurve] using
      PConstructible.div (PConstructible.mul
        (PConstructible.add PConstructible.base_one hmP) (sq_Pconstructible hTP))
        two_Pconstructible

/-! #### Eliminating the auxiliary integral

Two integrations by parts. The first, in `t`, converts the Bézier's arc length into the
two integrals `∫ dt/√P` and `∫ t² dt/√P`; the second, in `ψ`, identifies the latter with
the second-kind integral. Together they leave `F` alone on one side. -/

-- Theorem: `3J - T √P(T) = (1 + m²) I₂ + 2 I₀`, from differentiating `t √P`.
theorem firstKind_ibp_t (m T : ℝ) :
    3 * (∫ t in (0 : ℝ)..T, Real.sqrt (firstKindQuartic m t))
        - (1 + m ^ 2) * (∫ t in (0 : ℝ)..T, t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
        - 2 * ∫ t in (0 : ℝ)..T, (Real.sqrt (firstKindQuartic m t))⁻¹
      = T * Real.sqrt (firstKindQuartic m T) := by
  have hc1 : Continuous fun t => Real.sqrt (firstKindQuartic m t) :=
    continuous_sqrt_firstKindQuartic m
  have hc2 : Continuous fun t : ℝ => (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    hc1.inv₀ fun t => (sqrt_firstKindQuartic_pos m t).ne'
  have hc3 : Continuous fun t : ℝ => t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_pow 2).mul hc2
  have hcD : Continuous fun t : ℝ => 3 * Real.sqrt (firstKindQuartic m t)
      - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t) :=
    (hc1.const_mul 3).sub (Continuous.div (by fun_prop) hc1
      fun t => (sqrt_firstKindQuartic_pos m t).ne')
  have i1 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc1.intervalIntegrable 0 T
  have i2 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc2.intervalIntegrable 0 T
  have i3 : IntervalIntegrable _ MeasureTheory.volume 0 T := hc3.intervalIntegrable 0 T
  have iD : IntervalIntegrable _ MeasureTheory.volume 0 T := hcD.intervalIntegrable 0 T
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => s * Real.sqrt (firstKindQuartic m s))
    (fun t _ => hasDerivAt_mul_sqrt_firstKindQuartic m t) iD
  rw [zero_mul, sub_zero] at hkey
  have e1 : (∫ t in (0 : ℝ)..T, (3 * Real.sqrt (firstKindQuartic m t)
        - ((1 + m ^ 2) * t ^ 2 + 2) / Real.sqrt (firstKindQuartic m t)))
      = ∫ t in (0 : ℝ)..T, (3 * Real.sqrt (firstKindQuartic m t)
          - ((1 + m ^ 2) * (t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
            + 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)) := by
    refine intervalIntegral.integral_congr fun t _ => ?_
    have := (sqrt_firstKindQuartic_pos m t).ne'
    field_simp
  rw [e1, intervalIntegral.integral_sub (i1.const_mul 3)
      ((i3.const_mul (1 + m ^ 2)).add (i2.const_mul 2)),
    intervalIntegral.integral_add (i3.const_mul (1 + m ^ 2)) (i2.const_mul 2),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const_mul] at hkey
  linarith [hkey]

-- Theorem: `m² I₂ + E(φ) = tan φ · Δ(φ)`, from differentiating `tan ψ · Δ(ψ)`.
theorem firstKind_ibp_angle {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1) {φ : ℝ}
    (hφ : |φ| < Real.pi / 2) :
    m ^ 2 * (∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ) + ellipticE c φ
      = Real.tan φ * ellipticEIntegrand c φ := by
  have htanC : ContinuousOn (fun ψ : ℝ => Real.tan ψ ^ 2) (Set.uIcc (0 : ℝ) φ) :=
    ContinuousOn.pow (fun ψ hψ =>
      (Real.continuousAt_tan.mpr (cos_pos_of_mem_uIcc hφ hψ).ne').continuousWithinAt) 2
  have i1 : IntervalIntegrable (fun ψ => Real.tan ψ ^ 2 * ellipticFIntegrand c ψ)
      MeasureTheory.volume 0 φ :=
    ContinuousOn.intervalIntegrable
      (htanC.mul (continuous_ellipticFIntegrand hc).continuousOn)
  have hcont : ContinuousOn
      (fun ψ => m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ)
      (Set.uIcc (0 : ℝ) φ) :=
    ((continuousOn_const.mul htanC).mul
      (continuous_ellipticFIntegrand hc).continuousOn).add
      (continuous_ellipticEIntegrand c).continuousOn
  have hkey := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun s : ℝ => Real.tan s * ellipticEIntegrand c s)
    (fun ψ hψ => hasDerivAt_tan_mul_ellipticEIntegrand hm hc
      (cos_pos_of_mem_uIcc hφ hψ).ne') hcont.intervalIntegrable
  rw [Real.tan_zero, zero_mul, sub_zero] at hkey
  have e1 : (∫ ψ in (0 : ℝ)..φ,
        (m ^ 2 * Real.tan ψ ^ 2 * ellipticFIntegrand c ψ + ellipticEIntegrand c ψ))
      = ∫ ψ in (0 : ℝ)..φ,
        (m ^ 2 * (Real.tan ψ ^ 2 * ellipticFIntegrand c ψ) + ellipticEIntegrand c ψ) := by
    refine intervalIntegral.integral_congr fun ψ _ => ?_
    ring
  rw [e1, intervalIntegral.integral_add (i1.const_mul (m ^ 2))
      (intervalIntegrable_ellipticEIntegrand c 0 φ),
    intervalIntegral.integral_const_mul] at hkey
  rw [ellipticE]
  linarith [hkey]

-- Theorem: the auxiliary integral in `t` is the auxiliary integral in `ψ`.
theorem integral_sq_div_sqrt_firstKindQuartic {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {φ : ℝ} (hφ : |φ| < Real.pi / 2) :
    (∫ t in (0 : ℝ)..Real.tan φ, t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹)
      = ∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ := by
  have hg : Continuous fun t : ℝ => t ^ 2 * (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_pow 2).mul ((continuous_sqrt_firstKindQuartic m).inv₀
      fun t => (sqrt_firstKindQuartic_pos m t).ne')
  rw [← integral_comp_tan hφ hg]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  have hE := ellipticEIntegrand_pos hc ψ
  rw [sqrt_firstKindQuartic_tan hm hc hcos.ne', ellipticFIntegrand]
  field_simp

-- Theorem: the first-kind integral in `ψ` is the reciprocal-quartic integral in `t`.
theorem integral_inv_sqrt_firstKindQuartic {c m : ℝ} (hm : m ^ 2 = 1 - c) (hc : c < 1)
    {φ : ℝ} (hφ : |φ| < Real.pi / 2) :
    (∫ t in (0 : ℝ)..Real.tan φ, (Real.sqrt (firstKindQuartic m t))⁻¹) = ellipticF c φ := by
  have hg : Continuous fun t : ℝ => (Real.sqrt (firstKindQuartic m t))⁻¹ :=
    (continuous_sqrt_firstKindQuartic m).inv₀ fun t => (sqrt_firstKindQuartic_pos m t).ne'
  rw [← integral_comp_tan hφ hg, ellipticF]
  refine intervalIntegral.integral_congr fun ψ hψ => ?_
  have hcos := cos_pos_of_mem_uIcc hφ hψ
  have hE := ellipticEIntegrand_pos hc ψ
  rw [sqrt_firstKindQuartic_tan hm hc hcos.ne', ellipticFIntegrand]
  field_simp

/-! #### The construction -/

-- Theorem: `F(φ)` is P-constructible for `0 < φ < π/2`.
--
-- This is the construction itself. `J` is the Bézier's arc length, the only geometric
-- input; the two integrations by parts and a division by `m²` do the rest.
theorem ellipticF_Pconstructible_of_pos {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (h0 : 0 < φ) (hlt : φ < Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  have hpi := Real.pi_pos
  have habs : |φ| < Real.pi / 2 := by rw [abs_lt]; constructor <;> linarith
  obtain ⟨m, hmpos, hm, hmP⟩ : ∃ m : ℝ, 0 < m ∧ m ^ 2 = 1 - c ∧ PConstructible m :=
    ⟨Real.sqrt (1 - c), Real.sqrt_pos.mpr (by linarith), Real.sq_sqrt (by linarith),
      sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)⟩
  have hm0 : m ^ 2 ≠ 0 := by positivity
  have hTP : PConstructible (Real.tan φ) := tan_Pconstructible hφP
  -- the geometric input
  have hJ := arcLength_firstKind_Pconstructible hm hc hmpos hmP hφP h0 hlt
  rw [arcLengthOf_firstKindTanParam hm hc habs] at hJ
  -- the two integrations by parts, transported to the angle
  have ha := firstKind_ibp_t m (Real.tan φ)
  rw [integral_inv_sqrt_firstKindQuartic hm hc habs,
    integral_sq_div_sqrt_firstKindQuartic hm hc habs] at ha
  have hb := firstKind_ibp_angle hm hc habs
  -- solve for `F`
  have hkey : ellipticF c φ
      = (3 * (∫ t in (0 : ℝ)..Real.tan φ, Real.sqrt (firstKindQuartic m t))
          - (1 + m ^ 2) * ((Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / m ^ 2)
          - Real.tan φ * Real.sqrt (firstKindQuartic m (Real.tan φ))) / 2 := by
    have hI2 : (∫ ψ in (0 : ℝ)..φ, Real.tan ψ ^ 2 * ellipticFIntegrand c ψ)
        = (Real.tan φ * ellipticEIntegrand c φ - ellipticE c φ) / m ^ 2 := by
      field_simp
      linarith [hb]
    rw [hI2] at ha
    linarith [ha]
  rw [hkey]
  -- and every piece of that is P-constructible
  have hEint : PConstructible (ellipticEIntegrand c φ) := by
    unfold ellipticEIntegrand
    exact sqrt_Pconstructible (PConstructible.sub PConstructible.base_one
      (PConstructible.mul hcP (sq_Pconstructible (sin_Pconstructible hφP))))
  have hQ : PConstructible (Real.sqrt (firstKindQuartic m (Real.tan φ))) := by
    refine sqrt_Pconstructible ?_
    unfold firstKindQuartic
    exact PConstructible.add
      (sq_Pconstructible (PConstructible.sub PConstructible.base_one
        (PConstructible.mul hmP (sq_Pconstructible hTP))))
      (sq_Pconstructible (PConstructible.mul
        (PConstructible.add PConstructible.base_one hmP) hTP))
  have hE := ellipticE_Pconstructible hcP hφP hc
  exact PConstructible.div
    (PConstructible.sub
      (PConstructible.sub (PConstructible.mul three_Pconstructible hJ)
        (PConstructible.mul (PConstructible.add PConstructible.base_one (sq_Pconstructible hmP))
          (PConstructible.div (PConstructible.sub (PConstructible.mul hTP hEint) hE)
            (sq_Pconstructible hmP))))
      (PConstructible.mul hTP hQ))
    two_Pconstructible

-- Theorem: `F` is odd, since its integrand is even.
theorem ellipticF_neg (c φ : ℝ) : ellipticF c (-φ) = -ellipticF c φ := by
  have heven : ∀ x : ℝ, ellipticFIntegrand c (-x) = ellipticFIntegrand c x := fun x => by
    simp [ellipticFIntegrand, ellipticEIntegrand]
  have h := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := -φ)
    (ellipticFIntegrand c)
  simp only [heven, neg_neg, neg_zero] at h
  rw [ellipticF, h, intervalIntegral.integral_symm, ellipticF]

-- Theorem: `F(φ)` is P-constructible for every `|φ| < π/2`.
theorem ellipticF_Pconstructible_of_abs_lt {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| < Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  rcases lt_trichotomy φ 0 with hneg | rfl | hpos
  · have h := ellipticF_Pconstructible_of_pos hcP (neg_Pconstructible hφP) hc
      (by linarith) (by rw [abs_lt] at hφ; linarith [hφ.1])
    rw [← neg_neg φ, ellipticF_neg]
    exact neg_Pconstructible h
  · simpa [ellipticF] using zero_Pconstructible
  · exact ellipticF_Pconstructible_of_pos hcP hφP hc hpos (by rw [abs_lt] at hφ; exact hφ.2)


/-! #### Past the quarter turn

`tan φ` runs out at `φ = π/2`, so the construction above stops there. Two symmetries carry
it over the whole line. The integrand has period `π`, exactly as in the second-kind case;
and reflecting in `π/2` sends

  `1 - c sin²(π/2 + w) = 1 - c cos²w = (1 - c)(1 - c' sin²w)`,  `c' = -c/(1 - c)`,

so a quarter turn past `π/2` is a quarter turn from `0` at the *complementary* parameter
`c'`, scaled by `1/√(1 - c)`. Since `c > 0` makes `c' < 0`, this is what forces the whole
development to be indexed by a parameter rather than a modulus `k`: there is no real `k`
with `k² = c'`. Note `c' < 1` whenever `c < 1`, so the complementary parameter stays
inside the hypothesis. -/

-- Theorem: the complementary parameter is again admissible.
theorem compl_param_lt_one {c : ℝ} (hc : c < 1) : -c / (1 - c) < 1 :=
  (div_lt_one (by linarith)).mpr (by linarith)

-- Theorem: reflecting the integrand in `π/2` moves to the complementary parameter.
theorem ellipticFIntegrand_pi_div_two_add {c : ℝ} (hc : c < 1) (w : ℝ) :
    ellipticFIntegrand c (Real.pi / 2 + w)
      = (Real.sqrt (1 - c))⁻¹ * ellipticFIntegrand (-c / (1 - c)) w := by
  have h1c : (0 : ℝ) < 1 - c := by linarith
  have hsin : Real.sin (Real.pi / 2 + w) = Real.cos w := by
    rw [show Real.pi / 2 + w = Real.pi / 2 - -w by ring, Real.sin_pi_div_two_sub, Real.cos_neg]
  simp only [ellipticFIntegrand, ellipticEIntegrand, hsin]
  rw [← mul_inv, ← Real.sqrt_mul h1c.le]
  congr 2
  field_simp
  linear_combination (-c) * Real.sin_sq_add_cos_sq w

-- Theorem: hence `F` past `π/2` is `F` at the complementary parameter.
theorem ellipticF_pi_div_two_add {c : ℝ} (hc : c < 1) (u : ℝ) :
    ellipticF c (Real.pi / 2 + u)
      = ellipticF c (Real.pi / 2) + (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) u := by
  have hshift : (∫ ψ in (Real.pi / 2)..(Real.pi / 2 + u), ellipticFIntegrand c ψ)
      = (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) u := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := u)
      (ellipticFIntegrand c) (Real.pi / 2)
    rw [add_zero] at h
    rw [← h, ellipticF, ← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun w _ => ellipticFIntegrand_pi_div_two_add hc w
  rw [← hshift, ellipticF, ellipticF,
    intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_ellipticFIntegrand hc 0 (Real.pi / 2))
      (intervalIntegrable_ellipticFIntegrand hc (Real.pi / 2) (Real.pi / 2 + u))]

-- Theorem: the complete integral `F(π/2) = K` is P-constructible, as two quarter turns:
-- one at `c` and one at the complementary parameter.
theorem ellipticF_pi_div_two_Pconstructible {c : ℝ} (hcP : PConstructible c) (hc : c < 1) :
    PConstructible (ellipticF c (Real.pi / 2)) := by
  have hpi := Real.pi_pos
  have hquarter : |Real.pi / 4| < Real.pi / 2 := by
    rw [abs_of_pos (by linarith)]; linarith
  have hpi4 : PConstructible (Real.pi / 4) := by
    have h4 : PConstructible (4 : ℝ) := by
      convert PConstructible.mul two_Pconstructible two_Pconstructible using 1
      norm_num
    exact PConstructible.div pi_Pconstructible h4
  have hc'P : PConstructible (-c / (1 - c)) :=
    PConstructible.div (neg_Pconstructible hcP)
      (PConstructible.sub PConstructible.base_one hcP)
  have h := ellipticF_pi_div_two_add hc (-(Real.pi / 4))
  rw [show Real.pi / 2 + -(Real.pi / 4) = Real.pi / 4 by ring, ellipticF_neg] at h
  have hkey : ellipticF c (Real.pi / 2)
      = ellipticF c (Real.pi / 4)
        + (Real.sqrt (1 - c))⁻¹ * ellipticF (-c / (1 - c)) (Real.pi / 4) := by
    linear_combination -h
  rw [hkey]
  exact PConstructible.add
    (ellipticF_Pconstructible_of_abs_lt hcP hpi4 hc hquarter)
    (PConstructible.mul
      (inv_Pconstructible
        (sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)))
      (ellipticF_Pconstructible_of_abs_lt hc'P hpi4 (compl_param_lt_one hc) hquarter))

-- Theorem: `F(φ)` is P-constructible for `|φ| ≤ π/2`, the quarter turn now included.
theorem ellipticF_Pconstructible_of_abs_le {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (hφ : |φ| ≤ Real.pi / 2) :
    PConstructible (ellipticF c φ) := by
  have hpi := Real.pi_pos
  rcases eq_or_lt_of_le hφ with h | h
  · rcases (abs_eq (by positivity)).mp h with rfl | rfl
    · exact ellipticF_pi_div_two_Pconstructible hcP hc
    · rw [ellipticF_neg]
      exact neg_Pconstructible (ellipticF_pi_div_two_Pconstructible hcP hc)
  · exact ellipticF_Pconstructible_of_abs_lt hcP hφP hc h

-- Theorem: `F(φ)` is P-constructible for `0 ≤ φ ≤ π`, one full period.
theorem ellipticF_Pconstructible_of_mem_Icc {c φ : ℝ} (hcP : PConstructible c)
    (hφP : PConstructible φ) (hc : c < 1) (h0 : 0 ≤ φ) (hpi : φ ≤ Real.pi) :
    PConstructible (ellipticF c φ) := by
  have hpipos := Real.pi_pos
  have hc'P : PConstructible (-c / (1 - c)) :=
    PConstructible.div (neg_Pconstructible hcP)
      (PConstructible.sub PConstructible.base_one hcP)
  have huP : PConstructible (φ - Real.pi / 2) :=
    PConstructible.sub hφP (PConstructible.div pi_Pconstructible two_Pconstructible)
  have hu : |φ - Real.pi / 2| ≤ Real.pi / 2 := by
    rw [abs_le]; constructor <;> linarith
  rw [show φ = Real.pi / 2 + (φ - Real.pi / 2) by ring, ellipticF_pi_div_two_add hc]
  exact PConstructible.add (ellipticF_pi_div_two_Pconstructible hcP hc)
    (PConstructible.mul
      (inv_Pconstructible
        (sqrt_Pconstructible (PConstructible.sub PConstructible.base_one hcP)))
      (ellipticF_Pconstructible_of_abs_le hc'P huP (compl_param_lt_one hc) hu))

-- Theorem: the first-kind integrand has period `π`, being the reciprocal of the
-- second-kind one.
theorem periodic_ellipticFIntegrand (c : ℝ) :
    Function.Periodic (ellipticFIntegrand c) Real.pi := fun θ => by
  simp [ellipticFIntegrand, ellipticEIntegrand, Real.sin_add_pi]

-- Theorem: `F(φ + nπ) = F(φ) + n · F(π)`, exactly as for `E`.
theorem ellipticF_add_int_mul_pi {c : ℝ} (hc : c < 1) (φ : ℝ) (n : ℤ) :
    ellipticF c (φ + n * Real.pi) = ellipticF c φ + n * ellipticF c Real.pi := by
  have hper := periodic_ellipticFIntegrand c
  have hint : ∀ t₁ t₂ : ℝ,
      IntervalIntegrable (ellipticFIntegrand c) MeasureTheory.volume t₁ t₂ :=
    fun t₁ t₂ => intervalIntegrable_ellipticFIntegrand hc t₁ t₂
  have hA : (∫ θ in (0 : ℝ)..(n : ℝ) * Real.pi, ellipticFIntegrand c θ)
      = n * ellipticF c Real.pi := by
    have h := hper.intervalIntegral_add_zsmul_eq n 0 hint
    simpa [ellipticF, zsmul_eq_mul] using h
  have hB : (∫ θ in ((n : ℝ) * Real.pi)..(φ + (n : ℝ) * Real.pi), ellipticFIntegrand c θ)
      = ellipticF c φ := by
    have h := intervalIntegral.integral_comp_add_right (a := (0 : ℝ)) (b := φ)
      (ellipticFIntegrand c) ((n : ℝ) * Real.pi)
    have hshift : ∀ x : ℝ,
        ellipticFIntegrand c (x + (n : ℝ) * Real.pi) = ellipticFIntegrand c x :=
      fun x => hper.int_mul n x
    simp only [hshift, zero_add] at h
    rw [ellipticF, h]
  rw [ellipticF, ← intervalIntegral.integral_add_adjacent_intervals
    (b := (n : ℝ) * Real.pi) (hint 0 _) (hint _ _), hA, hB]
  ring

-- Theorem: `F(φ)` is P-constructible for every P-constructible `φ` and every
-- P-constructible parameter `c < 1`.
--
-- Reduction modulo `π` on top of the reflection above, so no restriction on `φ` at all —
-- matching `ellipticE_Pconstructible`.
theorem ellipticF_Pconstructible {c φ : ℝ} (hcP : PConstructible c) (hφP : PConstructible φ)
    (hc : c < 1) : PConstructible (ellipticF c φ) := by
  obtain ⟨n, h0, hpi⟩ := exists_int_half_turns φ
  have hrP : PConstructible (φ - n * Real.pi) :=
    PConstructible.sub hφP (PConstructible.mul (int_Pconstructible n) pi_Pconstructible)
  have hr := ellipticF_Pconstructible_of_mem_Icc hcP hrP hc h0 hpi
  have hFpi := ellipticF_Pconstructible_of_mem_Icc hcP pi_Pconstructible hc
    Real.pi_pos.le le_rfl
  have hkey : ellipticF c φ
      = ellipticF c (φ - n * Real.pi) + n * ellipticF c Real.pi := by
    have h := ellipticF_add_int_mul_pi hc (φ - n * Real.pi) n
    rwa [sub_add_cancel] at h
  rw [hkey]
  exact PConstructible.add hr (PConstructible.mul (int_Pconstructible n) hFpi)

/-! #### In terms of the modulus

Legendre writes both integrals with the modulus `k`, where `c = k²`. Those are the
statements one would quote; they are the case `c = k²` of the theorems above, and the
hypothesis `k² < 1` is the usual `|k| < 1`. -/

-- Theorem: `E(φ, k) = ∫₀^φ √(1 - k² sin²θ) dθ` is P-constructible.
theorem ellipticE_sq_Pconstructible {k φ : ℝ} (hk : PConstructible k)
    (hφ : PConstructible φ) (hk1 : k ^ 2 < 1) : PConstructible (ellipticE (k ^ 2) φ) :=
  ellipticE_Pconstructible (sq_Pconstructible hk) hφ hk1

-- Theorem: `F(φ, k) = ∫₀^φ dθ/√(1 - k² sin²θ)` is P-constructible.
theorem ellipticF_sq_Pconstructible {k φ : ℝ} (hk : PConstructible k)
    (hφ : PConstructible φ) (hk1 : k ^ 2 < 1) : PConstructible (ellipticF (k ^ 2) φ) :=
  ellipticF_Pconstructible (sq_Pconstructible hk) hφ hk1

/-! ### The complete elliptic integral of the third kind

  `Π(n, c) = ∫₀^{π/2} dθ / ((1 - n sin²θ) √(1 - c sin²θ))`

is the one Legendre integral that is not an arc length and cannot be made into one. An arc
length is `∫ √(x'² + y'²)`; the third-kind integrand has a pole, at `sin θ = 1/√n`, whose
position moves with `n`, and no drawable family has that — Béziers and polynomial graphs
are traced at speed `√(quartic)`, ellipses at `√(1 - c sin²θ)`, and scaling, rotating and
cropping only change which quadratic form of the velocity is taken. So `Π` has to be
carried back to `K` and `E`, which are already P-constructible, by an identity in the
*parameter* `n` rather than by a construction.

Write `Δ(θ) = √(1 - c sin²θ)` and

  `A(n) = ∫₀^{π/2} sin²θ dθ / ((1 - n sin²θ) Δ(θ))`,

so that `Π(n, c) = K + n A(n)`. The cubic `P(n) = n (c - n) (1 - n)` governs `A`: for every
`n < 1` and `θ` there is the elementary identity `hasDerivAt_thirdKindAnti`,

  `P'(n) sin²θ/((1-n s²)Δ) + 2P(n) sin⁴θ/((1-n s²)²Δ) - (1-n)/Δ + Δ`
      `= d/dθ [ n sin θ cos θ Δ(θ) / (1 - n sin²θ) ]`,

whose right-hand side vanishes at `θ = 0` and at `θ = π/2`. Integrating over the quarter
turn therefore leaves `P'(n) A(n) + 2 P(n) B(n) = (1 - n) K - E`, with `B` the same integral
with the denominator squared. The missing relation `B = A'` is obtained not by
differentiating under the integral sign but by moving the parameter: run `n` along a path
`ν(τ)` carrying `Q` with `Q² = ±P(ν)`, and Fubini on `[0, π/2] × [τ₀, τ₁]` gives

  `Q(τ₁) A(ν τ₁) - Q(τ₀) A(ν τ₀) = ∫_{τ₀}^{τ₁} ρ ((1 - ν) K - E)`.

That is `thirdKindPath_key`, the whole analytic content; the rest is a choice of path.
Nothing constrains `ν` beyond `Q' = ρ P'(ν)` and `Q ν' = 2 ρ P(ν)`, so paths are free.

`P` has roots `0`, `c`, `1` and `√(±P)` is real only between consecutive roots, so three
paths are needed, each starting at a root (where `Q = 0`, pinning `A`): `ν = c sin²β` on
`(0, c)`, `ν = (c + x²)/(1 + x²)` on `(c, 1)`, and `ν = -c x²` below `0`. The last two are
written in `x`, not in the angle they are read in, because `ν` must stay below `1` on all of
`ℝ` and the angular form `1 - (1-c) sin²φ` hits `1` at `φ = 0`.

The roots themselves are reached by no path and are done separately: `n = 0` gives `Π = K`
by inspection, and at `n = c` the cubic vanishes, so the displayed relation has only `A` in
it and gives `Π = E / (1 - c)`.

The standing hypothesis is `0 < c < 1`. The lower bound is what makes the complementary
parameter `1 - c` itself less than `1`, as the first- and second-kind theorems require;
`c = 0` is the circle, where `Π(n, 0) = π / (2 √(1 - n))` is elementary. -/

/-- The cubic `P(n) = n (c - n) (1 - n)`. -/
def thirdKindCubic (c n : ℝ) : ℝ := n * (c - n) * (1 - n)

/-- Its derivative in `n`. -/
def thirdKindCubicDeriv (c n : ℝ) : ℝ := c - 2 * (c + 1) * n + 3 * n ^ 2

/-- The integrand of the elliptic integral of the third kind. -/
noncomputable def ellipticPiIntegrand (c n θ : ℝ) : ℝ :=
  1 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)

/-- The complete elliptic integral of the third kind. -/
noncomputable def ellipticPi (c n : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..(Real.pi / 2), ellipticPiIntegrand c n θ

/-- The auxiliary integral `A(n, φ) = ∫₀^φ sin²θ / ((1 - n sin²θ) Δ(θ)) dθ`. -/
noncomputable def ellipticPiAux (c n φ : ℝ) : ℝ :=
  ∫ θ in (0 : ℝ)..φ,
    Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)

/-- The integrand that the master identity integrates. -/
noncomputable def thirdKindMaster (c n θ : ℝ) : ℝ :=
  thirdKindCubicDeriv c n * Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)
    + 2 * thirdKindCubic c n * Real.sin θ ^ 4
        / ((1 - n * Real.sin θ ^ 2) ^ 2 * ellipticEIntegrand c θ)

/-- The elementary antiderivative in `θ` of the master identity. -/
noncomputable def thirdKindAnti (c n θ : ℝ) : ℝ :=
  n * Real.sin θ * Real.cos θ * ellipticEIntegrand c θ / (1 - n * Real.sin θ ^ 2)

/-! #### The master identity

`thirdKindAnti_alg` is the comparison of derivatives with `sin θ`, `cos θ` and `Δ(θ)`
replaced by plain variables subject to `s² + w² = 1` and `E² = 1 - c s²`. -/

theorem hasDerivAt_ellipticEIntegrand (c θ : ℝ) (h : 1 - c * Real.sin θ ^ 2 ≠ 0) :
    HasDerivAt (ellipticEIntegrand c)
      (-(2 * c * Real.sin θ * Real.cos θ) / (2 * ellipticEIntegrand c θ)) θ :=
  (((((Real.hasDerivAt_sin θ).pow 2).const_mul c).const_sub 1).congr_deriv
    (by push_cast; ring)).sqrt h

theorem thirdKindAnti_alg {s w E c n : ℝ} (hw : s ^ 2 + w ^ 2 = 1) (hE : E ^ 2 = 1 - c * s ^ 2)
    (hEne : E ≠ 0) (hu : (1 : ℝ) - n * s ^ 2 ≠ 0) :
    (((n * w * w + n * s * -s) * E + n * s * w * (-(2 * c * s * w) / (2 * E))) * (1 - n * s ^ 2)
        - n * s * w * E * -(2 * n * s * w)) / (1 - n * s ^ 2) ^ 2
      = (c - 2 * (c + 1) * n + 3 * n ^ 2) * s ^ 2 / ((1 - n * s ^ 2) * E)
        + 2 * (n * (c - n) * (1 - n)) * s ^ 4 / ((1 - n * s ^ 2) ^ 2 * E)
        - (1 - n) / E + E := by
  field_simp
  linear_combination (n ^ 2 * s ^ 2 * w ^ 2 + n * s ^ 2 + n * w ^ 2 - 1) * hE
    - n * (2 * c * s ^ 2 - n * s ^ 2 - 1) * hw

-- Theorem: the master identity. `thirdKindMaster` differs from an explicit elementary derivative
-- by the two Legendre integrands, so integrating it over a full quarter turn reduces to
-- `K` and `E`.
theorem hasDerivAt_thirdKindAnti {c n : ℝ} (hc : c < 1)
    {θ : ℝ} (hune : 1 - n * Real.sin θ ^ 2 ≠ 0) :
    HasDerivAt (thirdKindAnti c n)
      (thirdKindMaster c n θ - (1 - n) / ellipticEIntegrand c θ + ellipticEIntegrand c θ) θ := by
  have hE := ellipticEIntegrand_pos hc θ
  have hEsq := ellipticEIntegrand_sq hc θ
  have hD := hasDerivAt_ellipticEIntegrand c θ (one_sub_mul_sin_sq_pos hc θ).ne'
  have hu : HasDerivAt (fun t : ℝ => 1 - n * Real.sin t ^ 2)
      (-(2 * n * Real.sin θ * Real.cos θ)) θ :=
    ((((Real.hasDerivAt_sin θ).pow 2).const_mul n).const_sub 1).congr_deriv (by push_cast; ring)
  have hnum : HasDerivAt
      (fun t : ℝ => n * Real.sin t * Real.cos t * ellipticEIntegrand c t)
      ((n * Real.cos θ * Real.cos θ + n * Real.sin θ * -Real.sin θ) * ellipticEIntegrand c θ
        + n * Real.sin θ * Real.cos θ
            * (-(2 * c * Real.sin θ * Real.cos θ) / (2 * ellipticEIntegrand c θ))) θ := by
    have h1 : HasDerivAt (fun t : ℝ => n * Real.sin t * Real.cos t)
        (n * Real.cos θ * Real.cos θ + n * Real.sin θ * -Real.sin θ) θ :=
      ((Real.hasDerivAt_sin θ).const_mul n).mul (Real.hasDerivAt_cos θ)
    have h2 : HasDerivAt (fun t : ℝ => ellipticEIntegrand c t)
        (-(2 * c * Real.sin θ * Real.cos θ) / (2 * ellipticEIntegrand c θ)) θ := hD
    exact h1.mul h2
  refine (hnum.div hu hune).congr_deriv ?_
  simp only [thirdKindMaster, thirdKindCubic, thirdKindCubicDeriv]
  exact thirdKindAnti_alg (Real.sin_sq_add_cos_sq θ) hEsq hE.ne' hune

theorem continuous_thirdKindMaster {c n : ℝ} (hc : c < 1) (hn : n < 1) :
    Continuous (thirdKindMaster c n) := by
  have hD : Continuous (ellipticEIntegrand c) := continuous_ellipticEIntegrand c
  have hu : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2 := by fun_prop
  have hune : ∀ θ : ℝ, (1 : ℝ) - n * Real.sin θ ^ 2 ≠ 0 :=
    fun θ => (one_sub_mul_sin_sq_pos hn θ).ne'
  have hDne : ∀ θ : ℝ, ellipticEIntegrand c θ ≠ 0 := fun θ => (ellipticEIntegrand_pos hc θ).ne'
  unfold thirdKindMaster
  refine Continuous.add ?_ ?_
  · exact (by fun_prop : Continuous fun θ : ℝ => thirdKindCubicDeriv c n * Real.sin θ ^ 2).div
      (hu.mul hD) fun θ => mul_ne_zero (hune θ) (hDne θ)
  · exact (by fun_prop : Continuous fun θ : ℝ => 2 * thirdKindCubic c n * Real.sin θ ^ 4).div
      ((hu.pow 2).mul hD) fun θ => mul_ne_zero (pow_ne_zero 2 (hune θ)) (hDne θ)

-- Theorem: the master integrand is continuous wherever `1 - n sin²θ` does not vanish.
theorem continuousOn_thirdKindMaster {c n : ℝ} (hc : c < 1) {s : Set ℝ}
    (hs : ∀ θ ∈ s, 1 - n * Real.sin θ ^ 2 ≠ 0) : ContinuousOn (thirdKindMaster c n) s := by
  have hD : Continuous (ellipticEIntegrand c) := continuous_ellipticEIntegrand c
  have hu : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2 := by fun_prop
  have hDne : ∀ θ : ℝ, ellipticEIntegrand c θ ≠ 0 := fun θ => (ellipticEIntegrand_pos hc θ).ne'
  unfold thirdKindMaster
  refine ContinuousOn.add ?_ ?_
  · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn (hu.mul hD)) fun θ hθ => mul_ne_zero (hs θ hθ) (hDne θ)
  · exact ContinuousOn.div (Continuous.continuousOn (by fun_prop))
      (Continuous.continuousOn ((hu.pow 2).mul hD))
      fun θ hθ => mul_ne_zero (pow_ne_zero 2 (hs θ hθ)) (hDne θ)

-- Theorem: the antiderivative vanishes at the quarter turn, since `cos (π/2) = 0`.
theorem thirdKindAnti_pi_div_two (c n : ℝ) : thirdKindAnti c n (Real.pi / 2) = 0 := by
  simp [thirdKindAnti]

-- Theorem: integrating the master identity over `[0, φ]` leaves `F` and `E` plus the
-- boundary value of the elementary antiderivative. Over a quarter turn that boundary term
-- vanishes, which is exactly what makes the *complete* integral reducible and the
-- incomplete one not.
theorem integral_thirdKindMaster {c n : ℝ} (hc : c < 1) (φ : ℝ)
    (hune : ∀ θ ∈ Set.uIcc (0 : ℝ) φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    (∫ θ in (0 : ℝ)..φ, thirdKindMaster c n θ)
      = (1 - n) * ellipticF c φ - ellipticE c φ + thirdKindAnti c n φ := by
  have hMc : IntervalIntegrable (thirdKindMaster c n) MeasureTheory.volume 0 φ :=
    (continuousOn_thirdKindMaster hc hune).intervalIntegrable
  have hFc := continuous_ellipticFIntegrand hc
  have hEc := continuous_ellipticEIntegrand c
  have hkey : (∫ θ in (0 : ℝ)..φ,
      (thirdKindMaster c n θ - (1 - n) * ellipticFIntegrand c θ + ellipticEIntegrand c θ))
      = thirdKindAnti c n φ - thirdKindAnti c n 0 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ hθ => ?_) ?_
    · have h := hasDerivAt_thirdKindAnti hc (hune θ hθ)
      simpa [ellipticFIntegrand, div_eq_mul_inv] using h
    · exact (hMc.sub ((hFc.const_mul _).intervalIntegrable _ _)).add
        (hEc.intervalIntegrable _ _)
  have hzero : thirdKindAnti c n 0 = 0 := by simp [thirdKindAnti]
  rw [hzero, sub_zero] at hkey
  rw [intervalIntegral.integral_add, intervalIntegral.integral_sub,
    intervalIntegral.integral_const_mul] at hkey
  · rw [← ellipticF, ← ellipticE] at hkey
    linarith
  · exact hMc
  · exact (hFc.const_mul _).intervalIntegrable _ _
  · exact hMc.sub ((hFc.const_mul _).intervalIntegrable _ _)
  · exact hEc.intervalIntegrable _ _

/-! #### Carrying `A` along a path of parameters

The τ-derivative of the weighted integrand is `ρ` times `thirdKindMaster`, which the master
identity integrates in `θ` to `ρ ((1 - ν) K - E)`; Fubini does the rest. `ν t < 1` is needed
only on `[τ₀, τ₁]`, which lets a path run up to the root `n = 1` without reaching it. -/

/-- The two-variable integrand carried along a path of parameters. -/
noncomputable def thirdKindPathIntegrand (c : ℝ) (ν Q : ℝ → ℝ) (θ τ : ℝ) : ℝ :=
  Q τ * Real.sin θ ^ 2 / ((1 - ν τ * Real.sin θ ^ 2) * ellipticEIntegrand c θ)

theorem hasDerivAt_thirdKindPathIntegrand {c : ℝ} (hc : c < 1) {ν Q ρ νd : ℝ → ℝ}
    (hν : ∀ t, HasDerivAt ν (νd t) t)
    (hQ : ∀ t, HasDerivAt Q (ρ t * thirdKindCubicDeriv c (ν t)) t)
    (hrel : ∀ t, Q t * νd t = 2 * ρ t * thirdKindCubic c (ν t))
    {τ : ℝ} (hτ : ν τ < 1) (θ : ℝ) :
    HasDerivAt (thirdKindPathIntegrand c ν Q θ) (ρ τ * thirdKindMaster c (ν τ) θ) τ := by
  have hDpos := ellipticEIntegrand_pos hc θ
  have hupos := one_sub_mul_sin_sq_pos hτ θ
  have hnum : HasDerivAt (fun σ : ℝ => Q σ * Real.sin θ ^ 2)
      (ρ τ * thirdKindCubicDeriv c (ν τ) * Real.sin θ ^ 2) τ := (hQ τ).mul_const _
  have hden : HasDerivAt
      (fun σ : ℝ => (1 - ν σ * Real.sin θ ^ 2) * ellipticEIntegrand c θ)
      (-(νd τ * Real.sin θ ^ 2) * ellipticEIntegrand c θ) τ :=
    (((hν τ).mul_const (Real.sin θ ^ 2)).const_sub 1).mul_const _
  refine (hnum.div hden (mul_ne_zero hupos.ne' hDpos.ne')).congr_deriv ?_
  simp only [thirdKindMaster, thirdKindCubic, thirdKindCubicDeriv]
  have h := hrel τ
  simp only [thirdKindCubic] at h
  field_simp
  ring_nf
  linear_combination Real.sin θ ^ 4 * h

theorem continuousAt_thirdKindMaster_prod {c : ℝ} (hc : c < 1) {θ m : ℝ} (hm : m < 1) :
    ContinuousAt (fun p : ℝ × ℝ => thirdKindMaster c p.2 p.1) (θ, m) := by
  have hD : Continuous fun p : ℝ × ℝ => ellipticEIntegrand c p.1 :=
    (continuous_ellipticEIntegrand c).comp continuous_fst
  have hu : Continuous fun p : ℝ × ℝ => 1 - p.2 * Real.sin p.1 ^ 2 := by fun_prop
  have hupos : (0 : ℝ) < 1 - m * Real.sin θ ^ 2 := one_sub_mul_sin_sq_pos hm θ
  have hDpos := ellipticEIntegrand_pos hc θ
  simp only [thirdKindMaster, thirdKindCubic, thirdKindCubicDeriv]
  refine ContinuousAt.add (ContinuousAt.div (by fun_prop) (hu.mul hD).continuousAt ?_)
    (ContinuousAt.div (by fun_prop) ((hu.pow 2).mul hD).continuousAt ?_)
  · exact mul_ne_zero hupos.ne' hDpos.ne'
  · exact mul_ne_zero (pow_ne_zero 2 hupos.ne') hDpos.ne'

theorem continuous_thirdKindPathIntegrand {c : ℝ} (hc : c < 1) {ν Q : ℝ → ℝ} {τ : ℝ}
    (hτ : ν τ < 1) : Continuous fun θ : ℝ => thirdKindPathIntegrand c ν Q θ τ := by
  simp only [thirdKindPathIntegrand]
  exact (by fun_prop : Continuous fun θ : ℝ => Q τ * Real.sin θ ^ 2).div
    ((by fun_prop : Continuous fun θ : ℝ => 1 - ν τ * Real.sin θ ^ 2).mul
      (continuous_ellipticEIntegrand c))
    fun θ => mul_ne_zero (one_sub_mul_sin_sq_pos hτ θ).ne' (ellipticEIntegrand_pos hc θ).ne'

theorem integral_thirdKindPathIntegrand {c : ℝ} {ν Q : ℝ → ℝ} (τ φ : ℝ) :
    (∫ θ in (0 : ℝ)..φ, thirdKindPathIntegrand c ν Q θ τ)
      = Q τ * ellipticPiAux c (ν τ) φ := by
  simp only [thirdKindPathIntegrand, ellipticPiAux, mul_div_assoc]
  exact intervalIntegral.integral_const_mul _ _

-- Theorem: the path lemma. Carrying the auxiliary integral `A` along any smooth path of
-- parameters `ν`, the combination `Q · A(ν)` has an elementary derivative: all the
-- `n`-dependence collapses into `K` and `E`.
theorem thirdKindPath_key {c : ℝ} (hc : c < 1) {ν Q ρ νd : ℝ → ℝ}
    (hνc : Continuous ν) (hρ : Continuous ρ)
    (hν : ∀ t, HasDerivAt ν (νd t) t)
    (hQ : ∀ t, HasDerivAt Q (ρ t * thirdKindCubicDeriv c (ν t)) t)
    (hrel : ∀ t, Q t * νd t = 2 * ρ t * thirdKindCubic c (ν t))
    {τ₀ τ₁ : ℝ} (hlt : ∀ t ∈ Set.uIcc τ₀ τ₁, ν t < 1) (φ : ℝ) :
    Q τ₁ * ellipticPiAux c (ν τ₁) φ - Q τ₀ * ellipticPiAux c (ν τ₀) φ
      = ∫ t in τ₀..τ₁,
          ρ t * ((1 - ν t) * ellipticF c φ - ellipticE c φ
            + thirdKindAnti c (ν t) φ) := by
  have hcontAt : ∀ θ : ℝ, ∀ t ∈ Set.uIcc τ₀ τ₁,
      ContinuousAt (fun s : ℝ => ρ s * thirdKindMaster c (ν s) θ) t := by
    intro θ t ht
    have h2 : ContinuousAt (fun s : ℝ => ((θ : ℝ), ν s)) t := by fun_prop
    have h3 := ContinuousAt.comp (f := fun s : ℝ => ((θ : ℝ), ν s))
      (continuousAt_thirdKindMaster_prod hc (hlt t ht)) h2
    exact hρ.continuousAt.mul h3
  have hstep : ∀ θ : ℝ, thirdKindPathIntegrand c ν Q θ τ₁ - thirdKindPathIntegrand c ν Q θ τ₀
      = ∫ t in τ₀..τ₁, ρ t * thirdKindMaster c (ν t) θ := fun θ =>
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hasDerivAt_thirdKindPathIntegrand hc hν hQ hrel (hlt t ht) θ)
      (ContinuousOn.intervalIntegrable fun t ht => (hcontAt θ t ht).continuousWithinAt) |>.symm
  have hswap : (∫ θ in (0 : ℝ)..φ, ∫ t in τ₀..τ₁, ρ t * thirdKindMaster c (ν t) θ)
      = ∫ t in τ₀..τ₁, ∫ θ in (0 : ℝ)..φ, ρ t * thirdKindMaster c (ν t) θ := by
    refine MeasureTheory.intervalIntegral_intervalIntegral_swap ?_
    have hcpt : IsCompact (Set.uIcc (0 : ℝ) φ ×ˢ Set.uIcc τ₀ τ₁) :=
      isCompact_uIcc.prod isCompact_uIcc
    refine MeasureTheory.IntegrableOn.mono_set ?_
      (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)
    refine ContinuousOn.integrableOn_compact hcpt ?_
    simp only [Function.uncurry_def]
    rintro ⟨θ, t⟩ ⟨-, ht⟩
    refine ContinuousAt.continuousWithinAt ?_
    have h2 : ContinuousAt (fun p : ℝ × ℝ => (p.1, ν p.2)) (θ, t) := by fun_prop
    have h3 := ContinuousAt.comp (f := fun p : ℝ × ℝ => (p.1, ν p.2))
      (continuousAt_thirdKindMaster_prod hc (hlt t ht)) h2
    have h4 : ContinuousAt (fun p : ℝ × ℝ => ρ p.2) (θ, t) := by fun_prop
    exact h4.mul h3
  have hlt0 : ν τ₀ < 1 := hlt τ₀ Set.left_mem_uIcc
  have hlt1 : ν τ₁ < 1 := hlt τ₁ Set.right_mem_uIcc
  have hL : (∫ θ in (0 : ℝ)..φ,
        (thirdKindPathIntegrand c ν Q θ τ₁ - thirdKindPathIntegrand c ν Q θ τ₀))
      = Q τ₁ * ellipticPiAux c (ν τ₁) φ - Q τ₀ * ellipticPiAux c (ν τ₀) φ := by
    rw [intervalIntegral.integral_sub
      ((continuous_thirdKindPathIntegrand hc hlt1).intervalIntegrable _ _)
      ((continuous_thirdKindPathIntegrand hc hlt0).intervalIntegrable _ _),
      integral_thirdKindPathIntegrand, integral_thirdKindPathIntegrand]
  have hmid : (∫ θ in (0 : ℝ)..φ,
        (thirdKindPathIntegrand c ν Q θ τ₁ - thirdKindPathIntegrand c ν Q θ τ₀))
      = ∫ θ in (0 : ℝ)..φ, ∫ t in τ₀..τ₁, ρ t * thirdKindMaster c (ν t) θ :=
    intervalIntegral.integral_congr fun θ _ => hstep θ
  have hR : (∫ t in τ₀..τ₁, ∫ θ in (0 : ℝ)..φ, ρ t * thirdKindMaster c (ν t) θ)
      = ∫ t in τ₀..τ₁,
          ρ t * ((1 - ν t) * ellipticF c φ - ellipticE c φ
            + thirdKindAnti c (ν t) φ) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [intervalIntegral.integral_const_mul,
      integral_thirdKindMaster hc φ
        (fun θ _ => (one_sub_mul_sin_sq_pos (hlt t ht) θ).ne')]
  rw [← hL, hmid, hswap, hR]

/-! #### Two tools

The Legendre integrals differentiate in their upper limit, their integrands being
continuous. This is what makes the antiderivatives below checkable by `HasDerivAt`. -/

theorem hasDerivAt_ellipticE (c φ : ℝ) :
    HasDerivAt (ellipticE c) (ellipticEIntegrand c φ) φ := by
  refine (intervalIntegral.integral_hasStrictDerivAt_right
    (intervalIntegrable_ellipticEIntegrand c 0 φ) ?_
    (continuous_ellipticEIntegrand c).continuousAt).hasDerivAt
  exact (continuous_ellipticEIntegrand c).stronglyMeasurableAtFilter _ _

theorem hasDerivAt_ellipticF {c : ℝ} (hc : c < 1) (φ : ℝ) :
    HasDerivAt (ellipticF c) (ellipticFIntegrand c φ) φ := by
  refine (intervalIntegral.integral_hasStrictDerivAt_right
    (intervalIntegrable_ellipticFIntegrand hc 0 φ) ?_
    (continuous_ellipticFIntegrand hc).continuousAt).hasDerivAt
  exact (continuous_ellipticFIntegrand hc).stronglyMeasurableAtFilter _ _

theorem continuous_ellipticPiAuxIntegrand {c n : ℝ} (hc : c < 1) (hn : n < 1) :
    Continuous fun θ : ℝ =>
      Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ) :=
  (by fun_prop : Continuous fun θ : ℝ => Real.sin θ ^ 2).div
    ((by fun_prop : Continuous fun θ : ℝ => 1 - n * Real.sin θ ^ 2).mul
      (continuous_ellipticEIntegrand c))
    fun θ => mul_ne_zero (one_sub_mul_sin_sq_pos hn θ).ne' (ellipticEIntegrand_pos hc θ).ne'

-- Theorem: splitting off the `n = 0` part of the third-kind integrand leaves `n · A(n)`.
theorem ellipticPi_eq_aux {c n : ℝ} (hc : c < 1) (hn : n < 1) :
    ellipticPi c n = ellipticF c (Real.pi / 2) + n * ellipticPiAux c n (Real.pi / 2) := by
  have hpt : ∀ θ : ℝ, ellipticPiIntegrand c n θ
      = ellipticFIntegrand c θ
        + n * (Real.sin θ ^ 2 / ((1 - n * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) := by
    intro θ
    have h1 := (one_sub_mul_sin_sq_pos hn θ).ne'
    have h2 := (ellipticEIntegrand_pos hc θ).ne'
    simp only [ellipticPiIntegrand, ellipticFIntegrand]
    field_simp
    ring
  unfold ellipticPi ellipticF ellipticPiAux
  rw [← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add ((continuous_ellipticFIntegrand hc).intervalIntegrable _ _)
      (((continuous_ellipticPiAuxIntegrand hc hn).const_mul n).intervalIntegrable _ _)]
  exact intervalIntegral.integral_congr fun θ _ => hpt θ

/-! #### The parameter between `0` and `c`

`P(c sin²β) = (c sin β cos β Δ(β))²` is a square outright, so `Q = c sin β cos β Δ(β)` and
`ρ = 1/Δ(β)`; since `1 - ν = Δ(β)²`, the weight `ρ ((1 - ν) K - E)` is `Δ(β) K - E/Δ(β)`,
which integrates to `K E(β) - E F(β)` with no substitution. -/

-- Theorem: the middle path stays below `1`, whatever the sign of `c`.
theorem middleNu_lt_one {c : ℝ} (hc : c < 1) (t : ℝ) : c * Real.sin t ^ 2 < 1 := by
  have := one_sub_mul_sin_sq_pos hc t; linarith

-- Theorem: the normalisation `Q = c sin β cos β Δ(β)` has the derivative the path lemma
-- asks for.
theorem hasDerivAt_middleQ {c : ℝ} (hc : c < 1) (t : ℝ) : HasDerivAt
    (fun s : ℝ => c * Real.sin s * Real.cos s * ellipticEIntegrand c s)
    (ellipticFIntegrand c t * thirdKindCubicDeriv c (c * Real.sin t ^ 2)) t := by
  have hE := ellipticEIntegrand_pos hc t
  have hEsq := ellipticEIntegrand_sq hc t
  have h1 : HasDerivAt (fun s : ℝ => c * Real.sin s * Real.cos s)
      (c * Real.cos t * Real.cos t + c * Real.sin t * -Real.sin t) t :=
    ((Real.hasDerivAt_sin t).const_mul c).mul (Real.hasDerivAt_cos t)
  have h2 : HasDerivAt (fun s : ℝ => ellipticEIntegrand c s)
      (-(2 * c * Real.sin t * Real.cos t) / (2 * ellipticEIntegrand c t)) t :=
    hasDerivAt_ellipticEIntegrand c t (one_sub_mul_sin_sq_pos hc t).ne'
  refine (h1.mul h2).congr_deriv ?_
  simp only [ellipticFIntegrand, thirdKindCubicDeriv]
  field_simp
  linear_combination (c * Real.cos t ^ 2 - c * Real.sin t ^ 2) * hEsq
    + (c - 2 * c ^ 2 * Real.sin t ^ 2) * Real.sin_sq_add_cos_sq t

-- Theorem: and `Q ν' = 2 ρ P(ν)` along it, since `P(c sin²t) = Q²`.
theorem middleRel {c : ℝ} (hc : c < 1) (t : ℝ) :
    c * Real.sin t * Real.cos t * ellipticEIntegrand c t * (2 * c * Real.sin t * Real.cos t)
      = 2 * ellipticFIntegrand c t * thirdKindCubic c (c * Real.sin t ^ 2) := by
  have hE := (ellipticEIntegrand_pos hc t).ne'
  have hEsq := ellipticEIntegrand_sq hc t
  simp only [ellipticFIntegrand, thirdKindCubic]
  field_simp
  linear_combination (c ^ 2 * Real.sin t ^ 2 * Real.cos t ^ 2) * hEsq
    + (c ^ 2 * Real.sin t ^ 2 * (1 - c * Real.sin t ^ 2)) * Real.sin_sq_add_cos_sq t

-- Theorem: the path lemma along the middle path, at an arbitrary upper limit `φ`. The
-- complete case `φ = π/2` is `ellipticPiAux_middle` below; a general `φ` leaves the
-- boundary term of the master identity behind, and that term is what the interchange
-- relation for the incomplete integral is made of.
theorem middlePath_key {c : ℝ} (hc : c < 1) (β φ : ℝ) :
    c * Real.sin β * Real.cos β * ellipticEIntegrand c β
        * ellipticPiAux c (c * Real.sin β ^ 2) φ
      = ∫ t in (0 : ℝ)..β, ellipticFIntegrand c t
          * ((1 - c * Real.sin t ^ 2) * ellipticF c φ - ellipticE c φ
            + thirdKindAnti c (c * Real.sin t ^ 2) φ) := by
  have key := thirdKindPath_key (ν := fun s : ℝ => c * Real.sin s ^ 2)
    (Q := fun s : ℝ => c * Real.sin s * Real.cos s * ellipticEIntegrand c s)
    (ρ := ellipticFIntegrand c) (νd := fun s : ℝ => 2 * c * Real.sin s * Real.cos s)
    hc (by fun_prop) (continuous_ellipticFIntegrand hc)
    (fun t => (((Real.hasDerivAt_sin t).pow 2).const_mul c).congr_deriv (by push_cast; ring))
    (hasDerivAt_middleQ hc) (middleRel hc) (τ₀ := 0) (τ₁ := β)
    (fun t _ => middleNu_lt_one hc t) φ
  simp only [Real.sin_zero, Real.cos_zero] at key
  norm_num at key
  exact key

-- Theorem: along the path `n = c sin²β` the path lemma reads off `K E(β) - E F(β)`.
theorem ellipticPiAux_middle {c : ℝ} (hc : c < 1) (β : ℝ) :
    c * Real.sin β * Real.cos β * ellipticEIntegrand c β
        * ellipticPiAux c (c * Real.sin β ^ 2) (Real.pi / 2)
      = ellipticF c (Real.pi / 2) * ellipticE c β
        - ellipticE c (Real.pi / 2) * ellipticF c β := by
  rw [middlePath_key hc β (Real.pi / 2)]
  simp only [thirdKindAnti_pi_div_two, add_zero]
  have hpt : ∀ t : ℝ,
      ellipticFIntegrand c t * ((1 - c * Real.sin t ^ 2) * ellipticF c (Real.pi / 2)
          - ellipticE c (Real.pi / 2))
        = ellipticF c (Real.pi / 2) * ellipticEIntegrand c t
          - ellipticE c (Real.pi / 2) * ellipticFIntegrand c t := by
    intro t
    have hE := (ellipticEIntegrand_pos hc t).ne'
    have hEsq := ellipticEIntegrand_sq hc t
    simp only [ellipticFIntegrand]
    field_simp
    linear_combination (-ellipticF c (Real.pi / 2)) * hEsq
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ellipticF c (Real.pi / 2) * ellipticEIntegrand c t
        - ellipticE c (Real.pi / 2) * ellipticFIntegrand c t) fun t _ => hpt t,
    intervalIntegral.integral_sub
      (((continuous_ellipticEIntegrand c).const_mul _).intervalIntegrable _ _)
      (((continuous_ellipticFIntegrand hc).const_mul _).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rfl

/-! #### The parameter between `c` and `1`

Here `P(ν) < 0`, so `-P` is the square. With `S = √(c + x²)` and `R = √(1 + x²)`,
`√(-P(ν)) = (1-c) x S / R³` and `ρ = -1/(R S)`. At `ψ = π/2 - arctan x` one has `sin ψ = 1/R`,
so the integrands at the complementary parameter `1 - c` are `S/R` and `R/S`, and the weight
is the derivative of `(K - E) F(ψ, 1-c) - K E(ψ, 1-c)` — Heuman's `Λ₀` in the tables. -/

section Upper

variable {c : ℝ}

/-- `√(c + x²)`, the numerator of `√ν` along the upper path. -/
noncomputable def upperS (c x : ℝ) : ℝ := Real.sqrt (c + x ^ 2)

/-- `√(1 + x²)`, its denominator. -/
noncomputable def upperR (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2)

theorem upperS_pos (hc0 : 0 < c) (x : ℝ) : 0 < upperS c x := Real.sqrt_pos.mpr (by positivity)

theorem upperR_pos (x : ℝ) : 0 < upperR x := Real.sqrt_pos.mpr (by positivity)

theorem upperS_sq (hc0 : 0 < c) (x : ℝ) : upperS c x ^ 2 = c + x ^ 2 :=
  Real.sq_sqrt (by positivity)

theorem upperR_sq (x : ℝ) : upperR x ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)

theorem hasDerivAt_upperS (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (upperS c) (x / upperS c x) x :=
  ((((hasDerivAt_pow 2 x).const_add c).sqrt (by positivity)).congr_deriv (by
    rw [upperS]; push_cast; field_simp))

theorem hasDerivAt_upperR (x : ℝ) : HasDerivAt upperR (x / upperR x) x :=
  ((((hasDerivAt_pow 2 x).const_add 1).sqrt (by positivity)).congr_deriv (by
    rw [upperR]; push_cast; field_simp))

/-- The path of parameters running from `c` up to `1`. -/
noncomputable def upperNu (c x : ℝ) : ℝ := (c + x ^ 2) / (1 + x ^ 2)

/-- The normalisation `Q` along it. -/
noncomputable def upperQ (c x : ℝ) : ℝ :=
  (1 - c) * x * upperS c x / ((1 + x ^ 2) * upperR x)

/-- The weight `ρ` along it. -/
noncomputable def upperRho (c x : ℝ) : ℝ := -(1 / (upperR x * upperS c x))

theorem upperNu_lt_one (hc : c < 1) (x : ℝ) : upperNu c x < 1 := by
  rw [upperNu, div_lt_one (by positivity)]
  linarith

theorem hasDerivAt_upperQ (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (upperQ c) (upperRho c x * thirdKindCubicDeriv c (upperNu c x)) x := by
  have hS := upperS_pos hc0 x
  have hR := upperR_pos x
  have hSsq := upperS_sq hc0 x
  have hRsq := upperR_sq x
  have hN : HasDerivAt (fun y : ℝ => (1 - c) * y * upperS c y)
      ((1 - c) * upperS c x + (1 - c) * x * (x / upperS c x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (1 - c) * y) (1 - c) x := by
      simpa using (hasDerivAt_id x).const_mul (1 - c)
    have h2 : HasDerivAt (fun y : ℝ => upperS c y) (x / upperS c x) x := hasDerivAt_upperS hc0 x
    exact h1.mul h2
  have hD : HasDerivAt (fun y : ℝ => (1 + y ^ 2) * upperR y)
      (2 * x * upperR x + (1 + x ^ 2) * (x / upperR x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => upperR y) (x / upperR x) x := hasDerivAt_upperR x
    exact h1.mul h2
  refine (hN.div hD (by positivity)).congr_deriv ?_
  simp only [upperRho, upperNu, thirdKindCubicDeriv]
  field_simp
  linear_combination
    ((c - 1) * (upperR x ^ 2 * x ^ 2 - upperR x ^ 2 + x ^ 4 + x ^ 2)) * hSsq
      - x ^ 2 * (c - 1) * (c + x ^ 2) * hRsq

/-- The derivative of the upper path. -/
noncomputable def upperNuDeriv (c x : ℝ) : ℝ := 2 * (1 - c) * x / (1 + x ^ 2) ^ 2

/-- The angle at the complementary parameter that the upper path lands on. -/
noncomputable def upperAngle (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

theorem hasDerivAt_upperNu (c x : ℝ) : HasDerivAt (upperNu c) (upperNuDeriv c x) x := by
  have h1 : HasDerivAt (fun y : ℝ => c + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add c
  have h2 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  refine (h1.div h2 (by positivity)).congr_deriv ?_
  rw [upperNuDeriv]
  field_simp
  ring

theorem continuous_upperNu (c : ℝ) : Continuous (upperNu c) := by
  unfold upperNu
  exact (by fun_prop : Continuous fun x : ℝ => c + x ^ 2).div
    (by fun_prop) fun x => by positivity

theorem continuous_upperS (c : ℝ) : Continuous (upperS c) := by
  unfold upperS; fun_prop

theorem continuous_upperR : Continuous upperR := by unfold upperR; fun_prop

theorem continuous_upperRho (hc0 : 0 < c) : Continuous (upperRho c) := by
  unfold upperRho
  exact ((continuous_const.div ((continuous_upperR).mul (continuous_upperS c))
    fun x => (mul_pos (upperR_pos x) (upperS_pos hc0 x)).ne')).neg

theorem upperRel (hc0 : 0 < c) (x : ℝ) :
    upperQ c x * upperNuDeriv c x = 2 * upperRho c x * thirdKindCubic c (upperNu c x) := by
  have hS := upperS_pos hc0 x
  have hR := upperR_pos x
  have hSsq := upperS_sq hc0 x
  have hRsq := upperR_sq x
  simp only [upperQ, upperNuDeriv, upperRho, upperNu, thirdKindCubic]
  field_simp
  linear_combination ((1 - c) ^ 2 * x ^ 2) * hSsq

-- Theorem: the integrand met along the upper path is an exact derivative, the
-- antiderivative being a combination of the two Legendre integrals at the
-- complementary parameter `1 - c`.
theorem hasDerivAt_upperAnti (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
        (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
            * ellipticF (1 - c) (upperAngle y)
          - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (upperAngle y))
      (upperRho c x * ((1 - upperNu c x) * ellipticF c (Real.pi / 2)
        - ellipticE c (Real.pi / 2))) x := by
  have hS := upperS_pos hc0 x
  have hR := upperR_pos x
  have hSsq := upperS_sq hc0 x
  have hRsq := upperR_sq x
  have hc' : (1 : ℝ) - c < 1 := by linarith
  have hsin : Real.sin (upperAngle x) = 1 / upperR x := by
    rw [upperAngle, Real.sin_pi_div_two_sub, Real.cos_arctan, upperR]
  have hEint : ellipticEIntegrand (1 - c) (upperAngle x) = upperS c x / upperR x := by
    have h : (1 : ℝ) - (1 - c) * Real.sin (upperAngle x) ^ 2 = (c + x ^ 2) / (1 + x ^ 2) := by
      rw [hsin, div_pow, one_pow, upperR, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + x ^ 2)]
      field_simp
      ring
    rw [ellipticEIntegrand, h, upperS, upperR, Real.sqrt_div (by positivity)]
  have hFint : ellipticFIntegrand (1 - c) (upperAngle x) = upperR x / upperS c x := by
    rw [ellipticFIntegrand, hEint, inv_div]
  have hpsi : HasDerivAt upperAngle (-(1 / (1 + x ^ 2))) x := by
    have := (Real.hasDerivAt_arctan x).const_sub (Real.pi / 2)
    exact this.congr_deriv (by ring)
  have hF := ((hasDerivAt_ellipticF hc' (upperAngle x)).comp x hpsi).const_mul
    (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
  have hE := ((hasDerivAt_ellipticE (1 - c) (upperAngle x)).comp x hpsi).const_mul
    (ellipticF c (Real.pi / 2))
  refine (hF.sub hE).congr_deriv ?_
  rw [hEint, hFint]
  simp only [upperRho, upperNu]
  field_simp
  linear_combination ellipticF c (Real.pi / 2) * hSsq
    + (ellipticE c (Real.pi / 2) - ellipticF c (Real.pi / 2)) * hRsq

-- Theorem: the path lemma along the upper path, integrated.
theorem ellipticPiAux_upper (hc0 : 0 < c) (hc : c < 1) (X : ℝ) :
    upperQ c X * ellipticPiAux c (upperNu c X) (Real.pi / 2)
      = ((ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
            * ellipticF (1 - c) (upperAngle X)
          - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (upperAngle X))
        - ((ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
            * ellipticF (1 - c) (Real.pi / 2)
          - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (Real.pi / 2)) := by
  have key := thirdKindPath_key (ν := upperNu c) (Q := upperQ c) (ρ := upperRho c)
    (νd := upperNuDeriv c)
    hc (continuous_upperNu c) (continuous_upperRho hc0) (hasDerivAt_upperNu c)
    (hasDerivAt_upperQ hc0) (upperRel hc0) (τ₀ := 0) (τ₁ := X)
    (fun t _ => upperNu_lt_one hc t) (Real.pi / 2)
  simp only [thirdKindAnti_pi_div_two, add_zero] at key
  have hQ0 : upperQ c 0 = 0 := by simp [upperQ]
  have hcont : Continuous fun t : ℝ =>
      upperRho c t * ((1 - upperNu c t) * ellipticF c (Real.pi / 2)
        - ellipticE c (Real.pi / 2)) :=
    (continuous_upperRho hc0).mul
      (((continuous_const.sub (continuous_upperNu c)).mul continuous_const).sub continuous_const)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_upperAnti hc0 t) (hcont.intervalIntegrable 0 X)
  have hpsi0 : upperAngle 0 = Real.pi / 2 := by simp [upperAngle]
  rw [hQ0, zero_mul, sub_zero, hint, hpsi0] at key
  exact key

end Upper

/-! #### Negative parameters

Again `-P` is the square: with `W = √((1 + x²)(1 + c x²))`, `√(-P(ν)) = c x W` and `ρ = 1/W`.
Read at `ψ = arctan x` the complementary integrands are `W/(1+x²)` and `(1+x²)/W`, and the
antiderivative needs an elementary term too, the `tan ψ · Δ'(ψ)` left by integrating
`∫ Δ'/cos²ψ` by parts. -/

section Lower

variable {c : ℝ}

/-- `√((1 + x²)(1 + c x²))`, the normalising root along the lower path. -/
noncomputable def lowerW (c x : ℝ) : ℝ := Real.sqrt ((1 + x ^ 2) * (1 + c * x ^ 2))

/-- The path of parameters running from `0` down to `-∞`. -/
noncomputable def lowerNu (c x : ℝ) : ℝ := -(c * x ^ 2)

/-- The normalisation `Q` along it. -/
noncomputable def lowerQ (c x : ℝ) : ℝ := c * x * lowerW c x

/-- The weight `ρ` along it. -/
noncomputable def lowerRho (c x : ℝ) : ℝ := 1 / lowerW c x

/-- The derivative of the lower path. -/
noncomputable def lowerNuDeriv (c x : ℝ) : ℝ := -(2 * c * x)

theorem lowerW_pos (hc0 : 0 < c) (x : ℝ) : 0 < lowerW c x :=
  Real.sqrt_pos.mpr (by positivity)

theorem lowerW_sq (hc0 : 0 < c) (x : ℝ) : lowerW c x ^ 2 = (1 + x ^ 2) * (1 + c * x ^ 2) :=
  Real.sq_sqrt (by positivity)

theorem continuous_lowerW (c : ℝ) : Continuous (lowerW c) := by unfold lowerW; fun_prop

theorem continuous_lowerNu (c : ℝ) : Continuous (lowerNu c) := by unfold lowerNu; fun_prop

theorem continuous_lowerRho (hc0 : 0 < c) : Continuous (lowerRho c) :=
  continuous_const.div (continuous_lowerW c) fun x => (lowerW_pos hc0 x).ne'

theorem lowerNu_lt_one (hc0 : 0 < c) (x : ℝ) : lowerNu c x < 1 := by
  have : 0 ≤ c * x ^ 2 := by positivity
  simp only [lowerNu]; linarith

theorem hasDerivAt_lowerNu (c x : ℝ) : HasDerivAt (lowerNu c) (lowerNuDeriv c x) x := by
  have h1 : HasDerivAt (fun y : ℝ => c * y ^ 2) (2 * c * x) x :=
    ((hasDerivAt_pow 2 x).const_mul c).congr_deriv (by push_cast; ring)
  exact h1.neg.congr_deriv (by rw [lowerNuDeriv])

theorem hasDerivAt_lowerW (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (lowerW c) (x * (1 + c + 2 * c * x ^ 2) / lowerW c x) x := by
  have hV : HasDerivAt (fun y : ℝ => (1 + y ^ 2) * (1 + c * y ^ 2))
      (2 * x * (1 + c * x ^ 2) + (1 + x ^ 2) * (2 * c * x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => 1 + c * y ^ 2) (2 * c * x) x := by
      have := ((hasDerivAt_pow 2 x).const_mul c).const_add 1
      exact this.congr_deriv (by push_cast; ring)
    exact h1.mul h2
  have hs : (0 : ℝ) < Real.sqrt ((1 + x ^ 2) * (1 + c * x ^ 2)) :=
    Real.sqrt_pos.mpr (by positivity)
  refine (hV.sqrt (by positivity)).congr_deriv ?_
  rw [lowerW]
  field_simp
  ring

theorem hasDerivAt_lowerQ (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (lowerQ c) (lowerRho c x * thirdKindCubicDeriv c (lowerNu c x)) x := by
  have hW := lowerW_pos hc0 x
  have hWsq := lowerW_sq hc0 x
  have h1 : HasDerivAt (fun y : ℝ => c * y) c x := by
    simpa using (hasDerivAt_id x).const_mul c
  have h2 : HasDerivAt (fun y : ℝ => lowerW c y) (x * (1 + c + 2 * c * x ^ 2) / lowerW c x) x :=
    hasDerivAt_lowerW hc0 x
  refine (h1.mul h2).congr_deriv ?_
  simp only [lowerRho, lowerNu, thirdKindCubicDeriv]
  field_simp
  linear_combination hWsq

theorem lowerRel (hc0 : 0 < c) (x : ℝ) :
    lowerQ c x * lowerNuDeriv c x = 2 * lowerRho c x * thirdKindCubic c (lowerNu c x) := by
  have hW := lowerW_pos hc0 x
  have hWsq := lowerW_sq hc0 x
  simp only [lowerQ, lowerNuDeriv, lowerRho, lowerNu, thirdKindCubic]
  field_simp
  linear_combination (-x ^ 2) * hWsq

theorem lowerEIntegrand_eq (hc0 : 0 < c) (x : ℝ) :
    ellipticEIntegrand (1 - c) (Real.arctan x) = lowerW c x / (1 + x ^ 2) := by
  have hW := lowerW_pos hc0 x
  have h : (1 : ℝ) - (1 - c) * Real.sin (Real.arctan x) ^ 2
      = (lowerW c x / (1 + x ^ 2)) ^ 2 := by
    rw [Real.sin_arctan, div_pow, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 1 + x ^ 2),
      div_pow, lowerW_sq hc0]
    field_simp
    ring
  rw [ellipticEIntegrand, h, Real.sqrt_sq (by positivity)]

theorem lowerFIntegrand_eq (hc0 : 0 < c) (x : ℝ) :
    ellipticFIntegrand (1 - c) (Real.arctan x) = (1 + x ^ 2) / lowerW c x := by
  rw [ellipticFIntegrand, lowerEIntegrand_eq hc0, inv_div]

-- Theorem: the integrand met along the lower path is again an exact derivative; here the
-- antiderivative also carries an elementary term.
theorem hasDerivAt_lowerAnti (hc0 : 0 < c) (x : ℝ) :
    HasDerivAt (fun y : ℝ =>
        ellipticF c (Real.pi / 2) * (y * lowerW c y / (1 + y ^ 2))
          + (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
              * ellipticF (1 - c) (Real.arctan y)
          - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (Real.arctan y))
      (lowerRho c x * ((1 - lowerNu c x) * ellipticF c (Real.pi / 2)
        - ellipticE c (Real.pi / 2))) x := by
  have hW := lowerW_pos hc0 x
  have hWsq := lowerW_sq hc0 x
  have hc' : (1 : ℝ) - c < 1 := by linarith
  have hnum : HasDerivAt (fun y : ℝ => y * lowerW c y)
      (1 * lowerW c x + x * (x * (1 + c + 2 * c * x ^ 2) / lowerW c x)) x := by
    have h1 : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
    have h2 : HasDerivAt (fun y : ℝ => lowerW c y) (x * (1 + c + 2 * c * x ^ 2) / lowerW c x) x :=
      hasDerivAt_lowerW hc0 x
    exact h1.mul h2
  have hden : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
    simpa using (hasDerivAt_pow 2 x).const_add 1
  have hel := ((hnum.div hden (by positivity)).const_mul (ellipticF c (Real.pi / 2)))
  have harctan : HasDerivAt Real.arctan (1 / (1 + x ^ 2)) x := Real.hasDerivAt_arctan x
  have hF := (((hasDerivAt_ellipticF hc' (Real.arctan x)).comp x harctan).const_mul
    (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2)))
  have hE := (((hasDerivAt_ellipticE (1 - c) (Real.arctan x)).comp x harctan).const_mul
    (ellipticF c (Real.pi / 2)))
  refine ((hel.add hF).sub hE).congr_deriv ?_
  rw [lowerEIntegrand_eq hc0, lowerFIntegrand_eq hc0]
  simp only [lowerRho, lowerNu]
  field_simp
  linear_combination (-(ellipticF c (Real.pi / 2)) * x ^ 2) * hWsq

-- Theorem: the path lemma along the lower path, integrated.
theorem ellipticPiAux_lower (hc0 : 0 < c) (hc : c < 1) (X : ℝ) :
    lowerQ c X * ellipticPiAux c (lowerNu c X) (Real.pi / 2)
      = ellipticF c (Real.pi / 2) * (X * lowerW c X / (1 + X ^ 2))
        + (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
            * ellipticF (1 - c) (Real.arctan X)
        - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (Real.arctan X) := by
  have key := thirdKindPath_key (ν := lowerNu c) (Q := lowerQ c) (ρ := lowerRho c)
    (νd := lowerNuDeriv c)
    hc (continuous_lowerNu c) (continuous_lowerRho hc0) (hasDerivAt_lowerNu c)
    (hasDerivAt_lowerQ hc0) (lowerRel hc0) (τ₀ := 0) (τ₁ := X)
    (fun t _ => lowerNu_lt_one hc0 t) (Real.pi / 2)
  simp only [thirdKindAnti_pi_div_two, add_zero] at key
  have hQ0 : lowerQ c 0 = 0 := by simp [lowerQ]
  have hcont : Continuous fun t : ℝ =>
      lowerRho c t * ((1 - lowerNu c t) * ellipticF c (Real.pi / 2)
        - ellipticE c (Real.pi / 2)) :=
    (continuous_lowerRho hc0).mul
      (((continuous_const.sub (continuous_lowerNu c)).mul continuous_const).sub continuous_const)
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_lowerAnti hc0 t) (hcont.intervalIntegrable 0 X)
  rw [hQ0, zero_mul, sub_zero, hint] at key
  simpa [ellipticF, ellipticE] using key

end Lower

/-! ### `Π(n, c)` in closed form

The two roots of `P` in range are the two values of `n` no path reaches. At `n = 0` the
third-kind integrand is the first-kind one; at `n = c` the cubic vanishes identically, so
the master identity has only `A` left in it. -/

-- Theorem: at `n = 0` the third-kind integral collapses to the first-kind one.
theorem ellipticPi_zero {c : ℝ} (hc : c < 1) :
    ellipticPi c 0 = ellipticF c (Real.pi / 2) := by
  rw [ellipticPi_eq_aux hc (by norm_num)]; ring

-- Theorem: at `n = c` the cubic `P` vanishes, the master identity has only one integral
-- left in it, and `Π` reduces to `E / (1 - c)`.
theorem ellipticPi_self {c : ℝ} (hc0 : 0 < c) (hc : c < 1) :
    ellipticPi c c = ellipticE c (Real.pi / 2) / (1 - c) := by
  have hkey := integral_thirdKindMaster hc (Real.pi / 2)
    (fun θ _ => (one_sub_mul_sin_sq_pos hc θ).ne')
  rw [thirdKindAnti_pi_div_two, add_zero] at hkey
  have hzero : thirdKindCubic c c = 0 := by simp [thirdKindCubic]
  have hpt : ∀ θ : ℝ, thirdKindMaster c c θ
      = thirdKindCubicDeriv c c
        * (Real.sin θ ^ 2 / ((1 - c * Real.sin θ ^ 2) * ellipticEIntegrand c θ)) := by
    intro θ
    simp only [thirdKindMaster, hzero]
    ring
  rw [intervalIntegral.integral_congr (g := fun θ : ℝ => thirdKindCubicDeriv c c
      * (Real.sin θ ^ 2 / ((1 - c * Real.sin θ ^ 2) * ellipticEIntegrand c θ)))
      fun θ _ => hpt θ, intervalIntegral.integral_const_mul] at hkey
  rw [← ellipticPiAux] at hkey
  rw [ellipticPi_eq_aux hc hc]
  have hcc : thirdKindCubicDeriv c c = c ^ 2 - c := by simp only [thirdKindCubicDeriv]; ring
  rw [hcc] at hkey
  have hne : c ^ 2 - c ≠ 0 := by nlinarith
  have hne1 : (1 : ℝ) - c ≠ 0 := by linarith
  rw [eq_div_iff hne1]
  linear_combination -hkey

theorem ellipticEIntegrand_Pconstructible {c θ : ℝ} (hc : PConstructible c)
    (hθ : PConstructible θ) : PConstructible (ellipticEIntegrand c θ) :=
  sqrt_Pconstructible (PConstructible.sub PConstructible.base_one
    (PConstructible.mul hc (sq_Pconstructible (sin_Pconstructible hθ))))

theorem pi_div_two_Pconstructible : PConstructible (Real.pi / 2) :=
  PConstructible.div pi_Pconstructible two_Pconstructible

-- Theorem: the complete elliptic integral of the third kind `Π(n, c)` is P-constructible
-- for every P-constructible parameter `n < 1` and every P-constructible `0 < c < 1`.
theorem ellipticPi_Pconstructible {c n : ℝ} (hcP : PConstructible c) (hnP : PConstructible n)
    (hc0 : 0 < c) (hc : c < 1) (hn : n < 1) : PConstructible (ellipticPi c n) := by
  have hK : PConstructible (ellipticF c (Real.pi / 2)) :=
    ellipticF_Pconstructible hcP pi_div_two_Pconstructible hc
  have hEE : PConstructible (ellipticE c (Real.pi / 2)) :=
    ellipticE_Pconstructible hcP pi_div_two_Pconstructible hc
  have hccP : PConstructible (1 - c) := PConstructible.sub PConstructible.base_one hcP
  have hcc : (1 : ℝ) - c < 1 := by linarith
  rcases lt_trichotomy n 0 with hneg | hzero | hpos
  · set X := Real.sqrt (-n / c) with hXdef
    have hXpos : 0 < X := Real.sqrt_pos.mpr (div_pos (by linarith) hc0)
    have hX2 : X ^ 2 = -n / c := Real.sq_sqrt (div_pos (by linarith) hc0).le
    have hnu : lowerNu c X = n := by
      rw [lowerNu, hX2]; field_simp
    have hkey := ellipticPiAux_lower hc0 hc X
    rw [hnu] at hkey
    have hQne : lowerQ c X ≠ 0 := by
      have := lowerW_pos hc0 X
      simp only [lowerQ]
      positivity
    have hA : ellipticPiAux c n (Real.pi / 2)
        = (ellipticF c (Real.pi / 2) * (X * lowerW c X / (1 + X ^ 2))
            + (ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
                * ellipticF (1 - c) (Real.arctan X)
            - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (Real.arctan X)) / lowerQ c X := by
      rw [eq_div_iff hQne]; linear_combination hkey
    rw [ellipticPi_eq_aux hc hn, hA]
    have hXP : PConstructible X :=
      sqrt_Pconstructible (PConstructible.div (neg_Pconstructible hnP) hcP)
    have hWP : PConstructible (lowerW c X) :=
      sqrt_Pconstructible (PConstructible.mul
        (PConstructible.add PConstructible.base_one (sq_Pconstructible hXP))
        (PConstructible.add PConstructible.base_one (PConstructible.mul hcP
          (sq_Pconstructible hXP))))
    have hatP : PConstructible (Real.arctan X) := arctan_Pconstructible hXP
    exact PConstructible.add hK (PConstructible.mul hnP (PConstructible.div
      (PConstructible.sub (PConstructible.add
        (PConstructible.mul hK (PConstructible.div (PConstructible.mul hXP hWP)
          (PConstructible.add PConstructible.base_one (sq_Pconstructible hXP))))
        (PConstructible.mul (PConstructible.sub hK hEE)
          (ellipticF_Pconstructible hccP hatP hcc)))
        (PConstructible.mul hK (ellipticE_Pconstructible hccP hatP hcc)))
      (PConstructible.mul (PConstructible.mul hcP hXP) hWP)))
  · rw [hzero, ellipticPi_zero hc]; exact hK
  · rcases lt_trichotomy n c with hlt | heq | hgt
    · set B := Real.arcsin (Real.sqrt (n / c)) with hBdef
      have hnc1 : Real.sqrt (n / c) ≤ 1 := by
        rw [show (1 : ℝ) = Real.sqrt 1 by simp]
        exact Real.sqrt_le_sqrt (by rw [div_le_one hc0]; linarith)
      have hnc0 : (0 : ℝ) < n / c := div_pos hpos hc0
      have hsin : Real.sin B = Real.sqrt (n / c) :=
        Real.sin_arcsin (by linarith [Real.sqrt_nonneg (n / c)]) hnc1
      have hsinpos : 0 < Real.sin B := by
        rw [hsin]; exact Real.sqrt_pos.mpr hnc0
      have hsin2 : Real.sin B ^ 2 = n / c := by
        rw [hsin]; exact Real.sq_sqrt hnc0.le
      have hnu : c * Real.sin B ^ 2 = n := by rw [hsin2]; field_simp
      have hcos : Real.cos B = Real.sqrt (1 - n / c) := by
        rw [hBdef, Real.cos_arcsin, Real.sq_sqrt hnc0.le]
      have hcospos : 0 < Real.cos B := by
        rw [hcos]
        exact Real.sqrt_pos.mpr (by rw [sub_pos, div_lt_one hc0]; exact hlt)
      have hkey := ellipticPiAux_middle hc B
      rw [hnu] at hkey
      have hDpos := ellipticEIntegrand_pos hc B
      have hQne : c * Real.sin B * Real.cos B * ellipticEIntegrand c B ≠ 0 := by positivity
      have hA : ellipticPiAux c n (Real.pi / 2)
          = (ellipticF c (Real.pi / 2) * ellipticE c B
              - ellipticE c (Real.pi / 2) * ellipticF c B)
            / (c * Real.sin B * Real.cos B * ellipticEIntegrand c B) := by
        rw [eq_div_iff hQne]; linear_combination hkey
      rw [ellipticPi_eq_aux hc hn, hA]
      have hBP : PConstructible B :=
        arcsin_Pconstructible (sqrt_Pconstructible (PConstructible.div hnP hcP))
      exact PConstructible.add hK (PConstructible.mul hnP (PConstructible.div
        (PConstructible.sub (PConstructible.mul hK (ellipticE_Pconstructible hcP hBP hc))
          (PConstructible.mul hEE (ellipticF_Pconstructible hcP hBP hc)))
        (PConstructible.mul (PConstructible.mul (PConstructible.mul hcP
          (sin_Pconstructible hBP)) (cos_Pconstructible hBP))
          (ellipticEIntegrand_Pconstructible hcP hBP))))
    · rw [heq, ellipticPi_self hc0 hc]
      exact PConstructible.div hEE hccP
    · set X := Real.sqrt ((n - c) / (1 - n)) with hXdef
      have hXpos : 0 < X := Real.sqrt_pos.mpr (by apply div_pos <;> linarith)
      have hX2 : X ^ 2 = (n - c) / (1 - n) :=
        Real.sq_sqrt (le_of_lt (by apply div_pos <;> linarith))
      have hnu : upperNu c X = n := by
        have h1 : (1 : ℝ) - n ≠ 0 := by linarith
        have hden : (1 : ℝ) + X ^ 2 ≠ 0 := by positivity
        rw [upperNu, div_eq_iff hden, hX2]
        field_simp
        ring
      have hkey := ellipticPiAux_upper hc0 hc X
      rw [hnu] at hkey
      have hQne : upperQ c X ≠ 0 := by
        have h1 := upperS_pos hc0 X
        have h2 := upperR_pos X
        have h3 : (0 : ℝ) < 1 - c := by linarith
        simp only [upperQ]
        positivity
      have hA : ellipticPiAux c n (Real.pi / 2)
          = (((ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
                  * ellipticF (1 - c) (upperAngle X)
                - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (upperAngle X))
              - ((ellipticF c (Real.pi / 2) - ellipticE c (Real.pi / 2))
                  * ellipticF (1 - c) (Real.pi / 2)
                - ellipticF c (Real.pi / 2) * ellipticE (1 - c) (Real.pi / 2)))
            / upperQ c X := by
        rw [eq_div_iff hQne]; linear_combination hkey
      rw [ellipticPi_eq_aux hc hn, hA]
      have hXP : PConstructible X := sqrt_Pconstructible
        (PConstructible.div (PConstructible.sub hnP hcP)
          (PConstructible.sub PConstructible.base_one hnP))
      have hSP : PConstructible (upperS c X) :=
        sqrt_Pconstructible (PConstructible.add hcP (sq_Pconstructible hXP))
      have hRP : PConstructible (upperR X) :=
        sqrt_Pconstructible (PConstructible.add PConstructible.base_one (sq_Pconstructible hXP))
      have hpsiP : PConstructible (upperAngle X) :=
        PConstructible.sub pi_div_two_Pconstructible (arctan_Pconstructible hXP)
      have hQP : PConstructible (upperQ c X) := by
        rw [upperQ]
        exact PConstructible.div (PConstructible.mul (PConstructible.mul hccP hXP) hSP)
          (PConstructible.mul (PConstructible.add PConstructible.base_one
            (sq_Pconstructible hXP)) hRP)
      exact PConstructible.add hK (PConstructible.mul hnP (PConstructible.div
        (PConstructible.sub
          (PConstructible.sub (PConstructible.mul (PConstructible.sub hK hEE)
            (ellipticF_Pconstructible hccP hpsiP hcc))
            (PConstructible.mul hK (ellipticE_Pconstructible hccP hpsiP hcc)))
          (PConstructible.sub (PConstructible.mul (PConstructible.sub hK hEE)
            (ellipticF_Pconstructible hccP pi_div_two_Pconstructible hcc))
            (PConstructible.mul hK
              (ellipticE_Pconstructible hccP pi_div_two_Pconstructible hcc))))
        hQP))

/-! #### In terms of the modulus

As for `E` and `F`, the statement one would quote writes the parameter as the square of a
modulus `k`; `0 < k² < 1` is the usual `0 < |k| < 1`. -/

-- Theorem: `Π(n, k) = ∫₀^{π/2} dθ / ((1 - n sin²θ)√(1 - k² sin²θ))` is P-constructible for
-- every P-constructible `n < 1` and every P-constructible modulus `k` with `0 < k² < 1`.
theorem ellipticPi_sq_Pconstructible {k n : ℝ} (hk : PConstructible k)
    (hn : PConstructible n) (hk0 : 0 < k ^ 2) (hk1 : k ^ 2 < 1) (hn1 : n < 1) :
    PConstructible (ellipticPi (k ^ 2) n) :=
  ellipticPi_Pconstructible (sq_Pconstructible hk) hn hk0 hk1 hn1

end Pconstructible
