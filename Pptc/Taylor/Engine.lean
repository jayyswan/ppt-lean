/-
Copyright (c) 2024 Lean Community. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pptc contributors
-/

import Pptc.Basic

/-! # The trinomial engine

The paper's engine for `x ^ D + a * x + b` is geometric. The polynomial is not solved;
it is *drawn*. The power curve `y = x ^ D` and the straight line `y = -(a * x) - b` meet
exactly where `x ^ D + a * x + b = 0`, so a root of the trinomial is nothing but the
abscissa of a point where two constructible curves cross, and `PConstructible.inter_x`
extracts it. `power_law` draws the first curve and `poly_graph`, `scale_y` and
`translate_y` draw the second.

That reduction is unconditional in `D`, in `a` and in `b`, but `inter_x` only accepts a
crossing that is a *single* point, while the two curves may meet many times. What makes it
usable is a window: the caller supplies `l ≤ x ≤ r` with `l > 0` and asserts that `x` is
the only root in `[l, r]`. Cropping the line to `[l, r] × [-(r ^ D + 1), r ^ D + 1]` then
leaves exactly the wanted crossing, since the power curve carries the constraint `x ≥ 0`
itself and the height bound holds automatically on `0 ≤ x ≤ r`. The window is the entire
content of the isolation step of the paper; locating it (a rational interval, or a
`PConstructible` one produced by some other argument) is left to the caller.

The result is the constructive strengthening of the degree bound in `Pptc.Basic`: with
`a`, `b`, `l`, `r` P-constructible, a root of a trinomial of *any* degree is
P-constructible, no degree-6 or degree-8 ceiling in sight. The trinomial's two lower
coefficients are what `poly_graph` cannot supply on its own, and the power curve's
exponent is a natural number rather than a rational, so no `natDegree` hypothesis appears.

The window turns out to be removable altogether: `trinomial_root_pos_Pconstructible` proves
the same conclusion for a positive root of a nondegenerate trinomial without any isolation
hypothesis, using finiteness of the root set and `crossing_Pconstructible` in place of the
window. `trinomial_root_Pconstructible_of_lt` is the open-window form of the engine that
follows from it.
-/

namespace Pconstructible

open Polynomial

noncomputable section

/-! ### The two curves -/

/-- The graph of the monomial `y = x ^ D` over `x ≥ 0`, which is the part of the plane
that the power law `y = x ^ D` draws. -/
private def powGraph (D : ℕ) : Set (ℝ × ℝ) :=
  {pt : ℝ × ℝ | 0 ≤ pt.1 ∧ pt.2 = pt.1 ^ D}

/-- The graph of the affine function `x ↦ -(a * x) - b`. -/
private def affineLine (a b : ℝ) : Set (ℝ × ℝ) :=
  {pt : ℝ × ℝ | pt.2 = -(a * pt.1) - b}

/-- For a positive exponent the power law `y = 1 * x ^ D` is the graph of `y = x ^ D` over
`x ≥ 0`: the `x > 0` branch is the graph itself, and the extra origin that `power_law`
includes for a positive exponent is the point `(0, 0)`, which lies on it. -/
private theorem power_law_one_set (D : ℕ) (hD : 0 < D) :
    {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ (0 : ℚ) < (D : ℚ))) ∧
        pt.2 = ((1 : ℚ) : ℝ) * pt.1 ^ ((D : ℚ) : ℝ)} = powGraph D := by
  have hDq : (0 : ℚ) < (D : ℚ) := by exact_mod_cast hD
  have hpow : ∀ u : ℝ, u ^ ((D : ℚ) : ℝ) = u ^ D := by
    intro u
    push_cast
    exact Real.rpow_natCast u D
  ext ⟨u, v⟩
  simp only [powGraph, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hdom, hv⟩
    rw [hpow] at hv
    refine ⟨?_, by rw [hv]; push_cast; ring⟩
    rcases hdom with h | ⟨h0, -⟩
    · exact h.le
    · exact h0.ge
  · rintro ⟨h0, hv⟩
    refine ⟨?_, by rw [hpow, hv]; push_cast; ring⟩
    rcases eq_or_lt_of_le h0 with h | h
    · exact Or.inr ⟨h.symm, hDq⟩
    · exact Or.inl h

/-- The power curve `y = x ^ D` is constructible for every positive `D`. -/
private theorem powGraph_PConstructibleCurve (D : ℕ) (hD : 0 < D) :
    PConstructibleCurve (powGraph D) := by
  have h := PConstructibleCurve.power_law (1 : ℚ) (D : ℚ)
  rw [power_law_one_set D hD] at h
  exact h

/-- The graph of `x ↦ -(a * x) - b` is constructible when `a` and `b` are
P-constructible. The graph of the identity is a rational polynomial graph, a `y`-scaling
by `-a` tilts it into `y = -(a * x)`, and a `y`-translation by `-b` drops it onto the
wanted line. -/
private theorem affineLine_PConstructibleCurve {a b : ℝ} (ha : PConstructible a)
    (hb : PConstructible b) : PConstructibleCurve (affineLine a b) := by
  -- The graph of the identity.
  have hgraph : PConstructibleCurve {pt : ℝ × ℝ | pt.2 = pt.1} := by
    have h := PConstructibleCurve.poly_graph (Polynomial.X : Polynomial ℚ) (by simp)
    simpa [Polynomial.aeval_X] using h
  -- Scaling the `y` axis by `-a`.
  have hscaled : PConstructibleCurve {pt : ℝ × ℝ | pt.2 = -(a * pt.1)} := by
    have h := PConstructibleCurve.scale_y hgraph (s := -a) (neg_Pconstructible ha)
    convert h using 1
    ext ⟨u, v⟩
    simp only [Set.mem_ofPred_eq, Set.mem_image]
    constructor
    · intro hv
      exact ⟨(u, u), rfl, Prod.ext rfl (by rw [hv]; ring)⟩
    · rintro ⟨p, hp, hpv⟩
      obtain ⟨hpu, hpv⟩ := Prod.mk.inj hpv
      rw [← hpv, ← hpu, hp]
      ring
  -- Shifting down by `b`.
  have hshifted := PConstructibleCurve.translate_y hscaled (v := -b) (neg_Pconstructible hb)
  convert hshifted using 1
  ext ⟨u, v⟩
  simp only [affineLine, Set.mem_ofPred_eq, Set.mem_image]
  constructor
  · intro hv
    exact ⟨(u, v + b), by linarith, Prod.ext rfl (by ring)⟩
  · rintro ⟨p, hp, hpv⟩
    obtain ⟨hpu, hpv⟩ := Prod.mk.inj hpv
    rw [← hpv, ← hpu, hp]
    ring

/-! ### The engine -/

/-- **The trinomial engine.** A positive real root of `x ^ D + a * x + b` with
P-constructible `a`, `b` is P-constructible, provided it is the only root in a window
`[l, r]` with `0 < l` and P-constructible endpoints: cross the power curve `y = x ^ D`
with the line `y = -(a * x) - b` and read off the unique intersection. -/
theorem trinomial_root_Pconstructible {D : ℕ} (hD : 0 < D) {a b l r x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b)
    (hl : PConstructible l) (hr : PConstructible r)
    (hl0 : 0 < l) (hlr : l ≤ r)
    (hx : x ^ D + a * x + b = 0) (hxI : l ≤ x ∧ x ≤ r)
    (huniq : ∀ y : ℝ, l ≤ y → y ≤ r → y ^ D + a * y + b = 0 → y = x) :
    PConstructible x := by
  -- The crossing sits at `(x, x ^ D)`, and `x` lies in the window and on the power curve.
  have hxv : x ^ D = -(a * x) - b := by linarith
  have hx0 : 0 ≤ x := le_trans hl0.le hxI.1
  have hr0 : 0 ≤ r := le_trans hl0.le hlr
  -- The window is spanned by P-constructible numbers in both directions.
  have htop : PConstructible (r ^ D + 1) :=
    PConstructible.add (pow_Pconstructible hr D) PConstructible.base_one
  have hbot : PConstructible (-(r ^ D + 1)) := neg_Pconstructible htop
  -- Crop the line to the window. The power curve needs no cropping: it already carries
  -- the constraint `x ≥ 0`, and the window is exactly where the root is isolated.
  have hS := PConstructibleCurve.restrict (affineLine_PConstructibleCurve ha hb)
    l r (-(r ^ D + 1)) (r ^ D + 1) hl hr hbot htop
  refine PConstructible.inter_x (powGraph_PConstructibleCurve D hD) hS
    (x := x) (y := x ^ D) ?_
  -- The two cropped curves have exactly one point in common.
  have hmem : ((x, x ^ D) : ℝ × ℝ) ∈ powGraph D ∩
      (affineLine a b ∩ {p : ℝ × ℝ | l ≤ p.1 ∧ p.1 ≤ r ∧
        -(r ^ D + 1) ≤ p.2 ∧ p.2 ≤ r ^ D + 1}) := by
    refine ⟨⟨hx0, rfl⟩, hxv, hxI.1, hxI.2, ?_, ?_⟩
    · have := pow_nonneg hx0 D
      have := pow_nonneg hr0 D
      linarith
    · have := pow_le_pow_left₀ hx0 hxI.2 D
      linarith
  ext ⟨u, v⟩
  simp only [Set.mem_inter_iff, powGraph, affineLine, Set.mem_ofPred_eq,
    Set.mem_singleton_iff, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨-, hv⟩, hline, hb1, hb2, -, -⟩
    have hroot : u ^ D + a * u + b = 0 := by linarith
    have hu : u = x := huniq u hb1 hb2 hroot
    exact ⟨hu, by rw [hv, hu]⟩
  · intro h
    rw [h.1, h.2]
    exact hmem

/-! ### The engine without a window -/

/-- **The engine needs no isolation window.** A positive root of a *nondegenerate*
trinomial `x ^ D + a * x + b` is P-constructible outright. The power curve and the line
still cross at `(x, x ^ D)`, but no uniqueness is assumed: the trinomial has finitely many
roots, so every other crossing is the image of one of finitely many reals under
`t ↦ (t, t ^ D)`, and a rational box around the wanted crossing excludes them all.

Nondegeneracy is not a technicality. For `D = 1`, `a = -1`, `b = 0` the trinomial vanishes
identically, the two curves share a whole line, and no root is determined by the others;
the window of `trinomial_root_Pconstructible` excludes that case by hypothesis instead.
For `D ≥ 2` the coefficient of `X ^ D` is `1` whatever `a` and `b` are, so the polynomial
is automatically nonzero. -/
theorem trinomial_root_pos_Pconstructible {D : ℕ} (hD : 0 < D) {a b x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b) (hx0 : 0 < x)
    (hne : (Polynomial.X ^ D + Polynomial.C a * Polynomial.X + Polynomial.C b :
      Polynomial ℝ) ≠ 0)
    (hx : x ^ D + a * x + b = 0) :
    PConstructible x := by
  have heval : ∀ t : ℝ,
      (Polynomial.X ^ D + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial ℝ).eval t = t ^ D + a * t + b := by
    intro t
    simp
  -- The trinomial has finitely many roots.
  have hfin : {t : ℝ | t ^ D + a * t + b = 0}.Finite :=
    (Polynomial.finite_setOfPred_isRoot hne).subset fun t ht => by
      simpa [Polynomial.IsRoot, heval] using ht
  have hxv : x ^ D = -(a * x) - b := by linarith
  -- `Γ` traces the power curve; the line is its implicit equation read along `Γ`.
  refine (crossing_Pconstructible (powGraph_PConstructibleCurve D hD)
    (affineLine_PConstructibleCurve ha hb) (Γ := fun t : ℝ => (t, t ^ D))
    (F := fun u v => v + a * u + b) (p := fun t => t ^ D + a * t + b) (β := x)
    ?_ ?_ ?_ hfin ?_ ?_).1
  · rintro ⟨u, v⟩ ⟨-, hv⟩
    exact ⟨u, Prod.ext rfl hv.symm⟩
  · rintro ⟨u, v⟩ hv
    simp only [affineLine, Set.mem_ofPred_eq] at hv
    rw [hv]
    ring
  · intro t
    simp
  · exact ⟨hx0.le, rfl⟩
  · simp only [affineLine, Set.mem_ofPred_eq]
    linarith

set_option linter.unusedVariables false in
/-- The engine with the isolation hypothesis stated on the *open* window. Roots sitting
exactly at `l` or `r` are harmless — they are P-constructible already — so the closed form
`trinomial_root_Pconstructible` does not apply here, but none of it is needed: by
`trinomial_root_pos_Pconstructible` a positive root needs no isolation at all. The only
case that still needs care is the degenerate window `l = r`, where `x` is the common
endpoint; there the uniqueness hypothesis forces the trinomial to be nondegenerate.

The right endpoint is unused, and the linter is silenced for it: the open-window form does
not need `r` to be P-constructible at all. -/
theorem trinomial_root_Pconstructible_of_lt {D : ℕ} (hD : 0 < D) {a b l r x : ℝ}
    (ha : PConstructible a) (hb : PConstructible b)
    (hl : PConstructible l) (hr : PConstructible r)
    (hl0 : 0 < l) (hlr : l ≤ r)
    (hx : x ^ D + a * x + b = 0) (hxI : l ≤ x ∧ x ≤ r)
    (huniq : ∀ y : ℝ, l < y → y < r → y ^ D + a * y + b = 0 → y = x) :
    PConstructible x := by
  rcases eq_or_lt_of_le hlr with hEq | hlt
  · -- A window of a single point: `x` is that point.
    rw [← hEq] at hxI
    rw [le_antisymm hxI.2 hxI.1]
    exact hl
  · -- A genuine window. Were the trinomial the zero polynomial, every point of the open
    -- window would be a root, and two distinct ones would both have to equal `x`.
    have hne : (Polynomial.X ^ D + Polynomial.C a * Polynomial.X + Polynomial.C b :
        Polynomial ℝ) ≠ 0 := by
      intro hz
      have hzero : ∀ t : ℝ, t ^ D + a * t + b = 0 := by
        intro t
        have := congrArg (Polynomial.eval t) hz
        simpa using this
      have h₁ := huniq ((2 * l + r) / 3) (by linarith) (by linarith) (hzero _)
      have h₂ := huniq ((l + 2 * r) / 3) (by linarith) (by linarith) (hzero _)
      linarith
    exact trinomial_root_pos_Pconstructible hD ha hb (lt_of_lt_of_le hl0 hxI.1) hne hx

end

end Pconstructible
