# PLAN-offset-soundness: remodel `offset` to match what PowerPoint can actually do

**Status: open, blocking.** Decision owner: the user, since `Defs.lean` changes are theirs.
Nothing has been changed yet.

## The problem

As currently stated, `PConstructibleCurve.offset` (`Pptc/Defs.lean:430`) makes **every real
number P-constructible**. The full write-up is `../notes/offset-inversion/DEFECT-defs-soundness.md`.
A compiling proof is in the untracked file `Pptc/Scratch/CollapseTest.lean`.

- **Cause.** `offset` takes `hsub : γ '' Icc a b ⊆ S`, so *any* sub-arc of a drawn curve can
  be used. There is no condition on `a`, on `b`, or on the plane endpoints, and `a = b` is
  allowed. The offset is then a `PConstructibleCurve`, and `box_xmax` reads its endpoint.
- **Collapse.** Take the parabola `y = x²`, the interval `Icc b b` and `d = 0`. The offset is
  the single point `{(b, b²)}`, and its box gives `b`.
- **Not only a degenerate case.** It works for any `a < b` and any non-vertical graph.
- **Consequence.** `parabola_offset_root_Pconstructible` (`Pptc/OffsetInversion/Parabola.lean`)
  is true but vacuous: its proof offsets over `Icc 0 w` for arbitrary `w`. Treat any result
  that goes through `offset` as suspect until it has been re-checked.

## What needs doing

1. **Model PowerPoint first** (UI-only, observation by COM; see memory `ui-only-constructions`).
   Settle what the offset operation acts on in practice, and what it outputs:
   - **What PowerPoint offsets.** Possible routes: outline thickness converted to a shape, glow
     extents, bevel plateaus (exact offsets, mitred at corners, per `../notes/3d/M3.md`),
     Merge Shapes of a thick stroke. Does each act on a whole drawn shape, or on a piece of
     one?
   - **What can be offset.** Can you offset a piece cut by `restrict`, an arc laid by
     `arc_of_length`, or only whole shapes? What happens at the arc's ends: round caps, flat
     caps, or nothing?
   - **Closed curves** (ellipse, rectangle), and corners or cusps.
   - **Large distances.** Which sign and size of `d` are reachable. What happens beyond the
     radius of curvature: does PowerPoint draw the folded curve with cusps, or trim it?
   - **Idealization class** (a)/(b)/(c), as in the other plans.
2. **Choose the axiom shape** to match. Leading candidate, Option A: `hsub : γ '' Icc a b = S`.
   The arc must *be* the constructed curve, so the only arcs available are those already
   pinned by constructible data, through `restrict` or `arc_of_length`. The defect note §4
   lists other options. Whichever is chosen must agree with step 1, not only block the
   collapse.
3. **Audit the other constructors** for the same pattern: a hypothesis of the form "a sub-arc
   of `S`" that produces a new curve or number without pinning the sub-arc. Check
   `arc_length`, `arc_of_length`, `restrict`, `box_xmax` / `box_ymax`, `inter_x` / `inter_y`,
   and any lemma in `Basic.lean` that builds curves.
4. **Prove non-collapse,** at least informally. Under the new axiom the class should stay
   countable, or at least should not contain every real. A Lean statement that a specific
   number is *not* reachable is probably out of scope; a countability argument may not be.
5. **Repair the downstream files.** These use `offset`:
   - `Pptc/Offset.lean`;
   - `Pptc/BoxOffset.lean`;
   - `Pptc/OffsetInversion/Parabola.lean` (untracked). Re-prove it along the legitimate route:
     an `arc_of_length` arc of length `x`, then offset, then box. The hypotheses on `x` should
     then actually be used.

   Then check `Speed.lean` and `Projectile.lean` in `Pptc/OffsetInversion/`, and anything that
   imports the files above.
6. **Delete** `Pptc/Scratch/CollapseTest.lean`, or keep it as a regression test that must
   *fail* to compile.

## Findings, 2026-11-03: how PowerPoint actually offsets

Sources:
- the user's deck "constructible (1).pptx", slides 51–58 ("Parallel Curves"), plus slides
  38–43 and 67–76 for context;
- a COM-observed probe, `scratchpad/offset_probe/`.

**The route.**
1. Copy the curve and give it a 6 pt line.
2. Scale the curve so that `K` maps to a fixed fraction of that width: a 1/24 in square, then
   a further ½.
3. Set the line to a compound Thick-Thin style.
4. Copy, then Paste Special as EMF, and ungroup twice. The stroke outline is now a freeform.
5. Scale it back up, registering on the centreline copy's bounding box.
6. Align the straight end-cap segment on the original curve's endpoint.

**What it produces [Measured, probe].**
- **It acts on a whole drawn shape.** The stroke belongs to the shape's entire path. A piece of
  a curve can only be offset after it has been made into its own shape, for example by Edit
  Points ▸ Open Path, Merge Shapes, or the arc-division dash route.
- **Both sides at once,** at the band edges of the compound line: several fixed fractions of
  the width.
  - For an *open* curve, each band is one closed polygon: the `+d` offset, a flat end cap, the
    `−d` offset, then the other end cap.
  - For a *closed* curve (ellipse), each edge is its own closed offset curve. The probe gave 6
    concentric closed polylines.
- **The raw offset, folds included.** On a bend tighter than `d`, the inner offset keeps its
  swallowtail loop; it is not trimmed to the envelope. Slides 57–58 show the same loop. This
  matches `offsetParam γ d '' Icc a b`, cusps and all.
- **Corners** (not probed) get a line join: miter, round or bevel. This is outside the
  current `C¹` model, which is the conservative choice.
- **Idealization (b).**
  - The output is a polyline on the EMF grid, measured at 0.125 pt at the shrunken scale.
  - Because the curve is shrunk so that `K` ≈ a few pt and then enlarged, the error is a fixed
    fraction of `K`, a few percent. It does not converge.
  - Under the user's convention, this is still treated as the exact parallel curve.

**Consequences for the axiom.**
1. **The input must be a whole constructed curve**: `γ '' Icc a b = S`, not `⊆ S`. This is
   Option A. Pieces come only from constructors that pin them: `restrict`, `arc_of_length`,
   and so on.
2. **`a < b` is also required.** This is a second collapse that Option A alone does *not* block:
   - `restrict` with a degenerate window (`xmin = xmax`, `ymin = ymax`) yields a singleton
     `{p}`;
   - with `a = b`, `γ` is pinned only at `a`, so `deriv γ a`, and hence `unitNormal γ a`, is
     arbitrary;
   - `offset` then yields `{p + d·v}` for *any* unit vector `v`, and `box_xmax` reads every
     real in `[p.1 − |d|, p.1 + |d|]`.

   With `a < b`, `DifferentiableAt` at an endpoint forces the derivative to equal the one-sided
   derivative from inside `[a, b]`, so the normal is the tangent normal of `S` itself. Recheck
   the other constructors for the same `a = b` gap. `arc_of_length` and `arc_length` look
   harmless: a zero-length arc is just its constructible start point.
3. **Signed `d`, any P-constructible value:** matches PowerPoint, since both sides are produced
   and `K` is set by scaling.
4. **Closed curves** are offset whole by PowerPoint. Two choices:
   - keep `InjOn γ (Icc a b)` (open arcs only): conservative, since closed curves are offset
     piecewise after `restrict`;
   - or allow `InjOn γ (Ico a b)` with `γ a = γ b`, plus a matching-normal condition at the seam,
     so that the offset is the closed parallel curve PowerPoint draws.

**Recommended statement (draft, not applied):**

```lean
  | offset {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
      (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a < b)
      -- `γ` traces the *whole* drawn curve: PowerPoint strokes an entire shape,
      -- never an arbitrary piece of one ...
      (himg : γ '' Set.Icc a b = S)
      (hinj : Set.InjOn γ (Set.Icc a b))
      (hdiff : ∀ t ∈ Set.Icc a b,
        DifferentiableAt ℝ (fun s => (γ s).1) t ∧ DifferentiableAt ℝ (fun s => (γ s).2) t)
      (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
      (hC1 : ContinuousOn (deriv (fun s => (γ s).1)) (Set.Icc a b) ∧
        ContinuousOn (deriv (fun s => (γ s).2)) (Set.Icc a b))
      {d : ℝ} (hd : PConstructible d) :
      PConstructibleCurve (offsetParam γ d '' Set.Icc a b)
```

**Regression tests to keep, both must fail to compile:**
- the sub-arc collapse (`Scratch/CollapseTest.lean`);
- the singleton collapse (degenerate `restrict`, then `offset` with `a = b`).

## Notes

- Until this is resolved, results that depend on offset inversion, such as the
  `ln sec` row in `../notes/ppt-curves/M.md`, are conditional on the repaired axiom.
- No `Defs.lean` edits without the user's explicit decision.
