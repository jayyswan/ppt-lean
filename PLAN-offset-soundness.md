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

## Notes

- Until this is resolved, results that depend on offset inversion, such as the
  `ln sec` row in `../notes/ppt-curves/M.md`, are conditional on the repaired axiom.
- No `Defs.lean` edits without the user's explicit decision.
