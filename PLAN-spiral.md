# PLAN-spiral: everything the Archimedean spiral makes constructible

**Status:** plan, nothing launched. The spiral is **not** in `Defs.lean`. Adding it is the
user's decision; stream D drafts the constructor for that decision.

**Survey, not hunt.** The goal is to characterise the capability completely. Do not chase one
equation. For every operation, each stream records what the spiral gives:
- new equation classes, named or not;
- reductions to classes that are already reachable;
- negative results, together with what the failing path *does* give.

Named problems appear as examples inside the catalogue. They are never the filter (memory
`broad-sweeps-not-targets`).

## 0. The curve, as PowerPoint draws it

Sources: `notes/ppt-curves/P1.md`, `P1b.md`, and the session measurements of 2026-11-03.

- **Route.**
  1. Insert a text box holding a polygonal glyph.
  2. Choose Shape Format ▸ Text Effects ▸ Transform ▸ Warp ▸ **Warped Circle**
     (`textCirclePour`). Leave the yellow handle at its default.
  3. Make the box square with the size spinners (steps of 0.1 in).
- **The map** [Measured]: a glyph point at ink-box fractions `(u, v)` goes to polar coordinates
  `θ = π + 2πu`, `r = ρ + (R − ρ)v`, with `R = W/2` and `ρ = R/2`. Both radii are spec defaults.
  - A straight edge becomes an arc of `r = A + Bθ`.
  - Horizontal edges become circular arcs; vertical edges become radial segments.
- **Idealization** (b), treated as exact by the user's convention:
  - corners are exact to 0.16 pt;
  - between corners the Bézier fit is within 2.7 % of `R`.
- **Glyphs.**
  - ◢◣◤◥ (Segoe UI Symbol / Cascadia): a full turn, `Δu = Δv = 1`.
  - ▲▼ (Consolas, Arial): two half turns.
  - Consolas `╱`: span 966/1126.
  - Several glyphs in a row: each edge spans about `1/n` of a turn.
- **Open conditions:**
  - box sizes with both circles at 360° (only 1.0, 2.0, 2.1, 2.3, 2.9, 3.3, 3.5, 3.7, 4.0 and
    4.2 in are known);
  - the ink-box normalisation rule, which matters for glyphs that do not fill their cell.
- **Pure-spiral windows.** In the pure spiral `r = bθ`, an edge covers `θ ∈ [θ₀, 2θ₀]`, where
  `θ₀ = 2πΔu/Δv` (if `v` starts at 0). That suggests the windows reach all of `(0, 4π]`.
  [Unchecked derivation; stream W confirms or corrects it.]

## 1. Ground rules

- Read `CLAUDE.md` and `pptc/Pptc/Defs.lean` for the current constructors. Note that `offset`
  now acts on a whole curve (`a < b`, `γ '' Icc a b = S`, closed curves with a smooth seam).
- Use the Wolfram MCP for every identity and for every numeric check of 15 digits or more:
  one self-contained call per computation. Python is a fallback only, and the note must say
  so.
- Label every claim [Proof], [Wolfram], [Heuristic] or [Open]. A "new class" claim is
  [Heuristic] unless it has a proof of non-reducibility.
- **Reduction is required.** For each equation, state whether it is:
  - **E**: algebraic or elementary, adding nothing;
  - **R**: already reachable without the spiral, with the construction named;
  - **N**: new and named;
  - **?**: new and unnamed.

  Check **R** against `notes/sheared-sine-intersections.md`, `notes/ppt-curves/M.md` §2 (the T1–T6
  dictionary) and the offset-inversion notes.
- For each **N** or **?** class, record which roots the reachable θ windows (§0) actually hit.
- No Lean edits and no `Defs.lean` changes. Commit nothing. Do not modify ppt-sim. Never kill
  python/node/uvx processes.
- One agent per stream, with one deliverable each:
  - the note goes to `notes/spiral/<id>.md`, starting with a findings summary and ending with
    "Other things noticed";
  - the progress log goes to `HANDOFF-spiral-<id>.md` at `C:\dev\Powerpoint\lean`, one line
    per step.

## 2. Streams

| id | question | depends on |
|---|---|---|
| W | **Windows and normal form.** Exactly which arcs of `r = bθ` (θ windows, offsets, orientations) are reachable, using the PowerPoint data (§0) and the closure operations (`scale_x/y`, `rotate`, `translate`, `restrict`)? Settle the `(0, 4π]` claim and what lies beyond 4π. Is the *non-uniform* image (`scale_x ≠ scale_y`) of a spiral still useful, and what does it look like in polar form? | — |
| I1 | **Spiral ∩ lines and conics.** Cover lines, circles in every position (centred, off-centre, through the origin), ellipses, hyperbolas and parabolas. For each, derive the equation, then reduce and classify it. Example to settle: off-centre circle `cos(θ−φ) = (θ²+q)/(2Pθ)`. | — |
| I2 | **Spiral ∩ polynomial graphs (deg ≤ 6), power laws and cubic Béziers.** Example to settle: parabola `sin θ = kθ cos²θ` (`x = tan x sec x` when k = 1). Find out which sub-families collapse to one trig function, which need two harmonics, and which are named. | — |
| I3 | **Spiral ∩ transcendental base curves:** `exp_two`, `sine`, and their affine images. | — |
| I4 | **Spiral ∩ spiral:** same centre and different centres, any pitches and rotations. Also the spiral ∩ its own offset, and ∩ the exact warp by-products (circles, radial segments). | W |
| O | **Spiral-derived curves:** the offset spiral, *as a curve*: its intersections with lines and conics, and its arc length. Then offset inversion along the spiral, `½(sinh u cosh u + u) − d(sinh u + gd u) = x`, with the legitimate route (`arc_of_length`, then offset the whole arc, then box) checked against the new `offset` hypotheses. | W |
| B | **Read-outs beyond the basic box.** Boxes of every I1–I4 and O curve where the result is a new curve (offsets, restricted pieces). Boxes in a direction that is not a P-constructible angle. Arc lengths between intersection points. `arc_of_length` starting at a non-vertex point. | I1–I4, O |
| C | **Compositions (depth 2).** Does one spiral step, followed by existing constructors, give more than the one-step catalogue? Examples: a box value fed into a sine or `exp_two` intersection; a spiral root used as a rotation angle or scale; two spiral constructions combined. Look for closure: which families are fixed under composition. | I1–I4, B |
| L | **Literature and named problems.** For every N or ? class from I1–I4, O and B, search physics, engineering and mathematics. Candidates: Sturm–Liouville eigenvalue conditions, cam and gear profiles (Archimedean cams), antenna and spiral-coil design, spiral of Theodorus, spiral-tangent problems, Fresnel/Euler-type equations, Kepler-like equations. Wolfram-verify every match. | I1–I3 (starts as they land) |
| D | **Draft constructor and decision packet** for the user. Possible forms: a fixed curve (`r = θ` on a window, like `sine`), a parametric family, or a glyph-edge form mirroring the warp map. Include the evidence, the idealization category, the exact UI path, and what each form unlocks. Not for `Defs.lean`. | W, all |

**Ordering:**
- Wave 1: W, I1, I2 and I3 in parallel.
- Wave 2: I4, O and L.
- Wave 3: B, then C, then D.

## 3. Deliverable

The orchestrator writes `notes/spiral/SUMMARY.md`:
- the full table, operation → equation → E/R/N/? → named examples → reachable roots;
- the list of genuinely new classes, with the strength of each novelty claim;
- the constructor options from stream D for the user's decision.

Nothing goes into `Defs.lean` without the user's explicit decision.
