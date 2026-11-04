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

## 4. Wave 1 results and follow-ups (2026-11-03)

Notes: `notes/spiral/W.md`, `I1.md`, `I2.md`, `I3.md`.

**What wave 1 established:**

- **W: normal form [Proof].**
  - Every reachable arc is a mirrored similarity image of `r = ψ` over a window
    `ψ ∈ [2πq₁, 2πq₂]`, with `q₁ = Δu(1+v₀)/Δv` and `q₂ = q₁ + Δu`. This implies:
    - one arc turns at most once, and `q₂ ≤ 2q₁`;
    - the window ends and the plane endpoints are P-constructible;
    - `A` in `r = A + Bθ` adds nothing;
    - non-uniform scaling adds no new box values.
  - **The §0 "(0, 4π]" claim is false for fixed fonts:** there are gaps, for example between
    one and two ◢. Beyond 4π *is* reachable: flat edges, rotated text, mixed font sizes.
  - **Open:**
    - whether the warp normalises by the whole row's ink box;
    - the ink box under rotated text;
    - whether the Arch/Button Pour presets give exact spirals (Arch Down Pour defaults to
      `ρ = R/4`);
    - whether character spacing and font size can be set exactly by UI;
    - isolating a sub-arc.
- **I1: lines and conics.** One master equation covers every case:
  `Re(Aθ²e^{2iθ} + Bθe^{iθ}) + mθ² + f = 0`.
  - **E:** a line through the centre; a circle centred at the centre.
  - **R:** a general line; centred conics; off-centre circles and circles through the centre
    (the partner `x + q/x` is a sheared hyperbola); Dottie; Kepler.
  - **?:** generic conics; conics symmetric about a line through the centre (parabola `y = kx²`,
    `y² = 4x`); off-centre hyperbolas.
  - **Negative [Proof]:** no line or conic reaches T1, T2 or T6. Only the box gives a tan
    family (T3).
  - **Caveat:** root counts came from sign-change scans, which miss tangential double roots.
- **I2: polynomials, power laws, Béziers.** Equations collapse to R only as `θ^p ×` one
  harmonic.
  - **Parabola:** `sin θ = kθ cos²θ`, which is the sine meeting the non-drawable cubic
    `kx(1−y²) = y`. Class **?**.
  - **Power laws:** R for `b ∈ {0, −1}`, E for `b = 1`, **?** for every other `b`.
  - **Béziers:** the solitary-node Bézier with its node at the centre is R
    (`cos θ = θ^{−1/3}`); the loop and cusp are **?**.
  - **Scope gap:** only the *aligned* frame was enumerated. General position, a shifted
    spiral and non-uniform images were not.
- **I3: `exp_two` and the sine.** The normal forms nest `θ cos(θ−β)` inside a second
  transcendental. Both families are **?** [Heuristic], with no name found.
  - Roots of `θ sin θ = 2^{θ cos θ}` in (0, 4π]: four, then two per turn.
  - `θ sin θ = sin(θ cos θ)`: trivial roots at `mπ` plus a non-trivial root `0.75986…`. The
    sign-flipped case has no non-trivial root, which is unexplained.
  - A side claim, "spiral ∩ log spiral → Lambert W is likely N", is wrong: Lambert W is R (a
    line meeting `exp_two`). It is also moot, because no route draws a log spiral.

**Overall:** the box families (T3, and `(x+β)tan x = 1`) are the only named new numbers so
far. Many intersection families look new, but none is named and none is proved
non-reducible.

### Follow-up streams (wave 1b)

| id | kind | question | depends on |
|---|---|---|---|
| F1 | PowerPoint probe (real UI automation, COM/XML only to observe) | Settle W's open PowerPoint questions: (a) the normalisation of multi-glyph rows (whole-row ink box or per glyph?), measured on rows of ◢ and ▲; (b) Arch Up, Arch Down and Button Pour: are their edges exact spirals, and what are their default handle values and windows? (c) can the character-spacing control (spinner or preset list) and the font-size list set values exactly, and which ones? (d) what does "rotated text" mean in the UI (text direction, Rotate all text 90°/270°, shape rotation), and how does each change the warp? (e) the box sizes with both circles at 360° for the presets in (b). | — |
| F2 | math | **Reachable-roots audit.** Recompute the "reachable roots" column of I1, I2 and I3 against W's exact window set, and F1's once it lands. Redo the root counts with a method that catches double roots (resultant or derivative check, not sign changes). Produce one table: family → roots → which window reaches each → glyph/route. | W, F1 |
| F3 | math | **General position for I2.** Enumerate the spiral meeting polynomial graphs, power laws and Béziers in *general* affine position: shifted spiral, rotated partner, non-uniform image. Reduce each case (E/R/N/?). Find the general collapse conditions, for example which shifts or rotations bring the equation down to `θ^p ×` one harmonic. Also explain I3's sign-flipped sine case. | — |
| F4 | math (proof) | **Novelty.** Try to *prove* non-reducibility for the main **?** classes: the parabola class `sin θ = kθcos²θ`, the generic conic, and `θ sin θ = 2^{θ cos θ}`. Use the framework of `notes/sheared-sine-intersections.md` §3 (uniform convention, analytic continuation) or a differential-algebra / Ax–Schanuel-type argument. Settle the precise statement first: "no single intersection of existing curves solves this family uniformly in its parameters". A proof for one class is a success; a clear account of why the approach fails is also a result. | — |

**Order:** F1, F3 and F4 now; F2 after F1. Wave 2 (I4, O, L) follows as planned. L should take
F4's statements as input.

### Wave 1b results (2026-11-03)

Notes: `notes/spiral/F1.md` to `F4.md`.

- **F1: PowerPoint, measured by real UI.**
  - `(u, v)` are normalised by the **whole row's** ink box, so an edge's turn fraction is
    `a = glyph width / row ink width`.
  - Three spiral presets:

    | Preset | Inner radius ρ | Sweep |
    |---|---|---|
    | Warped Circle | R/2 | full turn |
    | Arch: Warped (and Warped Button, identical on one line) | R/2 | 180° |
    | Arch: Warped Down | R/4 | 180° |

    Corners match to within 0.06–0.74 pt; between corners the error is 2.8–5.4 % of R.
  - Character spacing (presets and a 0.1 pt spinner) and font size (list, then ×1.2 steps)
    snap to 0.75 pt. Rotating text 90°/270° is rigid. *Stacked* text gives new turn fractions.
  - Box sizes with both guides full are listed per preset.
  - **Pitfall:** ◢ and ▲ use the `ea` typeface, not the Latin one.
- **F2: reachable windows and root audit.**
  - The window law is the same for all three presets, with these limits: Warped Circle and
    Arch: Warped end at most at 2× their start; Arch: Warped Down at most at 4×.
  - Rows of up to 40 glyphs plus sizes from the list cover `[0.055, 4π]`. Mixed-height rows
    reach about `[0.76, 47]`. Starts go down to about 0.002 with Arch: Warped Down plus spacing.
    There is a ceiling near 50, so (0, ∞) is not covered.
  - All 343 roots so far are reachable, each with a route.
  - Interval-certified recount: no missed roots, no tangential double roots.
  - The box needs the stationary θ to be the arc's global extremum. Every audited box root has
    a suitable window.
  - M.md was corrected for `tan x = −x`.
- **F3: general position.**
  - **New R stratum:** a conic with a **focus at the spiral centre** (`B² = 8fA`) factors into a
    cosine meeting a hyperbola. It is the only factoring case for graphs.
  - Rotating the partner is the same as using the spiral `r = θ + α`.
  - Graphs of degree ≥ 2 never collapse to `θ^p ×` one harmonic [Proof].
  - The sign-flipped sine has no non-trivial root [Proof].
  - No polynomial, power law or Bézier reaches T1, T2 or T6 [Proof].
- **F4: novelty.** The setting is the "RU1" statement: no regular, uniform, one-step competitor
  from the spiral-free tower, using Ax–Schanuel.
  - **`exp_two` class:** argued non-reducible except for one degenerate case.
  - **Parabola class:** reducible only through a trig curve meeting an algebraic curve that
    contains `kx(1−y²) = y`. Shown impossible for phase (1, 0); open in general and for offset
    partners.
  - **Generic conic class:** its partner is elliptic, so no rational base curve contains it.
  - **Needs independent review.**

Next: wave 2 (I4, O, L). L takes F4's statements and the I1–I3/F3 "?" list as input.

### Wave 2 results (2026-11-03)

Notes: `notes/spiral/I4.md`, `O.md`, `L.md`.

- **I4: spiral ∩ spiral.**
  - **Same pole: E**, in closed form. With equal pitch the arms are disjoint.
  - **Same pole with a non-uniform partner: ?**
  - **Different poles: ?** No single-harmonic collapse. With mirror-symmetric poles, the
    on-axis roots are R (a spiral meeting a line).
  - **Spiral ∩ its own offset: ?** It is the normal-chord condition: an irreducible quartic
    meeting `t = tan(Δ/2)`. There are no intersections for `|d| < π/2`.
  - **Warp by-products:** circles and rays from the same pole are E; from another box they are
    R.
  - Arch presets have the same normal form, so all of the above applies to them.
  - Root counts are sign-change scans, not certified.
- **O: offset spiral.**
  - Closed form, curvature, and arc length verified. Cusps occur only for `d > 1/2`.
  - Box: the spiral's box value ± d, or a cusp coordinate: E/R.
  - Intersections: **?**
  - Warp arcs satisfy the new `offset` hypotheses, given a spiral constructor.
  - **Offset inversion:** arc → offset → box gives nothing beyond the parabola (R). The working
    route is: offset the whole arc, then `arc_of_length` along the offset, then two boxes in
    non-parallel directions. It solves `½(sinh u cosh u + u) − d(sinh u + gd u) = c` for all
    P-constructible `d` and `c`. Class **?**.
- **L: named problems.** Only the box families are named:
  - `x tan x = 1` (0.86033…): slab Biot number Bi = 1; rod with a tip mass equal to its own;
  - `tan x = −x` (2.02876…): rod with a Robin end, h = 1.

  No named match for any intersection or offset-inversion class [Heuristic: limited search; OEIS
  not fetchable]. Routes for each root were derived from F2's windows and are untested in
  PowerPoint.

Next: wave 3. B (read-outs beyond the basic box), then C (compositions), then D (draft
constructor and decision packet).

### Wave 3 results (2026-11-03)

Notes: `notes/spiral/B.md`.

- **B: read-outs beyond the basic box.**
  - **Boxing the uniform spiral gives nothing new.** Boxes of `restrict` pieces, of whole-arc
    offsets (either sign of d) and of uniform images give one of four things:
    - a T3/T2 box number;
    - that number shifted by ∓d;
    - an end coordinate;
    - a spiral∩line coordinate.
  - **Offset cusps** (d > 1/2) satisfy `c³ = d(c² + 1)` with `c = √(1+ψ²)`. Class E/R. For d = 1,
    c is the supergolden ratio.
  - **Non-uniform images.** They are invisible to the box, but not to offsets or arc length.
    - The cusp equation of an offset (diag(2,1), d = 1) is trig with polynomial coefficients:
      class **?** [Heuristic].
    - Inverting arc length along a non-uniform image inverts a non-elementary integral: class
      **?**.
  - **Isolating a sub-arc.** `arc_of_length` from any P-constructible start isolates a sub-arc.
    This removes F2's condition that the window must end before the next extremum, and answers
    W's open question.
  - **Directions.** Every spiral number is a legal rotation angle (`rotate` + scaling), so
    depth-2 boxes exist. Example: β₁ = 2.02875… gives θ = 2.42053345642…. Angles that are not
    P-constructible are unreachable.
  - **Arc lengths.** Between intersection points of the uniform spiral or its offset, they are
    elementary in P-constructible roots: R. On non-uniform images they are **?**.
  - **Inverse arc length from a non-vertex start.** On the uniform spiral it is R (parabola
    inversion). OI-S stays **?**.
  - **Degenerate `restrict` (xmin = xmax) plus box** returns the extreme crossing on a vertical
    line without isolation. Orchestrator check: this adds nothing. Crossings at algebraic or
    P-constructible heights are separated by a rational, so `restrict` + `inter_y` reaches them
    anyway.
  - No B read-out reaches T1, T2 (λ ≠ 1) or T6.
  - **Open:**
    - offset injectivity on windows longer than one turn;
    - the non-uniform cusp scan covered only starts 0.3–3.8;
    - mirrored arcs have cusps for the opposite sign of d, so a Lean form must fix the
      orientation.

Next: C (compositions), then D.
