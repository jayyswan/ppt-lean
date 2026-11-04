# PLAN-warp-sine, part 1: what curve does the sine glyph become under Warped Circle?

**Status:** plan, nothing launched (2026-11-03).

**Why.** Warped Circle sends a glyph point at ink-box fractions `(u, v)` to the polar point
`θ = π + 2πu`, `r = ρ + (R − ρ)v` (spiral notes `F1.md`, `W.md`). If a glyph edge is a sine
`v = c + e·sin(2πmu + φ)`, its image is `r = a + b·sin(mθ + φ′)`. For `m = 1` that is a limaçon. For
rational `m` it is a rose-like **algebraic** curve. That is the one route so far that points at new
algebraic numbers rather than new transcendental classes. The user's circle-glyph test (a filled ●
became a crescent pinched at θ = π) behaved exactly as the map predicts.

**Part 1 (this plan)** finds out which curve PowerPoint actually draws when the sine glyph is
warped, given that **the glyph is a thick band, not a line**.

**Part 2 (not in this plan)** asks what those curves make constructible: limaçon and rose
intersections against `poly_graph` degree ≤ 6, `DegreeSeven.lean`, and trisection. A cheap math
check of part 2 could run alongside part 1 as a gate; see §5.

**Survey, not hunt** (memory `broad-sweeps-not-targets`). Every stream records whatever the warp
produces: exact curves, approximate curves, by-products, and dead ends, each with its evidence.
The limaçon is one entry in that catalogue, not the success criterion.

## 0. How the project's sine is actually made (deck slides 59–65)

Source: `C:\Users\jason\Downloads\constructible (1).pptx`, slides 59–65. Session exports of those
slides are at
`C:\Users\jason\AppData\Local\Temp\claude\C--dev-Powerpoint-lean\c222b849-70f5-4b01-ad09-a19ea61d2b9d\scratchpad\sine_slides\s59.png`
to `s65.png`.

1. Insert U+3030 **〰 (Wavy Dash)** in **Yu Mincho**. It is two periods. Each end is cut
   vertically, at crest height.
2. Fragment-merge with a dummy object twice, to extract the glyph as a freeform.
3. Measure an end with a small square. Resize the square and the glyph together until the end is
   **1/12 in (6 pt)** thick.
4. Give the freeform a 6 pt outline with square caps and miter joins, and no fill.
   - In Edit Points, Open Path at a bottom node.
   - Delete the bottom edge, keeping only the end nodes.
   - What remains is the **top edge**, stroked at the band's thickness.
5. Add an arrow, so the two ends can be told apart. Paste-as-EMF twice turns the stroke into a
   shape, which is then aligned with the original line. The ends are not snappable, so use Merge
   Shapes to help.
6. Snap a rectangle from a crest to the next trough. Intersect it with the stroke outline.
7. Keep the **bottom** boundary of the intersected piece: crest to trough, half a period. Copies of
   it tile `y = sin x`; scaling it to width π and height 1 gives `cos`.

**What this route assumes.** The glyph is a constant-width band of width `w` about a **spine**,
and the spine is the sine. Its edges are the normal offsets `spine ± (w/2)·n`. Stroking the top
edge at width `w` gives the region between offsets 0 and `w` of the spine, so its lower boundary
is the spine itself. **The idealized sine is the glyph's centreline, not either edge.**

**Consequence for earlier notes.** `notes/ppt-curves/P1b.md` §4 measured **U+223F ∿** in Cambria
Math, Segoe UI Symbol and Lucida Sans Unicode, not U+3030 in Yu Mincho. It measured edge midlines,
not the spine recovered by this route.
- So the "sine glyph is 12–19 % off a best-fit sine" figure, and the comparison in
  `notes/spiral/D.md` that cites it, is about the wrong glyph.
- Stream G re-measures it.

## 1. Why warping is harder than the flat route

- **The warp acts on text, not on freeforms.** The thick glyph is the only possible input. The
  thin spine from steps 2–7 cannot be warped, because it is no longer text. [To confirm in WP:
  check that no UI path applies a Transform/Warp to a freeform or to text converted from one.]
- **The polar map is not an isometry, so the flat recovery trick fails after warping.**
  - Let `P` be the warp. The warped edges are `P(spine ± (w/2)n)`.
  - These are **not** normal offsets of `P(spine)`: the band's thickness changes with `r` and with
    the angle between the band and the radial direction.
  - So stroking a warped edge at one fixed width does not land on `P(spine)`.
- **What the warp does preserve.** A *vertical* segment in glyph space maps to a *radial* segment,
  scaled by `(R − ρ)/H`. So:
  - **If** the glyph's edges were vertical shifts of the spine (`v = spine(u) ± δ`), both warped
    edges would be `r = a ± δ′ + b·sin(mθ + φ′)`. Those are limaçons or roses themselves, and no
    recovery would be needed.
  - **If** they are normal offsets, as the deck route assumes, the warped edges are polar images of
    offset sines. Those are generally not algebraic.
  - Which one holds is the first thing to measure (stream G). With 〰's slope, the two models
    differ by a visible amount.
- **The ink box includes the thickness.** By F1, `(u, v)` are normalised by the whole row's ink
  box. That box spans the spine's amplitude plus the band's thickness, and its horizontal extent
  includes the vertical end cuts.
  - So the spine's image has `a`, `b` and phase set by those ratios.
  - `m` is the number of periods across the row: 2 per glyph, so `m = 2n` for `n` glyphs, unless
    spacing changes it.

## 2. Ground rules

- **UI only.** Every construction step is done by real UI actions inside PowerPoint (memory
  `ui-only-constructions`). Typing numbers into a dialog does not count as a construction step.
  - COM, VBA and XML are used **only to observe**: node lists, EMF frames, sizes.
  - Never use another app (Paint and so on) as a construction step.
  - Reading a font file with fontTools to get the glyph outline is observation and is allowed.
- **Numbers.** Use the Wolfram MCP for every fit, identity and ≥15-digit check, one self-contained
  call per computation. Python (`py`) is allowed only for font and EMF parsing; any number from it
  must say so.
- **Pitfall (F1).** 〰 is an East-Asian code point. Set **Yu Mincho as the `ea` (Asian text) font**,
  not only the Latin font, or another typeface is silently substituted.
- Label every claim [Measured], [Wolfram], [Proof], [Heuristic] or [Open].
- **Things not to touch:**
  - no `Defs.lean` or Lean edits, and commit nothing;
  - do not modify ppt-sim;
  - never kill python/node/uvx processes;
  - close any PowerPoint presentation the stream opened, and leave the user's open windows alone.
- **Outputs.** One agent per stream, with one deliverable:
  - the note goes to `notes/warp/<id>.md`, with a findings summary first and "Other things
    noticed" last;
  - the progress log goes to `C:\dev\Powerpoint\lean\HANDOFF-warp-<id>.md`, one line per step.

## 3. Streams

| id | kind | question | depends on |
|---|---|---|---|
| G | font geometry (fontTools + Wolfram; PowerPoint only to confirm the extracted freeform matches the font) | **The exact shape of 〰 in Yu Mincho**, in all available weights (Yu Mincho Light/Regular/Demibold, as installed). (a) The glyph's Bézier outline: node list, number of periods, end cuts. (b) **The edge model:** are the top and bottom edges normal offsets of a common spine, vertical shifts, or neither? Quantify each model's residual. (c) **The spine:** how close is it to a sine (amplitude, period, phase, max deviation as % of amplitude)? This corrects P1b's U+223F figure. (d) The thickness ratio `w/H` and how the ink box relates to the spine (crest height, end cuts). (e) A sweep for other sine-like code points and fonts (U+3030, U+301C 〜, U+FF5E ～, U+223F ∿, U+2053 ⁓, …): which are thinnest relative to the ink box, and which have vertical-shift edges? | — |
| WP | PowerPoint probe (real UI) | **The warped sine glyph.** Put 〰 (Yu Mincho as `ea` font) in a text box and apply Warped Circle; then repeat with Arch: Warped and Arch: Warped Down. Use F1's both-guides-full box sizes. Rows of 1, 2, 3 and 4 glyphs. (a) Extract the outline as the deck does (fragment with a dummy) and observe its nodes via COM. (b) Fit each warped edge against both models: `P(normal-offset edge)`, and a pure limaçon or rose `r = a + b·sin(mθ + φ)`. (c) Measure the accuracy at the extrema and between them, in pt and as % of R, in the same terms as F1's spiral figures. (d) Test **Text Outline** (and fill/no fill) on warped text: is the stroke applied before the warp (and warped) or after it (constant width in the plane)? (e) Confirm that no UI path warps a freeform. (f) Record where the band's ends land (the pinch seen with ●). | G (a) for the model; can start in parallel |
| M | math (Wolfram) | **The exact warped curves and recovery.** (a) From G's model and the warp map, derive the exact warped edges and the image of the spine, `P(spine)`, with the ink-box normalisation; give `a`, `b`, `m`, `φ` in terms of the glyph data. (b) If the edges are normal offsets: is any warped edge algebraic? Is there **any** sequence of available operations (`offset`, scale, rotate, `restrict`, intersection, Merge Shapes, stroke + EMF) that recovers `P(spine)` exactly from the warped band? Prove or disprove, labelling the result. (c) If not exact: how large is the gap between the best edge and a true limaçon or rose, against the idealization tolerance the project already accepts (the sine route's own accuracy from G, and the spiral's 2.8–5.4 % of R)? (d) The by-products: classify the warped edges themselves as curves, and say what the ● crescent (a polar ellipse) and other simple glyphs give. | G; WP for the measured parameters |

**Order:**
- G and WP start together. WP's model-fitting step (b) waits for G (b).
- M starts on G's model as soon as G lands, and takes WP's measurements when they land.
- The orchestrator then writes `notes/warp/SUMMARY-part1.md`:
  - the curve each glyph, font and preset gives;
  - the idealization category of each, with evidence;
  - whether a limaçon or rose is reachable, and by which exact UI path;
  - a draft constructor statement for the user's decision, not for `Defs.lean`.

## 4. Decisions that belong to the user

- If only an *approximate* limaçon or rose is reachable, with an error the size of the band
  thickness, does it count as an idealization? The deck goes to some length to remove the
  thickness for the flat sine, which suggests not, but it is the user's call.
- Any constructor (limaçon, rose, warped glyph image) goes into `Defs.lean` only on the user's
  explicit decision.

## 5. Part 2 preview (not launched with this plan)

Part 2 asks what limaçons and roses `r = a + b·sin(mθ + φ)` (with rational `m`) add to
P-constructibility:
- intersections with lines, circles and conics;
- limaçon ∩ limaçon;
- boxes;
- comparison with the degree ≤ 6 and degree-7 algebraic results already in Lean.

A short math-only gate could run alongside part 1. If limaçons add nothing beyond what
`poly_graph`, `DegreeSeven.lean` and trisection already give, part 1 is worth doing only for the
record.
