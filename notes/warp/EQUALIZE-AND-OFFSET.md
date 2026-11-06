# Equalize Character Height, superscript and subscript

Do these Font dialog effects give shapes that text warps could not otherwise draw?
Measured with `probes/probe_equalize.py` and `probes/probe_equalize2.py`, using COM
bakes for observation. In the UI, both are Font dialog checkboxes, and the Offset value
is a spinner with 2 % steps.

## What they do (measured)

**Equalize Character Height** stretches each glyph vertically, and only vertically.
- The map from the plain glyph to the equalized one is exactly affine, `(x, y) ↦ (x, k·y + c)`.
  The residual is 0.0001 pt, and the glyph's x coordinates don't change.
- Every glyph's ink box is sent onto one band, running from the baseline up a height `H`. `H`
  depends on the font and the size, and is snapped to 0.75 pt:

  | Font | Size | H (pt) |
  |---|---|---|
  | Segoe UI Symbol | 72 | 69.75 |
  | Segoe UI Symbol | 36 | 35.25 |
  | Arial | 72 | 70.5 |
  | Yu Gothic | 72 | 66 |

- Examples of the stretch:
  - `·` is stretched 8.8× into a tall ellipse, and `▪` 4.4×.
  - The descender of `g` is lifted onto the baseline.
  - A glyph with several contours (`A`, `g`) is moved by one map for all its contours.
- With mixed sizes, each glyph uses the band for its own size. All bands share the baseline.
- A warp sees the equalized outline. The Triangle model applied to the equalized row
  matches PowerPoint to 0.29 pt max (`●·`, `·●·`).

**Baseline offset** (Superscript is 30 %, Subscript −25 %; the spinner steps by 2 %).
- Any nonzero offset draws the glyph at **2/3 of its font size**, exactly. This held at
  30 %, 50 %, 100 % and −25 %.
- The glyph is shifted up by `offset × font size`, where the font size is the full one,
  not 2/3. The shift is snapped to 0.75 pt.
- Combined with Equalize, the glyph fills the band for 2/3 of its size, then gets shifted.

**Exact rule** (`probe_offset2.py`, about 800 glyphs at 9 sizes, no misses), with stored size
`S` and offset `p` (range −100 % to 100 %, COM rejects 1.02), and `d = |p|·S/100`:
- drawn size `snap(2S/3)`. It uses the stored size, not the drawn one: 72.4 gives 48, not 48.75.
- superscript rise `0.75·⌊4d/3 + ½⌋`, which is `d` rounded to the nearest pixel.
- subscript drop `0.75·max(0, ⌊4d/3 − ½⌋)`, one pixel less than `d` rounded, with ties going
  down. For example −25 % at 10.5 pt drops 2.25 pt, and −2 % at 13 pt doesn't move.
- the pen then advances by the offset glyph's drawn size.

This is formalized as `RowGlyph.size` / `RowGlyph.rise` in `Pptc/TextBox.lean`.

## Why neither gives a new kind of shape

The measured warp law reads every glyph only through its *rectangle*.
- **The rectangle.** It is the box `[a, b] × [c, d] ⊆ [0, 1]²` that the glyph's ink occupies
  after the row's ink box has been normalized.
- **The glyph inside it** is an axis-aligned affine image of the glyph's outline.
- **The warped row** is `⋃ F(glyph_i in R_i)`.

Size, spacing, superscript and Equalize all act on glyphs by axis-aligned affine maps. So
all of them, Equalize included, do only one thing: choose the rectangles `R_i`. None of
them changes what is drawn inside a rectangle.

The next question is how much the rectangle matters. Take a glyph lying in one half of a
Triangle (not across the apex `u = 1/2`), and write `u = a + (b − a)s`, `v = c + (d − c)t`.
The image is

```
x = w·u                      (affine in s)
y = α(u)·(1 − c) + c·h + (d − c)·t·(h − α(u)),    α(u) = adj·h·|2u − 1|  (affine in s here)
```

For two placements `(c, d)` and `(c′, d′)` with the same `(a, b)`, the two `y`s differ by a
constant factor, plus an affine function of `x`. So the two images are related by an
affine map `(x, y) ↦ (x, λy + px + q)`, which the class already has
(`linearMap_PConstructibleCurve`, translations).

**For the Triangle, vertical placement is irrelevant up to affine maps.**
- Up to affine maps, every piece of a Triangle image of a circle has the normal form
  `x = s, y = t·(1 + κ·s)`.
- That has a single modulus `κ = 2·adj·(b − a) / (1 − adj·(1 − 2a))`, which depends only on
  the handle and the horizontal placement.
- A glyph straddling the apex does pick up a dependence on `(c, d)`: the two halves meet
  at a different angle. But each half separately is still in the κ family, and
  `restrict` reaches the halves one at a time. So no new numbers come from it.

**For the Fade presets the roles swap.**
- Here `y` is linear in `v`, and `x` carries the `s·t` term.
- The normal form is `x = s·(1 + μ·t), y = t`, with `μ = 2·x₁·(d − c) / (w − 2·x₁·(1 − c))`,
  which depends on the vertical placement only.
- This is the Triangle family with its axes swapped. A 90° rotation is in the class.

**Conclusion for straight-guide presets:** Superscript, Subscript and Equalize add no new
curve families. They only add more values of the one modulus, and those values are rational
either way.

## Where they could matter

1. **Curved-guide presets** (Can, Ring, Wave, the Pours). Polar and arc-length maps are
   not bilinear, so the rectangle's `(c, d)` is a genuine second parameter. In a Pour it
   sets the ratio of the glyph's inner and outer radii.
   - The handle can only be at its default or a stop, so layout is the main way to vary
     these warps.
   - Without the offset, rectangles from same-baseline glyphs of different sizes lie on a
     one-parameter line, touching the bottom.
   - Superscript and Subscript free up `(c, d)` on a grid of 2 % of the font size. That is
     the useful effect.
2. **Equalize, for glyphs that aren't circles.** It gives any glyph a full-height rectangle
   with its natural width, decoupling height from width.
   - For a circle glyph this adds nothing, because a full-height `[a, b] × [0, 1]` is
     already reachable with `●`, a short companion glyph and character spacing.
   - It would matter for a glyph whose useful outline only ever appears at partial height,
     such as a dot, a small square, or the parts of a multi-contour glyph.
   - Even then, the curves it gives are warp images of glyph pieces in rectangles: new
     placements, not new kinds of shape.

## Consequence for `Pptc/TextBox.lean`

Layout could be modelled one level up: a row becomes a list of `(glyph, rectangle)`, and
`WellFormed` says the rectangles come from a reachable layout. Superscript and Equalize
then only add cases to that reachability predicate, and theorems about shapes quantify over
rectangles without seeing the layout at all.

Open questions:
- What `H` is in font metrics (it is not `hhea` ascent, typo ascent, or win ascent).
- The spacing range.
- Whether the reachable rectangle grid differs between the routes.
