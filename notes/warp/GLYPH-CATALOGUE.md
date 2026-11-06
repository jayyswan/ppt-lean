# Glyph catalogue: Unicode shapes with clear geometric analogues

Compiled 2026-11-06. Builds on the warp notes in this folder (`SUMMARY-part1.md`, `G.md`,
`WP.md`, `M.md`) and the spiral survey (`../spiral/SUMMARY.md`, `W.md`). The question is:
**which Unicode characters, in which installed fonts, have outlines that are exact geometric
figures, and what does each become under a PowerPoint text warp?**

## 0. Result in one paragraph

I scanned **3,981 code points** across **29 installed font faces** (the symbol blocks plus
ASCII, Latin-1, General Punctuation and the fullwidth forms). Of these, **3,644 code points
exist in at least one face**. **2,330** have an outline that the automatic rule decomposes
entirely into straight edges, circles, ellipses or circular caps. Removing letters, digits,
enclosed alphanumerics, format characters and non-figure punctuation leaves **1,933**; a
further **25** curved-stroke glyphs are added by hand, giving **1,958 catalogue entries**:

| Tier | Meaning | Count |
|---|---|---:|
| **P** | every contour is a straight-line polygon (exact) | 1,536 |
| **C** | every contour is a polygon, circle or axis-aligned ellipse (within 1 %) | 315 |
| **K** | as C, plus circular caps / rounded ends and thin stroke slivers | 82 |
| **M** | manual curved-stroke supplement (arcs, sectors, rounded square) | 25 |
| | **total** | **1,958** |

By shape class: **501** rectilinear polygons, **1,035** general polygons, **257** dot grids,
**82** compounds, **41** circles, **17** ellipses, **14** arcs, **8** sectors, **2**
semicircles, **1** rounded square. The companions are:

- `GLYPH-INDEX.md` — every qualifying run of code points, grouped by family.
- `glyph-catalogue.csv` — all 3,644 present code points, including the 1,686 rejects, with
  the best font, primitive counts and a `keep` flag.
- `glyphscan.py` — the outline classifier, and `glyphwarp.py` — the exact warp-coordinate
  probe used for the worked examples.

**The short answer for shapes.** Under the three measured presets, a straight glyph edge
becomes a circular arc (horizontal edge), a radial segment (vertical edge) or an
Archimedean-spiral window (slanted edge). Consequently:

- a **rectilinear polygon** (box drawing, blocks, squares, crosses, trigrams) becomes an
  **annular sector**: a region between two exact circles and two exact rays;
- a **general polygon** (triangle, diamond, star, arrow) becomes a closed chain of arcs,
  rays and spiral windows;
- a **circle or ellipse glyph** becomes a **polar ellipse** — a closed transcendental curve,
  not a circle;
- a **dot grid** (braille, ellipsis) becomes a set of small polar ellipses on a warped
  lattice;
- a **compound** (circled operator, alchemical diagram) becomes the union of the images of
  its primitives.

If you need an *exact* circle after warping, do not warp a circle glyph: warp a horizontal
edge that spans the full ink width. If you need an exact ray, warp a vertical edge.

## 1. What counts as a clear geometric analogue

A glyph is a filled outline, so the test is on its **contours**, one at a time.

- **Polygon contour.** Every drawing command is a `lineTo`. Font coordinates are integers,
  so the contour is an exact polygon. No tolerance is involved.
- **Circle contour.** A closed contour whose sampled points fit a circle with maximum radial
  deviation below **1 %** of the radius, whose signed turning is a full turn, and whose
  fitted radius matches the contour size (this rejects shallow arcs, which fit arbitrarily
  large circles).
- **Ellipse contour.** Same, for an axis-aligned ellipse; the fitted semi-axes must match
  the contour box.
- **Cap / arc contour.** A trimmed circle fit: at least 70 % of the points lie within 1 % of
  a circle, the contour is convex, and the covered arc is between 0.4π and 1.75π. This
  captures semicircles, quarter-circle corners, rounded stroke ends and pie slices.
- **Sliver.** A closed, very thin contour with almost no net turning; the inner edge of a
  thick stroke. It carries no shape and is ignored.

A glyph qualifies at tier **P** if all its contours are polygons, at **C** if all are
polygons/circles/ellipses, at **K** if caps and slivers are also allowed. A significant
freeform contour (one whose bounding-box diagonal is at least 40 % of the glyph's) makes the
glyph **X** and it is rejected.

The 1 % threshold is a choice, not a theorem. It is deliberately tighter than the eye:
the best font circles are 0.03–0.10 % off, ordinary ones 0.2–0.5 %, and the worst
"circle" glyphs in the set (Cascadia Code's large ○, SimSun's ●) are 1.2–1.5 % and are
rejected. A user who accepts 2 % can recover them; the CSV records the deviation for every
circle.

Two further caveats:

- **Font circles are Bézier approximations.** Even a 0.03 % circle is not an exact circle.
  The catalogue calls such a glyph a clear analogue, not an exact one. The exact primitives
  are the straight edges.
- **Filled versus outline.** A contour is the boundary of the ink region. `■` is one filled
  contour, `□` is two (outer and inner). Warping maps the boundary; the fill maps to the
  warped interior. For a ring the result is a band, for a disc a filled region. The CSV's
  `ncirc` counts contours: 1 = disc, 2 = ring, 3–4 = bullseye or ring-plus-dot.

## 2. The three measured warp maps

Only three Transform presets were measured (`WP.md`): **Warped Circle**
(`textCirclePour`), **Arch: Warped** (`textArchUpPour`) and **Arch: Warped Down**
(`textArchDownPour`), with the yellow handle at its default. The map acts on the **whole
row's ink box**, not on the glyph's box:

```
u = (x − x₀)/W,   v = (y − y₀)/H,   W = x₁ − x₀,   H = y₁ − y₀
```

with `u` left-to-right, `v` **bottom-to-top**, and `(x₀, y₀)` the lower-left corner of the
row's ink. Let `R = W/2`.

| Preset | Angle | Radius | Inner radius |
|---|---|---|---|
| Warped Circle | `θ = π + 2πu` | `r = R(1 − v/2)` | `R/2` |
| Arch: Warped | `θ = π + πu` | `r = R(1 − v/2)` | `R/2` |
| Arch: Warped Down | `θ = π − πu` | `r = R/4 + (3R/4)v` | `R/4` |

For **Warped Circle** and **Arch: Warped** the pole is **above the top centre of the ink
box**: `r = 0` would require `v = 2`, outside the text, and every glyph lies in
`R/2 ≤ r ≤ R`. For **Arch: Warped Down** the pole is **below the bottom centre**: `r = 0`
at `v = −1/3`, and every glyph lies in `R/4 ≤ r ≤ R`. In all three the map is a local
diffeomorphism on the ink.

The two presets differ in how the row closes. Under **Warped Circle** the sweep is a full
turn and `u = 0`, `u = 1` both map to `θ = π mod 2π`, the **9 o'clock ray**: a full-width
shape closes there, which is the seam in a warped square and the cusp in a warped triangle.
Under the **arches** the sweep is a half turn; `u = 0` is 9 o'clock and `u = 1` is 3 o'clock,
and the two presets traverse the half turn in opposite directions. There is no seam: the
two ends are the cut faces of a half-annulus. The catalogue images below are for Warped
Circle unless an example says otherwise; the arches replace the full turn by the half turn,
and the edge dictionary is unchanged apart from the halved angular span.

Accuracy (`WP.md`, 〰 at 72 pt): corners are within 0.04–0.08 pt of the map; between nodes
the error is 0.30–0.61 % of `R`. The edge law below is exact under the ideal map; the font
outline supplies the only approximation.

**Scope warning.** The other Transform presets (Arch: Warped Down's neighbours, Circle
Pour variants, Wave, etc.) were not measured, and the map above assumes a single row with
the default handle. In a mixed row the glyph's `u` interval shrinks and its `v` interval is
set by the tallest ink in the row; both change the radii and angles. The worked examples in
§6 use a **single glyph filling the ink box** — the cleanest case, not the typical row.

## 3. The primitive dictionary

### 3.1 Exact images

Let `C` be the pole and `R = W/2`. Under **Warped Circle**:

| Glyph primitive | Exact image |
|---|---|
| Horizontal edge `v = c`, `u ∈ [u₁, u₂]` | circular arc `r = R(1 − c/2)`, `θ ∈ [π + 2πu₁, π + 2πu₂]` |
| Vertical edge `u = c`, `v ∈ [v₁, v₂]` | radial segment `θ = π + 2πc`, `r ∈ [R(1 − v₂/2), R(1 − v₁/2)]` |
| Slanted edge, `u = u₁ + a s`, `v = v₀ + h s` | Archimedean window (below) |
| Circle / ellipse / arc | polar ellipse / polar-ellipse arc (§3.2) |
| Filled region | the warped region bounded by the images of its edges |

For a slanted edge with `a = Δu > 0`, `h = |Δv|`, `v₀ = min(v₁, v₂)`:

```
q₁ = a(1 + v₀)/h,     q₂ = q₁ + a,
λ  = R h/(4πa),       κ  = 2π(q₁ − u₁) − π,
z(ψ) = C + λ e^{iκ} ψ e^{−iψ},   ψ ∈ [2πq₁, 2πq₂].
```

This is the `r = A + Bθ` Archimedean spiral, rotated and scaled. A falling edge is the
mirror image (`scale_x(−1)`). The window always has `q₂ − q₁ = a ≤ 1`: one glyph edge never
turns more than a full revolution. The Arch presets halve the angular span; the same
computation with `π` in place of `2π` gives `ψ₁ = πa(1+v₀)/h`, `ψ₂ = ψ₁ + πa` for Arch:
Warped, and `ψ₁ = πa(1+3v₀)/(3h)` for Arch: Warped Down (`W.md` §4; the straight-edge
spiral exactness on the arches was not separately measured).

### 3.2 The polar ellipse

A glyph circle is not centred on the pole, so it does not map to a circle. With glyph
coordinates `(u, v)` and image coordinates `(θ, r)`:

```
circle:  (u − u₀)² + (v − v₀)² = s²,
u = (θ − π)/(2π),   v = 2(1 − r/R),
⇒  r(θ) = R(1 − v₀/2) ∓ (R/2) √(s² − ((θ − π)/(2π) − u₀)²).
```

The outer branch is a closed curve whose radius oscillates once per turn around the pole:
a **polar ellipse**. It is not a conic in polar coordinates, and its eccentricity depends
on the glyph's distance from the pole. For a small glyph near `v = 1/2` it is nearly a
circle; for a glyph that fills the height, especially near the top (`v = 1`, `r = R/2`), it
is visibly oval. An axis-aligned glyph
ellipse gives the same form with the quadratic divided by the two semi-axes. An arc gives
one branch of the same curve.

This is the exact image; the only approximation is the font's Bézier circle (0.03–1.5 %).
The existing warp notes call the same object a "transcendental polar ellipse" (`M.md`,
`SUMMARY-part1.md`).

### 3.3 Reading the dictionary geometrically

| Glyph family | Warped image |
|---|---|
| Rectilinear polygon (H/V edges only) | finite union of **annular sectors**: between exact circles `r = R(1 − c/2)` and exact rays `θ = π + 2πc` |
| Square / rectangle | one full annulus (if it spans the ink width) or one annular sector |
| Triangle | base arc + two spiral windows; cusp on the 9 o'clock seam |
| Diamond / lozenge | four spiral windows (no axis-aligned edges) |
| Star / asterisk | n-fold rosette of spiral windows, alternating inner and outer radii |
| Arrow | shaft (arc, ray or spiral) + two barbed spiral windows |
| Circle | one polar ellipse |
| Ring / bullseye | two or more nested polar ellipses |
| Dot grid | one small polar ellipse per dot, centres on a warped lattice |
| Trigram / parallel bars | two or three concentric annuli; a broken bar is two annular sectors with a gap |
| Compound (circle + cross, alchemical diagram) | union of the images of the parts |

Two consequences are worth stating plainly:

1. **Exact circles come from horizontal edges, not circle glyphs.** A full-width horizontal
   edge at `v = c` is the circle `r = R(1 − c/2)`; a full-width vertical edge is the ray
   `θ = π + 2πc`. A font circle is always a polar ellipse.
2. **The Warped Circle seam is at 9 o'clock.** Any shape that reaches both `u = 0` and
   `u = 1` closes on the same ray under Warped Circle, which is why a warped square is an
   annulus with a seam and a warped triangle has a cusp there. Under the arches the same
   shape instead ends on the 9 and 3 o'clock rays and is a half-annulus.

## 4. The catalogue

Coverage by Unicode block (catalogue entries only; the CSV also carries the rejects):

| Block | Entries | Block | Entries |
|---|---:|---|---:|
| Braille Patterns | 255 | Miscellaneous Symbols | 76 |
| Miscellaneous Symbols and Arrows | 180 | Dingbats | 67 |
| Miscellaneous Technical | 166 | Misc. Mathematical Symbols-B | 62 |
| Supplemental Arrows-C | 149 | General Punctuation | 41 |
| Mathematical Operators | 141 | Block Elements | 32 |
| Supplemental Mathematical Operators | 136 | Alchemical Symbols | 32 |
| Box Drawing | 128 | Misc. Mathematical Symbols-A | 25 |
| Arrows | 100 | Halfwidth and Fullwidth Forms | 22 |
| Geometric Shapes Extended | 96 | Basic Latin | 15 |
| Geometric Shapes | 95 | Latin-1 Supplement | 13 |
| Supplemental Arrows-B | 95 | Supplemental Arrows-A | 13 |
| Supplemental Punctuation | 9 | CJK symbols + compatibility | 10 |

The complete run-by-run index is `GLYPH-INDEX.md`. The subsections below give the shape
reading and the families that matter for construction; they do not repeat every code point.

### 4.1 Rectilinear shapes: lines, boxes, blocks, brackets

This is the largest exact class: **501 axis-aligned polygons** in total. 128 of the
catalogue entries are in Box Drawing — 121 rectilinear, 3 diagonal polygons, 4 manual arcs. The main sources:

- **Box Drawing U+2500–257F (128).** 124 are rectilinear: light/heavy/double lines, dashed
  variants, corners, tees, crosses, half-lines and the double-line junctions. The three
  diagonals `╱╲╳` (U+2571–2573) are exact polygons but not axis-aligned; the four rounded
  corners `╭╮╯╰` (U+256D–2570) are the manual arc supplement.
- **Block Elements U+2580–259F (32).** Half blocks, fractional blocks, quadrants and the
  three shade patterns. The shade glyphs `░▒▓` (U+2591–2593) are *dithered*: 100, 181 and 73
  tiny contours. They are polygons but not solid shapes; treat them as textures, not blocks.
- **Squares, rectangles and frames.** U+25A0–25AF (■□▣▤▥▦▧▨▩▪▫▬▭▮▯), U+25FB–25FE,
  U+25E7–25EB, U+1F78C–1F795, U+1F7E5–1F7EB, U+2B12–2B15, U+2B1A–2B1E, U+2BBA–2BBC,
  U+23F9, U+29C8–29C9, U+29E0, U+29EE–29EF, U+2A05–2A06, U+2A4E–2A4F, U+2ACD–2ACE.
- **Brackets, ceilings, floors and corners.** U+0028/0029 and U+007B/007D are curved and
  excluded; the rectilinear ones are U+005B/005D, U+2045/2046, U+2308–230B (⌈⌉⌊⌋),
  U+231C–231F (⌜⌝⌞⌟), U+23A1–23A6, U+23B4–23B6, U+27C0, U+299C, U+2BFE, U+2E0B.
- **Crosses and junctions.** The box-drawing tees/crosses (U+251C–254B, U+2560–256C), the
  Greek crosses U+1F7A1–1F7A7, and the axis-aligned daggers U+2020/2021.

**Warp image.** A rectilinear polygon is a union of **annular sectors**. Every horizontal
edge at height `v = c` becomes the circle `r = R(1 − c/2)`; every vertical edge at `u = c`
becomes the ray `θ = π + 2πc`. Because the vertices are at rational `u, v`, the radii and
angles are rational multiples of `R` and `2π`: the warped shape is a **rational annular
polygon**, with no transcendental data beyond `π` itself.

For a single glyph filling the ink box, the standard bars give:

| Glyph | Ink | Image |
|---|---|---|
| `─` U+2500 | 1044×134 | annulus `0.5 ≤ r ≤ 1`, seam at 9 o'clock |
| `│` U+2502 | 134×1941 | annulus `0.5 ≤ r ≤ 1`, seam at 9 o'clock |
| `═` U+2550 | 1044×402 | two annuli `0.833–1` and `0.5–0.667` |
| `☰` U+2630 | 1463×1434 | three annuli `0.94–1`, `0.721–0.781`, `0.5–0.56` |
| `■` U+25A0 | 1434×1434 | annulus `0.5 ≤ r ≤ 1` |
| `□` U+25A1 | 1434×1434 | outer annulus `0.5–1` + inner band `0.543–0.957` with a square hole |

The `─` and `│` rows are the extreme single-glyph case: the bar fills the ink box in one
direction, so its short ends wrap the full circle. In a real row the bar is thin relative to
the row, and the result is a **thin annulus** at the bar's height (for `─`) or a **narrow
radial wedge** at the bar's column (for `│`), not a full-width annulus. The formulas are
unchanged; only `v` and `u` change.

### 4.2 Triangles, diamonds and other polygons

- **Triangles (65).** U+25B2–25B9, U+25BC–25C3, U+25E2–25E5 (the four right triangles
  ◢◣◤◥), U+25F8–25FA, U+25FF, U+25EC–25EE, U+2BC5–2BC8, U+1F780–1F783, U+23E9–23EF,
  U+23F4–23F7, U+29CA–29CB, U+29CD–29D0, U+29E8–29E9, U+2A1E, U+234B/234D/2359,
  U+23C3–23C5, U+26DB.
- **Diamonds and lozenges (37).** U+25C6–25C8, U+25CA, U+2662/2666, U+2B16–2B19,
  U+2B25–2B2B, U+1F797–1F7A0, U+27E0, U+29EB, U+29F0–29F1, U+22C4, U+233A, U+235A.
- **Other n-gons (10).** U+2B1F–2B23 (pentagon, hexagon, octagon, horizontal hexagon),
  U+2B53–2B54, U+2BC2–2BC4 (⯂⯃⯄), plus the hexagonal benzene ring U+232C and the
  trapezium U+23E2.
- **Parallelograms and chevrons.** U+25B0/25B1 are parallelograms; U+25F8–25FA are right
  triangles; U+27E4/27E5 and U+2999 are chevron-like frames; U+3010/3011 are curved and
  excluded.

**Warp image.** Every slanted edge is a spiral window; every horizontal edge is an arc;
every vertical edge is a ray. A triangle therefore has one arc and two spiral windows; a
diamond has four spiral windows; a pentagon or hexagon has five or six spiral windows. The
window parameters are rational because the vertex coordinates are rational.

The right triangles are the cleanest non-rectilinear case: two edges are axis-aligned and
one is the diagonal. `◢` U+25E2 in Segoe UI Symbol (1434×1434) is exactly

```
V at u=1:        θ = 3π (9 o'clock), r from 0.5 to 1
H at v=0:        r = 1, θ from 3π to π (the full circle)
S (0,0)→(1,1):   ψ ∈ [2π, 4π], λ = 0.0796, κ = π
```

so the image is the unit circle, a radial seam on the 9 o'clock ray, and one spiral window
joining the inner end of the seam to the outer circle. `◣` is its mirror; `◤◥` use the
other diagonal.

### 4.3 Arrows

**503 entries**, the largest family. They are all exact polygons. Sources: Arrows
U+2190–21FF (100), Supplemental Arrows-A U+27F0–27FF (13), -B U+2900–297F (95), -C
U+1F800–1F8FF (149), Miscellaneous Symbols and Arrows U+2B00–2BFF (the arrow subset of
180), plus the halfwidth arrows U+FFE9–FFEC and the Dingbat arrows U+2794–27AF.

An arrow is a **shaft plus a head**: a horizontal or vertical shaft (arc or ray), two
slanted barbs (two short spiral windows), and optionally a tail or a second head. The head
tip is a vertex, so it lands on an exact ray; the barbs open into spiral windows. A
horizontal `→` in a row wraps its shaft into an arc and its head into a wedge at the 3
o'clock end of the arc; a vertical `↑` puts the shaft on a ray and the head at an outer
radius. Double arrows have two heads and two wedges.

The family is catalogued in full in `GLYPH-INDEX.md` (runs of 8–56 consecutive code
points). It is not useful to list 503 variants here: they differ in shaft length, head
shape, barb angle and whether the head is open or closed, and each is a small variation of
the same three-primitive construction.

**Curved arrows are excluded**: U+219C/219D (wave arrows), U+21A9/21AA (hook arrows),
U+21AB/21AC (loop arrows), U+21B6/21B7 (semicircle arrows), U+21BA/21BB (open-circle
arrows), U+2938–2941 (arc arrows), U+2B6E/2B6F, U+2B8C–2B8F, U+2BA8–2BAF (curved and
ribbon arrows). Their shafts are freeform curves, not arcs, so they are not exact
under the rule. Several are visually circular arcs and could be added by hand if needed;
the scan rejects them because the glyph's *outline* is a stroke band, not the arc.

### 4.4 Stars, asterisks and crosses

- **Stars (78).** U+2605/2606 (★☆), U+2728–273A (the sparkle/star series), U+2B50–2B52,
  U+1F7AF–1F7D4 (the five-, six-, eight-, twelve-pointed and pinwheel series),
  U+2217, U+204E, U+2051, U+22C6, U+2721, U+272C, U+29C6, U+29E6, U+2A6E, U+2BE8–2BEB,
  U+225B.
- **Crosses (108).** `+` U+002B, `−` U+2212, `=` U+003D, `±` U+00B1, `×` U+00D7,
  `÷` U+00F7, `✕✖` U+2715/2716, `✚✛✜✝✞✟` U+2719–271F, `☦☨☩` U+2626/2628/2629,
  `❖` U+2756, and the many math relations built from a cross and a bar
  (U+2A22–2A3B, U+2A66–2A78, U+2A97/2A98, …).

**Warp image.** A star is the archetypal **rosette**: `2n` edges alternate between the
outer and inner radius, so the image is `2n` spiral windows meeting at `2n` vertices. A
five-pointed star has 10 windows; an eight-pointed star has 16; a sixteen-pointed asterisk
has 32. (An asterisk's bars contribute two long edges each, so the count is twice the
number of points.) The rosette is centred on the image of the star's centre,
at `r = R(1 − v_centre/2)` (usually `3R/4`), not on the pole.

An axis-aligned cross (`+`) is different: its four arms are horizontal/vertical bars, so it
becomes four **annular sectors** meeting at the centre, not a rosette. A diagonal cross
(`×`) has four slanted bars, so it becomes four spiral windows; the Segoe `×` has 12 edges
because the ends are chamfered, and the probe shows 12 short windows rather than 4 long
ones. This distinction — rectilinear cross = annuli, diagonal cross = spirals — is a good
test of the dictionary.

### 4.5 Circles, ellipses and rings

**41 circle entries and 17 ellipse entries.** The main runs:

| Range | Characters | Reading |
|---|---|---|
| U+25CB, U+25CC, U+25CE–25D3 | ○ ◌ ◎ ● ◐ ◑ ◒ ◓ | circle, dotted circle, bullseye, disc, half-filled circles |
| U+25D6–25D9 | ◖ ◗ ◘ ◙ | half discs and inverse bullets |
| U+25E6, U+25EF | ◦ ◯ | white bullet, large circle |
| U+26AA–26AC | ⚪ ⚫ ⚬ | medium white/black/small circles |
| U+2B24, U+2B55–2B58 | ⬤ ⭕ ⭖ ⭗ ⭘ | large and heavy circles/ovals |
| U+2B2C–2B2F | ⬬ ⬭ ⬮ ⬯ | black/white horizontal/vertical ellipses |
| U+1F784–1F78B | 🞄 🞅 🞆 🞇 🞈 🞉 🞊 🞋 | bold/light circles and round target |
| U+29BE/29BF, U+2A00 | ⦾ ⦿ ⨀ | circled bullet, n-ary circled dot |
| U+233E, U+2365 | ⌾ ⍥ | APL circle jot / circle diaeresis |
| U+3036, U+FFEE | 〶 ￮ | circled postal mark, halfwidth white circle |

**Warp image.** Each circle is a **polar ellipse** (§3.2). A ring (`ncirc = 2`) gives two
nested polar ellipses — a band; a bullseye (`ncirc = 3` or 4) gives three or four nested
curves. A half-filled circle (`◐`) is one circle contour plus one half-disc contour; the
image is a polar ellipse plus a filled half-polar-ellipse. None of these is a circle.

Measured circle quality (max radial deviation, % of radius; lower is better):

| font | ○ | ● | ◎ | ◉ | ⬤ | ◯ |
|---|---:|---:|---:|---:|---:|---:|
| Cambria Math | 0.04 | 0.14 | 0.12 | 0.12 | — | 0.27 |
| Yu Gothic | 0.06 | 0.06 | 0.06 | 0.06 | — | 0.06 |
| Yu Mincho | 0.06 | 0.06 | 0.06 | 0.06 | — | 0.04 |
| Consolas | 0.07 | 0.26 | — | — | — | — |
| Lato | 0.05 | 0.10 | — | — | — | — |
| Segoe UI Symbol | 0.10 | 0.10 | 0.10 | 0.10 | 0.20 | 0.28 |
| Lucida Sans Unicode | 0.17 | 0.22 | 0.17 | 0.17 | — | — |
| Arial / Times / Courier | 0.30 | 0.30 | — | — | — | — |
| Meiryo | 0.95 | 0.30 | 0.34 | 0.20 | — | 0.29 |
| MS Gothic | 0.39 | 0.48 | 0.41 | 0.55 | — | 0.18 |
| SimSun | free | free | free | — | — | — |

The "free" entries are 1.2 % or worse and fail the rule. Cascadia Code's large ○ is 1.4 %
and likewise fails; its many small circular dots are fine (median 0.20 %). If a circle
must be as exact as possible, use Cambria Math or Yu Mincho; if it must be widely
available, Segoe UI Symbol; if it must be a *true* circle after warping, use a horizontal
edge instead.

### 4.6 Dots, braille and dot grids

- **Braille Patterns U+2801–28FF (255).** Every non-blank pattern: one to eight dots in a
  2×4 grid. The blank U+2800 has no contours and is not catalogued.
- **Dice U+2680–2685 (⚀–⚅) are a near-miss, not catalogue entries.** The square face is
  exact, but in every scanned face the pips are 12-segment *rounded squares* (squircles),
  not circles; the glyph therefore has a significant freeform contour and is rejected. The
  square face alone is usable as a rectilinear source; the pips are not exact circles.
- **Dot groups.** U+2024–2027 (one/two-dot leader, ellipsis, hyphenation point),
  U+2056, U+2058–205C (three/four/five-dot punctuation, dotted cross),
  U+205D/205E (tricolon, vertical four dots), U+2E2B/2E2D/2E3D, U+22EE/22EF
  (vertical/midline ellipsis), U+00A8 (diaeresis), U+2AF6 (triple colon operator), U+2E31/2E33.

**Warp image.** Each dot is a small polar ellipse. Braille is the most useful case: the
2×4 grid at `u = 0.192/0.808`, `v = 0.121/0.379/0.625/0.879` (Segoe) maps to **two angular
columns** at `θ = π + 2π·0.192` and `π + 2π·0.808`, and **four radii** `r = R(1 − v/2)`.
The dots are circular in font units but their `u` and `v` radii differ after normalization
(`r_u = 0.192`, `r_v = 0.121`), so the images are small ellipses even before the warp. A
braille pattern is therefore a **warped lattice of polar ellipses** — the closest thing in
Unicode to a regular point set.

### 4.7 Trigrams and parallel bars

**10 entries.** The eight trigrams U+2630–2637 (☰☱☲☳☴☵☶☷) and the two monograms
U+268A/268B (⚊⚋). Each trigram is three horizontal bars; a broken bar is two half-width
bars with a gap at `u = 1/2`.

**Warp image.** Three concentric annuli at the three bar heights; a broken bar becomes two
annular sectors separated by the gap angle `π` (half a turn). This is the cleanest
"multiple exact circles from one glyph" case: all radii and gap angles are rational. The
same construction works for U+2630's neighbours and for any stacked-bar glyph (U+2261 ≡,
U+2263 ≣, U+2A68/2A69, U+2058/2059, U+23BA–23BD scan lines).

### 4.8 Compounds: circled operators, alchemical and technical diagrams

**82 compounds** are catalogued. They are glyphs whose contours mix polygons with circles,
ellipses or caps. The main groups:

- **Circled operators and relations** (U+2295–229D, U+22BB–22BF, U+2A01/2A02,
  U+2A36–2A3B, U+2A51–2A52, U+2A66–2A67, U+2A79–2A7A, U+2A97/2A98): a circle plus a
  cross, bar, dot, asterisk or relation sign.
- **APL functional symbols** (U+2339, U+233B, U+235B/235C, U+235D, U+2361–2364, U+2369,
  U+236E): quad + circle, jot, diaeresis, underbar.
- **Suns and signals** (U+2600/2604/263C, U+26D4, U+26DA): a circle plus rays or a bar.
- **Alchemical symbols** (32): U+1F702, 1F704–1F705, 1F70A–1F70E, 1F719, 1F71E, 1F732,
  1F737, 1F739, 1F73F–1F740, 1F742–1F746, 1F74E, 1F750, 1F754–1F755, 1F757–1F75A,
  1F767–1F76A, 1F771. They are line-and-circle diagrams: a circle with a cross, a
  triangle, a bar or another circle.
- **Technical and APL shapes** (34): U+2336–2339, U+2343–2346, U+234C, U+234F,
  U+2352–2356, U+235D/235E, U+2360, U+236F, U+2386/2387, U+238D, U+238F–2396, U+23B7,
  U+23CE/23CF, U+2B97, U+2BFF.

**Warp image.** The union of the images of the parts. A circled plus is a polar ellipse plus
four annular sectors; a circled dot is a polar ellipse plus a small polar ellipse; an
alchemical "gold" (circle + centre dot) is two nested polar ellipses. The construction is
exact for the polygon parts and font-approximate for the circle parts.

### 4.9 The curved-stroke supplement (25 manual entries)

The automatic rule rejects a thin curved stroke because its closed outline goes out along
one edge and back along the other, so its net turning about any centre is near zero. These
25 glyphs are unambiguous geometric figures and are added by hand:

| Code points | Shape | Warp image |
|---|---|---|
| U+2312, U+2313 | arc, segment | one arc of a polar ellipse |
| U+2322, U+2323 | frown, smile | one arc of a polar ellipse |
| U+23DC, U+23DD | top/bottom parenthesis | one arc of a polar ellipse |
| U+256D–2570 | four quarter-circle box corners | a quarter arc of a polar ellipse |
| U+25DC–25DF | four quadrant circular arcs | a quarter arc of a polar ellipse |
| U+25E0, U+25E1 | upper/lower half circle | a half arc of a polar ellipse |
| U+25A2 | square with rounded corners | four rays/arcs + four corner arcs |
| U+25D4, U+25D5 | circle with one quadrant black | polar ellipse + filled sector |
| U+25F4–25F7 | white circle with one quadrant | polar ellipse + sector gap |
| U+25DA, U+25DB | inverse half white circle | half disc / half polar ellipse |

These are the only manual additions. Curved parentheses `(` `)`, braces `{` `}`, the
integral signs and the curved arrows are *not* added: their outlines are freeform curves,
not circular arcs, and their warp images are not a standard primitive.

## 5. Fonts

The 29 measured faces were chosen for coverage and design diversity. 379 installed faces
contain at least one of the scanned code points; the other ~350 cover at most 102 code
points (the Geometric Shapes block), so they only vary the basic circles, squares and
triangles. The symbolic fonts — Wingdings, Wingdings 2/3, Webdings, Symbol, Marlett,
Segoe MDL2 Assets — have **zero** coverage of these Unicode blocks; their geometric icons
live at ASCII or private-use code points and are a separate, font-specific route.

| Face | cps present | geometric* | axis | circular contours | median dev | best dev |
|---|---:|---:|---:|---:|---:|---:|
| Segoe UI Symbol | 3,403 | 2,041 | 475 | 1,942 | 0.63 % | 0.04 % |
| Cambria Math | 1,660 | 867 | 214 | 173 | 0.21 % | 0.04 % |
| Meiryo | 1,579 | 819 | 339 | 365 | 0.40 % | 0.05 % |
| MS Gothic | 1,489 | 759 | 300 | 368 | 0.23 % | 0.18 % |
| Cascadia Code | 849 | 645 | 214 | 1,082 | 0.20 % | 0.11 % |
| MS Mincho | 1,494 | 598 | 260 | 414 | 0.77 % | 0.18 % |
| Lucida Sans Unicode | 887 | 554 | 257 | 87 | 0.22 % | 0.06 % |
| Yu Gothic | 993 | 414 | 201 | 336 | 0.09 % | 0.04 % |
| Microsoft YaHei | 713 | 369 | 209 | 85 | 0.37 % | 0.22 % |
| Consolas | 507 | 304 | 173 | 136 | 0.31 % | 0.07 % |
| Yu Mincho | 958 | 299 | 168 | 380 | 0.08 % | 0.04 % |
| SimSun | 636 | 237 | 170 | 28 | 0.41 % | 0.41 % |
| Arial | 379 | 179 | 110 | 30 | 0.29 % | 0.13 % |
| Times New Roman | 568 | 197 | 110 | 175 | 0.36 % | 0.06 % |
| Century Gothic | 324 | 193 | 84 | 100 | 0.31 % | 0.09 % |
| Verdana | 281 | 140 | 49 | 13 | 0.32 % | 0.17 % |
| Georgia | 257 | 54 | 28 | 26 | 0.63 % | 0.17 % |
| Calibri | 362 | 19 | 10 | 71 | 0.28 % | 0.07 % |

\* "geometric" is the number of code points whose outline decomposes into P/C/K primitives
*before* the semantic filter; it therefore includes letters and enclosed alphanumerics.
"axis" is the number of rectilinear glyphs. "circular contours" and the two deviation
columns are over all circles in the face, including small dots; they are a quality guide,
not a per-glyph guarantee. `Cambria` and `Cambria Math` are two faces of the same TTC and
have identical symbol coverage; the table lists Cambria Math only.

**Recommendations.**

- **Widest choice, best default:** Segoe UI Symbol. It has 3,403 of the 3,644 code points,
  2,041 geometric glyphs, and 0.04 % best / 0.63 % median circles.
- **Cleanest circles:** Cambria Math (0.04 %), Yu Gothic and Yu Mincho (0.06 %), Lato
  (0.05 % on ○). For a polar-ellipse construction where the circle is the main shape, these
  are the best starting points.
- **Crisp box drawing and exact polygons:** Segoe UI Symbol, Consolas, Cascadia Code. All
  are exact; Cascadia's *large* ○ is 1.4 % and is rejected, but its small dots are the
  cleanest in the set (median 0.20 %).
- **CJK and fullwidth forms:** MS Gothic, Meiryo, Yu Gothic, Microsoft YaHei. MS Gothic
  draws the four rounded box corners as polygonal approximations; the manual supplement
  covers them.
- **Avoid for circles:** SimSun (1.2 % ●), Cascadia Code large circles (1.4 %), Batang
  (0.65 %), Georgia (0.63 %). For straight polygons they are fine.
- **Basic shapes only:** Arial, Times New Roman, Courier New, Verdana, Georgia and Calibri
  have 19–197 geometric glyphs, essentially the Geometric Shapes block. They are useful for
  a consistent Arial/Times look, not for coverage.

## 6. Worked examples (exact coordinates, `R = 1`)

All examples use a **single glyph filling the ink box**; `R = 1` is the half-width. The
pole is `C = (0,0)`; `θ` is measured from the positive x-axis, and the 9 o'clock seam is
`θ = π`. `ψ` is the spiral parameter.

| Glyph | Font | Ink | Exact edges | Warped image |
|---|---|---|---|---|
| `■` U+25A0 | Segoe | 1434² | H `v=0 → r=1`; H `v=1 → r=0.5`; V `u=0,1 → θ=π` | annulus `0.5 ≤ r ≤ 1`, seam at 9 o'clock |
| `□` U+25A1 | Segoe | 1434² | outer as `■`; inner H `v=0.086 → r=0.957`, `v=0.914 → r=0.543`; inner V `u=0.086,0.914` | outer annulus + inner band `0.543–0.957`, gap 62.3° |
| `─` U+2500 | Segoe | 1044×134 | H `v=0 → r=1`; H `v=1 → r=0.5`; V `u=0,1 → θ=π` | annulus `0.5–1` (single glyph) |
| `│` U+2502 | Segoe | 134×1941 | H `v=0 → r=1`; H `v=1 → r=0.5`; V `u=0,1 → θ=π` | annulus `0.5–1` (single glyph) |
| `═` U+2550 | Segoe | 1044×402 | H `v=0 → r=1`, `v=0.333 → r=0.833`; H `v=0.667 → r=0.667`, `v=1 → r=0.5` | two annuli `0.833–1` and `0.5–0.667` |
| `☰` U+2630 | Segoe | 1463×1434 | three bars at `v=0–0.12`, `0.439–0.559`, `0.88–1` | three annuli `0.94–1`, `0.721–0.781`, `0.5–0.56` |
| `▲` U+25B2 | Segoe | 1604×1434 | H `v=0 → r=1`; two S windows `ψ∈[π,2π]`, `λ=0.1592` | full circle + two spirals; apex `r=0.5, θ=2π`, cusp `θ=π` |
| `◢` U+25E2 | Segoe | 1434² | V `u=1 → θ=3π`; H `v=0 → r=1`; S `ψ∈[2π,4π]`, `λ=0.0796` | unit circle + radial seam + one spiral |
| `╱` U+2571 | Consolas | 1126×2398 | two S windows `ψ∈[5.390,10.781]`, `λ=0.0928`; two end arcs of 51.15° | two parallel spirals joined by short arcs at `r=0.5` and `r=1` |
| `⊕` U+2295 | MS Gothic | 112² | circles `r=0.500` and `0.437`; 11-edge cross | polar ring + a cross-shaped band of arcs/rays |
| `○` U+25CB | Segoe | 1484² | circles `r=0.500` and `0.416` | two nested polar ellipses |
| `●` U+25CF | Segoe | 1484² | circle `r=0.500` | one polar ellipse (filled disc) |
| `⠿` U+283F | Segoe | 911×1446 | six dots at `u=0.192,0.808`, `v=0.121,0.504,0.879` | six polar ellipses on a 2×3 lattice |

Two checks on the table:

- `▲` is a good test. The base is the full circle `r=1`; the two slanted edges are the
  same window `[π,2π]` (one rising, one falling), and they meet at the apex
  `u=0.5, v=1 → r=0.5, θ=2π`. The base corners `u=0` and `u=1` both land on `θ=π`; that is
  the cusp. The image is a teardrop wrapped once around the pole.
- `╱` is the parallelogram test. The two long edges are the same window, rotated relative to
  each other by a rational angle; the two short edges are arcs at `r=0.5` and `r=1`. This
  is the cleanest "two congruent spirals from one glyph" example, and it needs no mirroring:
  the other diagonal gives the opposite chirality.

## 7. What is not in the catalogue

**1,314 code points are not automatically decomposable** (they have a significant freeform
contour, or no geometric decomposition at all); 25 of them are rescued by hand. **397**
automatic geometric glyphs are excluded by the semantic scope. The main groups:

- **Letters and digits (225 + 59 present).** Many are geometric in some faces: `O` is a
  0.48 % circle in Century Gothic, `I`, `L`, `T` and `E` are rectilinear, `V`, `X`, `Y`,
  `K`, `M`, `N`, `Z` are polygons, `o` is a 0.71 % circle in Courier New. They are excluded
  because they are typeface-dependent letterforms, not symbols. The CSV flags them
  (`kind = letter`/`digit`); a user who wants letter shapes can filter on those flags.
- **Enclosed alphanumerics (170 present).** `①`, `Ⓐ`, `ⓐ`, `❶`, `➀`, … are a circle (or
  square) plus a letter or digit. The enclosing circle is a usable geometric primitive, but
  the enclosed glyph is not, so the compound is not a clean figure. Use `○` or `□` directly.
- **Non-figure punctuation (373 present: 256 `punct` + 117 `geopunct`; 103 kept).** Commas, quotes, apostrophes,
  exclamation marks, question marks, pilcrows, daggers, currency letters and the like are
  excluded. The kept punctuation is the geometric part: dashes, bars, bullets, ellipses,
  dot groups, primes, angle quotes, `#`, `+`, `=`, `<`, `>`, U+007C, `/`, `\`, `_`, `^`, `×`,
  `÷`, `±`, `°`, `·`, `•`, `…`, `‖`, and the halfwidth/fullwidth equivalents.
- **Freeform icons.** Hearts, faces, chess pieces, card suits, musical notes, weather,
  zodiac, recycling marks, vehicles, hands, clocks and the like are excluded because their
  outlines are not decomposable into the primitives. Many contain a circle (a sun, a clock
  face, a smiley) and could be used as approximate circle sources; they are recorded in the
  CSV with `tier = X` and a `big_circle` flag.
- **Curved arrows and parentheses.** Their shafts are freeform strokes, not arcs. They are
  visually curved and would be useful, but they are not exact under the rule (§4.3, §4.9).
- **The wave glyph 〰 U+3030.** It is the original subject of the warp notes and is
  deliberately not in the geometric catalogue: its edges are normal offsets of a sine, no
  installed glyph has exact vertical-shift sine edges, and the warped edges are
  transcendental polar graphs. The best pure-rose fit to an edge is 1.26 % of `R`; the only
  exact roses are images of the *spine*, which no UI operation produces. See
  `SUMMARY-part1.md`, `G.md`, `WP.md` and `M.md`.
- **Unmeasured presets.** Only Warped Circle, Arch: Warped and Arch: Warped Down were
  measured. The other Transform presets have different maps (or no map) and are not covered
  by the dictionary. The `W.md` spiral windows for the two arches are derived from the same
  map model, not separately measured on straight edges.

**Font caveats.** A glyph can be exact in one face and approximate in another: `□` is a
4-edge rectangle everywhere, but `●` is a 0.06 % circle in Yu Gothic, a 0.48 % circle in MS
Gothic and a 1.2 % near-circle in SimSun. The CSV's `font` column is the best face for that
code point under the ranking (P before C before K; within P the axis-aligned and simplest;
within C the lowest circle deviation); it is not a claim that the other faces fail.

## 8. Files and reproduction

- `GLYPH-CATALOGUE.md` — this document.
- `GLYPH-INDEX.md` — the complete run-by-run index, grouped by family.
- `glyph-catalogue.csv` — 3,644 rows, one per code point present in at least one face.
  Columns: `cp` (decimal), `cp_hex` (`U+` form), `char`, `name`, `block`, `kind` (symbol/geopunct/punct/letter/digit/
  enclosed/format), `keep` (1 = catalogue entry), `tier` (P/C/K/M/X), `gcls`
  (axis/polygon/circle/ellipse/dots/compound/arc/sector/semicircle/rounded/mixed), `family`,
  `font` (best face), `npoly`, `ncirc`, `nell`, `narc`, `ncap`, `nsliver`, `ndots`,
  `ncontours`, `circ_font`, `circ_dev` (%), `nfonts` (faces with the code point), `ngeo`
  (faces with a geometric version), `manual`.
- `glyphscan.py` — the classifier and scan driver. It uses `fontTools` and the Windows font
  paths in its `FONTS` list; the 29 faces are the ones in §5.
- `glyphwarp.py` — the exact warp-coordinate probe used for §6. It prints the normalized
  `(u, v)` edges and their images for any `(font, code point)`.

The classifier's rule is reproducible but not canonical: a different threshold (1 % versus
2 %), a different treatment of caps, or a different semantic scope will move the count by a
few hundred. The CSV keeps the raw deviation and primitive counts so the rule can be
re-run without rescanning the fonts.

## 9. Open questions

1. **Row composition.** The map is measured for a whole row's ink box. A mixed row (a bar
   next to a tall glyph), mixed font sizes, baseline shift and character spacing all change
   `u` and `v` and therefore the radii and windows. `W.md` treats these as open; a single
   PowerPoint probe per case would settle them.
2. **Text direction and rotation.** A 90°/270° text direction swaps the roles of `u` and
   `v`; the ink-box normalization under rotation was not measured.
3. **The unmeasured presets.** The catalogue says nothing about Circle Pour variants, Wave,
   etc. Each needs its own map probe.
4. **Exactness of the font circles.** Even the 0.03 % circles are Béziers. A user who needs
   an exact circle must use a horizontal edge; the catalogue cannot supply one from a
   circle glyph.
5. **Curved strokes.** The 25 manual entries cover the clear arcs; curved arrows,
   parentheses and the box-drawing arc corners in fonts that draw them as multi-segment
   polygons are not systematically covered.
6. **The remaining ~350 faces.** They were not scanned. They cover at most the basic
   Geometric Shapes block, but a face with an unusual circle or square design could matter
   for a specific look. The scan is cheap enough to extend.
