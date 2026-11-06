# Stream M: exact warped curves of the sine glyph 〰, and whether P(spine) can be recovered

Math stream of `pptc/PLAN-warp-sine.md`. No PowerPoint driving, no Lean/Defs edits, nothing committed.
Inputs: `notes/warp/G.md` (glyph model), `notes/warp/WP.md` (PowerPoint probe, landed before step (c)),
`notes/spiral/F1.md`, `W.md` (warp map). Labels: [Proof] [Wolfram] [Measured] [Heuristic] [Open].
Backends: every identity and number below is **Wolfram MCP** unless stated; the one Python item (font
outline of ●, fontTools + numpy, observation only) is labelled. Scratch: `...\scratchpad\warp_M\circ.py`.
Units: `R` = outer guide radius; `pt` figures use R = 144 pt (WP's box), so 1 % of R = 1.44 pt.

## Findings summary

1. **No exact route to P(spine) exists with the project's operations. [Proof]** Two independent arguments:
   - *Algebraicity.* P(spine) is an algebraic curve (a rose, degree 4n+2 for a row of n glyphs). Both
     warped edges P(E±) are **not algebraic**, not even on any sub-arc (Proposition T, section 2.2). Every
     available operation is either an invertible algebraicity-preserving map of an existing curve (translate,
     rotate, `scale_x/y`, `offset`, stroke + EMF) or takes a sub-arc or boundary piece of existing curves
     (`restrict`, `arc_of_length`, Merge Shapes, Edit Points path splitting; boundary lemma, section 2.3), or
     yields only numbers (`inter_x/y`, `arc_length`, boxes). So no sequence starting from the warped band can
     output an arc of P(spine). Only the base algebraic curves could, and they do not contain the band.
   - *Non-commutation.* The warp is not conformal, so the plane offset of a warped edge is not P of the
     offset: distance from P(E+) to P(spine) varies, e.g. 4.73 to 5.86 % of R (n = 1, Circle) [Wolfram].
2. **Why the text-level tricks fail.** WP measured that Text Outline is stroked **after** the warp, at constant
   plane width [Measured, WP]. So the deck's "stroke the top edge at width w" trick is the plane offset of a warped
   edge, section 2.1 case A. The pre-warp case B is moot (it would only give the exact spine as a degenerate
   zero-width hole at one tuned width, section 2.4), and WP also found that no UI path warps a freeform.
3. **Exact curves (a).** With the idealised glyph (spine `v = 1/2 + α cos 2πmu`, α = a/H = 0.4054, edges
   normal offsets, end cuts vertical, ink box H = 2a + w) the spine image is the rose
   - Warped Circle: `r = 3R/4 + (αR/2) cos(mφ)`, m = 2n, polar angle φ (counter-clockwise from 3 o'clock);
   - Arch: Warped: `r = 3R/4 + (αR/2) cos(2mφ)`, φ in [0, π]; Arch: Warped Down: `r = 5R/8 + (3αR/4) cos(2mφ + π)`,
     φ in [π, 2π].
   Numbers: `α R/2 = 0.2027 R` (WP measured 0.2022 R). Never m = 1 (a limaçon), because 〰 carries 2 periods.
   Edges are explicit closed forms, section 1.3; r_± depends on φ only through `mφ`.
4. **Gaps for the record (c)**, Circle, % of R (n = 1, 2, 3, 4): best constant plane offset of an edge toward
   P(spine): 0.57, 0.33, 0.73, 1.06; medial axis of the warped band (the equidistant locus, the best that offsets can
   do): 0.10, 0.12, 0.28, 0.55; radial midpoint of the two edges: 0.119 for every n (0.17 pt); best pure rose to a
   single edge: 0.935 for every n (1.35 pt). All below the 2.8 to 5.4 % of R of F1's spirals, none exact.
5. **By-products (d).** Warped edges are transcendental closed polar graphs with dihedral symmetry D_m. The ●
   crescent is a polar ellipse, transcendental; and ● in the installed fonts is a quadratic-spline approximation
   (0.10 to 0.30 % of radius off a circle), so it is not idealisable either.

## 0. Conventions

Glyph units (em 2048): spine `y = c + a cos(2π x/Wp)`, Wp = 1024, a = 158.8, band normal width w = 74.08,
H = 2a + w = 391.68 (G measured 393; the 1.4-unit difference is quantisation, it moves α by 0.001),
δ = w/H = 0.1891, α = (1 − δ)/2 = 0.4054. Row of n glyphs: abutting (advance = ink width, WP), Wt = 2048n,
m = 2n periods, whole-row ink box. Slope amplitude κ = 2πa/Wp = 0.97438. Ink fractions `u = x/Wt`,
`v = (y − y_min)/H`; v = 0 at the bottom-edge trough, 1 at the top-edge crest.

Preset maps `z = C + r e^{iφ}` (plane y up), from F1/WP:

| preset | φ(u) | r(v) |
|---|---|---|
| Warped Circle | π − 2πu (clockwise from 9 o'clock) | (R/2)(1 + v) |
| Arch: Warped (= Warped Button, one line) | π − πu | (R/2)(1 + v) |
| Arch: Warped Down | π + πu | R − (3R/4) v (ink top to R/4) |

## 1. (a) Exact warped curves

### 1.1 Spine image [Proof, checked in Wolfram]

Circle: `r = (R/2)(3/2 + α cos 2πmu)` and `cos(2πmu) = cos(m(π − φ)) = cos(mφ)` because m is even. Hence
`r = a_L + b_L cos(mφ + φ_0)` with `a_L = 3R/4`, `b_L = αR/2 = (1 − w/H)R/4`, `φ_0 = 0`.
Wolfram check, 30 digits, n = 1..4, five parameter values each: pipeline "glyph point -> (u, v) -> (r, φ)"
minus the rose formula is below 1e-39.

| preset | a | b | m_eff, φ_0 | window |
|---|---|---|---|---|
| Circle | 3R/4 | αR/2 | m = 2n, 0 | full turn, closed |
| Arch: Warped | 3R/4 | αR/2 | 2m = 4n, 0 | φ in [0, π], m = 2n periods |
| Arch: Warped Down | 5R/8 | 3αR/4 (sign: crest toward the inner circle) | 2m = 4n, π | φ in [π, 2π] |

(Arch: `cos(2πmu)` with `u = (π−φ)/π` gives `cos(2m(π − φ)) = cos(2mφ)`, frequency 2m = 4n in φ over a half turn,
i.e. m = 2n periods. WP quotes "m = 4n" for the arch presets, the same frequency.)

Generalisation (extra ink in the row so that 〰 occupies ink fractions `u in [u0, u0+f]`, `v in [v0, v0+h]`;
[Proof], not probed): Circle `r = (R/2)(1 + v0 + h/2) + (R h α/2) cos((m/f)(φ − φ_1))`, `φ_1 = π − 2πu0`,
valid on an arc of angular length 2πf. Rational `m/f` gives roses with rational frequency (partial arcs). A limaçon
(`m/f = 1`) needs `f = m`, i.e. only the full-turn single-period case; 〰 with m = 2n needs f = 2n > 1: impossible.
So **no limaçon from 〰 in any row** (agrees with WP); with f < 1 the frequency only goes up.

Degree [Proof]: `r = A + B T_m(x/r)`, m even, gives `r (x²+y²)^{m/2} = A (x²+y²)^{m/2} + B Q(x, x²+y²)`, whence
after squaring an algebraic curve of degree 2m + 2 = 4n + 2. For n = 1: `(x²+y²)³ = ((A+B)x² + (A−B)y²)²`, a sextic,
**irreducible** over Q(A, B) [Wolfram FactorList: one factor]. It is a closed convex-ish loop (B/A = 0.27 < 1, never
touches C). Arch rose: same with m replaced by 2m on an arc.

### 1.2 Anisotropy of the map (why offsets do not commute)

Local scale per glyph unit: radial `(R/2)/H` (Circle, Arch Up), `(3R/4)/H` (Arch Down); tangential `2πr/Wt`
(Circle), `πr/Wt` (arches). Ratio tangential/radial `η`: Circle `2.403 (r/R)/n`, Arch Up `1.202 (r/R)/n`,
Arch Down `0.801 (r/R)/n` [Wolfram arithmetic]. `η` depends on `r`, so P is **never conformal** [Proof] (a conformal
polar map must be log-polar). It is nearly a similarity only where `η ≈ 1` on the band (`r/R ≈ 0.7 to 0.9`):
Circle n = 2, Arch Up n = 1. This is exactly where the gaps in section 3 are smallest.

### 1.3 Edge images [Proof; closed forms checked against the direct normal offset, 1e-37]

Let `τ = 2πmx/Wt in [0, 2πm]` (spine parameter), `s = sin τ`, `q = √(1 + κ² s²)`, σ = +1 top edge, −1 bottom edge.
Glyph-space edge: `X_σ = Wp τ/(2π) + σ (w/2) κ s/q`, `Y_σ = c + a cos τ + σ (w/2)/q`
(normal offset; arithmetic: `s_slope = −κ s`). Ink fractions
`u_σ = τ/(2πm) + σ (wκ/(2 m Wp)) s/q`, `v_σ = 1/2 + (a cos τ + σ (w/2)/q)/H`.
Image: `z_σ(τ) = C + r(v_σ) e^{iφ(u_σ)}` with the table above. Explicitly Circle:

`φ_σ = π − τ/m − σ (π w κ/(m Wp)) s/q`, `r_σ = (R/2)[3/2 + (a cos τ + σ (w/2)/q)/H]`.

Consequences:
- `m φ_σ ≡ −(τ + σ c_0 s/q) (mod 2π)` with `c_0 = π wκ/Wp` independent of n, and `r_σ` independent of n. So every row
  curve is `r = f_σ(mφ)` with one universal 2π-periodic f_σ (n only sets the frequency). [Proof]
- Symmetry: D_m (rotations by 2π/m, reflections in the crest and trough rays), exactly, in the ideal model.
- Ends: cut at u = 0, 1 is the radial segment from `r(v_-)` to `r(1)` (Circle: both ends on the 9 o'clock ray, the
  seam; WP measured r = 130.63 to 144 pt).
- Edge to edge: `P(E+)`, `P(E-)` are not related to P(spine) by a fixed shift: distance from P(E±) to P(spine)
  ranges over (% of R) n=1 [4.73, 5.86], n=2 [4.23, 4.86], n=3 [3.31, 4.73], n=4 [2.65, 4.73]
  (min = Rδ/4 = 4.73 % at the extrema, where the normal is radial).

## 2. (b) Recovery of P(spine)

### 2.1 Plane offsets and strokes

- **Case A (the real one, WP finding 2):** the stroke of width ws is the plane offset of the warped outline.
  Pushing P(E+) inward by d: the offset curve meets the ray through the crest at `r_crest − d` and the spine
  point on that ray is `r_crest − Rδ/4`, so d would have to be `Rδ/4 = 0.0473 R`. But at the steep points the
  nearest spine point is 0.0584 R away (n = 1), so the offset cannot be P(spine). Numerically the best constant d is
  below, with error. The same holds for the bottom edge, for both edges at once, and for the stroke's two inner
  boundaries (they cross at distance d(τ) that varies, 0.0473 to 0.0584 R for n = 1).
- General proof (does not depend on numbers): offset of a non-algebraic arc is non-algebraic (the offset by −d of the
  offset by d returns the arc, and parallel curves of algebraic curves are algebraic), and P(spine) is algebraic.
  [Proof, Proposition T + section 2.3.]
- **Medial axis** of the band (centre of the maximal inscribed disc, equals the locus where the two inward offsets
  meet): it is **not** P(spine), by 0.10 to 0.55 % of R (section 3). So not even the degenerate "inner offset at
  half the local width" gives it, and half the local width is not constant (n = 1: 4.73 to 5.84 % of R) so no single
  stroke width could do it anyway.
- **Case B** (pre-warp stroke, hypothetical; WP shows PowerPoint does not do this). In glyph space the whole-contour
  stroke of width ws has inner hole `spine ± (w − ws)/2 n`. At ws = w exactly the hole degenerates to the spine
  itself, doubly covered by the stroker's two inner offset paths. Warped, these would be P(spine) twice. So the
  *only conceivable* exact route is "pre-warp stroke at ws = w exactly, EMF convert, keep the doubled inner path";
  it needs ws to equal the glyph's width exactly (same calibration idealisation as the deck's 6 pt), a stroke that is
  distorted by the warp, and an EMF that keeps degenerate inner paths. WP measured the stroke after the warp at
  constant width, so this is **dead [Measured, WP]**; I record it only so that a future PowerPoint version or a
  different effect (e.g. a Shape Outline on text converted differently) can be tested against it. For ws < w the
  hole boundaries are `P(spine ± ε n)` with ε = (w − ws)/2, never P(spine).

### 2.2 Proposition T (the warped edges are transcendental) [Proof]

Statement. For every n and every preset, no arc of `P(E+)` or `P(E−)` (the ideal normal-offset model) lies on an
algebraic curve.

Proof. Put `z = e^{iτ}` and `F = C(z, q)`, `q² = 1 + κ² sin² τ = 1 − κ²(z − 1/z)²/4`, a finite extension of C(z), the
function field of a compact Riemann surface. Then `r_σ ∈ F` (non-constant), `g := κ s/q ∈ F` is non-constant and
has a **pole** at a zero τ* of `q` (there `s ≠ 0`). Let `E = e^{iφ_σ}`. In every preset
`E^k = (const) z^{-1} ω` for a suitable integer k (Circle k = m, arches k = 2m) with `ω = exp(−i c g)`, c a non-zero
real constant (section 1.3).
Suppose an arc of the edge lies on an algebraic curve P(x,y) = 0. Since (r, E) -> (x, y) is dominant, P(rcosφ, rsinφ)
is a non-zero polynomial Q(r, E); it vanishes on the arc, hence by analytic continuation along all τ in C. So r is
algebraic over C(E), hence over C(W) with `W = E^k = z^{-1}ω`.
Now `ω = exp(−icg)` is transcendental over F: it has an essential singularity at the pole of g, while elements
algebraic over F have only algebraic singularities on the compact surface. Hence `K = F(ω)` has transcendence degree
2 over C. But r ∈ F is non-constant, so F is algebraic over C(r), and `ω = W z` with z ∈ F: therefore K is algebraic
over C(r, W), whose transcendence degree is 1 when r is algebraic over C(W). Contradiction. ∎

Remarks. (i) Sub-arcs are covered (analytic continuation). (ii) The argument only uses "the edge is a graph whose
X-coordinate is linear in the spine parameter plus an algebraic function of e^{iτ}", so it holds for every normal-offset
band (any width w > 0, any spine that is itself a trigonometric polynomial). (iii) For a hypothetical vertical-shift
band the correction `g` would be constant and the edges would be roses; G found no such glyph.

### 2.3 Boundary lemma and the closure statement [Proof]

Let 𝒜 be the set of real-analytic arcs lying on no algebraic curve.
- Affine maps (`translate`, `rotate`, `scale_x/y`, including the independent axis scalings) are bijections that map
  algebraic curves to algebraic curves, both ways: they preserve 𝒜 and its complement.
- `offset` and stroke + EMF: the parallel curve at distance d of an algebraic arc is algebraic (elimination), and the
  offset by −d inverts the offset by d on a regular arc, so offset preserves both classes. Stroke caps and miter
  joins add only line segments and circular arcs.
- Merge Shapes (union, intersect, subtract, fragment, combine): for sets A, B, `∂(A∪B), ∂(A∩B), ∂(A∖B) ⊆ ∂A ∪ ∂B`.
  So every boundary arc of the result lies on an operand's boundary. The spine is an interior curve of the band and
  lies on no operand's boundary, unless an operand edge coincides with it, which section 2.1 and Prop. T rule out.
- `restrict`, `arc_of_length`, Edit Points open path / delete a whole segment: sub-arcs of the same analytic curve.
  (Deleting a node and letting PowerPoint refit a Bézier is not an exact operation of the project; a refit would
  produce a cubic, and the rose has degree ≥ 6.)
- `inter_x/y`, `arc_length`, `box_x/ymax`: output a real number, not a curve.
Hence every curve arising from the warped band lies in 𝒜 piece by piece, while P(spine) is algebraic. Corollary:
**no sequence of the listed operations produces an arc of P(spine) from the warped band.** The only remaining
possibility is that P(spine) is generated from the base algebraic curves alone; that has nothing to do with the
warp and is a question for part 2 [Open]. I note that the n = 1 rose is an irreducible bicircular sextic
`(x²+y²)³ = ((A+B)x²+(A−B)y²)²`, whereas the parallel curve of an ellipse has degree 8 and a `poly_graph`
(degree ≤ 6 in x, linear in y) cannot be it; the family that could in principle reach it is not obvious [Heuristic].

### 2.4 Specific routes asked for, with verdicts

| route | verdict |
|---|---|
| offset of a warped edge (any d, either edge) | not P(spine), [Proof] (T + 2.3); best constant d leaves 0.33 to 1.06 % of R, 2.1 |
| both edges: stroke inner boundaries / medial axis | not P(spine) [Proof, Wolfram 0.10 to 0.55 % R]; and only ever finite point sets via `inter_x/y` |
| midpoints of constructible chords (radial chords, same ray) | chord midpoint locus is **not** P(spine): 0.119 % R (0.17 pt), nonzero for every n; it equals P(spine) only at the extremal rays (s = 0) [Wolfram]. As a curve it is a locus of a continuum of intersections, which the constructors do not give (inter_x/y give one number at a time) |
| chords of normal glyph pairs | their images are Archimedean spiral arcs (W edge law); the pairing is by glyph-space normality, which the plane has forgotten; spiral-parameter midpoint = P(spine) but unobtainable |
| pre-warp stroke | A is what PowerPoint does (WP); B would give P(spine) only at ws = w, as a doubled degenerate path [Heuristic, dead per WP] |
| overlapping/stacked glyphs (negative spacing, baseline offset, superscript, line spacing) | union/intersection boundaries are pieces of E± and their shifts; best affine image of E+ onto the spine: vertical gap `Y_+(X) − y(X)` ranges 37.04 to 51.69 (w/2 = 37.04), best shift+scale leaves 7.32 units = 4.6 % of a [Wolfram]. Never the spine. A vertically shifted copy shares no boundary with the spine |
| half-period shifted copy, mirrored copy | mirror/shift of a band by half a period is its reflection about the midline, edges swap E+ <-> reflected E-; boundary pieces of E± only |
| multiple sizes in one row | changes (f, h, u0, v0) (section 1.1 generalisation), not the edge type |
| Edit Points: delete bottom nodes | keeps E+ (exact), yields E+ not spine (deck step) |
| Text Outline on warped text | constant plane width, after the warp [Measured, WP] |

### 2.5 Which individual points of P(spine) are constructible

- **At extremal rays** (crests and troughs, φ_k = π − kπ/m): the vertical glyph chord between E+ and E− at s = 0 is
  also the normal chord, and it maps to a radial segment; its midpoint is exactly the spine extremum
  `r = (r_+ + r_-)/2` [Proof]. Obtainable from the band: ray ∩ edges, midpoint (sums/quotients).
- At the **midline crossings** (τ = π/2 + kπ): spine point is `(3R/4)e^{iφ}`, φ = π − (2k+1)π/(2m), which needs only
  C, R, `cos`, `sin` of a rational multiple of π (P-constructible) [Proof, using `cos_Pconstructible`].
- In fact **every point of P(spine) at a P-constructible angle with P-constructible cos mφ** is a P-constructible
  point, directly from `r = a + b cos mφ` with `a = 3R/4`, `b = αR/2` (a and b are read off the band: b = half the
  midpoint-radius swing). So the band is not needed for the points, and no choice of finitely or countably many points
  gives a curve. A `cubic_bezier` through them is a cubic, not a degree 4n+2 rose.
- The warped edges themselves are constructible *transcendental* curves (if admitted as a primitive); their
  intersections with lines or circles solve transcendental equations in `mφ`, a different class from roses. For part 2.

## 3. (c) Gap table, for the record (user ruled approximations out) [Wolfram]

Ideal glyph above, R = 1, polylines of 3000 samples per period, nearest-point Euclidean distance. Max distances.
"Const offset" = best single plane offset d of the edge toward the spine (grid 0.0005 R); "medial" = equidistant locus
of the two warped edges, 35-step bisection per sample; "radial mid" = midpoint of the two edge radii on the same ray,
exact formula `((r_+ + r_-)/2 − r_spine)`; "rose" = minimax fit of `A + B cos mφ + C sin mφ` to one edge in r.

| preset | n | const offset d, error (% R) | medial axis error (% R) | notes |
|---|---|---|---|---|
| Circle | 1 | 0.053, 0.57 (top); 0.0525, 0.57 (bottom) | 0.103 | η ≈ 1.8 |
| Circle | 2 | 0.0455, 0.33; 0.0445, 0.37 | 0.121 | η ≈ 0.9 to 1.2: best |
| Circle | 3 | 0.040, 0.73; 0.0395, 0.78 | 0.281 | |
| Circle | 4 | 0.037, 1.06; 0.0365, 1.14 | 0.554 | |
| Arch Up | 1 | 0.0455, 0.32 | 0.086 | same as Circle n = 2 |
| Arch Up | 2, 3, 4 | 1.05, 1.44, 1.68 | 0.55, 1.04, 1.24 | |
| Arch Down | 1 | 0.059, 2.9 | 3.8 | strong shear |
| Arch Down | 2..4 | not reliable | not reliable | radial scale 20x tangential at r near R/4, distance caps hit [Open] |

- Radial midpoint of the two edges: 0.1193 % of R = 0.17 pt at R = 144, **independent of n** (r depends on mφ only)
  for Circle; agrees with WP's measured 0.17 pt [Measured vs Wolfram, same number]. First-order glyph-space estimate
  `(w²/8) y'' s²(s²−1)/(1+s²)²` gives 0.054 % (too small by 2.2 because higher-order terms in w are dropped; the exact
  numeric is the one reported).
- Best pure rose to a single edge: minimax residual **0.935 % of R** (1.35 pt) for every n, with `B = 0.2027` (same
  amplitude as the spine rose) and `A = 0.8066` (top) / `0.6934` (bottom), i.e. a centre shifted by 0.0566 R
  (a vertical shift of the spine by about 0.15 H, not w/2 = 0.095 H, because the best constant exceeds the
  extremum shift). WP's measured 1.26 % of R (LS, with bake noise) is consistent.
- Glyph-space gap, same statement: best vertical shift + vertical scale of E+ onto the sine spine leaves 7.32 units
  (4.6 % of a); G's best sine to an edge was 5.3 %.
- Idealisation tolerance for comparison: sine route's own accuracy 1 to 2 % of a (G), spiral edges 2.8 to 5.4 % of R
  (F1), warp bake between nodes 0.3 to 0.9 pt (WP). The best medial or radial-midpoint curve (0.1 to 0.2 % R) is
  below the baking noise; that is not an exactness claim.
- Is any warped edge exactly a recognisable curve? No: by Prop. T it is not algebraic, so it is not a limaçon, rose,
  trochoid, conchoid, Cassini etc. It is an analytic transcendental closed curve of the form `r = f(mφ)`; in the
  sense of the polar map it is "the image of an offset sine", with no classical name [Proof].

## 4. (d) By-products

- **Warped edges P(E±):** transcendental, simple closed polar graphs `r = f_σ(mφ)`, D_m symmetric, with two
  radial extrema per period (crest radius `R(3/4 + (a + w/2)/(2H)) = R` exactly, trough `R/2`), plus the end cut as
  a radial segment on the seam (Circle) or two radial segments (arches). The warped band is a wavy annulus (Circle), or a
  wavy arc strip (arches), whose radial width varies from `Rδ/2 = 0.0946 R` to `0.1318 R` [Wolfram];
  at R = 144 that is 13.6 to 19.0 pt (WP: 13.5 to 19.1).
- **Circle/arc extremes:** each extremum of an edge is a circular arc touching `r = const` (horizontal tangent), so
  `box`-type readings of an edge give exact radii `R, R(3/4 ± ...)` [Proof] (not new numbers).
- **The ● crescent** [Proof]. A circle of diameter D in the ink box (u, v) = ((x − x0)/D, (y − y0)/D) with
  centre (1/2, 1/2): `(u − 1/2)² + (v − 1/2)² = 1/4`. With `u − 1/2 = −φ/(2π)` (Circle) and `v − 1/2 = (2/R)(r − 3R/4)`:
  `(φ/π)² + ((r − 3R/4)/(R/4))² = 1`, which is the user's polar ellipse (their θ is φ + 2π). It is **transcendental**:
  if algebraic, then r (algebraic over C(φ)) would be algebraic over C(e^{iφ}), but φ = −i log E is transcendental
  over C(E). Pinch at φ = ±π (the seam), as observed. Arch Up: `(2φ/π − 1)² + ((r − 3R/4)/(R/4))² = 1` on [0, π]; Arch Down: r-centre 5R/8, semi-axis 3R/8 in r
  (same transcendence proof).
- **Is ● an exact circle in a font?** [Measured, Python fontTools + numpy, algebraic circle fit of the flattened
  quadratic splines] U+25CF: Segoe UI Symbol max deviation 1.04e-3 of the fitted radius (29 on-curve/control points),
  Cambria 1.36e-3, Consolas and Segoe UI 2.62e-3 (13 points), Arial 2.97e-3. All contours are TrueType quadratic
  Béziers (`qCurveTo` only). So ● is a Bézier approximation of a circle to 0.10 to 0.30 % of its radius, not an exact
  circle, and by the same reasoning as 〰 the crescent is not an exact polar ellipse: **the ● crescent is not
  idealisable under the user's rule either**. (The deviation is far smaller than 〰's 1 to 2 % spine error, but the
  rule is categorical.) U+2B24 in Segoe UI Symbol: 2.04e-3.
- Rectangles, triangles, slashes (spiral survey, W): circular arcs, radial segments, Archimedean spiral windows: all
  algebraic or classical transcendental, exact because the glyph edges are exact lines; unchanged by this stream.
  The 〰 glyph is the only candidate that brings an algebraic *rose* (via its spine), and the spine is not an edge.

## Open / what would change a verdict

- [Open] **Part 2 / base curves:** whether the sextic or higher rose can be generated by offsets/affine images of the base
  algebraic curves alone (ellipse, rectangle, `poly_graph`, `power_law`, `cubic_bezier`). Nothing here suggests it; it
  would not use the warp.
- [Open] **WP residual:** WP found the EMF stroke stays a line in this build. If a future conversion made the stroke a
  filled region, nothing changes: that region is the plane offset of the warped outline (case A), already covered.
- [Open] Case B (pre-warp stroke) only if a text effect other than Text Outline stroked before warp is found.
- [Open] Arch Down numerics for n >= 2 (shear), and non-square boxes; none change the algebraic argument.
- [Open] Fonts other than Yu Mincho/Yu Gothic (G: no installed glyph has exact vertical-shift edges). For a glyph
  with vertical-shift edges the warped edges **are** exact roses `a ± δ' + b cos mφ`, so Prop. T would not apply; if
  one exists it is the only exact route.

## Other things noticed

- The warped-edge radial function is independent of n: all rows of 〰 are the same curve f(ψ) pulled back by
  ψ = mφ. So measurements on n = 1 transfer, apart from the anisotropy of the plane distance.
- Circle n = 2 and Arch Up n = 1 are the near-isotropic cases (η ≈ 1); n = 2 gives the smallest const-offset gap
  (0.33 % R) of the circle rows. This is a useful row length if an approximate figure were ever wanted.
- The crest radius is exactly R and the trough exactly R/2 for the outer/inner edges: the top-edge crest is the ink-box
  top (v = 1) and the bottom-edge trough is v = 0. The spine rose lies strictly inside: crest `R(3/4 + αR/2·1/R)` =
  0.9527 R, trough 0.5473 R (α = 0.4054).
- Why G's 1 to 2 % spine error does not matter here: it perturbs a and the phase of the glyph spine, but the question
  of exact recoverability depends only on E± being normal offsets, which is the model G confirmed (0.5 % of H).
- In the Defs `offset` constructor the full band outline has corners (the vertical end cuts), so `hC1`/`hseam` block
  offsetting it whole; an edge would have to be isolated first (`restrict` or `arc_of_length`). That does not alter the
  verdict, only how the offset of an edge would be formalised.
