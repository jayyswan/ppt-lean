# NOTES X4 — audit of the formal constructors in `pptc/Pptc/Defs.lean`

Read `PLAN-jacobi-X0-overview.md` and `PLAN-jacobi-X4-defs-audit.md`. Research only; no
`.lean` file was created, edited or deleted. Scripts live in
`archived files/jacobi-scripts/` (`X4-01-bezier-loop.py`).

## Plain-language summary

1. I audited every constructor in `Defs.lean` for being more or less permissive than the
   drawing operation it models.
2. **No mismatch lets you reach `am`, and none can make every real number constructible.**
   The latter is impossible on cardinality grounds: every derivation is a finite tree built
   from finitely many rules whose only number seed is `1`, so `PConstructible` is countable.
3. The clear over-permissivenesses are all *degenerate cases* the geometry would not draw:
   scaling an axis by `0`, an inverted/zero-area `restrict` window, a Bézier with all four
   control points equal, an inward `offset` that closes a circle onto its centre, `x/0 = 0`,
   and `power_law` at exponent `0`.
4. In every one of those cases the set produced is a single point, an empty set, or a
   segment/line through **constructible** coordinates, so no new number is extracted; the
   usual suggestions are `s ≠ 0`, `xmin ≤ xmax`/`ymin ≤ ymax`, and non-degenerate controls.
5. The `inter_x`/`inter_y` "singleton crossing" rule is exactly as strong as it should be:
   it can read a transversal *or* tangential unique crossing (intended), but the degenerate
   singletons above all have constructible coordinates, so nothing non-constructible is
   smuggled in.
6. `arc_length`'s hypotheses are strong enough for the integral to be a genuine length
   (differentiability on the whole interval plus integrability of `speed` forces the tracing
   to be absolutely continuous), so reparametrisation cannot distort it; this checks out.
7. The set-valued semantics of `arc_of_length`/`offset` is a mild mismatch at *tangential*
   self-touches only, because switching branches at a transversal crossing is non-differentiable
   and is rejected by `hdiff`; harmless for numbers so far.
8. More important for the programme are places the model is **weaker** than the program: no
   union/concatenation of strokes, no string past a closed curve's start (the `hinj` bound),
   no chaining of `arc_of_length` from its own far endpoint, C¹-only offsets, and bases limited
   to the six families. These cannot *reach* `am` but they weaken any impossibility proof.

---

## Table of findings

Severity key: **H** = harmless (modelling blemish, no new values), **C** = changes what is
constructible, **E** = makes everything constructible.

| # | Constructor & hypothesis | Mismatch | Concrete degenerate example | New numbers? | Sev | Suggested tightening |
|---|---|---|---|---|---|---|
| F1 | `scale_x`/`scale_y` (`Defs.lean:267,270`), hypothesis `hs : PConstructible s`, no `s ≠ 0` | factor `0` collapses/projects a curve the program can only resize | `scale_x 0 (sine) = {0}×[−1,1]`; `scale_x 0 (poly_graph X)` is the whole `y`-axis | none: singleton/segment at constructible coords; full lines already come from `poly_graph`+`rotate` | H | require `s ≠ 0` for a resize; permit `0` only if projections are intended |
| F2 | `restrict` (`Defs.lean:295`), hypotheses `PConstructible` bounds only | no ordering / non-degeneracy; empty and zero-width boxes allowed | `restrict S 0 0 0 0`; with `S=exp_two` gives `{(0,1)}`; inverted box gives `∅` | none: the point is `(xmin,ymin)`, both constructible; `∅` gives no crossing | H | require `xmin < xmax ∧ ymin < ymax` (a genuine window) |
| F3 | `cubic_bezier` (`Defs.lean:234`), all four controls `PConstructible`, no non-degeneracy | all controls equal yields a single point | `p₁=p₂=p₃=p₄=(0,0)` → `{(0,0)}` | none: the point is the constructible control point | H | optionally require the controls not all equal; the comment already calls it harmless |
| F4 | `offset` (`Defs.lean:372`), `hreg`, `hC1`, `hd : PConstructible d`, `d` unbounded | `d = ±radius` closes a circular arc to its centre; `|d| > ρ` makes cusps/self-crossings | unit circle, `d = 1` → `{(0,0)}`; parabola offset by `−ρ(vertex)` → cusp at the focus | none: the centre is constructible; cusp coordinates are not isolable by constructible windows | H | none required (the comment intends cusps); optionally forbid `d` that makes the offset map singular |
| F5 | `power_law` (`Defs.lean:198`), `a b : ℚ`, domain `x > 0` | exponent `0` gives a horizontal ray `y=a`; `a=0` gives the positive axis; `poly_graph` constants give full lines | `power_law 1 0 = {(x,1) : x>0}`; `poly_graph (C 3) = {y=3}` | none: rays/lines at constructible height | H | none (rays/lines are already reachable and harmless) |
| F6 | `div` (`Defs.lean:122`), no `y ≠ 0` | `x/0` is `0` in a field | `div base_one base_one`-then-`0` etc. | none: `0` is already `1−1` | H | none (arithmetic rule, not geometry) |
| F7 | `inter_x`/`inter_y` (`Defs.lean:126,131`), hypothesis `S ∩ T = {(x,y)}` | accepts tangential (non-transverse) unique crossings | ellipse tangent to `y=1`; `exp_two` tangent to a line at a non-constructible parameter | yes, but **intended**: this is the rule that solves transcendental equations | H | none; this is the closure's designed power |
| F8 | `arc_of_length` (`Defs.lean:324`) & `offset`, set-valued output | only the *set* `S` is stored, so a tracing may pick any injective path in it; at a **tacnode** (tangential self-touch) branch-switching is differentiable | a self-touching figure-eight; at a transversal crossing the switch has a corner and `hdiff` rejects it | no value example found | H (mild set-level permissiveness) | store a stroke/parametrisation in `PConstructibleCurve`, or require `γ` to reparametrise the generating map |
| F9 | `arc_length` (`Defs.lean:148`), `hdiff` (pointwise) + `hint` | check: is the integral a true length? | differentiable-with-integrable-speed ⇒ AC ⇒ yes; jumps blocked by differentiability on all of `Icc` | — | H (verified sound) | none |
| F10 | any constructor | can a mismatch make **every** real constructible? | — | no | H | none (cardinality argument below) |

---

## Detail

### F1 — `scale_x` / `scale_y` by zero (`Defs.lean:267-272`)

The rule is `PConstructibleCurve ((fun p => (s * p.1, p.2)) '' S)` given `PConstructible s`.
Nothing excludes `s = 0`, which the drawing program's resize handle cannot do (it would
collapse the shape). Concretely:

* `scale_x 0` of `sine` is `{(0, sin x) : x ∈ ℝ} = {0} × [−1,1]`, a vertical segment.
* `scale_x 0` of `poly_graph X` (the diagonal) is `{0} × ℝ`, the whole `y`-axis.
* `scale_x 0` of a curve with a non-constructible vertical extent produces a segment whose
  **endpoints are non-constructible**, but the endpoints cannot be isolated: `restrict`
  bounds are constructible, and any `inter` with a horizontal line `y=t` returns the
  constructible `t`.

This adds **no new lines or numbers**: full lines are already available (`poly_graph` of a
constant is a full horizontal line; `rotate 90` of it is the `y`-axis), and every bounded
vertical segment is already available from a `rectangle` edge / `restrict`. Extraction of a
value still requires `inter_x`/`inter_y` on a unique crossing or `arc_length` with
constructible endpoints, and the projections supply neither. So the mismatch is a genuine
modelling blemish, harmless in value terms. Suggested tightening: `hs_ne : s ≠ 0`.

### F2 — inverted or zero-area `restrict` windows (`Defs.lean:295-300`)

The rule intersects `S` with
`{p | xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax}`, with no hypothesis relating the
bounds. `xmin = xmax = x0`, `ymin = ymax = y0` gives the singleton `{(x0,y0)}` when that point
lies on `S`, and `xmin > xmax` gives `∅`. Both are sets the geometry cannot draw, but all
extractable coordinates are the constructible `x0, y0`; `∅` can never form the singleton
required by `inter_x`/`inter_y`. Suggested tightening: `xmin < xmax`, `ymin < ymax`.

### F3 — degenerate `cubic_bezier` (`Defs.lean:234-239`)

With all four control points equal the image is one point; with three or more coincident the
speed vanishes somewhere but the image is still a segment/loop. The point in the all-equal
case is `p₁`, constructible by hypothesis, so no non-constructible value is produced. The
constructor's comment already declares this intentional. If desired, add
`¬(p₁=p₂ ∧ p₂=p₃ ∧ p₃=p₄)`.

### F4 — `offset` collapse and cusps (`Defs.lean:372-386`)

`offsetParam γ d = γ(t) + d·unitNormal γ t`. For an exact circular arc of radius `r` centred
at `c`, `d = ±r` maps the whole arc to `{c}`. Since exact circles in the class come from
`ellipse` (or its affine images), `c` is constructible, so the collapse yields no new value.
For `|d|` beyond the radius of curvature the offset acquires cusps and self-crossings; the
cusp points are generally non-constructible but are not isolable by any constructor (windows
have constructible bounds), so nothing is extracted. The comment explicitly intends the
folding. No tightening needed for the programme; optionally require that `d` not make
`t ↦ offsetParam γ d t` singular.

### F5 — `power_law` and constant `poly_graph`

`power_law a b` is `{x>0} ∋ x ↦ a·x^b`. At `b = 0` this is the ray `{(x,a) : x>0}` (`x^0=1`),
and at `a = 0` the positive `x`-axis. `poly_graph` of a constant polynomial is a full
horizontal line. These are straight half-lines/lines at constructible positions, i.e. weaker
objects than curves but harmless; they cannot encode a free parameter.

### F6 — `div` by zero (`Defs.lean:122`)

The division constructor has no `y ≠ 0` side condition and `x / 0 = 0` in `ℝ`. This only ever
produces `0`, already reachable as `1 − 1`; it is an arithmetic rule, not a geometric one, so
it is harmless.

### F7 — non-transverse `inter_x`/`inter_y`

`inter_x`/`inter_y` fire whenever `S ∩ T` is a singleton, with no transversality requirement.
Tangency therefore qualifies. This is intended: solving `sin x = x/2`, or a tangent condition,
is exactly what the rule is for, and the drawing program can click a tangency as readily as a
crossing. The degenerate singletons produced elsewhere (F1–F5) are not a loophole because
their coordinates are constructible or their `y`/`x` is not isolable. No tightening.

### F8 — set-valued semantics of `arc_of_length` and `offset` (mild)

`PConstructibleCurve S` records the point-set, not the stroke. A witness `γ` in
`arc_of_length` therefore only has to be injective, differentiable and into `S`; it need not
be a reparametrisation of the map that generated `S`. The only way this could differ from the
drawn stroke is a **path that switches branches at a self-intersection**. At a transversal
self-crossing the two branches have different tangents, so such a switch has a corner and
`hdiff` (pointwise differentiability on `Icc`) rejects it. The mismatch survives only at a
**tangential self-touch** (tacnode/self-oscillation), where the tangents agree and the switch
is differentiable. I found no value that this reaches and the stroke cannot. `X4-01-bezier-loop.py`
exhibits a self-intersecting cubic Bézier — integer controls
`((−2,−2),(−2,−1),(2,0),(−1,−1))`, self-crossing at `t ≈ 0.40109` and `t ≈ 0.97391`,
point `≈(−0.77930,−0.92578)` — whose two branches through the crossing have lengths
`2.15130` and `0.23285` to the parameter end, confirming that a set with a self-intersection
does have distinct sub-arcs; it is the transversality that keeps them from being spliced.
Suggested (optional) tightening for full fidelity: store the generating parametrisation, or
require `γ` to be a reparametrisation of it.

### F9 — is `arc_length`'s integral a true length? (checklist item 1)

Hypotheses (`Defs.lean:148-161`): `a ≤ b`; `γ '' Icc a b ⊆ S`; `Set.InjOn γ (Icc a b)`;
`∀ t ∈ Icc a b`, the two coordinate functions are `DifferentiableAt`; and
`IntervalIntegrable (speed γ) volume a b`.

* **Jumps:** `DifferentiableAt` at every point of `Icc` (endpoints included) makes each
  coordinate continuous there, so a tracing cannot jump inside or at the ends. Behaviour of
  `γ` outside `Icc` is irrelevant because both the image condition and the integral are on
  `Icc`.
* **Wild speed:** `speed ≥ 0` and integrable; differentiability plus an integrable derivative
  makes each coordinate absolutely continuous (classical theorem: a derivative that is
  Lebesgue integrable satisfies the Newton–Leibniz formula), so `arcLengthOf γ a b` is exactly
  the 1-dimensional length of a simple arc, and any two injective tracings of the same
  sub-arc give the same value. In particular a "reparametrisation with jumps" is ruled out by
  `hdiff`, and retracing is ruled out by `hinj`.
* **`speed` uses `deriv`**, whose value at a non-differentiable point is junk `0`; since
  `hdiff` holds at every point of `Icc`, `deriv` is the true derivative almost everywhere on
  `[a,b]`, so the junk value never enters the integral.
* **Trace of a piece that is not an interval:** `γ''Icc` is a continuous image of an interval,
  hence connected, and lies in one component of `S`; there is no way to stitch several
  disconnected pieces into one tracing.

Conclusion: the differentiability/integrability side conditions are adequate; the interior
machinery is **not** over-permissive. The only freedom left is the intended one — which
constructible `S` and which constructible endpoints — and that is the real content of the
programme.

### F10 — why no mismatch can make "everything" constructible

Each derivation of `PConstructible x` or `PConstructibleCurve S` is a finite tree. The rules
are finitely many, the only number seed is `1`, and every parameter (centre, size, scale,
translation, window bound, control point, arc length `x`, offset `d`) is itself drawn from a
finite earlier derivation. Hence the derivation trees are countable and the set
`{x | PConstructible x}` is **countable**. No finitary rule can enumerate `ℝ` from a
countable seed set, so "makes everything constructible" is impossible unless a rule were
changed to quantify over an uncountable family (e.g. allow a non-constructible window bound or
translation, which would immediately make every real constructible via a vertical line at
`x = ζ`). The current hypotheses prevent exactly that: `scale`, `translate`, `restrict`,
`power_law`, `poly_graph`, and `cubic_bezier` all demand constructible/rational data.

---

## Where the model is weaker than the drawing program (checklist item 5)

These do not let anything *in*, but they mean a proof of "no construction reaches `am`" in
this model does **not** immediately exclude the drawing program.

1. **No union or concatenation of strokes.** `PConstructibleCurve` has no union/set-difference
   rule; `restrict` only intersects. The program can string a path across several shapes (and
   group/merge them). `Defs.lean` has no constructor for "curve 1 followed by curve 2".
2. **A string cannot pass a closed curve's start, or go round more than once.** `arc_of_length`
   (`Defs.lean:328`) requires `Set.InjOn γ (Icc a b)`. For the circle, `Basic.lean:2536`
   records that this is exactly why the construction is capped at `L ≤ π` (in fact `< 2π`):
   at length `2π` the endpoint revisits the start, breaking injectivity. The program's path
   length can loop. Elliptic periods live precisely at such wrap-arounds.
3. **No chaining `arc_of_length` from its own far endpoint.** The start point must be
   `PConstructible` (`Defs.lean:333`) while the far endpoint is deliberately not
   (`Defs.lean:309-312`). So you cannot lay a first string, then a second from where it ended,
   unless a crossing has already pinned that point. The programme needs chained/duplicated
   arcs (addition and duplication theorems), so this is a real gap. There is also no rule for
   the *sub-segment* between two arc-length marks on the same curve.
4. **`inter_x` requires a singleton intersection.** A crossing among several must be isolated
   with an axis-aligned `restrict` window whose bounds are constructible; some genuine
   crossings may not be isolable without a non-constructible bound.
5. **`offset` needs `hreg` and `hC1` on `Icc`** (`Defs.lean:381-383`), so a corner (a
   polygon vertex, or a curve the program offsets with a miter/round join) cannot be offset.
6. **Base families are limited.** `poly_graph` is rational and `natDegree ≤ 6`; `power_law`
   is `a,b ∈ ℚ`; drawing cannot represent the lemniscate, the genus-1 Serret curves used in
   `NOTES-jacobi-R2.md`, or general graphs `y = p(x)` with constructible non-rational
   coefficients. `Basic.lean:4219-4222` states the lemniscate case explicitly.
7. **`arc_length` needs both endpoints `PConstructible`** (`Defs.lean:159-160`), so a length
   is only readable between constructible plane points; the program can measure between any
   two drawn marks (in practice those are constructible, so this is minor).
8. **`rotate` is an axiom only for whole degrees** (`Defs.lean:279`). This is not a real
   restriction: `rotate_PConstructibleCurve` plus the axis scalings recovers every
   `PConstructible` angle, and `cos`/`sin` of constructible angles are already
   `PConstructible`. Listed for completeness.
9. **`Restrict` windows are axis-aligned** in the rule, but `rotate`+`restrict` recovers
   rotated crops, so this is not a restriction.
10. **`hdiff` is pointwise, not `C¹`, for `arc_of_length`.** This is *stronger* than the
    drawing program needs (fine); the converse mismatch, `offset` demanding `C¹`/regular,
    is the real gap (item 5).

---

## Does any mismatch reach `am`?

No.

* Every non-constructible number the rules can emit comes from exactly two number rules:
  `inter_x`/`inter_y` (a unique crossing, i.e. the solution of a constructible system) and
  `arc_length` (a genuine arc length of a constructible curve between constructible
  endpoints). The degenerate constructions (F1–F6) only ever yield constructible
  coordinates, empty sets, or sets whose non-constructible features cannot be isolated,
  because all window/bound data is constructible (F10).
* `am` is the **inverse** of the first-kind integral `F`, not a crossing-solution or a
  forward arc length that is currently reachable: `NOTES-jacobi-R1a/R1b/R1c/R2.md` show no
  drawable curve has arc length `F`; offsets give third-kind combinations plus a boundary
  term; and `NOTES-jacobi-X2.md` §2.3 makes the crossing calibration `φ' = dn φ` precise.
  A definitional bug would have to let a constructor *choose the far endpoint freely* or
  supply a curve whose arc length is `F`; `arc_of_length` does neither (the endpoint is fixed
  by the length and the curve; F8's only loophole is at a tacnode and preserves that).
* The one genuine slack — `S` is a set, not a stroke, and `arc_of_length` permits any
  injective `γ` into it — is neutralised for values because branch-switching at a transversal
  crossing is non-differentiable and is rejected by `hdiff`.

So the X4 outcome is **negative for the exploit** (no definitional loophole opens `am`), and
the audit's real product is the over-permissiveness list to tighten (chiefly `scale`/`restrict`
degeneracies and the C¹/union/wrapping weaknesses) plus the confirmation that the
crossing-vs-arc-length design is doing what it claims.

### Reproduction

`archived files/jacobi-scripts/X4-01-bezier-loop.py` (run with the workspace Python 3.12)
exhibits the self-intersecting Bézier quoted in F8 and prints the two branch lengths and the
two distinct far endpoints for one fixed length budget. All of F1–F6 are direct evaluations
of the definitions (e.g. `power_law 1 0`, `cubic_bezier` with equal controls,
`offsetParam` of the unit circle with `d = 1`).
