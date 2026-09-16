# Notes: extracting arc endpoints / bounding boxes from a `PConstructibleCurve`

> **CORRECTION HEADER — added 2026-09-16, after review. Read this before using the note.**
>
> The proposal was accepted and the bounding box is **landed** as `PConstructible.box_xmax` /
> `box_ymax` in `Pptc/Defs.lean`, but **not in the form §3 states**, and several claims below are
> wrong. Superseded by `Pptc/PLAN-bounding-box.md`; where the two disagree, the plan wins.
>
> 1. **§3 Option A is unsound as written, and §0's safety bullet with it.** Stating the box on
>    `γ '' Icc a b` with `hsub : γ '' Icc a b ⊆ S` and free `a, b` collapses `PConstructible` to
>    all of `ℝ`: take `S = {y = x²}`, `γ t = (t, t²)`, `a = 0`, `b = r`; every hypothesis holds
>    and the box returns `max x = r`, with `r` constrained by nothing. §0's "the class stays
>    countable" and §3's "finitely many per traced arc" both fail, because there are uncountably
>    many traced arcs. This is the *same* collapse §1 correctly diagnoses for `arc_length`.
>    The landed form pins the arc by requiring it to be a `PConstructibleCurve` in its own right
>    and uses `IsCompact` for attainment, with no tracing in the axiom at all.
> 2. **§5.2 is false.** `ellipticF` is *not* "realised as a Bézier arc length".
>    `Basic.lean:3514-3550` gives `F` as a *combination* of the Bézier arc length `J`, a
>    second-kind integral `E`, and an algebraic boundary term. `Jacobi.lean:711-716` already
>    states the refutation: laying an arc of length `L` gives the `T` with `J(T) = L`, not the
>    `T` with `J(T) − (algebraic in T) = L`, which is what the amplitude solves. **The box does
>    not reach `am`, `sn`, `cn` or `dn`.** §5.2's second half (inverting the complete integrals
>    for eccentricity) fails separately: it inverts in the curve's *parameter* `c`, not in arc
>    length along a drawn curve, and you need a constructible `c` to draw the ellipse at all.
> 3. **§5.3 resolves negatively for every base curve.** The offset's velocity is `(1 − dκ)·γ'`,
>    parallel to the base velocity, so offset extrema sit at the base curve's extrema (quadratic
>    for a cubic pair) plus the cusps. And `poly_graph` extrema solve `p'(x) = 0` with `p'`
>    itself drawable, rotated-`sine` extrema need only `arccos`, and `exp_two` tangency
>    constants reduce to `log₂(e·ln 2)` — all already reachable, the last because
>    `log_Pconstructible` (`Basic.lean:1899`) and `exp_one_Pconstructible` (`:1926`) exist.
>    Only the offset **cusps** (a degree-12 equation) remain open.
> 4. **Both numbers in the §4 table are wrong past ~15 digits**, despite carrying `[NC 35]`
>    labels. Correct: `y = x³` gives `0.790706893627604843078476035616…` and `y = x⁴` gives
>    `0.810451620058442235121609068479…` (`[NC 45]`, back-substitution returns `1.000…` to 47
>    digits). The §2 parabola witness `b` was re-verified and **is** correct as given.
> 5. **Not adopted:** §6.5 / the Serret curve. Out of scope — not an operation a drawing
>    program has. Non-constructibility (§6.3, `PLAN §7`) is also explicitly out of scope.
>
> What the note gets right and is worth keeping: the §1 asymmetry analysis, the §3b
> counterexample to the `restrict`/zoom heuristic, the §2 parabola witness, and the framing of
> inverse arc length as a genuinely new *kind* of operation (§4).

Discussion note (not part of the R1-R4 research series). No `.lean` file was created, edited or
deleted; no `lean-lsp` tool and no `lake` command was used. Numeric witnesses were computed with
the Wolfram kernel.

Purpose: record a question raised while finishing R4 (the inbound survey), namely whether
`Pptc/Defs.lean` should gain an operation that reads a *point* (or at least an extreme
coordinate) off a constructible curve, and first impressions of what such an operation would
unlock.

---

## 0. Summary

- The axioms let you get numbers *out of* a curve in only two ways: `arc_length` (the length of an
  arc whose two plane endpoints you already have) and `inter_x` / `inter_y` (a coordinate of a
  unique intersection of two curves). No rule takes a point, an endpoint, or an extreme
  coordinate from a curve.
- Therefore the far endpoint of an `arc_of_length` stroke is **not produced by any rule** in
  general. For a closed curve it is recovered by laying a second, complementary arc and
  intersecting (this is how `cos`/`sin` and the Jacobi ellipse construction work); for an open
  curve there is no second curve to intersect with and nothing yields it.
- A bounding-box operation (the width/height of a drawn stroke) is the natural missing
  primitive. It returns the far endpoint whenever that endpoint is a coordinate extreme — in
  particular for every monotone arc, e.g. any graph — and the extrema in general.
- It produces values not currently obtainable. Concrete witness: the length-`1/2` arc of `y = x²`
  laid from the origin has width `b = 0.44633388551759072893813142528…`, the inverse of an
  elementary arc-length function at `1/2`.
- The real consequence is not one number but a new *operation*: **inversion of the arc-length
  function**. It is the first principle in the language that inverts a transcendental, and it is
  what would make Jacobi elliptic functions and modular functions reachable (sketched in §5).
- Safety: the class stays countable, so there is no collapse to `ℝ`; but the primitive must be
  stated on a compact *traced* arc so the extrema are attained rather than taken as a `sSup` of a
  possibly non-closed set.

---

## 1. What the axioms give, and the asymmetry

From `Pptc/Defs.lean`:

- `arc_length` (`:148`): given `hS : PConstructibleCurve S`, a tracing `γ`, `a ≤ b`, the
  subset/injectivity/differentiability/integrability conditions, **and P-constructible plane
  endpoints `γ a`, `γ b`**, concludes `PConstructible (arcLengthOf γ a b)`. The endpoint
  constructibility is an *input*.
- `arc_of_length` (`:324`): given `hS`, a tracing `γ`, `a ≤ b`, the same regularity conditions,
  a P-constructible *start* `γ a`, and `{x} (hx : PConstructible x) (hlen : arcLengthOf γ a b = x)`,
  concludes only `PConstructibleCurve (γ '' Set.Icc a b)`. The far endpoint `γ b` appears nowhere
  in the conclusion, and `Defs.lean:306-312` says so on purpose (the far endpoint is
  *emphatically not required* to be P-constructible, and intersecting the arc is what would make
  its coordinates reachable).
- `offset` (`:372`) likewise concludes only `PConstructibleCurve (offsetParam γ d '' Set.Icc a b)`.

So the language is asymmetric by design: endpoints are *data you supply*, never data you
extract. The only extraction is `inter_x`/`inter_y`, which needs a second curve meeting the arc in
exactly one point.

The class is countable: constructors whose free real data are P-constructible (or `ℚ`/`ℤ`), plus
`arc_length`/`arc_of_length`/`offset`, whose arbitrary tracing `γ` and parameters `a,b` only ever
produce outputs determined by the traced geometric arc (the output is parametrization-invariant).
Stratifying by derivation height gives countably many numbers and curves at each level; the union
is countable. This is why `arc_length` must pin *plane endpoints* rather than the parameters
`a,b`: with arbitrary parameters, fixing the parabola tracing `γ t = (π t, (π t)²)` and letting
`b` range over `ℝ` would make every real an arc length (`Defs.lean:140-147`).

---

## 2. The gap, with a witness

**Closed curves: recoverable.** The circle (`Basic.lean:2471-2485, 2578-2589`) and the ellipse
(`Jacobi.lean:469, 494`) lay an arc of length `x` from a marked point and a *complementary* arc
from another marked point of total length `perimeter − x`; the two meet in exactly the far/abutment
point, and `inter_x`/`inter_y` reads its coordinates. This works because the curve is closed, so
the complement is a second constructible arc ending at the same point.

**Open curves: not recoverable.** Take `S = {y = x²}` (a legal `poly_graph`), start `(0,0)`, and
length `x = 1/2`. Let `b > 0` satisfy

```
G(b) := ∫₀^{b} √(1 + 4 t²) dt = (b/2)·√(1 + 4b²) + (1/4)·asinh(2b) = 1/2.
```

Then `arc_of_length` yields the arc `A = {(t, t²) : 0 ≤ t ≤ b}` as a `PConstructibleCurve`. Its
bounding box is `[0, b] × [0, b²]`, so its width is `b` and its height `b²`:

```
b  = 0.44633388551759072893813142528262481720135752704286437386727212215…   [NC 50]
b² = 0.19921393736122978704177641005666855494130680551311263513616068307…   [NC 50]
```

Nothing else in the language produces `b`. `arc_length` would need the endpoint `(b, b²)`, which
is exactly what is missing; `inter_x` would need a second constructible curve through `(b, b²)`
meeting `A` only there, and there is none — the parabola is the only constructible curve through
that point that the language builds, and it does not isolate it. `b` is the inverse of an
elementary function at a rational, so it is not a low-degree algebraic number either
(`RootApproximant` to degree 12 returns ever-growing coefficients, the signature of a
transcendental). The project has no tools to prove non-P-constructibility (`PLAN §7`), so this is
a statement that *no rule produces `b`*, not a proof that `b` is unconstructible.

---

## 3. Constructor options

Two natural primitives, both matching operations a drawing program offers:

- **Option A — bounding box of a traced arc.** Given `hS`, a tracing `γ`, `a ≤ b`, and that `γ`
  is continuous on `[a,b]`, conclude that the four numbers `min/max` of the two coordinate
  projections of `γ '' [a,b]` (hence the width `max x − min x` and height `max y − min y`) are
  P-constructible. This is the operation described as "select the stroke, read its box".
- **Option B — endpoints of a traced arc.** The same data, concluding
  `PConstructible (γ a).1 / .2` and `PConstructible (γ b).1 / .2`. This is the direct fix for the
  `arc_of_length` far endpoint, and is strictly more targeted.

Notes for whoever formalizes either:

- State it on a **compact traced arc** (`γ` continuous on `[a,b]`), where the extrema are
  *attained* (Weierstrass), giving an honest min/max. Do **not** state it on an arbitrary
  `PConstructibleCurve S`: `power_law` omits `x = 0` and a raw `sSup` of a non-closed or
  unbounded projection may be a limit that is not attained, which is the kind of limit the
  language avoids.
- Option A gives the far endpoint only when the endpoint is a coordinate extreme; it always gives
  the extrema. Option B gives both endpoints unconditionally. Which is wanted depends on the
  modelling claim: a drawing program can both read a bounding box and click an endpoint.
- Neither collapses the class: per level the new outputs are finitely many per traced arc, so
  countability is preserved.
- Adding a constructor **strengthens the logic**. Every existing theorem remains valid, but the
  meaning of `PConstructible` grows, so the value surveys (R1, R4) would need re-auditing.

**Decision (project owner).** Only the bounding box (Option A) is to be added, since that is the
primitive the drawing program actually has; endpoint extraction (Option B) is not added. Whether
the box can always recover the endpoint — in particular via `restrict` (see §3b) — is left as an
open question to settle separately.

---

## 3b. Why the zoom heuristic does not give the endpoint in general

A tempting argument is that one can always `restrict` to a window near the end of the arc until
the remaining piece looks like a segment, and read the endpoint off the box. This fails in
general, because a box reports coordinate *extrema*, and an endpoint interior to the projection
of the restricted arc is never an extreme.

**Counterexample.** Let `A` be the unit-circle arc traced at unit speed from `(1,0)` for length
`x` with `3π/2 < x < 2π`. This is a legal `arc_of_length` stroke: injective (length `< 2π`), unit
speed, constructible start and constructible length. Its endpoint is `P = (cos x, sin x)` with
`cos x ∈ (0,1)` and `sin x ∈ (-1,0)`, so `P` is interior in both coordinates — the arc's
coordinate extrema are `max x = 1`, `min x = -1`, `max y = 1`, `min y = -1`. The whole-arc box
misses `P`.

For an axis-aligned window `W` (what `restrict` gives) to report `max x = P.x`, `W` must contain
no arc point with `x > cos x`. Those points are exactly the opening stretch at angles `[0, α)`
with `α = arccos(cos x) ∈ (0, π)`, and every one of them has `y ≥ 0`; the endpoint has
`y = sin x < 0`. So `W` must cut below the x-axis, with a y-upper-bound in `[sin x, 0)` — and
`sin x` is exactly the unknown endpoint ordinate, so any constructible bound in that interval
already encodes where `P` is. Without it, every constructible axis-aligned window either keeps
the opening stretch (so the box maximum exceeds `P.x`) or clips `P`. Rotation does not help: the
circle is rotation-invariant, so no support direction separates `P` from the opening stretch.

The heuristic is right for a *free end* that no earlier part of the arc shadows in the chosen
coordinate — every graph stroke (the parabola witness), and generically the end of a laid
string. It is not a general endpoint extractor, and a literal zoom is a limit, not a finite
constructible operation: each `restrict` needs constructible bounds, and the bound that would
isolate `P` is `P` itself.

**Consequence.** For endpoint extraction in full generality, add the endpoint primitive
(Option B). Keep the bounding box as the extrema / width-height operation: it does yield new
values (the witness `b`) but not every endpoint.

---

## 4. Why this gives *new* values, when earlier operations did not

The existing operations only *measure* (arc length) or *locate* (intersection). Inverse
*functions* are already reachable by locating: intersect the graph of `f` with the horizontal
line `y = y₀` and read `x`, giving `f⁻¹(y₀)`. What no operation does is invert the **arc-length
functional** `G(X) = length from the start to the point over abscissa X`. A bounding box of a
monotone arc does exactly that: it returns the endpoint, i.e. `G⁻¹(x)`, and that is a genuinely
new kind of output. (It is also not a function inverse: `b` above is pinned by the *length* `1/2`,
not by a `y`-value.)

Two more witnesses of the same kind, unit length laid from the origin on the graph families:

| graph | density | arc-length inverse at length 1 |
|---|---|---|
| `y = x²` (`m = 2`, elementary) | `√(1+4t²)` | length `1/2` gives `X = 0.4463338855…` |
| `y = x³` (`m = 4`, elliptic) | `√(1+9t⁴)` | `X = 0.790706893627604150341…` [NC 35] |
| `y = x⁴` (`m = 6`, genus 2) | `√(1+16t⁶)` | `X = 0.810451620058458702784…` [NC 35] |

The `m = 4, 6` cases invert the very arc-length `₂F₁`s that H6 / R4 classify; they are not
themselves `₂F₁` values at constructible arguments, but the arguments at which the arc-length
`₂F₁` takes a prescribed value.

---

## 5. Research avenues (initial feel, largely `[SP]`)

1. **Inverse arc length per curve.** For every constructible curve, the operation makes
   `G⁻¹` available at P-constructible lengths: inverse elementary arc length (parabola), inverse
   incomplete elliptic `E` (ellipse partial arcs), inverse of the H6 `₂F₁` arc-length function
   (`y = xᵐ`, `m = 6, 8, 10`). New values even at the first test case, `b`.
2. **Inverse elliptic integrals, hence elliptic functions.** `ellipticF` is *realised as a Bézier
   arc length* in `Pptc/Basic.lean`; laying a Bézier arc of prescribed length and reading the box
   would invert `F`, giving the Jacobi amplitude `am(u, k)` and thence `sn`, `cn`, `dn`. This is
   the classical route from integrals to elliptic functions, and it is a qualitatively new kind of
   source for the class. Inverting the *complete* integrals (quarter arc of the ellipse) gives the
   eccentricity as a function of the quarter perimeter — the modular-function / singular-modulus
   territory — which connects back to the Γ frontier (Chowla-Selberg periods at CM points), where
   the project already has `Γ(n/24)`. High potential, entirely unverified.
3. **Extrema as roots.** For a Bézier arc the coordinate extrema are roots of `x'(t) = 0`
   (quadratic), so no new algebraic values; for `offset` curves the extrema are roots of the
   higher-degree polys already appearing in `Offset.lean`, whose values the project may or may not
   already reach by intersection. Worth checking whether the box adds anything algebraic.
4. **B6 is not obviously affected.** The B6 gap is about the *density* laid (`∫dx/√(1+xᵐ)`, a
   first-kind differential) versus `∫√(1+xᵐ)`. A bounding box changes no density; it extracts
   extrema. So the box does not by itself close B6.
5. **Effect on the R4 survey.** With endpoint extraction, the caveat that an `arc_of_length` arc
   has no obtainable endpoint dissolves (for monotone arcs): the offset of a prescribed-length arc
   becomes measurable, and its length is `arcLength(base) − d·Δφ` as before, so still no new `₂F₁`
   family — but the reachability question is settled. New offset bounding boxes may give new
   numbers.

---

## 6. Open questions / recommendation

1. (Decided: add the bounding box only; see §3.) State it on a compact traced arc, and prove
   countability is preserved.
2. Settle whether the box always extracts the endpoint. §3b gives a counterexample to the
   `restrict`/zoom heuristic, so this needs either a different argument or stays open.
3. **Test case `b`:** try to show it is not reachable by any current combination; if that holds,
   the box genuinely enlarges the class.
4. Re-audit R1 and R4 under the new axiom (the surveys assumed no endpoint extraction).
5. Decide whether inverting arc length is a construction the project *intends* the drawing program
   to have. If yes, avenue 2 is the most valuable direction opened; if no, the current
   intersection-only route stands.

---

## 7. Ledger

| claim | label |
|---|---|
| `arc_of_length` conclusion is a curve only; no endpoint extraction rule exists | `[SY]` from `Defs.lean:324-336, 306-312` |
| closed curves recover the far endpoint by complementary arc + `inter` | `[SY]`/ref (`Basic.lean:2578`, `Jacobi.lean:469,494`) |
| parabola length-`1/2` arc width `b = 0.44633388551759072893813142528…` | `[NC 50]` |
| `y=x³`, `y=x⁴` arc-length inverses at length 1 | `[NC 35]` |
| `b` has no low-degree algebraic relation | `[NC]` (RootApproximant deg ≤ 12) |
| no current rule produces `b` | argument, not a non-constructibility proof (cf. `PLAN §7`) |
| inverting `F` reaches `am`, `sn`, `cn`, `dn`; modular-function connection | `[SP]` |
| box does not affect the B6 density gap | `[SY]` |
