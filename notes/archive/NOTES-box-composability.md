# Notes: `arc_of_length` composability — the structural gain (plan §3.N7 / task B11)

Research note. **No `.lean` file was created, edited or deleted; no `lake` command and no
`lean-lsp` tool was used.** The library was read only (`read` / `rg`). Every exact-symbolic and
every numeric witness below was computed with the Wolfram kernel
(`wolfram_WolframLanguageEvaluator`); the backend is stated per number. Numerics use
`FindRoot` at `WorkingPrecision -> 80`, and each value was back-substituted at that precision.

Labels follow the house convention: `[SY]` syntactic / from source or an exact symbolic
identity, `[NC n]` numeric to `n` digits from a computation actually run at that precision,
`[SP]` speculative. This note responds to `PLAN-bounding-box.md` §3.N7 (lines 283–294) and its
task-table row B11; it depends on the landed B8 (`Pptc/BoxGraph.lean`) and W1–W4
(`Pptc/Box.lean`).

---

## 0. Verdict

- **Composability holds, and it is genuine.** `arc_of_length` is no longer a dead end:
  W3/W4 (`Pptc/Box.lean`) and B8 (`Pptc/BoxGraph.lean:116`) recover the far endpoint, so a
  stroke's endpoint can start the next stroke, be a control point of the next curve, etc. The
  constructor's own docstring (`Defs.lean:360-363`) warning that the endpoint is "emphatically
  not" P-constructible is superseded by a *derived* rule. `[SY]`
- **But composability yields no genuinely new number.** Every chained-stroke output is, by
  definition, an output of W4/B8; and W4/B8 already accept an *arbitrary P-constructible start
  point and arbitrary P-constructible curve parameters*. "Lay on `C₁`, then on `C₂` through the
  endpoint" is therefore *one* application of W4/B8 whose start point and curve were assembled
  in earlier construction steps. The `PConstructible`/`PConstructibleCurve` pair is a least
  fixed point closed under finite construction trees, so iterating a derived rule cannot enlarge
  it. In one line: **the new reach is the single inverse step (already N1/N2/N4); iterating it is
  closure, not content.** `[SY]`
- **Same-curve composition is literally a single stroke at the summed length** — the additivity
  of `arcLengthOf`. Verified: the two-step result and the one-step result at `5/6` agree to 59
  digits. `[SY]` + `[NC 59]`
- **Cross-curve candidates collapse too.** The tangent-line composition is a closure-op
  (arithmetic + `sqrt`) expression; the translated-cubic composition is a *sum of two independent
  single-stroke numbers*. Values in §3. `[SY]` + `[NC 40]`
- **Verdict on the plan's claim.** N7 is real relative to the *pre-box* language (on an open
  curve, the endpoint was unreachable there, so two-stroke numbers were inexpressible) and empty
  relative to the *post-box* language. It adds no constants. The plan's own phrasing — "changes
  the *shape* of the language rather than adding to it" — is correct; the reason it does not
  "add to it" is stronger than the plan states, namely that N7 is a corollary of W4, not an
  independent source of reach.

---

## 1. What "strokes chain" means now, and the side conditions per link

A **closed stroke** is the composite of two library results:

1. `PConstructibleCurve.arc_of_length` (`Defs.lean:375-387`) — lays the arc as a
   `PConstructibleCurve`, given a tracing `γ`, an interval `[a, b]`, a P-constructible start
   point `γ a`, and a P-constructible length `x = arcLengthOf γ a b`.
2. `arcLength_inverse_Pconstructible` / `arc_xendpoint_Pconstructible` / `arc_yendpoint_…`
   (`Box.lean:343, 368, 386`) — recovers the far endpoint `γ b` from that arc via the box, when
   the tracing is coordinate-monotone; or, for a graph, the unconditional
   `graphArcLength_inverse_Pconstructible` (`BoxGraph.lean:116`).

A chain is: closed stroke on `C₁` from start `s₀` → endpoint `p₁`; build `C₂` *through* `p₁`;
closed stroke on `C₂` from `p₁` → `p₂`; etc.

**Link A — graph stroke (B8).** `[SY]` The hypotheses are exactly those of
`graphArcLength_inverse_Pconstructible`:

- `PConstructibleCurve S` for the graph's ambient curve;
- `hmem : ∀ t, (t, f t) ∈ S` (the curve contains the *whole* graph — true of `poly_graph`);
- `hdiff : ∀ t, DifferentiableAt ℝ f t` and `hC1 : Continuous (deriv f)`;
- start `a` with `ha : PConstructible a` and `hfa : PConstructible (f a)`;
- `hL : PConstructible L`, `hL0 : 0 ≤ L`.

It returns `b ≥ a` with `arcLengthOf (t ↦ (t, f t)) a b = L` and `PConstructible b`. **The
monotonicity side condition is free** (the graph tracing's abscissa is the identity), and **the
`IsCompact` side condition of the box is supplied, not assumed**: the tracing's `hdiff` gives
`ContinuousOn`, so `isCompact_Icc.image_of_continuousOn` closes it inside
`arc_xendpoint_Pconstructible` (`Box.lean:222`). The ordinate `f b` is then P-constructible by
arithmetic (`pow_Pconstructible` `Basic.lean:843`, `rat_Pconstructible` `Basic.lean:82`), so the
endpoint is a fully P-constructible point.

**Link B — general monotone-arc stroke (W4/Box).** `[SY]` The hypotheses are exactly
`arc_of_length`'s bundle (`Defs.lean:375-387`): `PConstructibleCurve S`; `γ`; `a ≤ b`; `hsub`,
`hinj`, `hdiff`, `hint`; P-constructible start coordinates; P-constructible length. On top of
that, `arcLength_inverse_Pconstructible` (`Box.lean:343`) needs a monotonicity-or-antitonicity
hypothesis *per coordinate to be extracted*. To recover both coordinates: both coordinates
monotone (box twice), or one coordinate monotone and the other via `inter_y` against a vertical
line (`poly_graph` of degree 1, rotated by `90`). Compactness is again supplied by the
constructor, not assumed (`isCompact_traced_arc`, `Box.lean:186`; `nonempty_traced_arc`,
`Box.lean:200`).

**Link C — building `C₂` through `p₁`.** `[SY]` `translate_x`/`translate_y` (`Defs.lean:302-307`)
and optionally `scale_x`/`scale_y`/`rotate` (`Defs.lean:318-335`) carry P-constructible data.
These are exactly what need `p₁`'s coordinates to be P-constructible — which is Link A/B's
output. No new side condition: the offsets are P-constructible because the endpoint is.

So every link is discharged by landed lemmas; nothing in a chain needs a new axiom.

---

## 2. What is genuinely new

**Relative to the pre-box language.** `[SY]` Before the box, on an *open* curve the far endpoint
of an `arc_of_length` stroke was not obtainable: the constructor deliberately does not produce
it, and there is no second shape to intersect the arc against that would isolate it (intersecting
the arc with a line `x = c` needs the unknown `c`; intersecting it with its own ambient curve
returns the whole arc). On a *closed* curve the endpoint could be reached by the
complementary-arc + `inter_x`/`inter_y` trick (this is how `cos`/`sin` were first obtained,
`Basic.lean:2512-2607`). Therefore **any** number that consumes the far endpoint as a datum —
i.e. every two-stroke number on an open curve — was unreachable. That is a real change in the
*expressible constructions*: the marked points of a drawable curve are now closed under adding
P-constructible arc lengths.

**Relative to the post-box language.** `[SY]` Nothing. The argument is structural, not case-by-case:

> W4/B8 are *theorems* about the inductively defined `PConstructible`, not constructors. Their
> inputs include an arbitrary P-constructible start point and arbitrary P-constructible curve
> parameters. So a two-stroke value is `W4(C₂, p₁, L₂)` where `p₁ = W4(C₁, s₀, L₁)` and `C₂` is
> built from `p₁` by closure operations. Both `p₁` and `C₂` are already P-constructible data, so
> the whole computation is one W4/B8 application — with a more elaborate start and curve. The
> class contains all finite construction trees; adding a second closed stroke lengthens a tree,
> it does not add a leaf outside the class.

**Enumeration of second-stroke shapes and their status.**

| shape | example | status |
|---|---|---|
| two lengths on the *same* curve | `L₁` then `L₂` on `y = x²` | `= ` one stroke at `L₁ + L₂` (additivity). Not new. `[SY]` |
| `C₂` an *affine image* of a fixed curve through the endpoint (translate / scale / rotate by P-constructible data) | tangent line to `y = x²` at `p₁`; translated `y = x³` | displacement is an arithmetic / single-stroke expression in `p₁`. Not new. `[SY]` `[NC 40]` |
| `C₂` with *nonlinear* dependence on the endpoint (e.g. Bézier control points nonlinear in `b₁`) | — | a genuine single W4/B8 application, but a **single** one. Still a W4 output. Not new. `[SY]` |
| a coordinate of a stroke endpoint fed to a later construction | any of the above | subsumed by the previous rows. Not new. `[SY]` |

---

## 3. The cheapest concrete candidate — and why none is new

The three natural candidates. All lengths below are P-constructible (`1/2`, `1/3`, `1` are
rationals; `rat_Pconstructible`).

**Candidate 1 — two arcs of the same parabola (additivity).**
Let `A(x) = (x/2)·√(1+4x²) + (1/4)·arsinh(2x)` be the parabola's arc-length function from the
origin (`Basic.lean:1830`, `arcLengthOf_parabolaParam`). Lay `L₁ = 1/2` from the origin, then
`L₂ = 1/3` from the resulting point. The total length from the origin is `5/6`, so the final
abscissa is the *single-stroke* inverse at `5/6`:

```
b(5/6) = 0.66853980531481528583030370971811105499750151685395   [NC 50]  Wolfram
```

Back-substitution: solving `A(c) − A(b(1/2)) = 1/3` for the two-step `c` gives
`c − b(5/6) = 0` to 59 digits (`~10⁻⁵⁹`). `[NC 59]` Wolfram. So the two-stroke value **is** the
one-stroke value; this is `arcLengthOf` additivity, not a new number. `[SY]`

**Candidate 2 — tangent line through the endpoint (arithmetic).**
`b* = A⁻¹(1/2) = 0.44633388551759072893813142528262481720135752704286437386727212215`
`[NC 50]` (plan N2; independently reproduced to 35 digits, with `A(b*) − 1/2 = 0` to 40 digits,
`[NC 40]` Wolfram). At `p₁ = (b*, b*²)` draw the tangent line (the affine image of `y = x`);
its unit tangent is `(1, 2b*)/√(1+4b*²)`, so laying `L₂ = 1/2` moves the abscissa by
`(1/2)/√(1+4b*²)`. Final abscissa:

```
x_tan = b* + (1/2)/√(1+4·b*²) = 0.8193378068802944789000789643424797534864   [NC 40]  Wolfram
```

This is built from the already-reachable `b*` by `sqrt_Pconstructible` (`Basic.lean:215`) and the
arithmetic closure — reachable with **no** second stroke. It is the *weakest* candidate, since a
straight second curve is forwarded-computable. `[SY]` `[NC 40]`

**Candidate 3 — translated cubic through the endpoint (a real second inversion, still a sum).**
`A₃(X) = ∫₀^X √(1+9t⁴) dt`; note `A₃(0.7907…) = 1` gives exactly plan N4's
`cubicUnitArcAbscissa = 0.790706893627604843078476035616379666889633851` `[NC 45]` (Wolfram,
reproduced here as a check). Take `C₂` = the translate of `y = x³` through `p₁`. Laying
`L₂ = 1/2` gives a displacement `A₃⁻¹(1/2)`, so

```
A₃⁻¹(1/2) = 0.4786687394430595168341968358357266058243                    [NC 40]  Wolfram
x_3       = b* + A₃⁻¹(1/2) = 0.9250026249606502457723282611183514230256    [NC 40]  Wolfram
```

This *does* require a second, genuinely transcendental inverse-arc-length step (the cubic's is
elliptic). Yet the answer is a **sum of two independent single-stroke numbers** — `b*` from the
parabola, `A₃⁻¹(1/2)` from the cubic — each of which B8 already produces on its own. It is not
new. `[SY]` `[NC 40]`

**Conclusion for item 3.** No candidate is genuinely new. The cheapest *would have been*
Candidate 1 (same curve), but it is provably the one-stroke value at the summed length. The
strongest-looking (Candidate 3) still factors as a sum. A witness that is "not already reachable
by a single-stroke or forward computation" would have to be a number not equal to any W4/B8
output — but every stroke endpoint **is** a W4/B8 output by construction, so no such witness
exists within this language. **Stated plainly: composability yields no new number.** `[SY]`

---

## 4. The honest case for and against

**For N7 being worth something.**

- `[SY]` It removes a real expressive obstacle. Pre-box, `arc_of_length` was a dead end on open
  curves (`Defs.lean:360-363` says so explicitly), so no construction could even be *written*
  that starts from the far endpoint. Chaining is now nameable, and the constructor's docstring is
  superseded (by a theorem, not by changing the constructor).
- `[SY]` It upgrades "marked points closed under adding P-constructible lengths" from folklore to
  a theorem-level statement, via `arcLengthOf` additivity.
- `[SP]` It can shorten some constructions: a two-stroke number is built without the
  bespoke complementary-arc/isolation argument that the pre-box route needed on closed curves.

**Against N7 being worth more than any individual constant.**

- `[SY]` It adds no numbers. N7 ⊆ W4/B8: every chained-stroke output is a single W4/B8
  application once the intermediate start/curve are admitted as P-constructible data, which the
  inductive closure already permits. The genuinely new reach is the *single* inverse step
  (`arcLengthOf`-inversion), which is N1 and is instantiated by N2/N4.
- `[SY]` + `[NC 59]` Same-curve composition is not merely "reducible": it is literally
  `arc_length`'s additivity, i.e. the one-stroke value at the summed length (verified to 59
  digits).
- `[SY]` + `[NC 40]` The cross-curve candidates collapse to arithmetic (tangent) or to sums of
  independent single-stroke values (translated cubic).
- `[SP]` The "shape of the language" gain is an API/documentation gain, not a mathematical one.
  The mathematical change of shape was W4, landed as N1. N7 should be read as the observation
  that W4 is composable — which is true and worth writing down, but is a corollary, not a new
  source of reach.

**Verdict.** A negative result, cleanly. The plan's sentence "arguably worth more than any
individual constant" is defensible only in the weaker sense that *knowing* W4 is composable is
worth recording; it is not defensible in the sense of enlarging what the drawing program can
reach. The box's reach is exhausted by the single inverse step.

---

## 5. What would need formalizing

**Already proved in the library (no work needed).**

- `[SY]` `Pptc/BoxGraph.lean`: `graphArcLength_inverse_Pconstructible` (116),
  `graphArcLength_endpoint_Pconstructible` (103), the three B9 witnesses (195/212/229), the
  private `graph_xendpoint_Pconstructible` (61).
- `[SY]` `Pptc/Box.lean`: W3 `arc_xendpoint_Pconstructible` (216), `arc_yendpoint_Pconstructible`
  (235), the antitone twins (253/272), W4 `arcLength_inverse_Pconstructible` (343) and the
  single-coordinate forms (368/386), the compactness toolkit (186/200).
- `[SY]` `Pptc/Defs.lean`: `arc_of_length` (375), `box_xmax` (207), `box_ymax` (210).

**Proposed, to state the negative result as a theorem.**

1. `arcLengthOf_add` (new). For `a ≤ b ≤ c` and `IntervalIntegrable (speed γ) volume a c`,
   `arcLengthOf γ a b + arcLengthOf γ b c = arcLengthOf γ a c`.
   `rg` finds **no** such lemma in `pptc/Pptc`; it follows in a few lines from
   `intervalIntegral.integral_add_adjacent_intervals` (Mathlib
   `MeasureTheory/Integral/IntervalIntegral/Basic.lean:1095`), which the project already invokes
   at `Basic.lean:3475, 4089, 4179`, `Jacobi.lean:349, 405`, `ThirdKind`-adjacent files.
2. `monomialArc_add` / a composition-collapse corollary (new). Given `monomialArc_exists n` at
   `L₁` producing `b₁`, and again at `L₂` from `b₁` producing `b₂`, additivity (1) gives
   `arcLengthOf γ 0 b₂ = L₁ + L₂`, so `b₂` equals the single application at `L₁ + L₂` by
   uniqueness of the graph abscissa. Needs `PConstructible.add` and (1).
3. `graphArcLength_inverse_add` (new) — the `graphArcLength_inverse_Pconstructible` version of
   (2), same shape.

**To make N7 *positive* one would need** an explicit witness plus a proof it is *not* a W4/B8
output. No such witness is found here, and a non-membership proof would need
non-constructibility/independence methods the project explicitly excludes
(`PLAN-bounding-box.md:58`). So the cheapest formalization path is the *negative* pair (1)+(2);
it is API hygiene rather than new mathematics, and may not be worth the build.

---

## 6. Ledger

| claim | label |
|---|---|
| W4/B8 recover the far endpoint of an `arc_of_length` stroke; on a graph the monotonicity side condition is free | `[SY]` `Box.lean:216,343`, `BoxGraph.lean:116` |
| `arc_of_length`'s docstring ("endpoint emphatically not `PConstructible`") is superseded by a derived theorem | `[SY]` `Defs.lean:360-363` vs `Box.lean:343` |
| the box's `IsCompact` side condition is *supplied* by the tracing's `hdiff`, not assumed by callers | `[SY]` `Box.lean:186,200,222` |
| pre-box, two-stroke numbers on an open curve were unreachable; closed curves used the complementary-arc + `inter_x`/`inter_y` trick | `[SY]` `Defs.lean:360-363`, `Basic.lean:2512-2607` |
| every chained-stroke output is a single W4/B8 application with a derived start/curve, so N7 does not enlarge `PConstructible` | `[SY]` — structural argument |
| two arcs on `y = x²` (`1/2` then `1/3`) equal the one stroke at `5/6` | `[NC 59]` Wolfram |
| `b(5/6) = 0.66853980531481528583030370971811105499750151685395` | `[NC 50]` Wolfram |
| tangent-line composition `x = 0.8193378068802944789000789643424797534864` is arithmetic in `b*` | `[NC 40]` + `[SY]` Wolfram |
| translated-cubic composition `x = 0.9250026249606502457723282611183514230256 = b* + A₃⁻¹(1/2)` is a sum of single-stroke values | `[NC 40]` + `[SY]` Wolfram |
| `A₃⁻¹(1) = 0.790706893627604843078476035616379666889633851` reproduces plan N4's `cubicUnitArcAbscissa` | `[NC 45]` Wolfram |
| no `arcLengthOf` additivity lemma exists yet; it follows from `intervalIntegral.integral_add_adjacent_intervals` | `[SY]` `rg` + Mathlib:1095 |
| composability is a corollary of W4 (N1), not an independent source of reach; it adds no constants | `[SY]` |
| if N7 is worth "more than any individual constant", that is as API/documentation, not reach | `[SP]` |
