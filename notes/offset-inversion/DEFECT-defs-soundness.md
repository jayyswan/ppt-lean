# DEFECT: `PConstructibleCurve.offset` + `box_xmax` make every real P-constructible

**Status: RESOLVED (2026-11-03) by option 2 — the offset acts on a whole curve, open or
closed.** This note records the defect for history. The current `Pptc/Defs.lean` no longer
has either hole; see §4 for the new signature and §5 for the downstream changes.

**Severity when found: critical.** This was a soundness hole in the fixed base
`Pptc/Defs.lean`, not a gap in a downstream proof. It was found while checking L2 (the
parabola headline theorem).

## 1. The two theorems

### 1.1 Sub-arc collapse

The following compiled against the old tree (`Pptc/Scratch/CollapseTest.lean`):

```lean
theorem all_real_Pconstructible_test (b : ℝ) : PConstructible b
```

So `PConstructible = Set.univ`. It used the *parabola*, `d = 0`, and the degenerate arc
`Icc b b`:

1. `PConstructibleCurve.poly_graph` gives the whole parabola `S = {p | p.2 = p.1^2}`.
2. The old `PConstructibleCurve.offset` was applied with `γ t = (t, t^2)`, `a = b`,
   `d = 0`, and only `hsub : γ '' Icc b b ⊆ S`. Its other hypotheses were trivial on the
   singleton. Its conclusion was `PConstructibleCurve (offsetParam γ 0 '' Icc b b)`, and
   `offsetParam γ 0 = γ`, so `PConstructibleCurve {γ b}`.
3. `Box.arc_xendpoint_Pconstructible` applied to that singleton curve with the monotone
   abscissa returned `(γ b).1 = b`.
4. Hence `PConstructible b`.

The failure was not an artefact of the degenerate interval: any sub-arc with an arbitrary
endpoint worked the same way.

### 1.2 Singleton collapse (`a = b`)

Even after replacing `⊆` by an equality with the whole curve, allowing `a = b` left a
second hole. Crop the parabola to the singleton `S = {(b, b^2)}` with a degenerate
`restrict` window; that singleton really is a `PConstructibleCurve`. Offset it with
`a = b`. The "normal" at the singleton is not determined by the singleton: it is the
one-sided normal of the tracing, which may be chosen by how `γ` continues away from the
point. With `d ≠ 0` the offset then lands anywhere on a circle of radius `|d|` around the
point, and `box_xmax` reads an arbitrary real.

Written out, the only missing ingredient was `hab : b < b`; there is no proof of that
proposition. `Pptc/Scratch/CollapseTest.lean` now records exactly this failed step, and
`linarith` is the only error in the file.

## 2. Why it happened

The old `PConstructibleCurve.offset` (`Defs.lean` lines 430–444) had

```lean
(hsub : γ '' Set.Icc a b ⊆ S)
```

and **no hypothesis on `a`, `b`, or on the plane endpoints `γ a`, `γ b`**. Thus *any*
sub-arc of a drawn curve could be offset, including a sub-arc whose endpoint was an
arbitrary real. The offset was then itself a `PConstructibleCurve`, and `box_xmax`
measured it.

This defeated the safeguard the file itself states for `box_xmax`:

> Takes `PConstructibleCurve A` for the curve *being measured* — not an arc merely lying
> inside one, which would admit uncountably many arcs and collapse the class.

`offset` was exactly the constructor that turned "an arc merely lying inside one" into a
`PConstructibleCurve`.

The same hole was used by L2:
`halfParabolaOffsetArc_PConstructibleCurve` applied `offset` to `Icc 0 w` for an arbitrary
real `w ≥ 0`, then `halfParabolaOffsetEndpoint_Pconstructible` boxed the endpoint and
`halfParabolaOffset_w_Pconstructible` concluded `PConstructible w` **with no hypothesis on
`w`**. The headline `parabola_offset_root_Pconstructible` was therefore **true but
vacuous**: it held for the trivial reason that everything held.

## 3. The intended construction, and why the old axiom was too weak

The planned L2 route was:

1. draw the parabola (`poly_graph`);
2. choose a P-constructible window `W` containing the desired parameter, and offset the
   *whole* half-parabola over `[0, W]`;
3. lay the arc of P-constructible length `x` along that offset curve with `arc_of_length`;
4. read the endpoint off with `box_xmax`.

The window `W` is built from `x` and `d`, never from the unknown `w`. Step 2 needs
`offset` to act on the **whole drawn curve**, not on an arbitrary sub-arc, and the window
must be nondegenerate so that the endpoint normal is the curve's normal.

## 4. Resolution applied (option 2: whole curve, open or closed)

`PConstructibleCurve.offset` in `Pptc/Defs.lean` now reads:

```lean
| offset {S : Set (ℝ × ℝ)} (hS : PConstructibleCurve S)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a < b)
    (himg : γ '' Set.Icc a b = S)
    (hinj : Set.InjOn γ (Set.Ico a b))
    (hseam : γ b = γ a → unitNormal γ b = unitNormal γ a)
    (hdiff : ∀ t ∈ Set.Icc a b, ...)
    (hreg : ∀ t ∈ Set.Icc a b, speed γ t ≠ 0)
    (hC1 : ContinuousOn ... ∧ ContinuousOn ...)
    {d : ℝ} (hd : PConstructible d) :
    PConstructibleCurve (offsetParam γ d '' Set.Icc a b)
```

The two changes close the two holes:

* `himg` is an **equality with the whole curve**, so the singleton `{γ b}` cannot be
  passed off as the parabola. A piece must first become a curve of its own via `restrict`
  or `arc_of_length`.
* `hab : a < b` rules out the singleton window. At each endpoint the derivative is then
  the one-sided derivative from inside `[a, b]`, so the normal is that of the curve.

Closed curves are allowed: `hinj` is only on `Ico a b`, so `γ b = γ a` is permitted, and
`hseam` asks that the normal match at the join. This is the correct model of offsetting a
whole PowerPoint outline. `Pptc/Offset.lean` provides `offset_open` for the common open
case, deriving `hseam` vacuously and weakening injectivity from `Icc` to `Ico`.

## 5. Downstream repair

* `Pptc/Offset.lean` — `offset_open` added; `offsetCubicPairArc_PConstructibleCurve` now
  uses it. Also `ellipseOffset_PConstructibleCurve`, the first closed-curve use of the
  constructor, with `hseam` discharged by `2π`-periodicity.
* `Pptc/BoxOffset.lean` — `offsetArc_box_xmax_of_offsetHyp` takes the new hypotheses.
* `Pptc/OffsetInversion/Parabola.lean` — the headline is no longer vacuous. The proof
  builds a P-constructible window `W ≥ w` from `x` and `d` alone
  (`halfParabolaOffsetWindow_exists`), offsets the whole half-parabola over `[0, W]`, lays
  the arc of length `x` on it, and reads the endpoint. Both `hx` and `hweq` are used.
* `Pptc/Scratch/CollapseTest.lean` — now a documented negative test. It fails only at
  `b < b`; the old sub-arc call is kept in a comment for comparison.
* `Pptc.lean` — imports neither `Pptc.Scratch.CollapseTest` nor the scratch `OffsetA3` /
  `OffsetB4` files.

## 6. Status of the current Lean streams

| stream | status |
|---|---|
| L0 `Projectile.lean` | **unaffected** — uses only `laplaceLimit`, `arctan`, arithmetic; no `offset`/box. |
| L1 `Speed.lean` | **unaffected** — genuine analytic theorems about `offsetParam`, no `PConstructible` reasoning. |
| L2 `Parabola.lean` | **repaired and non-vacuous** under the whole-curve axiom; uses the intended whole-arc route and both `hx`/`hweq`. |

All four files were re-checked from source on 2026-11-03 with `lake env lean` (exit `0`, no
diagnostics); `Pptc.OffsetInversion.Projectile` and the scratch `OffsetA3` / `OffsetB4`
files also still compile.

## 7. Audit of the other constructors

The `offset` hole had the shape "a hypothesis that says *some* arc of `S`, with the arc
itself unpinned". Every constructor was re-read for that pattern, now including the
`a = b` / singleton variant:

| constructor | what pins the extracted thing | verdict |
|---|---|---|
| `arc_length` | both *plane* endpoints `γ a`, `γ b` must be P-constructible; `a = b` returns `0` | sound. Countably many endpoint pairs, finitely many arcs between two points of a constructible curve, so countably many lengths. |
| `arc_of_length` | the start point is P-constructible and the length is pinned to the P-constructible `x`; the produced set is exactly `γ '' Icc a b` | sound. `a = b` gives the singleton `{γ a}`, a P-constructible point, not a free normal. |
| `box_xmax` / `box_ymax` | takes `PConstructibleCurve A` for the curve *being measured*, plus compactness | sound, and this is exactly what the old `offset` defeated. |
| `inter_x` / `inter_y` | both curves constructible, intersection a singleton | sound. |
| `restrict` | four P-constructible bounds; a degenerate window can give a singleton | harmless in itself: the singleton has P-constructible coordinates, and `offset` on it fails `hreg` (its tracing is constant) as well as `a < b`. |
| `translate_*` / `scale_*` / `rotate` | whole curve, P-constructible factor or integer degrees | sound. |
| the base curves | sets fixed by their parameters | sound. |

Two lemmas in `Basic.lean` were also re-read because they take a `⊆` hypothesis:

* `arcLength_segment_Pconstructible` feeds `arc_length` a segment whose plane endpoints are
  P-constructible. It grants only the distance between two P-constructible points, which
  `dist_Pconstructible` already gave, so it adds no numbers.
* `crossing_Pconstructible` takes `hSrange : S ⊆ Set.range Γ`, the *opposite* direction of
  slack: `Γ` may trace more than `S`, never less, and the crossing point is pinned by
  `Γ β ∈ S ∩ T`. Sound.

## 8. Why the class does not collapse (informal)

The repaired axiom does not reintroduce the collapse. The argument below is geometric
rather than a formal Lean theorem; a formal non-reachability statement is out of scope.

* Every `PConstructible` derivation is a finite term over countably many rules, so there
  are countably many derivations and hence countably many P-constructible reals.
* A `PConstructibleCurve` derivation is likewise a finite term. Its real parameters are
  either P-constructible (ellipse data, `restrict` bounds, `d`, `x`) or a parametrization
  `(γ, a, b)`. Once the curve `S` is fixed, the parametrization cannot change *which set*
  is produced:
  * `arc_of_length` produces the sub-arc of `S` of length `x` from a fixed start point;
    there are at most two of those, one in each direction.
  * `offset` produces the parallel set of `S` at distance `d`. `himg` with `hinj` on
    `Ico a b` makes `γ` a monotone reparametrization of `S` (or of `S` traced once round),
    and reparametrizing preserves the unit normal up to orientation. Reversing the
    orientation flips the sign of the normal, which is the same as replacing `d` by `-d`,
    and `-d` is P-constructible whenever `d` is.
* So each derivation's output is determined by finitely many P-constructible reals, and the
  class of constructible curves — hence of P-constructible numbers — stays countable.

The caveat is the usual one: this assumes constructible curves are finite unions of simple
`C¹` arcs, which holds for the base curves and is preserved by every constructor (`offset`
of a simple arc is an immersed arc; `restrict` and `arc_of_length` take sub-arcs). Together
with the two regression tests in `Pptc/Scratch/CollapseTest.lean`, this is the intended
non-collapse story.
