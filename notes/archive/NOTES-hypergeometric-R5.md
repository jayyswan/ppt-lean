# NOTES-hypergeometric-R5

**The B6 gap after the bounding box: does inverting a second-kind arc length, or reading
curve extrema, open any route to a first-kind complete period?**

Research note, task **R5** of `PLAN-hypergeometric-00-overview.md` §7 (the "breakthrough"
restated after R1). No `.lean` file was created, edited or deleted; no `lean-lsp` tool and no
`lake` command was used. Numeric work used the **Wolfram Language kernel**
(`wolfram_WolframLanguageEvaluator`); no Python, no `sympy`. Script:
`archived files/hypergeometric-scripts/R5-box-b6-checks.wl`.

Labels:

* **[NC n]** numeric, checked to `n` significant digits (Wolfram);
* **[SY]** proved symbolically here, proof written out;
* **[CL]** classical, cited (not re-derived);
* **[SP]** speculative / not established.

Background read and relied on: `AGENTS.md`; `PLAN-hypergeometric-00-overview.md` (§2 V4, §4
H6, §5 B6/B7, §6–§7); `NOTES-hypergeometric-R1.md` §1, §2.3, §3, §4; `NOTES-hypergeometric-R4.md`
and `NOTES-hypergeometric-R4a/-b/-c`; `Pptc/Defs.lean`; `Pptc/PLAN-bounding-box.md`;
`Pptc/Box.lean`; `Pptc/BoxGraph.lean`; `Pptc/BoxOffset.lean`.

---

## 0. Answer in brief

**B6 is unchanged.** The bounding box does not move the first-kind obstruction, and the reason
is now sharper than R1's.

1. **Q1 — no.** The box inverts a **second-kind** arc-length function; a first-kind period is an
   integral of a **different** differential. Inverting an integral produces its **upper limit**
   (an abscissa/endpoint), never a period. On the graph `y = x⁶` (`m = 10`), the first-kind
   differential is `dx/√(1+x^10)`, but the arc-length density is `√(1+36x^10)dx`; a
   reparametrization `θ(t) = ∫₀^t dx/√(1+x^10)` changes only which differential is *available in
   the density*, not the integral the box reads. The first-kind incomplete integral at every
   box-produced abscissa is **strictly below** the complete period `A = (1/10)B(1/10,2/5) =
   1.1905798216203709653…` [NC 25]: e.g. at the genus-2 quartic abscissa `0.8104516200…`,
   `I(b) = 0.80615035` — the box reaches a *point*, not a cycle. PSLQ at 120 digits finds **no
   relation** between any box number and `A` or the other m=10 period [NC 120].

2. **Q2 — no.** An exhaustive density audit over all constructors and their compositions shows
   no arc-length density can equal the first-kind density `1/√(1+x^m)`: the two differ in sign
   of curvature (second kind `≥ 1`, first kind `≤ 1`), and the forced graph `f'² = x^m` is the
   old power law. The genus claim survives: **every object of `PConstructibleCurve` has genus
   ≤ 1** as a curve, and **no constructor produces a closed curve of genus ≥ 2** (details §2.4).

3. **Q3 — a new primitive is needed, and it can be phrased soundly but does not reach the full
   period.** Two shapes work: (a) a first-kind analogue of `arc_of_length` (a constructor whose
   traced speed is `1/√(1+x^m)`), or (b) a closed genus-≥2 base curve. Both stay countable (the
   data are P-constructible, so no free real parameter and no collapse). But even shape (a)
   yields only the **incomplete** integral at constructible lengths: the corresponding arc has
   **infinite** Euclidean length (`∫√(1+x^10)dx = ∞` beyond the first-kind range [NC 60]), so
   `L` finite never reaches `A`, which is a **supremum over the trace**, not a value at a
   P-constructible stage. Only the closed genus-≥2 curve (b) closes the period.

4. **Q4 — nothing new.** `BoxSine`, the offset extrema and the Legendre relations are all
   closed: sine's box inversion re-derives `ellipticEAm` (already landed), offset cusps are
   algebraic, and the Legendre relation only produces `π/2`. One red herring is recorded: the
   offset cusp abscissa `3.0151518126…` sits where `I(b) = 1.18755498`, numerically within 0.25%
   of `A` — a coincidence of a bounded algebraic endpoint, with no mechanism behind it [NC 25].

**One correction to R1.** R1's §3.2 table lists the second m=10 period as
`(1/10)B(1/5,3/10) = 0.7748481388…`. That number is `Γ(1/5)Γ(3/10)/(10√π)`, but it is **not** an
integral of the form `∫₀^∞ x^{p-1}/√(1+x^m)dx` [NC 60]: the genuine second period is
`(1/10)B(3/20,7/20) = 0.8935481715…`. The headline target `A` is unaffected and correct.

---

## 1. The target, and why it is new

### 1.1 The B6 target, restated precisely [CL] + [NC 30]

For the hyperelliptic curve `y² = 1 + x^m` the holomorphic differentials are
`x^k dx/y`, `k = 0,…,m−2`. The substitution `u = x^m` gives, for `1 ≤ p ≤ m/2 − 1`,

```
∫₀^∞ x^{p−1} / √(1+x^m) dx = (1/m) B(p/m, ½ − p/m).            (⋆)
```

At `m = 10` the two admissible periods (`p = 1` and `p = 3/2`) are

```
A := (1/10) B(1/10, 2/5)  = Γ(1/10)Γ(2/5)/(10√π)  = 1.1905798216203709653197821695…  [NC 30]
C := (1/10) B(3/20, 7/20) =                         0.893548171514111083764…          [NC 25]
```

`A` is exactly `∫₀^∞ dx/√(1+x^10)` [NC 25], the period R1 and PLAN §7 name; its `Γ` arguments
`1/10, 2/5` are not of the form `k/24` (`1/10 = 2.4/24`, `2/5 = 9.6/24`), so it lies outside
`Gamma.lean`'s denominator-24 family — denominators 5 and 10, genuinely new. `C`'s arguments
`3/20, 7/20` are likewise outside. Nothing here is re-derived; R1 §3.1–3.2 has the details.

### 1.2 Why the box *looked* like it might help

`PLAN-bounding-box.md` landed `PConstructible.box_xmax` / `box_ymax` (`Defs.lean:207–212`) and
`arcLength_inverse_Pconstructible` (`Box.lean:450`), whose content is: on a coordinate-monotone
tracing, the far endpoint of an `arc_of_length` stroke is P-constructible. `BoxGraph.lean:116`
sharpens this to **every drawable graph** at **every** P-constructible length `L ≥ 0`, with the
monotonicity side condition free because a graph tracing has `speed ≥ 1` and abscissa the
identity. The most exotic instance, `quarticUnitArcAbscissa` (`BoxGraph.lean:229`), inverts a
**genus-2** arc length: the abscissa `b₄` with `∫₀^{b₄}√(1+16x⁶)dx = 1`, value
`0.8104516200584422351…` [NC 18]. So the box reaches a genus-2 quantity. The question is whether
that genus-2 reach can be turned into a genus-2 **period**.

### 1.3 Why it cannot — the differentials are different [SY] + [NC 25]

Two facts, each fatal on its own.

**(i) Inversion returns a limit, not an integral.** The box computes
`sSup {x : (x,y) ∈ traced arc}` for a compact arc. W4 composes this with `arc_of_length`: given a
P-constructible length `L` and a tracing `γ`, it returns `γ b` where `arcLengthOf γ a b = L`.
That `b` is the **upper limit** of the integral `G(s) = ∫_a^s speed`. No operation integrates a
differential *around a cycle*: `arc_length` integrates over a bounded interval `[a,b]` of one
tracing with P-constructible **plane** endpoints, and the box measures extrema of a compact
curve. There is no cycle in the language.

**(ii) On a graph, the two densities are reciprocals-and-signs apart.** Parametrize `y = f(x)` by
`x`. The arc-length density is `√(1+f'²)dx`; demanding it equal the first-kind density
`dx/√(1+x^m)` forces

```
(1 + f'²) = 1/(1+x^m)   ⇒   f'² = −x^m/(1+x^m) < 0   (x ≠ 0),    (†)
```

a contradiction [SY]. Equivalently [SY]: if a real traced arc satisfies `speed γ(t) = 1/√(1+x(t)^m)`
then `(dx/ds)² + (dy/ds)² = 1` and `dx/ds = 1/√(1+x^m)`, so `(dy/dx)² = x^m` and the arc is the
graph of `y = ±(2/(m+2))x^{m/2+1} + c` — the *same power law* of R1 §1.4, whose own arc length is
`∫√(1+Cx^m)dx`, a **second-kind** integral. This reciprocal relation is the exact reason the two
problems do not meet: the second-kind density is `≥ 1`, the first-kind density is `≤ 1`.

Numerically, the first-kind incomplete integral `I(b) = ∫₀^b dx/√(1+x^10)` at the four box
numbers is [NC 25]:

| box number `b` | `I(b)` | `A = 1.1905798216…` |
|---|---|---|
| `parabolaHalfArcAbscissa` = 0.4463338855 | 0.44632752075442257192 | incomplete |
| `cubicUnitArcAbscissa` = 0.7907068936 | 0.78739563340806196996 | incomplete |
| `quarticUnitArcAbscissa` = 0.8104516201 | 0.80615035185856287907 | incomplete |
| `offsetCuspAbscissa` = 3.0151518126 | 1.18755498254455444 | incomplete |

Every value is `< A`; none is the complete period. A graph arc of finite Euclidean length simply
cannot carry the cycle.

### 1.4 The near-hit, and why it is a coincidence [NC 25]

The offset cusp abscissa `3.0151518126…` gives `I(b) = 1.18755498`, within 0.25% of `A`. This is
recorded so nobody mistakes it for a lead. `b` is **algebraic** (§2.3) and `A` is transcendentally
unreachable by such an endpoint; the proximity is an accident of `b ≈ 3` and the fast decay of
`x^{-5}`. PSLQ at 120 digits with tolerance `10^{-90}` finds no integer relation among
`{1, A, (1/10)B(1/5,3/10), b}` for **any** of the four box numbers [NC 120]. The tail is
`A − I(b) = 0.00302484`, a positive residue, not a vanishing identity.

### 1.5 Q1 verdict

**No box route to a first-kind period.** The box inverts a second-kind integral to an endpoint;
periods are integrals of a different differential around a cycle. The numerical target remains
unreached at every box value, and PSLQ excludes the obvious coincidences.

---

## 2. Exhaustive composite audit

Question: for every constructor in `Defs.lean` — every base curve and every closure operation,
**including compositions** — can its arc-length **density** be a first-kind differential
`dx/√(1+x^m)`, or any density whose complete integral is a Beta value at a new modulus? And is
every drawable curve (after all closure ops and compositions) still genus ≤ 1?

### 2.1 Base curves

| base curve | parametrization | `ds²/dt²` | first-kind density possible? |
|---|---|---|---|
| `ellipse` | `(a cos t, b sin t)` | `a² sin²t + b² cos²t` | no — bounded analytic, `(†)` forces a power law |
| `rectangle` | straight edges | `1` (unit speed) | no — `ds = dx` is not `dx/√(1+x^m)` |
| `poly_graph p`, deg ≤ 6 | `(t, p(t))` | `1 + p'(t)²` | no — `(†)` forces `p'² = x^m`, i.e. `p = Cx^{m/2+1}` |
| `power_law a b` | `(t, at^b)`, `t > 0` | `1 + a²b²t^{2b−2}` | no — same, and `x = 0` is excluded |
| `exp_two` | `(t, 2^t)` | `1 + (ln2·2^t)²` | no — `(†)`: `(ln2·2^t)² = −t^m/(1+t^m) < 0` |
| `sine` | `(t, sin t)` | `1 + cos²t` | no — `(†)`: `cos²t = −t^m/(1+t^m) < 0` |
| `cubic_bezier` | `(x(t), y(t))`, cubic | quartic `Q(t) = x'²+y'²` | no — see 2.2 |

For a **graph** the master statement is (†): the only graph whose length element is the
first-kind one is the power law `f'² = x^m`, and its own arclength is second kind [SY]. For
`poly_graph` this is exactly R1 §1.4; nothing about the box changes it, because the box reads a
graph's **inverse** arclength function, and the inverse of `∫√(1+x^m)dx` is still a second-kind
inverse.

### 2.2 Bézier, including affine images and compositions

A cubic Bézier has `x(t), y(t)` cubic, so `Q(t) = x'(t)² + y'(t)²` is **quartic** and
`speed = √Q`. For `speed` to equal `1/√(1+x(t)^m)`:

```
Q(t) = 1/(1 + x(t)^m)   ⇒   Q(t)·(1 + x(t)^m) = 1.
```

If `x` is nonconstant, `x(t)^m` is not a polynomial in `t` for non-integer `m`, so the product
cannot equal the constant `1`. If `x` is constant the curve is vertical, and `1+const` ≠ 1/Q
unless the curve is a point. For **integer** `m` the product is a polynomial of degree `3m ≥ 12`
whose leading coefficient is `(leading coeff of Q)·(leading coeff of x)^m`: for `Q` to be nonzero
(otherwise the speed vanishes and `(†)`-like positivity fails) the product has positive degree,
contradicting `= 1`. So no cubic Bézier, at any integer `m`, has the first-kind density. Affine
images (`translate`, `scale`, `rotate`) map a Bézier to another Bézier with transformed control
points (`linearMap_PConstructibleCurve`, `stretch_PConstructibleCurve`), so the conclusion is
unchanged. This is the Bézier half of R1 §1.5 and R4a, restated for the density rather than the
₂F₁ family.

### 2.3 Closure operations and compositions

| operation | effect on the density / curve | first-kind? | genus |
|---|---|---|---|
| `translate_x` / `translate_y` | `speed` unchanged; density re-expressed in shifted coordinates | no — same functional form shifted | 0/1 |
| `scale_x s`, `scale_y s` | `speed ↦ √(s²x'² + y'²)` | no — degree/coefficient change only | 0/1 |
| `rotate n` | orthogonal, `speed` unchanged | no | 0/1 |
| `restrict` | subset of the curve in a box | no — density inherited | ≤ orig |
| `arc_of_length` | a piece of `S`; density = the base density | no — inherited | ≤ orig |
| `offset d` | `speed_d = |1 − dκ|·speed` | no — see below | 0/1 |
| `box_xmax` / `box_ymax` | extracts a coordinate of an attained extreme | no — no integral at all | — |

**Offset, precisely.** `unitNormal` is built from `γ'`, so `offset(γ)_x' = x' + d·(n_x)'`; Frenet
gives the offset velocity `(1 − d·κ(s))·γ'(s)`, hence

```
speed(offsetParam γ d) = |1 − d·κ|·speed γ.
```

Demanding this equal `1/√(1+x^m)` is an identity between `|1 − dκ|·speed` and a first-kind
density; either side is positive/analytic, and the same power-law argument as (†) fails: the
offset of a graph is not a graph, but on the arc the equality again forces `speed = 1/√(1+x^m)`
up to the elementary factor `|1 − dκ|`, i.e. `speed` must be the first-kind density divided by
an elementary function of the same arc — impossible because `speed ≥ 1` while
`1/√(1+x^m) ≤ 1`, equality only at `x = 0`. This is R4b's `ds_d = ds − d·dφ` seen at the density
level: `offset` adds an elementary turning-angle term to a second-kind density and cannot flip
its kind. The same argument applies to **compositions**: `offset` of an `arc_of_length` arc of an
offset of an affine image of `poly_graph` is still a regular parametrized arc of a graph's
function field, with `speed = (elementary)·√(1+Cx^m)`, never `1/√(1+x^m)`.

### 2.4 The genus claim, revisited carefully

* **No constructor increases genus.** The base curves have genus 0 (`rectangle`, `poly_graph`,
  `power_law`, `exp_two`, `sine`, `cubic_bezier` are all parametrized by rational functions or by
  a single exponential/trig parametrization, hence function field of genus 0 or non-algebraic) or
  genus 1 (`ellipse`). An affine image preserves genus. `restrict` is intersection with a
  half-open box — a subset, hence no new function field. `arc_of_length` yields a subset of `S`.
  `offset` is a local diffeomorphism of the arc (its derivative `(1−dκ)γ'` vanishes only at
  isolated cusps), so the offset arc is the image of an interval/circle: genus 0 or a curve in
  the same pencil as the base. Compositions are compositions of these maps.
* **No closed curve of genus ≥ 2.** `Defs.lean` has exactly one closed base curve, `ellipse`, and
  the rectangle boundary; everything else is an unbounded or open graph. `restrict` can form a
  closed loop only as an arc of the ellipse glued to rectangle edges, whose underlying algebraic
  curve is the ellipse (genus 1); the intersection of a graph with a box boundary is a graph over
  a closed interval (genus 0). `Box.lean` itself already proves the relevant compactness facts
  (`isCompact_restrict_of_isClosed`, `isCompact_restrict_poly_graph`), and those sets are subsets
  of genus-0/1 curves. The arclength double cover of `y = x^n`, `y² = 1+Cx^{2n−2}` (genus
  `⌊(2n−1)/2⌋ = n−1`), is **not** a constructor: it is the auxiliary Riemann surface on which the
  second-kind integral lives, not a drawable curve.
* So the re-audited claim is the same as R1 §1.6, now with the precise qualifier: **every member
  of `PConstructibleCurve` is a finite union of arcs of a genus-≤1 curve; in particular no
  member is a closed genus-≥2 curve.** [SY]

### 2.5 Q2 verdict

No constructor and no composition yields a first-kind density. No constructor yields a closed
genus-≥2 curve. Both negatives are structural (positivity of `(†)`, degree of the Bézier
quartic, function-field preservation), not endpoint accidents.

---

## 3. Is a new primitive needed, and can it be sound?

### 3.1 What the primitive must look like

Two shapes, in the style of `Defs.lean`:

**(a) First-kind arc-laying constructor** — the exact mirror of `PConstructible.arc_length`
(`Defs.lean:151`) with the *speed prescribed*:

```lean
| first_kind_arc {m : ℚ} (hm : PConstructible (m : ℝ)) (hmpos : 0 < m)
    (γ : ℝ → ℝ × ℝ) {a b : ℝ} (hab : a ≤ b)
    (hsub : γ '' Set.Icc a b ⊆ {p | p.2 = ...})            -- traces the first-kind arc
    (hinj : Set.InjOn γ (Set.Icc a b))
    (hdiff : ...) (hint : IntervalIntegrable (speed γ) volume a b)
    (hspeed : ∀ t ∈ Set.Icc a b, speed γ t = (1 + (γ t).1 ^ m) ^ (-(1/2) : ℝ))
    (hx₀ : PConstructible (γ a).1) (hy₀ : PConstructible (γ a).2) :
    PConstructibleCurve (γ '' Set.Icc a b)
```

More cleanly still, one states it **on the integral directly**, using `integral_hasDerivAt`:

```lean
| first_kind_length {m : ℚ} (hm : PConstructible (m : ℝ)) (h : 0 < m)
    {a b : ℝ} (hab : a ≤ b)
    (hx₀ : PConstructible a) (hx₁ : PConstructible b) :
    PConstructible (∫ x in a..b, (1 + x ^ (m : ℝ)) ^ (-(1/2) : ℝ))
```

with `a, b` P-constructible (or the lower limit a P-constructible plane point) — this is the
pure first-kind integral over a bounded interval. Its box-inverted form is the new function
`X_m^{-1}(L)`, the arc-length parametrization of `y' = x^{m/2}`.

**(b) A closed genus-≥2 base curve** — e.g. a constructor for the fixed smooth projective
compactification of `y² = x^6 + x + 1` (genus 2, real locus one oval), or for the fixed
"drawable genus-2 oval" of the plan. Then the period is available directly, without any
arc-length or box step.

### 3.2 Soundness: does either collapse `PConstructible` to all of `ℝ`?

**No, provided the family is parameterized by P-constructible data only.** This is exactly the
discipline that makes `box_xmax` sound (`Defs.lean:177–206`) and that the failed `⊆`-form of the
box violated (`PLAN-bounding-box.md` §0): "subset of a constructible curve" admits every subset
of the parabola, so a free `b = r` returns `r`. The primitives above avoid this:

* In (a), the free data are `m` and the plane endpoints `γ a`, `γ b` (or the interval endpoints
  `a, b`); all are P-constructible, hence countably many. The traced speed is *pinned* to
  `1/√(1+x^m)` by `hspeed`, so the arc is determined by `m` and the start — no free real enters.
* In (b), the fixed curve is a single point-set; a family `{V_h}` indexed by P-constructible `h`
  is countable.

Two dangers, both avoidable but worth naming:

1. **A free real parameter.** `first_kind_length` with a *free* `b` (no `PConstructible b`)
   collapses: take `a = 0`, any `r`, `b = r`, and the constructor returns the numerically
   P-constructible integral to `r`. Ordering `hx₁ : PConstructible b` is the whole safety.
2. **A limit/`sSup` operation.** The box is safe because `IsCompact` makes the sup *attained*
   (`IsCompact.sSup_mem`). A first-kind primitive stated as "the sup over the trace" without
   attainment reintroduces the `power_law`-at-`x=0` failure and would assert that an infinite
   limiting process is finite. The constructions above have no such step.

### 3.3 The catch: even a sound first-kind primitive does **not** reach `A`

This is the sharpened negative, and it is independent of the soundness analysis. Suppose shape
(a) is added. Its length datum is a P-constructible `L ≥ 0`; the first-kind integral is
`s ↦ ∫_a^{X(s)} dx/√(1+x^m)`, and the primitive returns the abscissa reached at first-kind
length `L`. Because `(1+x^m)^{-1/2} ≤ 1`, the abscissa is at most `L`, and as `L` grows the
first-kind measure saturates at `A = 1.1905798…`, the **supremum over the infinite trace**. For
every finite P-constructible `L` the value is `< A`; the complete period is attained only "at
`x = ∞`". Equivalently, the corresponding **Euclidean** arc has infinite length:

```
∫₀^X √(1+x^10) dx  =  126.2193315847936782…   at X = 3.0151518126, and → ∞ as X → ∞.  [NC 60]
```

So the tracing can never be compact over the full first-kind range: no `arc_of_length` stroke
with finite P-constructible length covers it. To *close* the period you need the cycle returned
by shape (b): a closed genus-≥2 curve. Shape (a) is a sound, genuinely new primitive that
produces many new numbers (all the incomplete values `∫_a^b dx/√(1+x^m)` at P-constructible
`a, b` — themselves arguably outside the current class), but **not** `A`.

### 3.4 Q3 verdict

A new primitive is required and can be stated soundly (3.1). But a first-kind integral
constructor yields only incomplete values; the complete period `A` needs **a closed drawable
curve of genus ≥ 2**. The plan's phrase "a primitive that lays a first-kind hypergeometric
differential along a **bounded** arc" is therefore not sufficient as written — the bounded arc
gives the incomplete integral. The load-bearing replacement is: *a closed drawable genus-≥2
curve*, or an explicit `sSup`-free attainment mechanism on the first-kind trace.

---

## 4. Anything else new? (Q4)

R4 closed the inbound map; the box adds three new mechanisms to check. All are closed:

1. **`BoxSine` / sine box inversion** (`Pptc/BoxSine.lean`,
   `ellipticEAm_Pconstructible_via_sine`). The sine arc length is `√2·E(X|½)`, whose inverse is
   `ellipticEAm` at a P-constructible parameter — already landed (`Jacobi.lean`). It is a
   *cross-check of the axiom*, explicitly "landed but vacuous" (`PLAN-bounding-box.md` N3); it
   yields **zero** new numbers. [SY] from source.
2. **Offset extrema** (`BoxOffset.lean`). The offset cusp abscissa is **algebraic**: the cusp
   parameter `t*` is a root of the honest degree-12 polynomial `D(t)³ − w(t)²`
   (`D = x'²+y'²`, `w = x'y'' − y'x''`) [SY], and the abscissa `x(t*) − y'(t*)/√D(t*)` is
   algebraic of degree ≤ 24. It is new relative to `inter_x`/`inter_y` (B7/B12), but it is an
   **algebraic** number: it cannot contribute a `Γ` product, and it cannot equal `A`. No route
   here.
3. **Legendre relations / `K`,`E` mix** (R4a §4b). The Legendre relation
   `E(k)K(k') + E(k')K(k) − K(k)K(k') = π/2` at the box-reachable `k = 1/√2` evaluates to `π/2`
   [NC 60], and `π` is already P-constructible. No new constant.
4. **Gauss's second theorem at `a = 1/10`** (`₂F₁(1/10,9/10;1;½) = √π/(Γ(11/20)Γ(19/20))`)
   is the B1 runner-up, not B6, and needs a mechanism outside the Schwarz list (R1 §2.5). The
   box does not supply one. [NC 25] for the value.
5. **Quartic (genus-2) arc inverse** (`quarticUnitArcAbscissa`). The box reaches a genus-2
   *inverse* but the value is the inverse of a second-kind integral; §1.3–1.4 show it is not a
   first-kind period. The most exotic box number remains just that, and nothing more. [SP] that
   its transcendence is provable with current tools.

No other unexplored route was found. The inbound map is exactly: the elliptic class, the graph
family, and the `z=1` Γ route (R4 §0); the box adds no fourth field.

---

## 5. Label ledger

| statement | label | where |
|---|---|---|
| `A = (1/10)B(1/10,2/5) = ∫₀^∞ dx/√(1+x^10) = 1.1905798216…` | [CL] + [NC 30] | §1.1 |
| `C = (1/10)B(3/20,7/20) = 0.89354817…` is the second m=10 period | [SY] + [NC 25] | §1.1, correction |
| R1's `(1/10)B(1/5,3/10) = 0.7748481…` is not an integral of the `(⋆)` form | [SY] + [NC 60] | §0, §1.1 |
| box inverts a second-kind integral to an endpoint, never a period | [SY] | §1.3 |
| `speed = 1/√(1+x^m)` ⇒ `f'² = x^m` (power law); first kind ≤ 1 vs second kind ≥ 1 | [SY] | §1.3 |
| `I(b) < A` at all four box abscissas | [NC 25] | §1.3 |
| PSLQ: no relation `{1,A,D,box}` at 120 wp / tol 1e−90 | [NC 120] | §1.4 |
| no Bézier/image/offset/composition density is first-kind | [SY] | §2.2–2.3 |
| every `PConstructibleCurve` member has genus ≤ 1; no closed genus-≥2 curve | [SY] | §2.4 |
| offset cusp abscissa `3.0151518126…` is algebraic (cusp param, degree-12 `D³−w²`) | [SY] + [NC 40] | §4 |
| first-kind curve `y = (1/5)arcsinh(x^5)` has infinite Euclidean arclength | [SY] + [NC 60] | §3.3 |
| `quarticUnitArcAbscissa` inverts a second-kind, not first-kind, integral | [NC 18] + [SY] | §1.2 |
| sine box inversion (`BoxSine`) yields no new numbers (N3) | [SY] source | §4 |
| Legendre relation at `k=1/√2` gives only `π/2` | [NC 60] | §4 |

No `sorry`, no Lean file touched.

---

## 6. Scripts

| script | contents |
|---|---|
| `archived files/hypergeometric-scripts/R5-box-b6-checks.wl` | box constants and back-substitution; m=10 periods `A`, `C`; first-kind incomplete integrals; coincidence/PSLQ tests; cusp parameter degree-12; Legendre check |

Source of every number above: the **Wolfram Language kernel** (MCP
`wolfram_WolframLanguageEvaluator`). No Python was used.
