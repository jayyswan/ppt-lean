# Notes: the one algebraic lead — offset cusps (plan §3.N6 / task B7)

Research note. No `.lean` file was created, edited or deleted; no `lake` command and no
`lean-lsp` tool was used. Every exact-symbolic and every numeric witness below was computed
with the Wolfram kernel (`wolfram_WolframLanguageEvaluator`); the backend is stated per
number. Exact factorisations, resultants and irreducibility tests use Wolfram's exact
rational arithmetic; numerics use `FindRoot` / `NMaximize` / `NSolve` at
`WorkingPrecision -> 120`, and each value was back-substituted at that precision.

Labels follow the house convention: `[SY]` exact/syntactic (here: exact symbolic identity or
exact factorisation, computed in Wolfram, **not** formalized in Lean), `[NC n]` numeric to
`n` digits from a computation actually run at that precision, `[SP]` speculative.
Corrections to `PLAN-bounding-box.md` §3.N6 and to
`Hypergeometric/NOTES-defs-arc-endpoint-extraction.md` are flagged **CORRECTION**.

---

## 0. Verdict

- **Degree count.** A cubic-pair offset's cusp parameters solve a degree-**12** equation in
  `t`, but the plan's stated reason is wrong: `x'y'' − y'x''` is at most **quadratic**, not
  cubic, for a pair of cubics. The degree-12 count survives because `x'² + y'²` is quartic
  and its cube dominates. **CORRECTION** to plan N6. `[SY]`
- **Concrete.** Two explicit examples (`d = 1`, rational control data) give cusp polynomials
  that are **irreducible of degree 12 over `ℚ`**, with real genuine cusps. `[SY]` exact
  Wolfram + `[NC 50]` parameters + `[NC 40]` points.
- **Escape verdict: y — with caveats.** For a generic cubic pair the cusp *parameter* and the
  cusp *coordinate* are algebraic of degree **12** over `ℚ`; the degree-10 crossing engine in
  `Offset.lean`, the degree-7/8 theorems and the degree-9 nonic provably cannot present such a
  number (a degree-12 number is the root of no polynomial of degree ≤ 10). So the cusp is
  outside the *direct* algebraic reach of the crossing machinery. `[SP]`
  - Caveat 1 (real): the symmetric example `(x,y) = (t,t³)`, `d = 1` — the cleanest one —
    has cusp parameter `t*` with `t*²` a root of an **irreducible sextic**; hence
    `t* = √(PConstructible)` is *already* PConstructible via `root_Pconstructible_le_six_coeffs`
    + `sqrt_Pconstructible`, with no box. So cusp numbers are **not automatically new**;
    genericity matters. `[SY]` exact.
  - Caveat 2: no non-constructibility proof exists (plan §7), and iterated towers of degrees
    ≤ 6/7/8/9/10 are not excluded; the degree-12 minpoly only excludes *direct* presentation
    by a single low-degree polynomial. `[SP]`
- **Window/isolation.** The plan's "expect the window argument to be the hard part" is
  **half right**. The §3b self-referential-bound failure does **not** transfer literally: a
  cusp is a critical point of the offset (`Γ' = 0`), hence a genuine local coordinate
  extremum, and isolating it needs only the `offset` constructor's own *parameter* window
  (`restrict` in the plane is unnecessary and is where §3b would bite). What remains is a
  real but tamer obligation: prove that `κ − 1/d` has a single sign change in the window. `[SP]`
- **Both examples need no window at all**: over the natural `[0,1]` stroke, the cusp is
  already the global `x`-extremum, so `box_xmax` returns the cusp abscissa directly. `[NC 40]`

---

## 1. The Frenet observation `[SY]`

Write `γ t = (x t, y t)`, `w = √(x'² + y'²)` (the `speed` of `Defs.lean`), unit normal
`N = (−y'/w, x'/w)`, and offset `Γ t = γ t + d·N t`. In the plane the Frenet equation is
`dN/ds = −κT` (`τ = 0`), so `dN/dt = −κ·w·T = −κγ'` and

    Γ'(t) = γ'(t) + d·N'(t) = (1 − d·κ(t))·γ'(t),   κ(t) = W(t)/w(t)³,
    W(t) := x'(t)y''(t) − y'(t)x''(t).

This was checked exactly for a general cubic pair `x = c₃t³+c₂t²+c₁t+c₀`,
`y = e₃t³+e₂t²+e₁t+e₀` and general `d` in Wolfram (`Simplify` of the residual returned
`{0, 0}`). `[SY]` exact.

Consequences, exactly as the plan states:

- Each coordinate's derivative is `(Γ_x)' = (1 − dκ)·x'` and `(Γ_y)' = (1 − dκ)·y'`, so the
  coordinate-critical parameters of the offset are the union of
  - the *base* critical points `x'(t) = 0` (resp. `y'(t) = 0`) — for a cubic pair a
    **quadratic**, i.e. reachable by `sqrt`; and
  - the cusps `1 − d·κ(t) = 0`.
- Geometric reading worth recording: at a cusp `d = 1/κ`, so `Γ(t*) = γ(t*) + (1/κ)N(t*)` is
  the **centre of curvature** of the base curve at `t*`. The offset cusps are exactly where
  the offset meets the base curve's evolute.
- At a cusp `Γ'(t*) = 0`. With `x'(t*) ≠ 0` (transverse to the `y`-axis) and `κ'(t*) ≠ 0`,
  `(Γ_x)''(t*) = −κ'(t*)·x'(t*)`, so the cusp is a genuine local extremum of the coordinate,
    not merely stationary.

**CORRECTION (plan N6).** The plan says "`x'y'' − y'x''` is a cubic". For a pair of cubics
`x', y'` are quadratic and `x'', y''` linear; the `t³` terms of the two products cancel
identically (`3c₃t²·6e₃t − 3e₃t²·6c₃t = 0`). Wolfram gives the general forms `[SY]` exact:

    W(t) = (−2c₂e₁ + 2c₁e₂) + (−6c₃e₁ + 6c₁e₃) t + (−6c₃e₂ + 6c₂e₃) t²,        deg W ≤ 2
    Q(t) = (c₁²+e₁²) + 4(c₁c₂+e₁e₂) t + (4c₂²+6c₁c₃+4e₂²+6e₁e₃) t²
             + 12(c₂c₃+e₂e₃) t³ + 9(c₃²+e₃²) t⁴.                            deg Q ≤ 4

The plan's degree-12 *conclusion* is nonetheless right, for a different reason (§2).

---

## 2. The degree count `[SY]`

`Q = x'² + y'²` is quartic and `W` is at most quadratic, so the squared cusp condition

    (x'² + y'²)³ = d²·(x'y'' − y'x'')²                                          (★)

is a polynomial equation of degree `max(12, 4) = 12` in `t`. For a genuine cubic pair
(`c₃,e₃` not both `0`) the `t¹²` coefficient is `729·(c₃²+e₃²)³ ≠ 0`, so the degree really is
12 (it drops only if the pair degenerates below cubicity). `[SY]` exact.

**CORRECTION (plan N6 / note §5.3).** The equation actually satisfied by a genuine cusp is
the *unsquared* `w³ = d·W`, equivalently `κ = 1/d`; `(★)` is its square and acquires
spurious real roots where `w³ = −d·W` (i.e. `κ = −1/d`). For `d > 0` the genuine cusps are
exactly the real roots of `(★)` with `d·W > 0`; the rest are the offset's other stationary
points. This sign split is visible in Example B below and matters if one wants to *name* the
cusp rather than just bound it.

As the plan notes, a degree-12 *equation* need not have a degree-12 *root*. In both examples
below it does: the polynomial is irreducible, so each of its roots has degree exactly 12.

---

## 3. Concrete computation `[SY]` exact + `[NC 20]`

All exact quantities (`FactorList`, `IrreduciblePolynomialQ`, `Resultant`) are exact Wolfram
rational computations; all displayed decimals come from `FindRoot` at
`WorkingPrecision -> 120` and were back-substituted at that precision (residuals quoted).

### 3.1 Example A — the symmetric case `x = t`, `y = t³`, `d = 1` (a cautionary example)

Bernstein form: control points `(0,0), (1/3,0), (2/3,0), (1,1)`. Then
`Q = 1 + 9t⁴`, `W = 6t`, and `(★)` is

    729 t¹² + 243 t⁸ + 27 t⁴ − 36 t² + 1 = 0.

- **Factorization:** irreducible over `ℚ`; degree 12. `[SY]` exact.
- **Real roots:** `±0.16848298708195529940647787015496915331504638282383` and
  `±0.63136339146010667972957681780739825223818844092456`. `[NC 50]`
- **Genuine cusps (`d = 1`, so `κ = +1 > 0`):** the two **positive** roots. With `x' = 1`,
  `Γ_x = t − 3t²/√(1+9t⁴)`, so the cusp at `t* = 0.16848298708195529940647787015496915331504638282383`
  is a local **max** of `Γ_x`, and the cusp at `0.631363…` a local **min**.
  `[NC 50]`
- **Cusp points** `Γ(t*) = (x − y'/w, y + x'/w)`:
  - `t* = 0.16848298708195529940647787015496915331504638…`
    → point `(0.08363056166992986701199251781422070395614, 1.001176174802846934063925719926321849720)`
    `[NC 40]`
  - `t* = 0.63136339146010667972957681780739825223818844…`
    → point `(−0.1357681365849395700723299029232665395591, 0.8931637489519674729523701195303905561020)`
    `[NC 40]`
- **Back-substitution:** `(★)` at `t*` residual `≈ 1e−119`; the coordinate minpolys below
  at the points `≈ 1e−117`, `1e−110`. `[NC 100]`-ish (residual at WP 120).
- **Coordinate minimal polynomials** (both irreducible, degree 12, **even**):
  - `X:  11664 U¹² − 58320 U¹⁰ + 120528 U⁸ − 12960 U⁶ + 194184 U⁴ − 4932 U² + 25`
  - `Y:  6198727824 V¹² − 6198727824 V¹⁰ + 25509168 V⁸ − 1700611200 V⁶ + 9349459992 V⁴ − 14806354500 V² + 7119815641`
  `[SY]` exact.
- **CORRECTION / caution.** Because `(★)` here is even in `t` (`t*²` satisfies
  `g(u) = 729u⁶ + 243u⁴ + 27u² − 36u + 1`, which Wolfram confirms is **irreducible of degree
  6**), `t* = √(t*²)` is already `PConstructible` by `root_Pconstructible_le_six_coeffs`
  (`t*² > 0`) followed by `sqrt_Pconstructible`. Likewise the even coordinate polys make the
  cusp coordinates square roots of degree-6 numbers. **This symmetric example is therefore
  not a new number and must not be quoted as one.** It is in the note precisely as the
  counterexample to any blanket claim that cusp parameters lie outside the current reach.
  `[SY]` exact.
- **Box behaviour (see §5):** over `[0,1]`, `NMaximize` gives `Γ_x` max
  `0.08363056166992986701199251781422070395614` at the cusp `t*`, and `NMinimize` gives `Γ_y`
  min `0.8931637489519674729523701195303905561020` at the other cusp. `[NC 40]`

### 3.2 Example B — a genuinely cubic pair, `d = 1` (the substantive example)

Cubic Bézier with control points `P₀=(0,0), P₁=(0,2), P₂=(2,0), P₃=(3,0)`, so

    x(t) = 6t² − 3t³,   y(t) = 6t − 12t² + 6t³,   c₃ = −3 ≠ 0, e₃ = 6 ≠ 0,

a genuine cubic-in-both-coordinates pair with small rational control data. `Q` is the quartic
`36 − 288t + 936t² − 1080t³ + 405t⁴` and `W = −72 + 108t` (here even linear).

- **Cusp polynomial** `(★)` (primitive part of `Q³ − W²`, after dividing the content 81):

      820125 t¹² − 6561000 t¹¹ + 23182200 t¹⁰ − 47628000 t⁹ + 63126540 t⁸ − 56738880 t⁷
        + 35499456 t⁶ − 15669504 t⁵ + 4892400 t⁴ − 1065600 t³ + 155376 t² − 13632 t + 512 = 0.

- **Factorization:** irreducible over `ℚ`; degree 12. `[SY]` exact.
- **Real roots** `[NC 40]`: `0.09991740968364765042608838276415505568277`,
  `0.3642476555014106799667620253852552277316`,
  `0.9690856778319226533665713079480781056018`,
  `1.233415923649685682907244950569178277651`.
- **Genuine cusps:** `W = 108t − 72 > 0` iff `t > 2/3`, and `κ = +1` there, so the genuine
  cusps for `d = 1` are the two large roots `0.969085…` and `1.233415…`; the two small roots
  are the spurious `κ = −1` roots of the square. Only `t* = 0.96908567783192265336657130794807810560176`
  lies in the drawn stroke `[0,1]`. `[NC 50]`
- **Cusp point** `Γ(t*)`:

      (3.015151812639309983896917609276868074014, 0.9994137526624290102026815591764698149397)   [NC 40]

- **Back-substitution:** `(★)` at `t*` residual `≈ 1e−110`; the `X`-coordinate minpoly below
  at the point `≈ 1e−97`; `κ(t*) = 1` to 30 digits. `[NC 30]+`
- **Minimal polynomials** (all irreducible, all degree **12**; resultants computed exactly):
  - cusp parameter squared, `t*² = 0.9391270509789569851908554714…`, minpoly
    `672605015625 s¹² − 5022117450000 s¹¹ + … − 26726400 s + 262144` — degree 12. So `t*` is
    **not** a square root of a degree-6 number; `[ℚ(t*):ℚ] = 12` and `t* ∈ ℚ(t*²)`.
  - `X`-coordinate: `5189853515625 U¹² − 110716875000000 U¹¹ + … + 14959679998135428` — degree 12.
  - `Y`-coordinate: `5189853515625 V¹² − 27679218750000 V¹¹ + … − 1978575740672` — degree 12.
  - `U²` and `V²` each have **irreducible degree-12** minimal polynomials as well, so neither
    cusp coordinate is a square root of a degree-6 number either. `[SY]` exact.
- **Heuristic only** `[SP]`: the discriminant is positive, and the factorisation types
  modulo `7, 11, 13` are `1+1+2+8`, `6+6`, `2+10`, consistent with a large (A₁₂/S₁₂-ish)
  Galois group. That is *evidence* against a small-degree subfield, not a reachability proof.

---

## 4. The comparison that matters `[SP]`

`Offset.lean:379` rationalises the crossing condition to the degree-**10** polynomial
`offsetCrossPoly = u²·(u'²+v'²) − d²(A²+B²)·v'²` (`offsetCrossPoly_normalForm`, `:815`), whose
real roots are provably `PConstructible` (`offsetCubicPair_axisCross_root_Pconstructible`,
`:722`) — and that family is itself only **codimension 3** inside degree-10 (`:775-810`).
`root_Pconstructible_le_eight`, the degree-7 theorem (`DegreeSeven.lean`), and the degree-9
nonic (`Nonic/Nonic.lean`) cover degrees 7, 8 and a special 9. Nothing there presents a
degree-12 number.

Compare with Example B:

- The cusp *parameter* and both cusp *coordinates* have **irreducible degree-12** minimal
  polynomials, so no degree-≤10 polynomial with rational coefficients vanishes on them.
  Directly: they are outside anything the degree-10 rationalisation can name. `[SY]` exact.
- The cusp polynomial `(★) = Q³ − d²W²` is *not* of the crossing normal form
  `u²(u'²+v'²) − D²v'²` (degree 10, with `u` cubic): the cusp equation cubes a quartic
  `Q`, while the crossing equation squares a cubic `u` times a quartic. Crossing the offset
  with a line cannot produce `(★)` — there is no cubic `g` with `g² = Q²`. So the degree-12
  cusp is not merely a higher instance of the same construction; it is a different shape.
  `[SY]`
- **Does the box reach it?** Yes, if the cusp is the box extremum. In Example B the offset
  arc over `[0,1]` has `NMaximize[Γ_x] = 3.015151812639309983896917609276868074014` **at the
  cusp** `t*` (`NMinimize` over `[0,1]` is `−1`, at `t = 0`). So `box_xmax` applied to the
  `offset` arc returns exactly the degree-12 cusp abscissa, with no `restrict` needed. `[NC 40]`

**Verdict.** `y`: cusp parameters (and coordinates) of a generic cubic-pair offset have
degree **12 > 10** and are outside the direct algebraic reach of the crossing engine; the
box, which carries no polynomial at all, presents them. But two honest hedges: (i) the
symmetric Example A is already reachable without the box, so this is a statement about
*generic* cubic pairs, not all cusps; (ii) "not presented by a degree-≤10 polynomial" is not
"not PConstructible" — the project cannot currently prove non-constructibility (plan §7),
and an iterated tower of the allowed degrees is not excluded. `[SP]`

---

## 5. Window isolation — what actually breaks `[SP]`

### 5.1 Why the §3b counterexample does not transfer verbatim

The note's §3b counterexample (unit-circle arc ending at `P = (cos x, sin x)`,
`3π/2 < x < 2π`) is about a point that is **not** critical: `P` is interior to the
projection onto both axes, so *no* axis-aligned window can make it extreme; the window's
`y`-bound that would exclude the shadowing arc stretch must lie in `[sin x, 0)`, i.e. must
encode the unknown `sin x`.

A cusp is different in kind. `Γ'(t*) = 0`, so the cusp is stationary for *both* coordinate
functions, and (with `x'(t*) ≠ 0`, `κ'(t*) ≠ 0`) it is a strict local extremum of each
coordinate. Therefore a short enough piece of arc around the cusp *does* have the cusp as a
coordinate extremum, and the isolating bound need not be the unknown.

### 5.2 The right window is the `offset` parameter interval, not `restrict`

`offset` already concludes `PConstructibleCurve (offsetParam γ d '' Icc u v)` for
`PConstructible u, v`. Take `u < t* < v` rational. On `[u,v]`:

1. `x' ≠ 0` throughout (transversality; choose `v` before the next base critical point), and
2. `κ − 1/d` changes sign exactly once, at `t*` (simple cusp; choose `u,v` so no other root
   of `(★)` with the correct sign lies inside).

Then `(Γ_x)' = (1 − dκ)x'` has one sign change, so `Γ_x` increases then decreases (or the
reverse) on `[u,v]` and `Γ_x(t) ≤ Γ_x(t*)` for all `t ∈ [u,v]` **by monotonicity alone** —
no comparison to the unknown number is needed. `box_xmax` on that arc returns `Γ_x(t*)`.
This is the same mechanism the box already uses for a monotone graph; it is not the §3b
mechanism. In both §3 examples the `[0,1]` stroke already satisfies this (the cusp is the
global extremum), so one does not even choose a sub-window.

### 5.3 What a sufficient isolation hypothesis has to look like

If one wants a general theorem, the hypothesis is a pair of rationals `u < v` (or a plane
box) together with:

- **regularity:** `x'(t) ≠ 0` on `[u,v]` (so no base critical point competes), and
- **uniqueness of the cusp:** `(κ − 1/d)` has exactly one zero in `[u,v]`, with a sign change
  — a root-isolation statement for the degree-12 `(★)` restricted to the genuine branch
  `dW > 0`;
- **no competing extremum:** either `u,v` bound a sub-arc on which the above already forces
  the cusp to be the extremum, or (if the cusp sits inside a larger fixed arc that shadows
  it) a plane `restrict` box whose other edges provably exclude the shadowing branch.

The last clause is where §3b can reappear: if the competing larger coordinate lies
arbitrarily close to the cusp, a plane-window bound must approach the cusp coordinate, and
"the bound is the unknown" returns. The remedy is to **not** use `restrict` but to shrink the
`offset` parameter window, which is available because the offset is being built here, not
handed over fixed. In Lean the surviving obligation is a real algebraic inequality
(`κ − 1/d` simple sign change in `[u,v]`), which is finite but non-trivial.

### 5.4 Does the plan's expectation hold?

Partly. The plan's `[SP]` "expect the window argument to be the hard part, not the algebra"
is defensible — isolating the cusp and proving it is the box extremum is the real work — but
its stated *reason* ("the isolating bound can be the unknown itself", citing §3b) does not
apply to a cusp, because a cusp is a critical point and hence a local extremum. The
difficulty is root isolation of the degree-12 cusp equation and monotonicity of `κ − 1/d` on
the window, not a self-referential window bound.

---

## 6. Corrections ledger

| target | correction | label |
|---|---|---|
| plan N6: "`x'y''−y'x''` is a cubic" | it is at most **quadratic** for a cubic pair (cubic terms cancel); general formula in §1 | `[SY]` Wolfram exact |
| plan N6 / note §5.3: cusp parameters escape current reach | true *generically* (degree 12, Ex. B), but **not** for symmetric cases: Ex. A's `t*` is `√(irreducible sextic root)`, already PConstructible | `[SY]` exact |
| plan N6: cusp equation degree 12 | confirmed, but the honest equation is `w³ = dW`; `(★)` is its square and has `κ = −1/d` spurious real roots | `[SY]` |
| note §5.3: "extrema are roots of the higher-degree polys already appearing in `Offset.lean`, whose values the project may or may not already reach" | resolved: the extrema are degree-**12** roots, *not* the degree-10 `Offset.lean` crossing polys; outside their direct reach | `[SY]` exact |
| plan N6: window/isolation is the hard part | half right: it is the proof burden, but §3b's unknown-bound circularity does not transfer to cusps (they are critical points) | `[SP]` |

## 7. Ledger

| claim | label |
|---|---|
| `Γ' = (1 − dκ)γ'`; coordinate extrema = base extrema ∪ cusps | `[SY]` symbolic residual `{0,0}` (Wolfram) |
| `W = x'y''−y'x''` has degree ≤ 2 (plan says cubic) | `[SY]` Wolfram exact |
| `Q = x'²+y'²` degree ≤ 4; `(★)` degree 12 | `[SY]` Wolfram exact |
| Ex. A `(x=t,y=t³,d=1)`: `729t¹²+243t⁸+27t⁴−36t²+1` irreducible deg 12 | `[SY]` exact |
| Ex. A genuine cusp `t* = 0.16848298708195529940647787015496915331504638282383` | `[NC 50]` Wolfram WP 120 |
| Ex. A cusp point `(0.08363056166992986701199251781422070395614, 1.001176174802846934063925719926321849720)` | `[NC 40]` Wolfram |
| Ex. A `t*²` root of irreducible sextic → `t*` already PConstructible | `[SY]` exact |
| Ex. B Bézier `(0,0),(0,2),(2,0),(3,0)`, `d=1`: cusp poly deg 12 irreducible | `[SY]` exact |
| Ex. B genuine cusp `t* = 0.96908567783192265336657130794807810560176` | `[NC 50]` Wolfram WP 120 |
| Ex. B cusp point `(3.015151812639309983896917609276868074014, 0.9994137526624290102026815591764698149397)` | `[NC 40]` Wolfram |
| Ex. B coordinate minpolys, and their squares' minpolys, all irreducible degree 12 | `[SY]` exact |
| Ex. B `box_xmax` over `[0,1]` returns the cusp abscissa; no `restrict` needed | `[NC 40]` Wolfram `NMaximize` |
| cusp numbers escape *direct* crossing reach (degree 12 > 10, different shape) | `[SP]` |
| generic cusps are new; towers not excluded; symmetric cases already reachable | `[SP]` |
| window isolation is the burden; §3b circularity does not transfer to cusps | `[SP]` |
