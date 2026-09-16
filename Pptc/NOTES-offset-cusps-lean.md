# Notes: B12 — is the offset cusp of the Bézier `(0,0),(0,2),(2,0),(3,0)`, `d = 1`
reachable by the crossing machinery, or genuinely new?

Research note. No `.lean` file was created, edited or deleted; no `lake` command and no
`lean-lsp` tool was used. Every exact-symbolic and every numeric witness below was computed
with the Wolfram kernel (`wolfram_WolframLanguageEvaluator`); the backend is stated per
number. Exact factorisations, resultants and irreducibility tests use Wolfram's exact
rational arithmetic; numerics use `Root` objects / `FindRoot` / `NMaximize` at
`WorkingPrecision -> 50..80`, and each value was back-substituted at that precision.

This is task B12 of `Pptc/PLAN-bounding-box.md` (§6 Wave 2), settling §3.N6. It follows
B7 (`Pptc/NOTES-offset-cusps.md`), whose Example B is this curve; B7's facts are
re-derived here independently, and its "genuinely new" verdict is re-examined against the
crossing machinery actually in the tree.

Labels follow the house convention: `[SY]` exact/syntactic (here: exact symbolic identity
or exact factorisation, computed in Wolfram, **not** formalized in Lean), `[NC n]` numeric
to `n` digits from a computation actually run at that precision, `[SP]` speculative.

---

## 0. Verdict

- **(a) Crossing machinery: no.** No currently formalized crossing presents this cusp.
  The cusp is a *critical point* of the offset (`Γ' = 0`), not an intersection of the
  offset with any constructible curve in the library. A crossing step reads a point
  coordinate through `inter_x`/`inter_y`, so it needs a constructible second curve through
  the cusp and a proof that the meeting is a singleton; the only natural such curve is the
  base curve's evolute (a rational curve, not in the library). The offset engine's own
  reach theorem reaches crossings of the offset with a **line**, whose rationalized equation
  is degree `10` and of a fixed shape; the cusp equation is degree `12` and a different
  shape. `[SP]`
- **(b) Genuinely new: yes, in the only sense the project can currently assert.** The
  cusp abscissa has an **irreducible degree-`12` minimal polynomial over `ℚ`** `[SY]`, so
  it is presented by no polynomial of degree `≤ 10` with *rational* coefficients — outside
  `root_Pconstructible_le_eight`, the `power_law` engines and the rational nonic. More
  importantly it generates the same degree-`12` field as the cusp parameter, so the two are
  inter-expressible and stand or fall together. But the crossing coefficients in
  `Offset.lean` are `PConstructible`, not rational, so the minpoly degree alone is **not**
  a non-reachability proof: iterated degree-`≤ 6` towers with `PConstructible` coefficients
  must be excluded, and the project does that by an `A₁₂`-type Galois argument, which is
  heuristic. So "genuinely new" can mean only "not reachable by any currently formalized
  construction **other than the box**"; the box *does* reach it. `[SP]`, with `[SY]`
  degree facts.
- **(Both).** The plan's N6 claim **survives scrutiny, with corrections**: the plan's
  phrase "genuinely new" should be read as "the first number the box reaches that no other
  landed construction reaches", and the degree-`12` argument is necessary but not
  sufficient without the tower argument. `[SP]`
- **Lean, box route: a small/medium reachability task, plus a large identification task.**
  `PConstructible (sSup (Prod.fst '' A))` for the offset arc `A` follows from
  `box_xmax` once `A` is a `PConstructibleCurve`, `IsCompact` and nonempty — reusing
  `offsetCubicPairArc_PConstructibleCurve` (`Offset.lean:275`). That is the "reachability"
  half and is **small/medium**. Proving that this sup *is* the degree-`12` cusp abscissa
  (the "identification" half) needs the derivative factorisation `(Γ_x)' = (1 − dκ)x'`,
  root-isolation of the degree-`12` cusp equation on `[0,1]` and a monotonicity argument:
  **large**. `[SP]`

---

## 1. What a single crossing step actually presents

Three separate things in the tree, which must not be conflated.

### 1.1 `inter_x` / `inter_y` are unbounded in degree

`crossing_Pconstructible` (`Basic.lean:346`) produces the **coordinates** of a crossing of
two `PConstructibleCurve`s that meet in exactly one point, through the `inter_x`/`inter_y`
axioms (`Defs.lean:129,134`). Its docstring (`Basic.lean:337-341`) is explicit: the degree
of the equation solved is `max (i·deg x + j·deg y)` over the monomials `X^i Y^j` of the
implicit `F`, and "each construction buys its degree by choosing `F` and `Γ`". So there is
**no degree ceiling** on what a crossing can present — the reach is geometric (does a
constructible second curve pass through the point, and is the intersection isolable?),
not algebraic. This is the sharpest form of the "degree does not decide reachability"
subtlety. `[SY]` source.

### 1.2 The offset engine's explicit ladder

`Offset.lean` drives a specific crossing: the offset of a cubic pair against a **line**.
Its facts, precisely:

- `offsetCrossVal` (`Offset.lean:373`) is `w` times the line's implicit equation at the
  offset point; `offsetCrossPoly` (`Offset.lean:379`) is its rationalization,
  `g²·(x'²+y'²) − d²·h²`, degree at most `10` (`g` cubic, `x'²+y'²` quartic, `h` quadratic:
  `6 + 4 = 10`). `[SY]` source.
- The **crossing parameters** `β` are read off as follows
  (`offsetCubicPairCross_root_Pconstructible`, `Offset.lean:665`): the crossing *point*
  coordinates `(X, Y)` are first obtained through `crossing_Pconstructible` (hence
  `inter_x`/`inter_y`, no degree bound), and then `β` is recovered as a root of the
  **quintic** `normalEq_eq_quinticVal` (`Offset.lean:578`) with coefficients built from
  `X, Y` and the cubic coefficients. That quintic is fed to `quinticVal_root_Pconstructible`
  and hence `root_Pconstructible_le_six_coeffs`. So the *recovery* step is degree `≤ 5`.
- The degree-`10` `offsetCrossPoly` earns its keep only as the **finiteness** bound
  (`offsetCross_finite_roots`, `Offset.lean:402`) that `crossing_Pconstructible` needs for
  isolation. It is not the equation whose root is the answer. `[SY]` source.
- `offsetCrossPoly_normalForm` (`Offset.lean:815`) shows the crossing polynomial only ever
  has the shape `u²·(u'²+v'²) − D²·v'²` with `u` cubic, i.e. degree `≤ 10` and image
  codimension `3`; `cubic_bezier` pairs and lines cannot leave it. `[SY]` source.

### 1.3 The rest of the degree ladder

- `root_Pconstructible_le_six_coeffs` (`Basic.lean:1373`): real roots of degree `≤ 6`
  polynomials with **`PConstructible`** coefficients. Iterating it builds numbers in towers
  whose steps have degree at most `6` over the currently-reached field.
- `root_Pconstructible_le_seven` / `root_Pconstructible_le_eight` (`Basic.lean:587,633`):
  degree `≤ 7`/`≤ 8` over **`ℚ`**.
- `powerLaw_root_Pconstructible` (`Basic.lean:562`) and friends: `a·β^n = p(β)` with
  `p ∈ ℚ[X]` of degree `≤ 6` and `n > 6` (covers `n = 7, 8, …`).
- `nonicVal_root_Pconstructible` and `root_Pconstructible_of_rat_nonic_nonreal`
  (`Nonic/Nonic.lean:63`): degree `9` over `ℚ`, with a nonreal root.
- `root_Pconstructible_of_nonreal_root` (`DegreeSeven.lean:4488`): degree `7` over `ℝ[X]`
  with a nonreal root.

**The key subtlety, stated exactly.** A crossing step presents a number that is a root of
a polynomial whose coefficients are built from `PConstructible` inputs, *not* from `ℚ`.
Therefore a degree-`12` minimal polynomial over `ℚ` excludes only *direct presentation by a
single rational polynomial of degree `≤ 10`* (i.e. `root_Pconstructible_le_eight`, the
rational nonic, the `power_law` engines). It does **not** exclude an **iterated tower** of
degree-`≤ 6` steps with `PConstructible` coefficients, which is exactly what `Offset.lean`
itself uses to reach its degree-`10` numbers: they are roots of a degree-`10` polynomial but
become P-constructible because the crossing geometry supplies the point and the degree-`5`
recovery supplies the parameter. Whether the cusp falls to a tower is a *separate* question
from its minpoly degree.

---

## 2. The concrete value (Wolfram, exact + high precision)

Curve: Bézier control points `P₀=(0,0), P₁=(0,2), P₂=(2,0), P₃=(3,0)`, so

    x(t) = 6t² − 3t³,   y(t) = 6t − 12t² + 6t³    (= cubicPairParam 0 0 6 −3  0 6 −12 6)

with `d = 1`. The curve is a genuine cubic pair (`c₃ = −3`, `e₃ = 6`).

### 2.1 Frenet data `[SY]` exact

    x'(t) = 12t − 9t² = 3t(4 − 3t),    x'' = 12 − 18t
    y'(t) = 6 − 24t + 18t²,           y'' = −24 + 36t
    Q(t)  = x'² + y'² = 36 − 288t + 936t² − 1080t³ + 405t⁴            (degree 4)
    W(t)  = x'y'' − y'x'' = −72 + 108t                                 (degree 1)
    cusp equation (★):  Q³ − d²W² = Q³ − W²                            (degree 12)

Confirmed by Wolfram: `Exponent[Q,t]=4`, `Exponent[W,t]=1`, `Exponent[Q³−W²,t]=12`. `[SY]`

### 2.2 Cusp polynomial, factorisation, irreducibility `[SY]` exact

    Q³ − W² = 81 · P(t),
    P(t) = 820125 t¹² − 6561000 t¹¹ + 23182200 t¹⁰ − 47628000 t⁹ + 63126540 t⁸
           − 56738880 t⁷ + 35499456 t⁶ − 15669504 t⁵ + 4892400 t⁴
           − 1065600 t³ + 155376 t² − 13632 t + 512.

- `PolynomialGCD` of the coefficients is `81`; `P` is primitive.
- `FactorList[cusp] = {{81,1}, {P(t),1}}`; `IrreduciblePolynomialQ[P] = True`. Degree 12,
  **irreducible over ℚ**. `[SY]`
- Real roots of `P` (`[NC 30]`): `0.0999174096836476504260883827642`,
  `0.364247655501410679966762025385`, `0.969085677831922653366571307948`,
  `1.23341592364968568290724495057` (the remaining 8 roots are two complex-conjugate
  quadruples).
- `W(t) = 108t − 72 > 0 ⟺ t > 2/3`, so the **genuine** cusps (`κ = +1/d`) are the two
  large roots; `0.0999…` and `0.3642…` are the spurious `κ = −1` roots of the square.

### 2.3 The genuine cusp parameter `[NC 60]`

`t* = Root[P, 3] = 0.969085677831922653366571307948078105601764278062112436550816`

`prim(t*)` residual `≈ 1e−45` at WP 60. `W(t*) = 32.6612532058476465635897012584`
`[NC 30]`, `Q(t*) = 10.2177489925890854623398983291` `[NC 30]`, so `t* > 2/3` and the
cusp is genuine. `W(t*) − Q(t*)^{3/2} = 0` to `1e−75` at WP 80 (`κ(t*) = 1`). `[NC]`

### 2.4 The cusp point, and the box fact `[NC 40]` + `[NC 50]`

    Γ(t*) = (3.015151812639309983896917609276868074014,
             0.9994137526624290102026815591764698149397)

This agrees with B7's Example B to all 40 digits (independently recomputed here via both
the direct `x − y'/w`, `y + x'/w` form and the rational form `(xW − y'Q)/W`,
`(yW + x'Q)/W` — they agree because at a genuine cusp `√Q = W/Q`). `[NC 40]`

`NMaximize[Γ_x, 0 ≤ t ≤ 1]` returns `3.0151518126393099838969176092768680740` **at the
cusp**; `NMinimize` returns `−1` at `t = 0`; `Γ_x(1) = 3` exactly, `Γ_x(1/3) = 5/9`. So over
the drawn `[0,1]` stroke the cusp is the **global abscissa maximum**, and `box_xmax` on the
offset arc returns exactly the cusp abscissa with no `restrict`. `[NC 50]`

### 2.5 Minimal polynomials of the coordinates `[SY]` exact

Eliminating `t` between `P(t)` and `X = (xW − y'Q)/W` (resp. `Y = (yW + x'Q)/W`) by
resultant gives a degree-`12` polynomial in `X` (resp. `Y`) that `FactorList` shows to be a
constant times a **single irreducible degree-`12`** factor. `[SY]`

    minX(X) = 5189853515625 X¹² − 110716875000000 X¹¹ + 983610255234375 X¹⁰
              − 4656004537500000 X⁹ + 12105834214792500 X⁸ − 13647217988160000 X⁷
              − 10792982890186880 X⁶ + 54324663841566720 X⁵ − 59537444207259384 X⁴
              − 5333500942004736 X³ + 70301209217000688 X² − 58648289441951232 X
              + 14959679998135428

    minY(Y) = 5189853515625 Y¹² − 27679218750000 Y¹¹ + 50839036171875 Y¹⁰
              − 25476271875000 Y⁹ − 64083542951250 Y⁸ + 158548997160000 Y⁷
              − 112177045240970 Y⁶ − 55930818664080 Y⁵ + 238227237251661 Y⁴
              − 268582717494864 Y³ + 105731781150423 Y² − 2606870041848 Y
              − 1978575740672

Both are degree `12` and irreducible; back-substitution residuals at WP 80 are `≈ 1e−38`
(minX) and `≈ 1e−44` (minY). `[SY]` + `[NC ~38]`. These match B7's leading/constant
coefficients.

### 2.6 The field `ℚ(t*) = ℚ(Γ_x) = ℚ(Γ_y)` `[SY]`

`Γ_x = (xW − y'Q)/W` evaluated at `t*` is a `ℚ`-rational function of `t*`, so
`ℚ(Γ_x) ⊆ ℚ(t*)`; both have degree `12` over `ℚ`, so they are **equal**. The same holds for
`Γ_y`. Consequences:

- No degree reduction is available from the curve's own parameters: the control data
  (`0,2,2,3`), `d = 1` and all of `Q, W`'s coefficients are rational, and `Γ_x ∉ ℚ`
  (degree `12`), so no rational re-expression lowers the degree.
- `t*` and the two coordinates are mutually `ℚ`-rational functions; **reachability of the
  cusp abscissa, the ordinate and the parameter are all equivalent** in the presence of
  field closure. In particular, the box reaching `Γ_x` is the same statement as the box
  reaching `t*`/`Γ_y` up to rational-function application. `[SY]`

### 2.7 Galois evidence `[SY]` + `[SP]`

The discriminant of `P` is a **perfect square** (`IntegerQ[Sqrt[disc]] = True`), and so is
that of `minX`; all computed Frobenius cycle types are even, so the Galois group is
contained in `A₁₂`:

| polynomial | mod 7 | mod 11 | mod 13 | mod 17 | mod 19 | mod 23 | mod 29 | mod 37 |
|---|---|---|---|---|---|---|---|---|
| `P` (param) | 1·1·2·8 | 6·6 | 2·10 | 2·10 | 6·6 | 1·1·2·2·3·3 | 2·10 | 3·3·3·3 |
| `minX` | 1·1·1·8 | 6·6 | 2·10 | 2·10 | 6·6 | 1·1·2·2·3·3 | 2·10 | 3·3·3·3 |
| `minY` | 1·1·2·8 | 6·6 | 1·10 | 1·10 | 6·6 | 1·1·2·2·3·3 | 2·10 | 3·3·3·3 |

This is **evidence** for `A₁₂` (or a large transitive subgroup), not a proof: the group is
transitive, contains cycles of length `8`, `10` and `6`, and sits inside `A₁₂`. `[SP]`

---

## 3. The tower argument, and the honest strength of "not reachable"

There are two distinct reaches to separate.

1. **Single-step / direct presentation.** The cusp abscissa (equivalently `t*`) has
   minpoly degree `12` over `ℚ`. So no polynomial of degree `≤ 10` with rational
   coefficients vanishes on it. This kills, directly: `root_Pconstructible_le_eight`,
   `root_Pconstructible_le_seven`, the `power_law` engines, and the rational nonic. It also
   kills the specific offset-line rationalization: `offsetCrossPoly` is degree `≤ 10` and of
   the shape `u²(u'²+v'²) − D²v'²`, while the honest cusp equation is the unsquared
   `Q^{3/2} = W`, whose square is `Q³ − W²` — degree `12` and a different shape
   (cubes a quartic rather than squaring a cubic). `[SY]` for the degree/shape facts.

2. **Iterated towers.** Because `root_Pconstructible_le_six_coeffs` allows
   `PConstructible` coefficients, the reachable set is closed under adjoining roots of
   degree-`≤ 6` polynomials **over the reached field**, iterated. `Offset.lean`'s own
   degree-`10` numbers (`:743-773`) are P-constructible precisely through such an iteration,
   yet their minpoly degree is `10`. So a degree-`12` minpoly does **not** by itself prove
   non-reachability; one needs the further claim that no degree-`≤ 6` tower reaches `t*`.
   The project's own argument for the degree-`10` example runs on the Galois group `A₁₀`:
   the smallest index of a proper subgroup of `A_n` (`n ≥ 5`) is `n`, so a chain of
   subgroups with all indices `≤ 6` cannot descend from `A₁₀` to a point stabiliser. The
   same argument applied to `A₁₂` would exclude degree-`≤ 6` towers for `t*` and for
   `Γ_x`/`Γ_y` (since `A₁₂` is transitive with minimal proper-subgroup index `12 > 6`, and
   even from `S₁₂` the `A₁₂` step is index `2` but the next step is stuck at `12`). `[SP]`
   — this is the same reasoning `Offset.lean:765-770` itself labels as an argument
   "run outside Lean and not formalized here", and it depends on the Galois group really
   being large (only evidence in §2.7, not a computation in Lean).

**Limits, stated plainly.** The project claims **no** non-constructibility results
(`PLAN-bounding-box.md` §7, out of scope). Therefore the strongest available assertion is:

> `t*`, `Γ_x`, `Γ_y` are **not reachable by any construction currently in the tree except
> the box** — no crossing, no arc-length inversion, no low-degree root engine — assuming
> the `A₁₂`-type tower exclusion (heuristic). They are reachable by `box_xmax` on the
> offset arc.

That is the honest content of "genuinely new" for B12. `[SP]`

---

## 4. Graded verdict

| question | answer | label |
|---|---|---|
| Reachable by existing crossing machinery? | **No.** No constructible curve through the cusp is available; the offset-line crossing is degree `≤ 10` and fixed shape; `inter_x`/`inter_y` reach is geometric, not degree-bounded, and no library curve closes it. | `[SP]` |
| Genuinely new assuming the minpoly/degree argument? | **Yes, qualified.** Degree-`12` irreducible minpoly (necessary, not sufficient alone); `ℚ(t*) = ℚ(Γ_x) = ℚ(Γ_y)`; tower exclusion needs the `A₁₂` heuristic. "New" = "no landed construction other than the box reaches it". | `[SY]` degree facts, `[SP]` verdict |
| Undetermined? | Not the right grade for the *operational* question — `box_xmax` demonstrably reaches the box edge, which numerically is the cusp abscissa. It is the right grade for "is it outside `PConstructible` without the box", which nobody can currently prove or refute. | `[SP]` |
| Does the plan's "genuinely new" survive? | **Yes, with the corrections in §0/§3** — read "new" as "box-necessary", not "provably non-constructible". | `[SP]` |

---

## 5. The Lean path

### 5.1 Box route versus crossing route

**Crossing route — blocked, and would be large/speculative.** To reach `Γ_x` by crossing,
some `PConstructibleCurve` must pass through the cusp point and meet the offset in exactly
that point. The candidates are absent: the base Bézier does not pass through its own offset
(the displacement is `d·N`, `|N|=1`); the evolute (the locus of centres of curvature) does
pass through the offset's cusps and is a *rational* curve (`t ↦ γ(t) + (Q/W)(−y', x')`,
degree-`6` numerator over a linear denominator), but it is **not** one of the library's
constructible curves; and a line through the cusp would need the cusp coordinates as its
defining data. So no crossing is available. `[SP]`

**Box route — the one that works.** The offset arc over `[0,1]` is

    A := offsetParam (cubicPairParam 0 0 6 −3 0 6 −12 6) 1 '' Set.Icc 0 1,

and the cusp is its global abscissa maximum (§2.4), so `box_xmax A` is the cusp abscissa.

### 5.2 The reachability half — small/medium

1. **`PConstructibleCurve A`.** Instantiate `offsetCubicPairArc_PConstructibleCurve`
   (`Offset.lean:275`) at `c = (0,0,6,−3)`, `e = (0,6,−12,6)`, `d = 1`, `u = 0`, `v = 1`.
   Its two side conditions:
   - `hreg : speed ≠ 0` on `[0,1]`: `Q(t) = 36 − 288t + … + 405t⁴` has no common root with
     its derivative on `[0,1]`; concretely `x' = 3t(4−3t)` vanishes only at `t = 0` (where
     `y' = 6`) and `y' = 6(1−t)(1−3t)` vanishes only at `t = 1/3, 1` (where `x' ≠ 0`).
     Small: a `Polynomial` gcd/root argument or a direct sign case split.
   - `hinj : InjOn (cubicPairParam …) (Icc 0 1)`: `t ↦ x(t) = 6t² − 3t³` is strictly
     increasing on `[0,1]` (`x' = 3t(4−3t) ≥ 0`, `= 0` only at the single point `t = 0`), so
     the pair is injective. Small.
2. **`IsCompact A`.** A is the continuous image of `Icc 0 1`. `isCompact_traced_arc`
   (`Box.lean:188`) would serve, but it wants the `DifferentiableAt` bundle of the *offset*
   tracing, so a new lemma is needed either way:
   - `ContinuousOn (fun t => offsetParam γ d t) (Icc a b)` on a regular window
     (`unitNormal = (−y'/speed, x'/speed)`, `speed > 0` continuous, derivatives polynomial).
     Medium (~30–60 lines of `ContinuousOn` arithmetic / `fun_prop` over `sqrt` and
     division).
3. **`A.Nonempty`.** `nonempty_traced_arc (by norm_num : (0:ℝ) ≤ 1)`. Small.
4. **`box_xmax`.** `PConstructible.box_xmax hA hcomp hne`
   (`Defs.lean:207`), giving `PConstructible (sSup (Prod.fst '' A))`. Small.

Net: the number `cuspAbscissa := sSup (Prod.fst '' A)` is P-constructible with **no root
isolation and no degree-`12` algebra**. This is the form of the theorem B12 can land
cheaply, and it does establish that the box reaches a number that numerically coincides
with the cusp abscissa.

### 5.3 The identification half — large

To make the theorem say "the degree-`12` cusp abscissa is P-constructible", one must
identify `sSup (Prod.fst '' A)` with the specific root of `P`, i.e. prove `Γ_x (t*) =
sSup (… )`. The pieces:

1. **Derivative factorisation.** `(Γ_x)' = (1 − d·κ)·x'` with `κ = W/Q^{3/2}`
   (`Γ' = (1−dκ)γ'`, B7 §1). This is a new lemma about `deriv (offsetParam γ d)`, needing
   the chain rule through `unitNormal`'s `sqrt`/division. **Medium.**
2. **Root isolation on `[0,1]`.** Show `W − Q^{3/2}` (equivalently `Q³ − W²` with the
   `W > 0` branch) has exactly one zero in `(2/3, 1)` — `t*` — and a single sign change
   there. The natural formalization uses Mathlib's `Polynomial`/Sturm root-counting on the
   degree-`12` `P` (huge integer coefficients) restricted to `[0,1]`, plus a sign check.
   **Large.**
3. **Monotonicity and the sup.** From (1)–(2), `Γ_x` increases on `[0,t*]` and decreases on
   `[t*,1]`, so `IsGreatest (Prod.fst '' A) (Γ_x t*)`; then `IsGreatest.csSup_eq` as in
   `arc_xendpoint_Pconstructible` (`Box.lean:323-338`). **Medium** once (2) is in hand.
4. **Naming `t*` is optional.** One can dodge the explicit root by noting the supremum is
   attained at an interior maximiser `t₀` (since `Γ_x(1) = 3 < sup`), which must satisfy
   `(Γ_x)'(t₀) = 0`; since `x' > 0` on `(0,1]`, that forces `κ(t₀) = 1`, so `t₀` is a root
   of `P` and the value is a root of `minX`. Pinning *which* root needs a comparison with
   the rational `Γ_x(1) = 3` (or a real-root count of `minX`). **Medium-to-large**, and it
   still needs (1) and enough algebra to conclude `P(t₀) = 0`.

**Blocker summary.** B7's ranking holds: the window/`restrict` question is **not** the
blocker (a cusp is a critical point, so a parameter window isolates it without comparing to
the unknown; here the `[0,1]` stroke already has it as the global extreme). The blockers are
(i) the differentiability/continuity bookkeeping for the offset (medium) and (ii)
root-isolating the degree-`12` cusp equation with a single sign change (large). The
reachability result needs neither (i) nor (ii) in full — only continuity for compactness;
the identification needs both.

**Named ingredients**
- existing: `offsetCubicPairArc_PConstructibleCurve` (`Offset.lean:275`),
  `cubicPairArc_PConstructibleCurve` (`Basic.lean:1226`),
  `PConstructible.box_xmax` (`Defs.lean:207`), `isCompact_traced_arc` /
  `nonempty_traced_arc` (`Box.lean:188,202`),
  `offsetParam_normal_eq_zero` (`Offset.lean:118`), `arc_xendpoint_Pconstructible`
  (`Box.lean:323`).
- new: `ContinuousOn (offsetParam γ d)`; `deriv_offsetParam_fst`/`_snd`;
  `cuspPoly` (`Q³ − d²W²`) and its `FactorList`/irreducibility facts (if the degree-`12`
  minimality is to be formalized at all — a big separate project); a root-isolation lemma
  on `[0,1]`; the sign-change/monotonicity lemma.

---

## 6. Ledger

| claim | label |
|---|---|
| `x = 6t² − 3t³`, `y = 6t − 12t² + 6t³`; `Q` deg 4, `W` deg 1, `Q³−W²` deg 12 | `[SY]` Wolfram exact |
| `Q³ − W² = 81·P`, `P` primitive, irreducible over `ℚ`, degree 12 | `[SY]` Wolfram `FactorList`/`IrreduciblePolynomialQ` |
| four real roots of `P`, only `0.96908…` and `1.23341…` are genuine (`W>0`) | `[NC 30]`/`[SY]` |
| `t* = 0.96908567783192265336657130794807810560176…` (`Root[P,3]`, residual 1e−45) | `[NC 60]` Wolfram WP 60 |
| `W(t*)=32.6612532058476465635897012584`, `Q(t*)=10.2177489925890854623398983291`, `κ(t*)=1` (residual 1e−75, WP 80) | `[NC 30]` |
| cusp point `(3.015151812639309983896917609276868074014, 0.9994137526624290102026815591764698149397)` | `[NC 40]` |
| `minX`, `minY` irreducible degree 12; residuals ~1e−38 / 1e−44 at WP 80 | `[SY]` exact + `[NC]` |
| `box_xmax` over `[0,1]` returns 3.0151… at `t*`; `NMinimize = −1` at `t=0`; `Γ_x(1)=3` | `[NC 50]` |
| `ℚ(t*) = ℚ(Γ_x) = ℚ(Γ_y)` (all degree 12) | `[SY]` |
| discriminants of `P` and `minX` are perfect squares; all mod-p cycle types even → group ⊆ `A₁₂` | `[SY]` + `[SP]` |
| crossing reach is geometric (via `inter_x`/`inter_y`), not degree-bounded; offset-line engine degree `≤ 10` with degree-5 recovery | `[SY]` source (`Basic.lean:337`, `Offset.lean:379,578,815`) |
| cusp not reachable by any landed construction other than the box, modulo `A₁₂` heuristic | `[SP]` |
| box route: `PConstructible (sSup (Prod.fst '' A))` via `offsetCubicPairArc_PConstructibleCurve` + compactness + `box_xmax` | `[SP]` (not yet formalized) |
| identification of the sup with the degree-12 root is the large obligation; window is not the blocker | `[SP]`, echoing B7 |
