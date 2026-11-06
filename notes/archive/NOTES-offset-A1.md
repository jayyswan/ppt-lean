# NOTES-offset-A1 — atlas of single offsets

Task: `PLAN-offset-A1`. Repo root `C:\dev\Powerpoint\lean`, package root `pptc/`.
Scripts: `archived files/offset-scripts/A1-01` … `A1-12`.
All results below carry one of the tags `[Lean]`, `[symbolic]`, `[numeric, N digits]`,
`[literature]`. `[Lean]` = a statement proved in the library (or a direct instantiation of
one). `[symbolic]` = a CAS computation (sympy); decisive ones were re-run in Wolfram.
`[numeric, N digits]` = a floating-point check to N significant digits.

## Summary (plain language)

1. Crossing the offset of a degree-`n` **polynomial graph** with a line produces a point
   coordinate of degree `4n−2` over ℚ, **directly**, because `crossing_Pconstructible`
   returns coordinates.
2. This beats the degree-10 cubic-pair engine: `n=4,5,6` give irreducible crossing
   polynomials of degree **14, 18, 22**, with the extracted coordinate of the same degree.
3. The offset constructor was believed to stop at degree 10; it does not. The cap was an
   artefact of only ever offsetting cubics.
4. For `n=4` the degree-7 recovery (normal) equation has non-real roots, so the septic
   engine `root_Pconstructible_of_nonreal_root` also returns the **parameter** `t` in `K`.
5. Galois/Chebotarev evidence (`14`-, `13`-, `11`-cycles) makes the degree-14 coordinate
   lie outside every tower of degree-≤6 steps.
6. Rational-offset curves (parabola, PH cubic, cuspidal cubic, `x^{3/2}`, `x^{2/3}`) have
   no square root to clear: their crossings are honest polynomial equations of degree 5–8.
7. Conics (ellipse, hyperbola) stay at degree 8; `x^{−2}` gives degree 12 with recovery 6.
8. Nothing below degree 8 is new (`root_Pconstructible_le_eight`).
9. The family images remain highly degenerate: codimension grows with `n`
   (cubic pair 3, quartic graph 6, sextic graph 12), so this does **not** cover whole degrees.
10. The evolute/cusp equation `d²(x'y''−y'x'')² = (x'²+y'²)³` has degree `6(n−1)` for a
    polynomial curve of degree `n`.
11. The frontier (totally real septics, whole degrees) is untouched by this atlas; what is
    new is a large supply of individual high-degree constructible numbers.
12. Highest-value next step: formalise `offsetPolyGraph_cross_point_Pconstructible` and use
    `n=4` to bank a degree-14 number in the library.

## Master table

`K` = P-constructible reals. "crossing deg" = degree in the base parameter of the genuine
offset × line equation (for rational-speed curves the unsquared equation). "eff. dim" =
monic Jacobian rank of (curve params, `d`, line) ↦ crossing polynomial, exact symbolic
Jacobian (`A1-07e`, `A1-07f`); "codim" = crossing deg − eff. dim. "max extracted" = the
greatest degree over ℚ of a single number the family provably yields **by this construction**
(coordinate via `inter_x`, or parameter via a recovery degree within the available engines).

| base curve | implicit deg | genus | rational? | cusp poly deg | crossing deg | recovery deg | eff. dim | codim | max extracted |
|---|---|---|---|---|---|---|---|---|---|
| line / segment | 1 | 0 | yes | – | 1 | 1 | 1 | 0 | 1 |
| circle | 2 | 0 | yes | – | 2 | 1 | ≤2 | 0 | 2 |
| ellipse `a≠b` | 8 | 1 | no | 4 (vertices) | 8 | 4 | 6 | 2 | 8 |
| hyperbola | 8 | 1 | no | 4 | 8 | 4 | 6 | 2 | 8 |
| parabola | 6 | 0 | **yes** | 6 | 6 | 3 | 6 | 0 | 6 |
| cubic pair (general) | 10 | 1 | no | 12 | 10 | 5 | 7 | 3 | 10 |
| cubic graph `y=p₃(x)` | 10 | 1 | no | 12 | 10 | 5 | 6 | 4 | 10 |
| cuspidal cubic `(t²,t³)` | 8 | 0 | **yes** | (base cusp) | 8 | 4 | 3 | 5 | 8 |
| nodal/acnodal `(t²+λ,t³+λt)` | 10 | 1 | no | 12 | 10 | 5 | 4 | 6 | 10 |
| PH cubic (Tschirnhausen) | 5 | 0 | **yes** | 6 | 5 | 5 | 3 | 2 | 5 |
| poly_graph deg 4 | 14 | 2 | no | 18 | 14 | 7 | 8 | 6 | **14** |
| poly_graph deg 5 | 18 | 3 | no | 24 | 18 | 9 | 8 | 10 | 18 (coord.) |
| poly_graph deg 6 | 22 | 4 | no | 30 | 22 | 11 | 10 | 12 | **22** (coord.) |
| power `x^{3/2}` | 8 | 0 | **yes** | – | 8 | 5 | 4 | 4 | 8 |
| power `x^{2/3}` | 8 | 0 | **yes** | – | 8 | 5 | 4 | 4 | 8 |
| power `x^{1/3}` | 10 | 1 | no | – | 10 | 5 | 4 | 6 | 10 |
| power `x^3` | 10 | 1 | no | – | 10 | 5 | 5 | 5 | 10 |
| power `x^{−1}` | 8 | 1 | no | – | 8 | 4 | 4 | 4 | 8 |
| power `x^{−2}` | 12 | 2 | no | – | 12 | **6** | 4 | 8 | **12** |
| `y = 2^x` | transcendental | n/a | n/a | n/a | mixed analytic | n/a | n/a | n/a | (B3) |
| `y = sin x` | transcendental | n/a | n/a | n/a | mixed analytic | n/a | n/a | n/a | (B3) |

Genus is that of the hyperelliptic function field `ℝ(t, √Q)`, `Q = x'²+y'²` (after removing
even multiplicities and any common pole factors); the offset map is generically birational,
so the offset curve has that genus. All rows `[symbolic]` (`A1-05`, `A1-06`, `A1-09`,
`A1-10`); the cubic-pair rank 7 / codim 3 row is independently `[Lean]`
(`offsetCrossPoly_normalForm`, `Offset.lean:815`, plus the file's rank discussion).

## Headline: degree `4n−2` from a polynomial graph

Setup. Let `p ∈ ℚ[t]` have degree `n`, `γ(t)=(t,p(t))`, so `S = Γ_p` is the `poly_graph`
curve. Then `γ` is injective (its first coordinate is the identity), `speed γ = √(1+p'²) ≥ 1`,
`γ` is polynomial (so differentiable with continuous derivative). Hence for any rational
`a<b` and any `d ∈ K`,

    S_d := offsetParam γ d '' Icc a b

is a `PConstructibleCurve` — a direct instance of `PConstructibleCurve.offset`
(`Defs.lean:372`). `[Lean for legality]`

Cross `S_d` with the horizontal line `Y = 0` (an arc of `rectangle`/`lineParam`, again a
`PConstructibleCurve`). At a point of the offset, `Y = p(t) + d/√(1+p'²)`, so the crossing
condition is `p(t)√(1+p'²) = −d`, i.e.

    P(t) := p(t)² (1 + p'(t)²) − d² = 0,        deg P = 2n + 2(n−1) = 4n−2.

The x-coordinate of the crossing is `X = t − d p'(t)/√(1+p'²) = t + p(t)p'(t)` (using
`1/√(1+p'²) = −p(t)/d` at the condition). `crossing_Pconstructible` (`Basic.lean:345`)
then puts `X` in `K`. `[Lean for the extraction; symbolic for the algebra]`

**Explicit instance (`A1-02`, `A1-03`, `A1-08`; re-run in Wolfram).** `p = t⁴+t+1`, `d=−1`:

    P(t) = 16 t¹⁴ + 40 t¹¹ + 32 t¹⁰ + 34 t⁸ + 48 t⁷ + 16 t⁶ + 12 t⁵ + 20 t⁴ + 8 t³ + 2 t² + 4 t + 1,

irreducible over ℚ (`sympy.is_irreducible`, `IrreduciblePolynomialQ`). The x-coordinate
`X = t + p p'` has irreducible minimal polynomial of degree 14

    4096·(65536 X¹⁴ − 262144 X¹² + 131072 X¹¹ + 358400 X¹⁰ + 440320 X⁹ + 1369488 X⁸
          − 1374208 X⁷ − 1062432 X⁶ + 1038240 X⁵ − 1411528 X⁴ + 2634720 X³
          − 1835096 X² + 762440 X − 150847).

The two real roots of `P` are genuine crossings with `|p·√(1+p'²)| = 1` exactly
(`[numeric, 40 digits]`):

    t₀ = −0.8216969253376584094428643623156593522764,   X₀ = −1.594883196255767380274759074200099347202,
    t₁ = −0.2698777893893131544363260466558390611340,   X₁ =  0.4077261656911388631837912922991303815614.

Both `X₀`, `X₁` satisfy the degree-14 minimal polynomial to `|value| < 10⁻³⁸`
(`[numeric, 40 digits]`). Construction tree: ① `poly_graph (t⁴+t+1)`; ② `offset` by `d=−1`
on the arc `[−1,1]`; ③ x-axis arc; ④ `restrict` both to a box round `(X₀,0)`; ⑤ `inter_x`.
Side conditions: injective, regular (`speed≥1`), `C¹`; isolated crossing; `d=−1 ∈ K`.

**n=5,6 (`A1-11`, Wolfram).** `p=t⁵+t+1`, `d=−1`: `deg P = 18`, irreducible,
`X` degree 18, `X₀ = −1.806222425757640991862456740643058418124`
(`[numeric, 40 digits]`). `p=t⁶+t+1`, `d=−1`: `deg P = 22`, irreducible, `X` degree 22,
`X₀ = −1.699807016118671739330932087513594505826` (`[numeric, 40 digits]`).

### The degree-7 recovery and the septic engine (`A1-03`)

The normal equation for the base parameter is

    (X − t)·1 + (Y − p(t))·p'(t) = 0,    i.e.   Q(z) = X − z − p(z)p'(z) = 0,

a degree-`2n−1 = 7` polynomial with coefficients in `K` (since `X,Y ∈ K`). For the instance
above `Q` has one real and **six non-real** roots (`[symbolic]`). By
`root_Pconstructible_of_nonreal_root` (`DegreeSeven.lean:4488`, `[Lean]`), every real root,
in particular the parameter `t₀`, is in `K`. So the **parameter** `t₀` (degree 14 over ℚ) is
constructible, not merely the coordinate.

### Genuinely-new checklist for `X₀` (and `t₀`)

* degree over `ℚ`: **14** (minimal polynomial irreducible), hence degree over `K` ≤ 14. `[symbolic]`
* not of degree ≤ 8 over ℚ: yes, 14 > 8.
* not a root of the nonic family `M³+λM²+v²`: yes, 14 ≠ 9.
* not a real root of a septic with a non-real root: yes, 14 ≠ 7.
* not in the codimension-3 decic offset family: yes, 14 ≠ 10.
* outside every tower of degree-≤6 steps: Chebotarev factor types mod primes include
  `(14)`, `(1,13)`, `(3,11)`, `(1,1,1,11)` (`A1-08`), so the group is transitive, primitive
  (13-cycle), and contains an 11-cycle with `11 ≤ 14−3`, so Jordan gives `G ⊇ A₁₄`; the
  smallest index of a proper subgroup of `A₁₄` is 14 > 6, so no step of index ≤ 6 exists.
  `[symbolic]`

## Per-curve derivations

### 1. Line / segment
`γ(t)=(αt+β, γt+δ)`; `x'²+y'²` constant, offset is a translate: line. Crossing with a line
is linear, so only rationals. Sanity check, `[symbolic]`.

### 2. Circle
`ellipse` with `width=height`. Offset is the concentric circle of radius `r±d`
(`= centre` iff `|d|=r`); crossing two circles is quadratic. `[symbolic]`

### 3. Ellipse / hyperbola
Rational parametrizations `x=a(1−t²)/(1+t²)`, `y=2bt/(1+t²)` (ellipse) and
`x=a(1+t²)/(1−t²)`, `y=2bt/(1−t²)` (hyperbola). The offset implicit equation has degree
**8** for each (`A1-10`: the elimination resultant has a single irreducible degree-8
factor; also `[literature]` Farouki–Neff. The non-circular ellipse offset is classical).
Genus 1. Recovery degree 4.

### 4. Parabola
`speed² = 1+(2t)²`, a non-square conic: the function field `ℝ(t,√(1+4t²))` is **genus 0**,
so the offset is **rational** — one of the two classical rational-offset families (the
other being PH curves). Offset implicit degree 6, crossing 6, recovery 3. `[symbolic]`

### 5. Cubic Bézier / cubic pair
* General pair `(x,y)` cubic: crossing 10, recovery 5, genus 1, codim 3
  (`offsetCrossPoly_normalForm` `[Lean]`; rank 7 verified `[symbolic]`).
* **PH cubic** (Tschirnhausen) `γ(t)=(t−t³/3, t²)`: `x'=1−t²`, `y'=2t`,
  `x'²+y'²=(1+t²)²`, so the speed is the polynomial `1+t²` and the offset is rational.
  Crossing 5, recovery 5, genus 0. `[symbolic]`
* **Cuspidal cubic** `(t²,t³)`: `x'²+y'²=t²(4+9t²)`; the factor `t²` is the cusp at `t=0`,
  removed (the arc must avoid it). Remaining `4+9t²` is a conic ⇒ genus 0, offset rational.
  Genuine crossing degree 8 (the raw resultant carries a spurious `X²+Y²=1` circle; `A1-06`).
* **Nodal/acnodal** `(t²+λ,t³+λt)`: `x'²+y'²` is squarefree quartic ⇒ genus 1; crossing 10,
  recovery 5. `[symbolic]`
* **Cubic graph** `y=p₃(x)`: crossing 10, recovery 5, genus 1, rank 6, codim 4.

### 6. Polynomial graphs `y=p(x)`, deg 4–6
General formula: implicit degree `4n−2`, genus `n−2`, crossing `4n−2`, recovery `2n−1`.
`[symbolic]` (`A1-04`…`A1-07e`). Rank/codim from `A1-07e`:

| n | crossing deg | recovery | genus | monic rank | codim |
|---|---|---|---|---|---|
| 2 | 6 | 3 | 0 | 6 | 0 |
| 3 | 10 | 5 | 1 | 6 | 4 |
| 4 | 14 | 7 | 2 | 8 | 6 |
| 5 | 18 | 9 | 3 | 8 | 10 |
| 6 | 22 | 11 | 4 | 10 | 12 |

The parabola (`n=2`) has codimension 0 in monic sextics: the family is universal for
sextics — but this is subsumed by `root_Pconstructible_le_six_coeffs`. The high-`n` graphs
are highly degenerate families, yet any one member yields a valid high-degree number.

### 7. Power laws `y = a x^{p/q}`
Parametrize `(t^q, a t^p)` (branch `t>0`). Genuine degrees (`A1-05`, `A1-10`):

| `p/q` | crossing | recovery | genus | rational |
|---|---|---|---|---|
| 3/2 | 8 | 5 | 0 | yes |
| 2/3 | 8 | 5 | 0 | yes |
| 1/3 | 10 | 5 | 1 | no |
| 3/1 | 10 | 5 | 1 | no |
| −1/1 | 8 | 4 | 1 | no (monic rank 4, codim 4) |
| −2/1 | 12 | 6 | 2 | no (monic rank 4, codim 8) |

`x^{−2}` is notable: crossing degree 12 but recovery degree only **6**, so
`root_Pconstructible_le_six_coeffs` returns the parameter. `[symbolic]`

### 8. `y=2^x` and `y=sin x` (brief)
Not algebraic. `y=2^x` has fixed-point/`ω`-equation crossings and no implicit polynomial;
the offset has the same analytic character. `y=sin x` crossings give mixed equations; only
`arc_of_length`/`arc_length` interactions produce new values. Both are B3's remit.
`[literature]`/deferred.

## Singularities and cusps

* **Cusps** of the offset lie on the evolute, where `1 − d κ = 0`. Squaring gives
  `d²(x'y''−y'x'')² = (x'²+y'²)³`; for a polynomial curve of degree `n` this has degree
  `6(n−1)` (`A1-10`): parabola 6, cubic pair 12, deg-4 graph 18, deg-5 24, deg-6 30.
  These counts include the base curve's own speed-zero parameters; remove them with `restrict`
  / by choosing a regular arc. `[symbolic]`
* **Self-crossings (swallowtail)**: occur when two parameters `t₁≠t₂` give the same offset
  point. Parameters of a double point are roots of the `t`-resultant of
  `(offsetParam t₁ − offsetParam t₂)` and it is not polynomial in closed form; the
  offset's own implicit singular locus is described instead by the cusp equation above.
* **Points at infinity**: a polynomial curve of degree `n` has a single point at infinity of
  multiplicity `n` on the base curve (the `y=x^n` direction), giving the offset curve its
  behaviour at infinity; for a graph the offset's leading behaviour is governed by the
  degree-`4n−2` leading coefficient of `F`, which is the top-degree part.
* **Isolated real points (acnodes)**: the nodal cubic `(t²+λ,t³+λt)` with `λ>0` has an
  acnode; its offset can have isolated real points reachable only by the crossing
  construction, exactly the escape covered in `NONIC-notes.md` for the nonic family.

## Ranked list — most promising offset curves for high-degree engines

1. **poly_graph deg 4.** Crossing 14, recovery 7 (septic engine; non-real generically),
   codim 6. Best single-offset engine: every generic instance gives a degree-14 number by
   **two independent routes** (coordinate via `inter_x`; parameter via the septic engine).
   `[symbolic]`
2. **power `x^{−2}`.** Crossing 12, recovery **6** (`root_Pconstructible_le_six_coeffs`),
   genus 2, few parameters. No septic side-condition needed. `[symbolic]`
3. **poly_graph deg 6.** Crossing 22, coordinate degree 22, codim 12. Highest degree
   available; recovery 11 exceeds current engines, so only the coordinate is extracted.
   `[symbolic]` + `[Wolfram]`
4. **cubic pair.** Crossing 10, recovery 5, codim **3** (smallest among non-trivial families);
   the library already formalises it. `[Lean]`
5. **Rational-offset family** (parabola, PH cubic, cuspidal, `x^{3/2}`, `x^{2/3}`). No square
   root to clear; exact polynomial crossings of degree 5–8; recovery ≤ 6. Cheap exact
   handles for A3/A4 (offset-offset, chains) rather than raw degree.
6. **poly_graph deg 5.** Crossing 18, codim 10; recovery 9 (open).
7. **Conics.** Degree 8 only, recovery 4: nothing new beyond `root_Pconstructible_le_eight`.

## Side discoveries

* **The degree-10 ceiling was an artefact.** `poly_graph` offset × line reaches degree
  `4n−2`, up to **22**, not 10. The mechanism needs no new axiom: `PConstructibleCurve.offset`
  applied to the graph, plus `crossing_Pconstructible`. This is the single most important
  finding of A1. `[symbolic]`/`[Wolfram]`/`[Lean for legality]`
* **Coordinate extraction is free.** Because `crossing_Pconstructible` returns *both*
  coordinates, the high-degree number is obtained without recovering the parameter at all.
  The project's emphasis on the recovery quintic understated the power of the constructor.
* **A degree-14 number with a fully worked checklist.** `X₀ = −1.5948831962557673802…`
  (quartic graph, `d=−1`) is a new explicit real algebraic number in `K`. `[symbolic]`
* **Septic engine reuse.** The degree-7 normal equation of a quartic graph is exactly the
  input class of `root_Pconstructible_of_nonreal_root`. So the (previously frontier)
  degree-7 theorem is the *recovery* engine for degree-4 graphs, giving the parameter too.
* **Genus formula.** The offset of a degree-`n` polynomial curve has genus `n−2`
  (from `ℝ(t,√Q)`, `deg Q = 2n−2`); conics give genus 1; the offset is rational exactly
  when `Q` is a square / a conic after removing cusp factors — recovering the classical
  PH/parabola rational-offset dichotomy from a single computation.
* **`x^{−2}` is a cheap degree-12 engine** with recovery degree 6, no septic hypothesis
  needed.

## Leads for other tasks

* **B4 / Lean.** Formalise the general
  `offsetPolyGraph_cross_point_Pconstructible` (the proof of
  `offsetCubicPair_cross_point_Pconstructible` generalises verbatim to `γ=(t,p(t))`); then
  the `n=4, p=t⁴+t+1, d=−1` instance is a degree-14 theorem. A scratch statement is in
  `pptc/Pptc/Scratch/OffsetA1.lean` (marked `sorry` if restricted).
* **B1 (totally real septic).** A quartic graph's recovery polynomial is a **generic**
  degree-7 polynomial over `K`; its real-root count is controllable. Can the degree-7
  *totally real* case be realised as a quartic-graph normal equation? If so, the septic
  obstruction is exactly the recovery step — a concrete reformulation of B1.
* **A2 (crossing families).** Redo the image-dimension count mod `PGL₂` for the
  `poly_graph deg 4` family against a general curve (not a line): recovery stays 7 while
  the crossing degree grows, which is the natural way to push past 14.
* **A3 / A4.** The rational-offset rows (parabola, PH cubic, `x^{±p/q}`) have polynomial
  offsets; chains and offset-offset constructions on them stay in closed form and are the
  cheapest source of exact high-degree equations.
* **B3.** `y=2^x`, `y=sin x` offsets: no implicit degree, but `arc_of_length` on the offset
  may yield new numbers (length of a parallel curve, O2).
* **Z (synthesis).** Reconcile "offset stops at 10" with the `4n−2` coordinate result;
  the honest statement is that *families* are low-dimensional while *individual numbers*
  can have degree up to 22. The frontier is coverage of whole degrees, not raw degree.
