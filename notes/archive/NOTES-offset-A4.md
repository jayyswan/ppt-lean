# NOTES-offset-A4: offset∘affine∘offset chains and rational offsets as new curves

Status: COMPLETE. Task id A4. Scripts: `archived files/offset-scripts/A4-*`. Lean scratch:
`pptc/Pptc/Scratch/OffsetA4.lean` (three [Lean]-certified polynomial identities; no imports of
`Pptc.*`, no `sorry`). All other identities are algebraic, checked symbolically/numerically.

## Summary (≤12 lines)

1. **The drawable curves with a rational offset are exactly**: lines, circles, parabolas, and
   PH cubics (Tschirnhausen and its similar images). No non-circular ellipse/hyperbola, no
   `poly_graph` of degree ≥ 2 other than a parabola, no `power_law`, no `sine`/`exp_two` curve.
2. Their offsets have implicit degrees **1, 2, 6, 5**; the parabola's is a degree-6 rational
   curve, the PH cubic's a degree-5 rational curve (Farouki–Neff, Lü, Pottmann).
3. **A PH curve's offset is again PH**, and offsetting twice along the same normal is one
   offset by `d₁+d₂`; so iterating "rational offset" with no affine map in between adds nothing.
4. **A non-similarity affine image of a PH curve is never PH again**; so `R`'s rational-offset
   iteration stops after one step. `R` is affine-closed by definition but degree-bounded (≤ 6).
5. Chains `off_{d₂}∘L∘off_{d₁}∘γ`: the **unit normal is preserved** by an affine map, so the
   second square root is `√|Lv|²`, *independent* of `√|v|²`. The tower is `√Q₁, √Q₁′`
   (degree ≤ 4 over `ℚ(t)`), not nested.
6. Function-field genus of a length-`n` chain: `gₙ = (n−1)·2ⁿ + 1` (g₁=1, g₂=5, g₃=17)
   [symbolic, Riemann–Hurwitz], assuming the plane map is birational.
7. Line-crossing polynomial degree: length 1 = **10** (irreducible; reproduces `Offset.lean`),
   length 2 = **28** (irreducible, 6 real roots), length 3 = **72** (generic) [symbolic/numeric].
   Affine cubic-pair offset implicit degree = 10; length-2 chain implicit degree = 28
   (parametrization is generically injective — all 28 roots give 28 distinct points).
8. A chain crossing hands back the parameter by a **degree-1 gcd** (proper parametrization) —
   far cheaper than the cubic-pair quintic [symbolic].
9. **Growth verdict**: degree grows like `2ⁿ` (or faster) while the parameter count grows
   linearly (`5n+4`), so `dimension − degree → −∞`; chains are **not** dimensionally dominant.
   The growth is in degree, not in reachable moduli.
10. **New numbers**: length-1 crossing gives the known decic; the length-2 chain gives a real
    algebraic number of **degree 28 over ℚ**, irreducible and with Galois group `S₂₈`/`A₂₈`
    (23-cycle + primitivity ⇒ Jordan), hence outside every tower of degree-≤6 steps. Wolfram
    confirms degree 28, irreducibility, 6 real roots, `mod 103 = (t+10)(t+81)(3)(23)`.
11. Legality: `crossing_Pconstructible` needs `S ⊆ range Γ` and `F∘Γ` finite; the rational
    parametrizations supply Γ and sub-arc/cusp handling costs one `restrict`.

## 1. Rational offsets, precisely

**Criterion (check).** A rational plane curve has a rational offset iff, after a rational
reparametrization, its unit tangent/normal is rational; equivalently its tangent indicatrix
`C → S¹` is a rational map (Pottmann's rational-support-function picture: an offset is
`h ↦ h+d` on the support function, linear). For a *polynomial graph* `(t,p(t))` the speed² is
`1+p′(t)²`; `1+p′²` a square in `ℝ(t)` forces `p′` constant (UFD: `(q−p′)(q+p′)=1`), so the only
graphs are the parabola (rational after `t=(s²−1)/(4s)`) and the line. [symbolic]

### 1.1 Parabola `y = x²` (base `(t,t²)`, `v=(1,2t)`, `w=√(1+4t²)`)
Reparametrize `t = (s²−1)/(4s)`, `w = (s²+1)/(2s)` (so `1+4t² = (s²+1)²/(4s²)`). Unit normal
`(−2t,1)/w`. Then

```
X(s) = (s²−1)(s²−4ds+1) / (4s(s²+1)),
Y(s) = (s⁶ − s⁴ − s² + 1 + 32 d s³) / (16 s²(s²+1)).
```

Homogeneous `(P₀:P₁:P₂)` has common factor `4s(s²+1)`; after cancelling, **proper
parametrization degree 6**. The implicit equation (monic in `X⁶`) is

```
X⁶ + X⁴(Y² − 5Y/2 − 3d² + 1/16)
   + X²(−2Y³ − 2d²Y² + 2Y² + (d²/2)Y − Y/8 + 3d⁴ − 5d²/4)
   + Y⁴ + (−2d² − 1/2)Y³ + (d⁴ − d²/2 + 1/16)Y² + (2d⁴ + d²/2)Y
   − d⁶ − d⁴/2 − d²/16 = 0,
```

so **implicit degree 6** [symbolic, sympy resultant; A4-01]. 35-digit check: every parametrized
point is at distance exactly `|d|` from the parabola and its displacement is orthogonal to
`v(t)` (`|dist−|d|| < 1e−36`, `|orth| < 1e−37`) [numeric, 35 digits]. The rationalisation
identity `(1+4t²)(2s)²=(s²+1)²` is also **[Lean]**-certified
(`Pptc/Scratch/OffsetA4.lean`, `parabola_radicand_is_square`, no `sorry`).

### 1.2 Affine image of a parabola; the `K`-square-roots needed
For `L = [[a,b],[c,e]]`, `L(t,t²) = (at+bt², ct+et²)`, speed² is the quadratic
`(a²+c²) + (4ab+4ce)t + 4(b²+e²)t²`. Rationalizing the conic `Y² = speed²` uses the point at
infinity, whose coordinates involve **`√(4(b²+e²))`** (the leading coefficient). Since `K` is
closed under square roots of positive elements (`sqrt_Pconstructible`), this stays in `K`. The
explicit substitution is `t(k) = (−a²−c²+k²) / (4(ab+ce − k√(b²+e²)))` [symbolic, A4-01].

### 1.3 Tschirnhausen cubic and general PH cubics
`r(t) = (t − t³/3, t²)`, `v = (1−t², 2t)`, `w = 1+t²` (a *polynomial* square root: this is
PH). Offset:
```
X(t) = −t(6d + t⁴ − 2t² − 3) / (3(t²+1)),
Y(t) = (−d t² + d + t⁴ + t²) / (t²+1).
```
**Implicit degree 5 and proper parametrization degree 5** [symbolic, A4-02]. Its offset speed²
is `((t⁴+2t²+1−2d)/(t²+1))²`, a perfect square, so the offset is **again PH** [symbolic]. The
unit-normal identity `(1−t²)²+(2t)²=(1+t²)²` and the PH-closure field identity are
**[Lean]**-certified (`Pptc/Scratch/OffsetA4.lean`, `ph_normal_unit`,
`tschirnhausen_offset_speed_square`, no `sorry`).

General PH cubic: with hodograph `(a+(b−a)t)²`, the Bézier increments are
`Δ₁=a²/3, Δ₂=ab/3, Δ₃=b²/3`, so PH ⟺ **`Δ₂² = Δ₁Δ₃`** [symbolic]. A concrete non-Tschirnhausen
PH cubic `(t²+t, 2t³/3+t²)` has `speed²=(2t²+2t+1)²` and gives a degree-5 offset too [symbolic].

### 1.4 Why the classification stops here
* Ellipse `(a cos t, b sin t)`: after `u=tan(t/2)`, `speed²·(1+u²)² = 4a²u² + b²u⁴ − 2b²u² + b²`,
  discriminant `4096 a⁴b⁴(a−b)²(a+b)²`. Nonzero unless `a=b`, so the curve is genus 1
  (non-rational) for every non-circular ellipse. [symbolic]
* `power_law (t, a t^{p/q})` after `t=u^q`: speed² `= q²u^{2q−2}+a²p²u^{2p−2}`, a binomial, a
  square only for the line/degenerate cases. [symbolic]
* `sine`, `exp_two` are transcendental (no algebraic implicit equation).

**Rational-offset list (parameter counts).**

| curve | how drawn | rational offset | implicit deg | params (drawing) | shape moduli (mod similarity) |
|---|---|---|---|---|---|
| line/rectangle edge | `poly_graph` deg 1 / `rectangle` | yes (parallel line) | 1 | 2 (A,B,C mod scale) | 0 |
| circle | `ellipse`, width=height | yes (concentric) | 2 | 3 (centre, radius) | 0 |
| parabola | `poly_graph` deg 2 | yes (§1.1) | 6 | 3 (a,b,c) | 1 (focal length) |
| PH cubic | `cubic_bezier` with `Δ₂²=Δ₁Δ₃` | yes (§1.3) | 5 | 6 (P₀∈ℂ, a,b∈ℂ) | 2 (ratio b/a) |
| Tschirnhausen | the case b/a = i | yes | 5 | 4 (P₀∈ℂ, scale∈ℝ) | 0 |

Everything else drawable is not rational-offset.

## 2. The curve family `R` and its closure

**Definition.** `R` = the curves reachable as finite affine images of rational offsets
(iterating "rational offset" only where PH-ness survives). By construction `R` is closed under
affine maps. Its members are affine images of the list in §1 and their offsets.

* **Affine closure.** Yes, by definition (the affine group generated by
  `translate_x/y`, `scale_x/y`, `rotate` acts on `PConstructibleCurve`).
* **Rational-offset closure.** Requires PH. For `L` applied to an offset PH cubic,
  `|L(1−t²,2t)|² = (1−t²)²m₁₁ + 4t(1−t²)m₁₂ + 4t²m₂₂` (with `M=LᵀL`) is a perfect square of a
  quadratic **iff `M` is a scalar matrix**, i.e. **iff `L` is a similarity** (matching
  coefficients forces `p=−r`, then `det M = 0`, impossible for invertible `L`, unless
  `m₁₂=0, m₁₁=m₂₂`). [symbolic, A4-02]
* Hence after any non-similarity affine map the curve is not PH, a second rational offset is
  impossible, and **`R` has bounded implicit degree (≤6)**. Offsetting a PH curve with no map
  in between just accumulates `d` (O3), so no new curves.

## 3. Crossings inside `R` (degrees and recovery)

Crossing a rational curve of proper parametrization degree `m` with an implicit curve of degree
`n` gives a polynomial in the rational parameter of degree `≤ m·n` (Bezout on the parametrized
curve). Cofactor coverage and dimension are structural: `R` is degree-bounded, so it cannot be
dimensionally dominant in any degree `N` beyond 6.

| first curve (param deg m) | second curve (implicit deg n) | crossing poly deg ≤ m·n | recovery |
|---|---|---|---|
| Tschirnhausen offset (5) | line (1) | 5 | gcd degree 1 |
| parabola offset (6) | line (1) | 6 | gcd degree 1 |
| Tschirnhausen offset (5) | cubic Bézier (3) | 15 | gcd degree 1 for t |
| parabola offset (6) | cubic Bézier (3) | 18 | gcd degree 1 for t |
| Tschirnhausen offset (5) | Tschirnhausen offset (5) | 25 | resultant |
| parabola offset (6) | Tschirnhausen offset (5) | 30 | resultant |

**Recovery of the rational parameter.** For a *proper* rational parametrization `Γ(s)` and a
point `(X₀,Y₀)=Γ(s₀)` on it, compute `g = gcd(n_X − X₀ d_X, n_Y − Y₀ d_Y)` over the field
`K(X₀,Y₀)[s]`; properness gives `deg g = 1`, so `s₀` is recovered by one gcd and one root.
This is degree ≤ 6 independent of the crossing degree — much cheaper than the cubic-pair
recovery quintic (`normalEq_eq_quinticVal`). Verified exactly: Tschirnhausen offset (`d=3/5`,
`s₀=2`, point `(−86/75, 91/25)`) gives `gcd = t−2`; parabola offset (`d=1/3`, `s₀=3`, `5`) gives
`gcd = t−3`, `t−5` [symbolic, A4-08]. So recovery really is degree 1.

**Cofactor coverage.** Because every `R`-member has implicit degree ≤ 6 and the crossing family
is a low-dimensional subvariety of the degree-`m·n` forms, the cofactor map
`(P monic deg n, g deg N−n) ↦ P·g` cannot cover degrees `n = 7…12` from an `R`-crossing: the
image is contained in a proper closed subset of the degree-`N` forms (dimension count:
`R`-crossing params < `N` coefficients), so the family is not dominant. This reproduces the A2
codimension obstruction in a sharper setting.

## 4. Chains with square roots: `off_{d₂} ∘ L ∘ off_{d₁}`

Let `γ` be a cubic pair, `v=γ'` quadratic, `Q₁=|v|²`, `L` a linear map, `Q₁′=|Lv|²`.

**Tower (side discovery / correction to the plan).** The first offset has velocity
`r₁′ = (1−d₁κ₁)v`, always parallel to `v`; the affine image `L r₁` has velocity parallel to
`Lv`; so the second offset's unit normal is `J(Lv)/√Q₁′`, with **no `√Q₁` inside it**. Hence

```
r₂ = Lγ + d₁ (L Jv)/√Q₁ + d₂ (J Lv)/√Q₁′,
```

a function in `ℚ(t)(√Q₁, √Q₁′)`, a **degree-≤4** extension of `ℚ(t)` — the two square roots are
**independent**, not nested. [symbolic derivation; A4-03]

**Genus.** Over `ℚ(t)`, adjoining `√Q₁` (a quartic) is a double cover ramified at the four
simple zeros of `Q₁`; then adjoining `√Q₁′` ramifies at the four `t`-roots of the second quartic,
each lifting to `2^{n−1}` places. Riemann–Hurwitz gives `2gₙ−2 = 2(2g_{n−1}−2) + 4·2^{n−1}`,
`solving to **gₙ = (n−1)·2ⁿ + 1**` (g₁=1, g₂=5, g₃=17), **provided the plane map
`t ↦ rₙ(t)` is birational** onto its image. [symbolic, A4-03]

**Crossing with a line.** For length 1 the resultant is degree **10** and irreducible
(same as `offsetCrossPoly`), calibrating the method. For length 2 the norm/doubling elimination
`a₀ + a₁/w₁ + a₂/w₁′ = 0` (with `a₀` cubic, `a₁,a₂` quadratics) clears to
`U² − V²Q₁ = 0`, `U = a₂²Q₁ − Q₁′(a₀²Q₁+a₁²)`, `V = 2a₀a₁Q₁′`, of **degree 28**, and sympy's
`factor_list` returns a single irreducible factor of degree 28 [symbolic, A4-04]. Iterating one
more norm step (three quartic square roots) gives **degree 72** generically (68 for one special
seed) [symbolic, A4-09]. The length-2 parametrization is generically injective: the 28 roots of
the crossing polynomial map to 28 *distinct* complex points, so the chain curve has **implicit
degree 28** [numeric, 40 digits, A4-09].

**Recovery through the chain.** The last step gives the point on `Lr₁`; the normal equation for
the second offset is again low-degree, and undoing `off_{d₁}` is the standard cubic-pair
recovery quintic (degree 5 ≤ 6). So the chain's parameter recovery is at most a quintic,
independent of the degree-28 crossing.

## 5. Growth table and verdict

`n` = chain length. Parameters counted as `8` (cubic pair) `+ n` (distances) `+ 4(n−1)` (two
real 2×2 linear maps per step) `= 5n+4`; crossing degree from the norm doubling.

| n | params (`5n+4`) | line-crossing degree | function-field genus | Jacobian rank / effective dim mod PGL₂ | `dim − degree` |
|---|---|---|---|---|---|
| 1 | 9 | 10 | 1 | 7 / 4 (matches codim 3) | −6 |
| 2 | 14 | 28 | 5 | 10 / 7 (codim 18 in degree 28) | −21 |
| 3 | 19 | 72 | 17 | not computed, ≤ 16 mod PGL₂ | ≤ −56 |

Length-1 line crossing degree 10 and effective dimension 7 (codim 3) are the `Offset.lean`
result [symbolic]; length 2 is degree 28 [symbolic] with Jacobian rank **10** (17 raw
parameters) and hence effective dimension **7** mod PGL₂ [numeric Jacobian rank at a random
rational point, complex-step, A4-09]; length 3 is degree 72 [symbolic/numeric, A4-09]. So each
offset step roughly **doubles the degree** while raising the dimension by only about **3**. The
length-`n` chain is a codimension-`≈ (2ⁿ·(1+o(1)) − 3n)` subvariety of the degree-`2ⁿ`-ish forms
(degree 10 → codim 3, degree 28 → codim 18), so `dimension − degree` is unbounded below.

**Verdict for B2.** Iterating offsets does **not** reach dimensionally dominant families in any
degree. A length-`n` chain is a codimension-`Ω(2ⁿ − n)` subvariety of the degree-`2ⁿ`-ish forms;
it can manufacture isolated high-degree numbers but cannot cover whole degrees. Reaching a
dominant family needs a genuinely different polynomial shape (A2's non-line second curve; B1),
not more offset iterations.

## 6. Legality on sub-arcs

`PConstructibleCurve.offset` needs the input arc injective, regular, differentiable with
continuous velocity. For `off_{d₂}∘L∘off_{d₁}(γ)`:
* `off_{d₁}` is applied on a regular window of `γ` (exists by `exists_rat_window_cubicPair`).
* Its image is `C¹` and regular except where `1−d₁κ₁=0` (a cusp). `L` is a diffeomorphism, so
  cusps persist but are isolated; the second offset is applied on any sub-arc avoiding them,
  which is free with one `restrict` to a rational window (both bounds rational, so `K`).
* Cost: the cusp set is the zero set of the polynomial `Q₁√Q₁ − d₁K₁`; choosing a window with
  rational endpoints off it is one `restrict` and never changes the number-theoretic output.
* **`crossing_Pconstructible` legality on a rational-offset curve**: present the curve by its
  rational parametrization `Γ`; the drawn set `S` (an arc of the offset) satisfies
  `S ⊆ range Γ`, `F∘Γ` is the crossing polynomial of §3/§4 (finite roots), so both coordinates
  of the crossing are `PConstructible`. The rational parametrization is used only as a
  *parameterization* (a tracing), which the constructor accepts; it is not itself required to be
  a `PConstructible` map.

## 7. Explicit new numbers

**(a) Length-2 chain crossing.** With `γ(t)=(t³+2t²−t, t³−t+1)`, `L=[[2,1],[1,3]]`,
`d₁=½`, `d₂=⅔`, and the line `X+2Y=½`, the reduction of §4 gives an explicit integer polynomial
of **degree 28**, **irreducible over ℚ**, with 6 real roots [symbolic, A4-07]. Leading
coefficient `311233107240000`, constant term `5459729809`; the real roots include
`−1.62965613544226008398760908765…`, `0.293183592223795385811521479042…`,
`0.537007515965832434868691367919…` [numeric, 40 digits]. Wolfram independently confirms
degree 28, `IrreduciblePolynomialQ = True`, `CountRoots = 6`, and the factorisation
`mod 103 = 55·(t+10)(t+81)·(cubic)·(degree 23)`, and reproduces the root `0.537008`
[Wolfram, A4-07]. Cycle types mod primes include `[23,3,1,1]` (q=103), `[13,12,2,1]` (q=107),
`[22,6]` (q=131) — a **23-cycle**. The group is transitive, so the 23-cycle (`23 > 28/2`) makes
it primitive, and `23 ≤ 28−3` with Jordan's theorem forces the Galois group to contain `A₂₈`;
hence it is `A₂₈` or `S₂₈`. A simple group of order `28!/2` has no composition factor of order
≤ 720, so **the root is not in any tower of degree-≤6 steps** — genuinely new, and degree 28
so not reachable by `root_Pconstructible_le_eight`, the nonic family, or the codimension-3 decic
family. Construction tree: cubic-pair base `γ` → `offset` by `d₁` → linear map
`L=[[2,1],[1,3]]` (a non-similarity, reached by `scale_x`/`scale_y`/`rotate`) → `offset` by
`d₂` → `crossing` with the line `X+2Y=½`; all parameters in ℚ. Side conditions: the arc is
regular off the cusp set (isolated), and the crossing polynomial has finitely many roots.
[symbolic + numeric + Wolfram]

**(b) `R`-crossing.** Parabola-offset (implicit degree 6) composed with a cubic Bézier
(parametrization degree 3), control points `(0,0),(1,2),(−1,1),(2,−1)`, `d=⅓`, gives a
**degree-18 irreducible** crossing polynomial over ℚ with 4 real roots [symbolic, A4-07]. A real
root is a new real algebraic number of degree up to 18, and the rational parameter is recovered
by a degree-1 gcd (`§3`). [symbolic]

## Side discoveries

1. **The chain tower is not nested.** An affine map preserves the *direction* of the tangent, so
   an offset's unit normal depends only on the once-mapped velocity `Lv`, never on the previous
   square root. The function field is `ℚ(t)(√Q₁,…,√Qₙ)` with *independent* quadratics.
2. **PH is closed under offset, and offsets along one normal commute**, so "iterate rational
   offset" with no affine map in between is exactly a single offset by the summed distance.
3. **Affine images of parabolas are parabolas** (so the whole parabola family is a base curve),
   and their rational offset needs exactly one new `K`-square root, `√(leading coeff of speed²)`.
4. **Polynomial graphs are never PH except lines** (`(q−p′)(q+p′)=1` in `ℝ[t]`).
5. The genus formula `gₙ=(n−1)2ⁿ+1` for offset chain function fields, a clean doubly-exponential
   genus growth.

## Leads for other tasks

* **A1**: affine-cubic-pair offset implicit degree is **10** (exact resultant verified); the
  branch structure mod p (factors 8+2 for one instance) is worth recording for A1's atlas.
* **A2**: the length-2 chain line-crossing poly is irreducible degree 28; the codimension of
  this family and its cofactor coverage should be computed on the incidence variety.
* **B1**: the degree-28 length-2 chain root **is new** (Galois ⊇ A₂₈); it is not totally real
  (only 6 of 28 roots real). Check whether any chain crossing is totally real (the Hermite
  obstruction then applies directly to the crossing polynomial).
* **B2**: the growth verdict above is the key input — chains give degree without moduli, so a
  real-closedness engine cannot come from iterated offsets.
* **B4**: the legality lemma to formalize is the rational-parametrization form of
  `crossing_Pconstructible` for non-Bézier rational curves, plus the cusp-avoiding `restrict`.
