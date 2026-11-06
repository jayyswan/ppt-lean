# NOTES offset A2 — one-offset crossing families (F1–F9)

Task A2. Scripts: `archived files/offset-scripts/A2-*.py`. Progress log: `HANDOFF-offset-A2.md`.
Tags: **[Lean]** (formalised), **[symbolic]** (exact algebra), **[numeric, N digits]**,
**[Jacobian rank mod p]** (rank at random rational points mod `p = 2⁶¹−1`).

## Summary (≤12 lines)

1. Base curve of degree `n` offset by `d`, crossed with an implicit curve of degree `m`,
   rationalises to degree `N = 2m(2n−1)`; for a cubic pair `N = 10m` (line 10, conic 20,
   cubic 30). [symbolic]
2. The parameter→coefficient map is intrinsically degenerate: **no** family F1–F9 is dense;
   the codimension is structural, not a shortage of parameters. [Jacobian rank mod p]
3. Image dimensions `D` (projective): line 7 (codim 3, reproduces `Offset.lean`), conic 10,
   **legal** cubic Bézier 11, nodal/general cubic 14 (upper bound), graph_m `7+m`, power_n 9.
4. Cofactor criterion: a family covers degree `n` iff `D ≥ n`, with expected solution
   dimension `D−n`. Dimensionally: line n≤7, conic n≤10, cubic Bézier n≤11, graph6 n≤13,
   power law n≤9.
5. Solving those covering systems **inside `K`** (and their real feasibility) is **open**:
   coverage here is dimensional only.
6. The direct crossing **is** an engine: by (O4) every real root with `w≠0` is a genuine
   crossing for one sign of `d`, so it lies in `K` (`offsetCubicPair_cross_root_Pconstructible`).
7. **Headline:** explicit irreducible degree-20 (F2, offset×ellipse) and degree-30 (F3,
   offset×nodal cubic) P-constructible real algebraic numbers, Galois `⊇ A₂₀` / `⊇ A₃₀`,
   genuine-crossing checked to ~1e−59, cross-checked in Wolfram. Previous record: degree 10.

## 0. Setup, conventions, side conditions

Base arc `γ(t) = (x(t), y(t))` a cubic pair with `P`-constructible coefficients; `w = √q`,
`q = x'² + y'²`; offset `Γ(t) = γ(t) + d·N(t)`, `N = (−y', x')/w`, `d ∈ K`.

Second curve `T` given implicitly by `F(X,Y) = 0`, `deg F = m`. Clear the square root:
`w^m F(Γ) = A(t) + B(t) w`, reduce `w² ≡ q`; the **rationalized crossing polynomial** is

    Q(t) = A(t)² − B(t)² q(t).

`Q` is not equivalent to the crossing condition — squaring forgets the sign of `w` — but by
(O4) `d ↦ −d` is free, so a root with `w ≠ 0` is a genuine crossing for exactly one sign of
`d`. (O4) is the only sign/branch input; the cusp locus `w = 0` is the only excluded set, and
in every instance below `q > 0` on `ℝ`. The recovery step is `offsetParam_normal_eq_zero`,
indifferent to `T`; for a cubic pair it is a quintic (≤6), so `T` may be arbitrarily hard.

Legality: the base arc is cut to a rational window (`exists_rat_window_cubicPair`, [Lean]);
`T` is a legal constructible curve in every instance used (ellipse base constructor; nodal
cubic = image of a cubic pair; polynomial graphs; power laws).

## 1. The degree law

Let the base be a polynomial parametrisation of degree `n` (so `x', y'` have degree `n−1` and
`q = x'²+y'²` degree `2n−2`), and `F` of degree `m`. Expanding
`w^m F(γ + d n/w) = Σ_k (d^k/k!) D^kF(γ)[n]^k w^{m−k}` and reducing gives
`A = P + Q₁ w` with maximal degrees

    deg A = m(2n−1),   deg B = m(2n−1) − (something ≤ 5),

so `Q = A² − B²q` has degree `N = 2m(2n−1)`. [symbolic] For `n = 3` this is `N = 10m`,
matching `offsetCrossPoly_normalForm` (m=1 → 10) and A2-03/05 (m=2 → 20, m=3 → 30,
**verified exactly**). [symbolic], scripts `A2-01`, `A2-03`.

For a **rational** base of parametrisation degree `n` the clearing raises the degree: the
ellipse (`n = 2`) gives `N = 8m` (line 8, conic 16, cubic 24, [symbolic], `A2-07`), i.e.
`(4n)m` rather than `(4n−2)m` — the `4n−2` of Farouki–Neff is the *polynomial* (`n = 2`:
parabola, `N = 6`) case. Both laws are confirmed numerically.

Normal forms:
* **line** (F1): `u = A₀x + B₀y − C`, `v = B₀x − A₀y`; up to the factor `A₀²+B₀²`,
  `Q = u²(u'²+v'²) − d²(A₀²+B₀²) v'²` (`offsetCrossPoly_normalForm`, [Lean]). Only
  `u` (4), `v'` (3), `d²(A₀²+B₀²)` (1) appear: 8 combinations from 12 parameters.
* **conic** (F2): with `Q₂` the quadratic part, `L` the linear part, `c` the constant of `F`,
  `A = Q₂(x,y)·q + d² Q₂(y',−x') + d² c·q`, `B = 2d·Q₂((x,y),(−y',x')) + d·L(−y',x')`,
  up to terms linear/constant in `(x,y)`. [symbolic]
* **general implicit** (F3, F4, F5): `Q = A² − B²q` as above; no further closed form.
* **parabola / ellipse bases** (F6, F8): same recipe with `n = 2` (and a rational `γ` for
  the ellipse, denominators cleared). [symbolic]

## 2. Effective dimension (Jacobian rank mod `2⁶¹−1`)

Method (`A2-02`, `A2-06`): evaluate `Q` and its first derivatives in all parameters at
`N+1` random rational `t` via dual numbers in `𝔽_p[w]/(w²−q)`; evaluation rank = coefficient
Jacobian rank. `D = rank − 1` (projective image dimension). `Dsat` adds the three `𝔰𝔩₂`
(Möbius-tangent) directions `Q', tQ', t²Q'`; mod-`PGL₂` dim `= Dsat − 3`.

| family | second curve | `m` | `N` | #par | rank | `D` | codim plain | `Dsat` | dim mod PGL₂ | codim mod PGL₂ |
|---|---|---|---|---|---|---|---|---|---|---|
| F1 | line | 1 | 10 | 12 | 8 | **7** | **3** | 8 | 5 | 2 |
| F2 | conic / ellipse | 2 | 20 | 15 | 11 | **10** | 10 | 11 | 8 | 9 |
| F3′ | general implicit cubic (upper bound) | 3 | 30 | 19 | 15 | 14 | 16 | 15 | 12 | 15 |
| F3 | **legal** cubic Bézier (affine nodal cubic) | 3 | 30 | 16 | 12 | **11** | 19 | 12 | 9 | 18 |
| F4 | graph `Y = h(X)`, deg 2 | 2 | 20 | 12 | 10 | 9 | 11 | 10 | 7 | 10 |
| F4 | graph, deg 3 | 3 | 30 | 13 | 11 | 10 | 20 | 11 | 8 | 19 |
| F4 | graph, deg 4 | 4 | 40 | 14 | 12 | 11 | 29 | 12 | 9 | 28 |
| F4 | graph, deg 6 | 6 | 60 | 16 | 14 | **13** | 47 | 14 | 11 | 46 |
| F5 | power `Y = X⁷` | 7 | 70 | 10 | 10 | 9 | 61 | 10 | 7 | 60 |
| F5 | power `Y = X⁸` | 8 | 80 | 10 | 10 | 9 | 71 | 10 | 7 | 70 |
| F5 | power `Y = X⁹` | 9 | 90 | 10 | 10 | 9 | 81 | 10 | 7 | 80 |
| F6 | parabola, line | 1 | 6 | 10 | 6 | 5 | 1 | 6 | 3 | 0 |
| F6 | parabola, conic | 2 | 12 | 13 | 9 | 8 | 4 | 9 | 6 | 3 |
| F6 | parabola, cubic Bézier | 3 | 18 | 14 | 10 | 9 | 9 | 10 | 7 | 8 |
| F8 | ellipse, line | 1 | 8 | 8 | 5 | 4 | 4 | 7 | 4 | 2 |
| F8 | ellipse, conic | 2 | 16 | 11 | 8 | 7 | 9 | 10 | 7 | 6 |
| F8 | ellipse, cubic Bézier | 3 | 24 | 12 | 9 | 8 | 16 | 11 | 8 | 14 |

All ranks are [Jacobian rank mod p] at one random rational point (seed fixed in scripts);
F1 reproduces the [Lean]-established `D = 7` / codim 3 of `Offset.lean`, a calibration.
Note the family is invariant under the two-dimensional affine subgroup of `PGL₂`
(`t ↦ at+b`), which is why `Dsat − D = 1` for F1 and the mod-`PGL₂` codimension drops by 2.

**Reading.** Richer second curves do enlarge the image (line 7 → conic 10 → cubic 11/14), but
never enough to be dense: the offset composite always has huge codimension (`N − D`). The
degeneracy is the normal-form collapse (`u²(u'²+v'²) − D²v'²` for the line), not a parameter
shortage; adding coefficients to `F` each buy at most one rank (`graph_m`: `D = 7+m`).

## 3. Cofactor coverage of degrees 7–12

Criterion: for a target monic `P` of degree `n`, the system `Q(params) = P·g` (`g` monic of
degree `N−n`) has `D + (N−n)` unknowns against `N` equations, so the generic fibre has
dimension `D − n`. Hence a family covers **all** degree-`n` forms only if `D ≥ n` (a necessary
dimensional condition):

| family | `D` | degrees `n` dimensionally covered | fibre dim `D−n` for n=7,8,9,10,11,12 |
|---|---|---|---|
| F1 line | 7 | 7 | 0,−,−,−,−,− |
| F2 conic | 10 | 7,8,9,10 | 3,2,1,0,−,− |
| F3 cubic Bézier | 11 | 7…11 | 4,3,2,1,0,− |
| F4 graph6 | 13 | 7…13 | 6,5,4,3,2,1 |
| F5 power9 | 9 | 7,8,9 | 2,1,0,−,− |
| F6 parabola×cubic | 9 | 7,8,9 | 2,1,0,−,− |

Modulo Möbius the moduli space has dimension `N−3`, so the codimension drops by exactly 3
for families with trivial Möbius stabiliser; for F1 it drops by 2 (2-dim affine stabiliser),
leaving mod-`PGL₂` codimension 2 (table §2). **This is only a dimension count.** §4.4 of the
overview warns — and it applies verbatim — that a closing count is not a proof: the system
`Q = Pg` must be solved by field operations, roots of degree ≤6, or free rational choices,
and its real solutions are what a totally real target needs. That was not achieved here.

## 4. Real feasibility and sign/branch conditions

* **(O4) settles the sign.** `d` and `−d` are both allowed, so `Q`'s roots with `w ≠ 0` are all
  genuine crossings: numerically confirmed at every real root of both certified examples
  (one of `F(+d)`, `F(−d)` vanishes to ~1e−59, the other is `O(1)`). [numeric, ~60 digits]
* **Root pattern.** `Q2` (deg 20) has **2 real roots** (18 non-real → 9 conjugate pairs);
  `Q3` (deg 30) has **4 real roots** (13 conjugate pairs). The real-root count is the number
  of genuine crossings on the chosen window; a totally real target septic, by contrast, would
  need a *real* solution of the covering system with 7 real roots, which is a strictly
  stronger demand than the dimensional count. No totally real example was produced.
* **Sampling (`A2-08`).** Random rational data, Sturm `count_roots`: F1 decic observes
  `{2:21, 4:11, 6:7}` real roots (never 0, 8, 10 — the normal form forces an even, bounded
  count); F2 (ellipse-type conic) observes `{0:5, 2:5, 4:10, 6:7, 7:1, 8:1}`; F3 observes
  `{2:11, 4:5, 6:2}`. So the F2 engine routinely produces 6–8 simultaneous real crossings.
* **Explicit 12-real-root legal instance (`A2-09`).** `x = (4/3)t³ − 3t + 4/3`,
  `y = t² + t/2 + 1/2`, `d = 1/2`, ellipse `F = (4/3)(X−5/4)² + (1/4)(Y−2)² − 1` (positive
  definite, so the `ellipse` constructor applies; `x'²+y'² = (4t²−3)²+(2t+1/2)² > 0` on ℝ,
  so the arc is regular). `Q` is **irreducible of degree 20** over `ℚ` with **12 real roots**,
  all genuine (`min|F(offset)| ≈ 1e−13` at 50-digit roots):
  `−1.64897, −1.61535, −1.39559, −1.30927, −0.21762, −0.00977, 0.05083, 0.41274, 1.19471,
  1.46807, 1.51733, 1.55557` (40-digit values in script output). Patterns mod
  `{1000003, 2000003, 3000017}`: `{7,6,4,1,1,1}`, `{18,2}`, `{8,5,4,2,1}`; the 7-cycle and the
  5-cycle each force primitivity and beat Jordan's threshold (`7,5 ≤ 17`), so **Galois `⊇ A₂₀`**
  again. This gives **12 simultaneous degree-20 P-constructible reals**.
* **`x>0` (power law).** Restricting `Y = X^n` to `X > 0` cuts the crossing to the component
  where the offset point has positive abscissa; it removes all-negative real roots but never
  removes a positive one, so it cannot *create* constructibility, only restrict the window.
* **Recovery.** For the cubic-pair base the parameter is recovered by a quintic
  (`normalEq_eq_quinticVal`, [Lean]) — always ≤6, whatever `F` is; this is the asymmetry that
  makes the engine work. In reversed roles the recovery is the other curve's equation.

## 5. New numbers

**F2, offset cubic pair × ellipse.** Base `x = t³+t+1`, `y = 2t³−t²+3`, `d = 2`; second
curve the ellipse `4X²+9Y² = 36` (constructor `ellipse`, centre `(0,0)`, widths 6, 4). The
rationalized crossing polynomial is the explicit irreducible degree-20

```
Q2 = 3240000 t^20 − 9288000 t^19 + 13960800 t^18 + 5557560 t^17 − 36221879 t^16
   + 52620456 t^15 − 5504928 t^14 − 48344024 t^13 + 66078012 t^12 − 15880600 t^11
   − 22675488 t^10 + 30570328 t^9 − 8892330 t^8 − 1883336 t^7 + 2282400 t^6
   − 696072 t^5 + 24380 t^4 − 18696 t^3 − 43584 t^2 − 5552 t − 4439.
```

Real roots [numeric, 40 digits]: `−1.125390657519400400563490539069391973167` and
`0.5541814860001227511587768565179868596174`; both satisfy `F(Γ_{−d}) = 0` to ~1e−59.
`Q2` is irreducible over `ℚ` (sympy; Wolfram `IrreduciblePolynomialQ` → True). Factor patterns
mod `p ∈ {1000003, 2000003, 3000017, 4000037, 5000011}`: `{1,5,14}`, `{1,1,3,4,5,6}`,
`{9,11}`, `{3,17}`, `{1,9,10}`. The `{9,11}` pattern gives an **11-cycle**; since `11` divides
no `20/b` for a proper block size `b | 20` and exceeds every proper `b`, it forces primitivity,
and Jordan's theorem (`11 ≤ 20−3`) gives **Galois `⊇ A₂₀`**.

**F3, offset cubic pair × nodal cubic.** Same base, `d = 2`; second curve the nodal cubic
`Y² = X³ − X²` (a cubic Bézier, parametrised by `(s²+1, s³+s)`, hence a legal
`PConstructibleCurve`). The crossing polynomial is the explicit irreducible degree-30

```
Q3 = −91125 t^30 + 145800 t^29 − 685260 t^28 + 1317924 t^27 − 3546990 t^26
   + 4939614 t^25 − 6096034 t^24 + 4598082 t^23 + 2636145 t^22 − 5313650 t^21
   + 13834261 t^20 + 5953896 t^19 − 11543799 t^18 + 28683942 t^17 + 5811663 t^16
   − 15967132 t^15 + 25334525 t^14 + 8475756 t^13 − 11863634 t^12 + 6596804 t^11
   + 3468188 t^10 − 3939278 t^9 + 2515196 t^8 − 895606 t^7 + 287871 t^6
   − 79986 t^5 + 17657 t^4 − 3200 t^3 − 47 t^2 − 70 t − 25.
```

Real roots [numeric, 40 digits]: `−0.9196373788128223299410046337582219903626`,
`−0.1290713821710224662384008939702593389916`,
`0.3502109114497269867599681128839674026848`,
`1.572170534515665832341673442263273146746`; each satisfies `F(±d) = 0` for one sign to
~1e−61. Irreducible over `ℚ` (sympy + Wolfram). Factor patterns: `{1,1,1,2,25}`, `{1,8,21}`,
`{1,29}`, `{1,1,6,9,13}`, `{1,3,4,22}`. The `{1,1,6,9,13}` pattern gives a **13-cycle**
(`13 ≤ 30−3`), and the `{1,29}` pattern forces primitivity; Jordan gives
**Galois `⊇ A₃₀`**.

**Genuinely-new checklist (overview §4).**
1. Construction tree: cubic-pair arc (control points in `ℚ`), one `offset` by `d = 2`, one
   `restrict` to a rational window around any regular real root, then `crossing` with the
   ellipse / nodal cubic. Explicit, finite, all parameters in `ℚ ⊂ K`.
2. 40-digit numerical check: done; the engine's conclusion is the *parameter* `β`, and
   `Γ(β)` is the offset point.
3. Side conditions: `x' = 3t²+1 > 0`, so `w ≠ 0` everywhere (base arc regular); the arc is
   injective on the rational window; `d = 2` fixed; the crossing is isolated (finite root set,
   `Q` nonzero).
4. Newness: degree 20 (resp. 30) over `ℚ`, hence not of degree ≤8, not in the nonic family
   (`M³+λM²+v²`, degree ≤9), not in the codim-3 decic family; Galois `⊇ A₂₀` / `⊇ A₃₀` puts
   the roots outside every tower of degree-≤6 steps (smallest proper-subgroup index of `A_n`
   is `n ≥ 20 > 6`).

This raises the project's explicit constructibility record from **degree 10** (`Offset.lean`)
to **degree 30**, and gives a second, independent degree-20 family. Both were cross-checked in
two systems (sympy and Wolfram).

## 6. Covering-system degree — open

The one thing that would upgrade §3 from a dimension count to a theorem is a *triangular*
solve of `Q = P·g` in `K` for a prescribed degree-7…12 `P`, plus real feasibility for totally
real `P`. For F1/degree 7 the system is square (fibre dim 0), so it is a finite set of
algebraic solutions in the family parameters, and their degree governs whether they lie in
`K`. Its Bézout bound is `2^{10}` from the quadratic normal form, but the true number is far
smaller and was not computed. For F4/degree 7 the fibre is 6-dimensional, which leaves room
for free rational choices and an IVT argument; no such argument was written. **Status: open.**
A `sorry`-free extraction of a totally real septic was not obtained (this is the same frontier
as `PLAN-offset-B1`).

A numeric attack (`A2-10`) set up `Q = P·g` for the F1 normal form (unknowns `u`, `v'`, `D`,
`g`) and scanned random real starts for `n = 4,5,6,7`. It found **no** real solution even for
`n ≤ 6`, where the incidence is positive-dimensional and real solutions are expected on
dimension grounds. The scan is therefore **inconclusive** — random starts do not land on a
positive-dimensional solution set — and is reported only to warn against using naive
`least_squares` on this covering problem. A homotopy continuation from a constructed solution
would be needed.

## 7. Strongest defensible result

**Proved / verified.** The offset×second-curve crossing is an engine: F2 (offset of a cubic
pair × an ellipse) and F3 (× a nodal cubic Bézier) produce explicit irreducible degree-20 and
degree-30 real algebraic numbers in `K`, with Galois groups containing `A₂₀` / `A₃₀`
respectively, genuine-crossing certified numerically to ~60 digits and cross-checked in
Wolfram. This is a strict, large advance on the degree-10 record.

**Dimensional (not yet a covering theorem).** Among F1–F9 the strongest cofactor coverage is
F4 (degree-6 polynomial graph) with `D = 13`, covering every degree `n ≤ 13` *dimensionally*;
the legal F3 (cubic Bézier) covers `n ≤ 11` and F2 covers `n ≤ 10`. **No family's covering
system was solved in `K`, so it is not claimed that every degree-7…12 polynomial has its real
roots in `K`.** What *is* established is that the older codimension-3 obstruction of the line
family is broken by richer second curves (the image dimension strictly increases: 7 → 10 → 11
→ 13), so the line is not the end of the story — but the offset composite remains far from
dense in every case.

## 8. Derivations and scripts

* `A2-01-rationalize.py` — symbolic rationalisation `w^m F(Γ) = A + Bw`, `Q = A²−B²q`;
  degree law and F1 normal-form check.
* `A2-02-dim.py` — mod-`p` dual-number rank engine (parameters only; hardcoded families
  line/conic/general-cubic/graph/power).
* `A2-06-dim2.py` — general symbolic engine (any base and implicit `F`), rational mod
  conversion, Möbius-saturated rank. Reproduces conic `D=10`, graph6 `D=13`, gives legal
  cubic Bézier `D=11`.
* `A2-07-f678.py` — F6 parabola (`D=5/8/9`), F8 ellipse (`D=4/7/8`, `N=8m`).
* `A2-08-realroots.py` — Sturm real-root-count sampling per family.
* `A2-09-seven-roots.py` — search for a legal-ellipse instance with ≥7 real roots; produced
  the explicit 12-real-root degree-20 instance.
* `A2-10-covering.py` — `Q = P·g` for the F1 normal form; random-start scan (inconclusive;
  see §6).
* `A2-03-instances.py`, `A2-05-certify.py` — explicit `Q2`, `Q3`: degree, irreducibility,
  factor patterns, 40-digit real roots, genuine-crossing check.
* `A2-04-verify.py` — first certification pass (fixed the mpmath descending-order bug).

## Side discoveries

* **A clean degree law.** `N = 2m(2n−1)` for a degree-`n` polynomial base and degree-`m`
  implicit crossing curve. The `m = 1` (line) case is `4n−2`, exactly the offset's own
  implicit degree (Farouki–Neff): `n = 2` → `6` (parabola, F6) and `n = 3` → `10`
  (`Offset.lean`'s decic, F1). So the `4n−2` is the line case, not a separate law. [symbolic]
* **The line's codim-3 is not the maximum degree reachable.** A richer second curve keeps the
  quintic recovery and raises the *solved* degree arbitrarily, giving degree-20 and degree-30
  constructible numbers with a quintic recovery step. The bottleneck is coverage, not degree.
* **`D = 7 + m` for polynomial graphs.** Each added coefficient of `Y = h(X)` contributes
  exactly one dimension, so graphs are the most efficient way to buy image dimension; degree 6
  reaches `D = 13`, the best of F1–F9.
* **Mod-`PGL₂` accounting.** The line family is invariant under the affine subgroup of
  `PGL₂`, so its mod-`PGL₂` saturation grows by only 1, not 3; its mod-`PGL₂` codimension is 2,
  not 0. Möbius freedom is real but smaller than a naive `dim PGL₂ = 3` subtraction suggests.
* **Wolfram confirmed both polynomials are irreducible** (`IrreduciblePolynomialQ`), and the
  sympy `is_irreducible` and modular factor patterns agree exactly across five primes.

## Leads for other tasks

* **B1 (totally real septic).** F1/degree 7 is square (fibre dim 0); solve the decic/`g` system
  for a totally real septic and decide reality. F4/degree 7 has fibre dim 6 — the natural place
  to look for free rational choices + IVT.
* **A3 (two offsets).** The reversed-role and offset×offset composites have the normal form of
  §1 with both curves carrying `w`; expect the same `N = 2m(2n−1)` law with `m` replaced by the
  implicit degree of an offset curve (10 for a cubic, 6 for a parabola, 8 for an ellipse).
* **A4 (chains/rational).** The F6 parabola-offset result (`N = 6m`, rational degree 4) suggests
  chains through rational offsets keep the *degree* low while the dimension grows additively;
  worth tabulating.
* **B4 (legality).** The ellipse instance uses the `ellipse` constructor directly; the nodal
  cubic uses a cubic-pair presentation. A Lean statement of the F2 headline would need only
  `offsetCubicPair_cross_root_Pconstructible` with `F = 4X²+9Y²−36`, plus the explicit
  rational window — a good first formalisation target.
* **Z (synthesis).** The degree-20/30 numbers are the concrete new content; they should be
  cross-referenced against A1's atlas and B1's septic attempt.
