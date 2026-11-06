# NOTES-jacobi-R2 — curves with first-kind arc length, drawability, and a minimal extension

Agent R2, brief `PLAN-jacobi-R2-serret-and-extensions.md`. Research only: no `.lean` file was
created, edited or deleted. Every identity below is tagged **[symbolic]** (proved with sympy) or
**[numeric]** (checked with mpmath at the stated precision). Scripts live in
`archived files/jacobi-scripts/` and are cited inline.

**Bottom line.** The classical single-curve catalogue of algebraic curves whose *Euclidean* arc
length is an elliptic integral of the first kind is essentially Serret's first-class family
(the lemniscate is its `n = 1` member), and it realises exactly the **rational** moduli
`c = n/(n+1)`. None of these curves — nor any arc, affine image, or offset of a curve already
in `Defs.lean` — is drawable. A single new constructor does the job for *every* P-constructible
`c < 1`: the **Serret generating-triangle family**, an analytic one-parameter family whose arc
from a vertex is exactly `√n · F(α, √(n/(n+1)))`. Taking `n = c/(1−c)` makes its modulus exactly
`c`, and the abutting-arcs argument of `ellipticEAm_Pconstructible_of_mem_Icc` then inverts `F`.

---

## A. Classical catalogue

### A.1 The problem and the sources

The relevant problem is Serret's: solve

```
dx² + dy² = C² / P(z) · dz²,        x, y, P, C rational in the parameter z,   [S45a]
```

with `P` a quartic with no real or multiple roots. Such an `x + i y` is a rational
parametrisation, and because `√(dx²+dy²) = C dz/√P(z)` its **arc length is an elliptic integral
of the first kind on the nose**. Serret solved the general indeterminate equation and extracted
the first-kind curves; he found infinitely many, in infinitely many classes, and the lemniscate
is the smallest. The construction he gave two years later is the one used below.

Primary sources (all Journal de Mathématiques Pures et Appliquées, Liouville's journal):

* **Serret 1843**, *Note sur les fonctions elliptiques de première espèce*, JMPA (1) **8** (1843)
  145–154 — the Cassini-oval representation. <https://www.numdam.org/item/JMPA_1843_1_8__145_0/>
* **Serret 1845a**, *Mémoire sur la représentation géométrique des fonctions elliptiques et
  ultra-elliptiques*, JMPA (1) **10** (1845) 257–285 — the general `dx²+dy²=Z dz²` solution and
  the class/modulus equations `Π_m(ζ)=0`.
  <https://www.numdam.org/item/JMPA_1845_1_10__257_0/> (PDF `…257_0.pdf`)
* **Serret 1845b**, *Note sur les courbes elliptiques de la première classe*, JMPA (1) **10**
  (1845) 421–429 — first-class curves, polar equation, degree `2(n+1)`, explicit sextic.
  <https://www.numdam.org/item/JMPA_1845_1_10__421_0/>
* **Serret 1846**, *Théorie géométrique de la lemniscate et des courbes elliptiques de la
  première classe*, JMPA (1) **11** (1846) 89–95 — **the generating-triangle construction used
  here**. <https://www.numdam.org/item/JMPA_1846_1_11__89_0/>
* **Liouville 1845**, *Rapport sur ce mémoire* and *Sur un mémoire de M. Serret*,
  JMPA (1) **10** (1845) 290–293 and 456–465 — states that Liouville extended Serret's integer
  parameter to a fractional one, so the moduli become all *rational* values.
  <https://www.numdam.org/item/JMPA_1845_1_10__290_0/> ·
  <https://www.numdam.org/item/JMPA_1845_1_10__456_0/>

Secondary/modern:

* **A. Morgan**, *On the Geometrical Representation of Elliptic Integrals of the First Kind*,
  Proc. Edinburgh Math. Soc. **21** (1903) 33–56 — careful exposition; contains Serret's
  `x+iy`, Kiepert's generalisation, and von Lilienthal's space-curve version.
  <https://doi.org/10.1017/S0013091500031965>
* **M. Tamiozzo**, *Algebraicity of the division points of the trifolium and related topics*,
  arXiv:1912.00204 (2019) — modern treatment, Erdős lemniscates, references.
  <https://arxiv.org/abs/1912.00204>
* **V. Pulov, M. Toda, V. Vassilev, I. Mladenov**, *The Geometry of the Kiepert Trefoil*,
  Mathematics **10** (2022) 3357 — explicit first-kind arclength of a sextic.
  <https://doi.org/10.3390/math10183357>
* **I. Mladenov**, *The Rectifications of the Cassinian Ovals: Third Round*, J. Geom. Symmetry
  Phys. **57** (2020) 87–98 — the Cassini perimeter is hyperelliptic (see A.5).
  <https://doi.org/10.7546/jgsp-57-2020-87-98>
* **I. Mladenov**, *New and Old Parameterizations of the Cassinian Ovals …*, Geom. Integrability
  & Quantization **23** (2022) 75–98. <https://doi.org/10.7546/giq-23-2022-75-98>
* **A. Lipkovski, F. Popelensky**, *About new examples of Serre[ t] curves*, Chebyshevskii
  Sbornik **21** (2020) — gives a new rational curve with first-kind arclength beyond the
  classical list. <https://geodesic.mathdoc.fr/item/CHEB_2020_21_2_a18/>
* **DLMF §19.30** *Lengths of Plane Curves* — standard reference for the elliptic arclength of
  the ellipse. <https://dlmf.nist.gov/19.30>
* **MathWorld**, *Cassini Ovals*. <https://mathworld.wolfram.com/CassiniOvals.html>

### A.2 Serret's first-class family: rederivation

This is Serret's own construction **[S46, §II]**, rederived and checked in
`R2-01-serret.py`.

Fix a point `O` and a real parameter `n > 0`. Consider a triangle `OMP` with

```
OP = √n,    MP = √(n+1),    OM = r,
```

and let `α = ∠MOP`, `β = ∠OMP`. The point `M` is placed in polar coordinates about `O` at angle
`θ` from a fixed axis, where

```
cos θ = cos(n α − (n+1) β).                                            (A.1)
```

As the triangle varies, `M` traces the **first-class Serret curve of parameter `n`**. The law of
cosines at `O` and at `M` give

```
r² − 2√n r cos α − 1 = 0,          cos β = (r²+1)/(2 r √(n+1)),       (A.2)
```

so `r = √n cos α + √(1 + n cos² α)`, and `r` ranges over
`[√(n+1) − √n, √(n+1) + √n]` (bounded, closed). The law of sines gives the important relation

```
sin β = k sin α,     k := √(n/(n+1)).                                  (A.3)
```

The text of [S46] then differentiates; doing it with sympy confirms
**[symbolic]** `R2-01-serret.py` lines "**(1)**", "**(2b)**", "**(3)**":

```
(1)   r² − 2√n r cos α − 1 = 0
(2b)  sin²β − (n/(n+1)) sin²α = 0
(3)   Δ² + (r² − (2n+1))² = 4 n (n+1),   where Δ² := −r⁴ + 2(2n+1) r² − 1.
```

Writing `dθ = n dα − (n+1) dβ` and differentiating (A.2) gives Serret's two displayed identities

```
dθ = (r² − (2n+1))/(r Δ) · dr,        ds = 2√(n(n+1)) · dr/Δ .         (A.4)
```

Finally, since `dβ/dα = k cos α / cos β`,

```
ds/dα = √n / √(1 − k² sin² α),     i.e.   arc(0→α) = √n · F(α, k).    (A.5)
```

(A.4)–(A.5) are the content of [S46, §§II–VI] and of the *Note* [S45b, eq. (6)]. The identity
(A.5) was verified **[symbolic]** (sympy: `speed²·(1−k²sin²α) − n = 0`) and **[numeric]** at
30 dps for `n ∈ {2, 1/2, 3, 1, 1.7}`, `α ∈ {0.3, 0.9}`: `|speed − √n/√(1−k²sin²α)| < 3·10⁻¹⁶`
and `|arc − √n F(α,k)| = 0` to 30 dps (mpmath `quad` vs `ellipf`). The lemniscate case
(`n = 1`, `k² = 1/2`) is exact to 30 digits. `R2-05-serret-geometry.py` additionally confirms at
40 dps that the `n = 1` curve *is* the standard lemniscate: with `O` at the focus `(1,0)`, points
`γ(α)` satisfy `(x²+y²)² = 2(x²−y²)` with residual `< 5·10⁻⁴⁰` **[numeric]**.

The parametrisation is, explicitly, with `θ(α) = π + nα − (n+1)β(α)` (the additive `π` is a
rotation; any constant works):

```
γ_n(α) = ( r_n(α) cos θ_n(α),  r_n(α) sin θ_n(α) ),
r_n(α) = √n cos α + √(1 + n cos² α),
β_n(α) = arcsin( k sin α ),
θ_n(α) = π + n α − (n+1) β_n(α).
```

All ingredients are elementary; `γ_n` is real-analytic, and it is **algebraic in `α`'s
coordinates exactly when `n` is rational** [S46].

### A.3 Moduli realised

By (A.5) the modulus is

```
k² = n/(n+1),      equivalently  n = k²/(1−k²).
```

* If `n ∈ ℚ_{>0}` — Serret's case, extended to fractional `n` by Liouville — the curve is
  algebraic and `k² = n/(n+1)` runs over **all of `ℚ ∩ (0,1)`**. This set is countable and
  dense in `(0,1)`. The lemniscate is `n = 1` (`k² = 1/2`); the next member is `n = 2`, a
  sextic (`k² = 2/3`), and its complementary curve `n = 1/2` has `k² = 1/3`, the complementary
  modulus [S45b §VIII].
* Serret's higher classes (`m ≥ 2`, [S45a §VII]) produce moduli that are roots of algebraic
  equations `Π_m(ζ)=0` whose coefficients depend on integers `m, n`; these are still
  **algebraic** numbers, so the union over the whole algebraic catalogue is countable.
* If `n` is allowed to be an arbitrary **real** number, (A.5) gives a single `F` for the modulus
  `k² = n/(n+1)`, i.e. **every** `c ∈ (0,1)`. The curve is then not algebraic (it contains
  `√n, √(n+1)` and `arcsin`, and its coordinates are not rational in the amplitude).

### A.4 Explicit small members

* `n = 1`, `k² = 1/2`: the Bernoulli lemniscate `(x²+y²)² = 2(x²−y²)` with `O` at a focus;
  `ds = dα/√(1 − ½ sin²α)`; quarter length `K(1/2)/√2 = 1.3110287771460599…` **[numeric]**,
  matching the classical `∫₀¹ dt/√(1−t⁴)`.
* `n = 2`, `k² = 2/3`: a sextic (degree `2(n+1) = 6`) of [S45b §VII]. Its arc is
  `√2 · F(α, √(2/3))`; verified numerically at 30 dps. (The explicit sextic equation is
  displayed in [S45b], but in an OCR-degraded form; it is not reproduced here.)
* `n = 1/2`, `k² = 1/3`: the complementary sextic of the same degree; arc
  `(1/√2)·F(α, √(1/3))`.

### A.5 Other families found

* **Legendre's sextic (1825)**, *Traité des fonctions elliptiques* I, pp. 35, 590: a degree-6
  curve whose arc is `F(·, k) +` an algebraic correction; the correction can be removed only by
  choosing *both* endpoints suitably, so it is not a genuine single-arc first-kind curve. It is
  the historical precursor of Serret's work.
* **Kiepert's class (1870)** and its **trefoil**: Kiepert generalised Serret using Weierstrass
  functions; the Kiepert trefoil is the sextic `(x²+z²)³ = a³x(x²−3z²)`, and Pulov–Toda–
  Vassilev–Mladenov (2022) prove its arclength is fully determined by an elliptic integral of
  the first kind (with one fixed modulus depending on the shape parameter `a`, twice that
  modulus for a single leaf). **[cited, not re-verified here]** The Kiepert class includes
  Serret's curves as a special case and still realises only a countable (algebraic) set of
  moduli.
* **von Lilienthal (1882)** extended the construction to space curves, as recounted in Morgan
  1903.
* **Erdős lemniscates** `r^{2k} − 2a^k r^k cos(kθ) + a^{2k} − 1 = 0` (level sets of `T_k − a^k`,
  i.e. the `k`-petal roses `r^k = 2a^k cos kθ`): these are a different family. Their lengths are
  hypergeometric/abelian, not a single elliptic integral; for `k = 2` they are the Cassini ovals,
  and for `k = 3` the 3-petal rose ("trifolium" of Tamiozzo), whose Jacobian is a genus-2
  hyperelliptic Jacobian and carries the interesting division-point structure. Do not conflate
  this trifolium with the *Kiepert* trefoil above.
* **Cassini ovals — important caveat.** Serret 1843 is often quoted as showing that first-kind
  elliptic integrals of *every* modulus are (sums/differences of) arcs of a Cassini oval. The
  modern computation says otherwise for the Euclidean arclength: writing
  `r⁴ − 2a²r²cos2θ + a⁴ − b⁴ = 0` and `u = r²`, one gets **[symbolic]** (see
  `R2-04-cassini-arclength.py`)

  ```
  ds = b² √u · du / √((P − u²)(u² − Q)),    P = (a²+b²)², Q = (a²−b²)²,
  ```

  and with `u² = α₀²cos²φ + β₀²sin²φ` (`α₀ = a²+b²`, `β₀ = |a²−b²|`, `k = 2ab/(a²+b²)`) the
  quarter-perimeter is

  ```
  (b²/√α₀) ∫₀^{π/2} (1 − k² sin²φ)^{−1/4} dφ .
  ```

  The exponent `−1/4` makes this a **hyperelliptic (superelliptic) integral, not elliptic**. This
  was confirmed numerically to 21 digits for `(a,b) ∈ {(1,2),(1,3),(1,1.5),(1,10),(2,3)}`
  (`R2-04`): the `−1/4` form matches direct quadrature to `< 3·10⁻²¹`, while the elliptic `−1/2`
  form is off by `O(0.1)`. Only `a = b` (the lemniscate, where `Q = 0` and the quartic degenerates
  to a cubic) is elliptic. Hence a general Cassini oval **cannot** serve as a first-kind
  arclength generator for `arc_of_length`. (The `s ± σ` combinations in [S43] are a different,
  non-Euclidean pair of integrals; the Euclidean perimeter is the hyperelliptic one.)
* **Curves `z = f(t)` with `|f′(t)|² = const/quartic(t)`.** With `f` rational this is exactly
  Serret's equation and the first-class solutions above; the realised moduli are the algebraic
  Serret moduli. With `f` merely real-analytic (e.g. the generating-triangle `γ_n`), *any*
  modulus occurs — see A.3. The `n = 1` member `f(t) = √2·t(e^{iπ/4}+t²e^{−iπ/4})/(1+t⁴)` has
  `|f′|² = 2/(1+t⁴)` **[numeric]** (`R2-03`, and F1 of the overview).
* **New example (2020).** Lipkovski–Popelensky give a rational curve with first-kind arclength
  outside the classical list; it does not change the countability statement.

### A.6 Answer to "every `c`, or only a countable set?"

**Only a countable set** for the *algebraic* (and, a fortiori, the rationally parametrised)
catalogue: it is exactly the union of the algebraic Serret/Kiepert moduli, contained in the
algebraic numbers. Every rational `c ∈ (0,1)` *is* realised (first class with `n = c/(1−c)`),
and the set is dense, but transcendental `c` are not. **Every** `c` is realised if one allows the
non-algebraic (real-analytic) Serret generating-triangle curve, which is the extension
recommended in Part C.

---

## B. Drawability

### B.1 The criterion

`Defs.lean` builds `PConstructibleCurve` from finitely many base sets (ellipse, rectangle,
`poly_graph`, `power_law`, `exp_two`, `sine`, `cubic_bezier`) under `translate_x/y`,
`scale_x/y`, `rotate`, `restrict`, `arc_of_length`, `offset`. If an arc of a Serret curve
coincided with an arc of a drawable algebraic curve, then the two irreducible algebraic
components would share infinitely many points, hence coincide (identity theorem for algebraic
curves). Therefore it suffices to compare the underlying algebraic curve of each catalogue
member with the underlying algebraic curves of the base family. Two invariants settle almost
everything: **degree** and **boundedness**. `R2-01`–`R2-05` supply the numbers.

### B.2 The Serret curves

By [S45b §VIII], the first-class curve of parameter `n` has

* degree `2(n+1)` if `n` is a positive integer, and `2(p+q)` if `n = p/q` in lowest terms;
* it is **unicursal** (the parametrisation is rational when `n` is rational), hence genus `0`;
* it is **bounded** and closed: `r ∈ [√(n+1)−√n, √(n+1)+√n]`;
* the `n = 1` member is a quartic with a node at `O` (the lemniscate), genus `0`.

The smallest degree is therefore `4` (the lemniscate), and every member has degree `≥ 4`.

### B.3 Comparison with each drawable family

| drawable ingredient | degree / nature | why a Serret arc cannot match |
|---|---|---|
| `ellipse` | conic, degree 2 | degree `< 4`; affine maps preserve degree |
| `rectangle` | union of 4 lines, degree 1 each | an arc of a Serret component inside a line is impossible (line is not a component) |
| `poly_graph p`, `natDegree p ≤ 6` | graph `y = p(x)`, unbounded | bounded Serret curve cannot equal an unbounded graph; a shared arc forces the whole component, and `y−p(x)` is unbounded |
| `power_law a b` | `y^q = a^q x^p` on `x>0`, unbounded | same boundedness argument; also every power law is unbounded in the affine chart |
| `exp_two`, `sine` | transcendental | an arc agreeing with an algebraic curve would make the transcendental function algebraic on an interval, impossible |
| `cubic_bezier` | image of a degree-3 polynomial map, degree `≤ 3` | degree `< 4`; affine images preserve degree |
| `translate/scale/rotate` | affine | preserves degree and genus |
| `restrict` | sub-arc/sub-set | does not change the underlying component |
| `offset` | see below | |

**Offsets.** For a base curve of velocity `v` and curvature `κ`, an offset at signed distance
`d` has speed `|v|·|1 − dκ|`; hence its arclength is
`(arc length of base) − d·(turning angle) + (corrections at cusps)`. The turning angle is
elementary (`arg v`). If the base is a line, circle or Pythagorean-hodograph cubic, its arclength
is elementary (polynomial/rational in the parameter), so the offset's arclength is elementary and
cannot equal the non-elementary first-kind `F` of a Serret curve. If the base is an ellipse or a
general Bézier, its arclength is an elliptic/hyperelliptic differential with a nonzero
second/third-kind component; subtracting an elementary form cannot remove that component, because
the decomposition of an abelian differential into exact + first + second + third kind is unique.
In every case the offset's arclength is not a pure holomorphic first-kind differential, so no
offset of a drawable curve coincides with a Serret curve. (Offsets of ellipses are degree 8 and
non-rational; offsets of PH cubics are rational of degree `≤ 5`. Even a rational degree-5 offset
would have elementary arclength, unlike a Serret curve.)

### B.4 Verdict for B

**Nothing in the catalogue is drawable**, and neither is any arc, affine image or offset of a
drawable curve. The obstruction is not rationality (the lemniscate *is* rationally
parametrised, correcting the final paragraph of `Jacobi.lean`) but **degree/boundedness combined
with the fact that the drawable algebraic curves have degree ≤ 3 or are graphs/unbounded**.
Cassini-type polar families are algebraic and could in principle realise transcendental moduli,
but their Euclidean arclength is hyperelliptic (§A.5), so they cannot generate `F` either.

---

## C. Minimal extension

Goal: a single new constructor that makes `jacobiAm c u` P-constructible for **every**
P-constructible `c < 1` and `u`.

### C.1 Rational cubic Bézier — rejected

A rational cubic Bézier is a degree-`≤ 3` rational map into the plane; its image has degree
`≤ 3`. Serret's classification puts the *least* first-class curve at degree 4 (the lemniscate),
and a curve whose arclength is a pure `F` is first class. So a rational cubic Bézier cannot have
single-`F` arclength for any non-degenerate `c`; adding weighted control points does not help
because the weights do not raise the image degree. **Rejected on degree.**

### C.2 A lemniscate base curve — rejected (only `c = 1/2`)

Adding the lemniscate as a base gives `F(·, 1/√2)` and hence only `c = 1/2`. One might hope that
`scale_x`, `scale_y` vary the modulus. They do not:

* uniform scaling is a similarity, leaves the quartic `1+t⁴` (equivalently the cross-ratio `1/2`)
  unchanged, so the modulus stays `1/2`;
* arbitrary linear maps have the same arclength as their singular-value diagonal form, so it is
  enough to test `diag(sx, sy)`. For the lemniscate `x = t(1+t²)/(1+t⁴)`, `y = t(1−t²)/(1+t⁴)`,
  `x′²+y′² = 2/(1+t⁴)`, `R2-03-affine-lemniscate.py` computes **[symbolic]**

  ```
  1/(sx²x′² + sy²y′²) = (1+t⁴)⁴ / (degree-12 polynomial)   for sx ≠ sy,
  ```

  which is **not** a quartic, so the affine image's arclength is **not** a single `F`
  (it acquires second/third-kind and elementary parts). Only `sx = ±sy` recovers
  `1/speed² = (1+t⁴)/2`, the same modulus `1/2`.

**Rejected:** one modulus only, and scaling cannot manufacture others. (The lemniscate with
`n = 1` is a *sub-*case of the recommended family below.)

### C.3 Algebraic families in general cannot cover all `c`

`c` ranges over all P-constructible reals, which include transcendental numbers (e.g. ellipse
arclengths, `π`, values of `exp`). By Serret's classification, a curve with *rational*
parametrisation and first-kind arclength exists only when the modulus is one of the algebraic
Serret/Kiepert moduli. Hence no algebraic base-curve family — however many parameters — realises
a general transcendental `c`; and by §A.5 the algebraic Cassini family, whose modulus is
continuous in its parameters and can be transcendental, has hyperelliptic (not first-kind)
arclength. **The extension must be a non-algebraic (real-analytic) one-parameter family.**

### C.4 Recommended constructor: the Serret generating-triangle family

Add **one** base-curve family, indexed by a P-constructible real parameter `n > 0`:

```
serret (n : ℝ) (hn : 0 < n) : PConstructibleCurve (γ_n '' Icc 0 π)
γ_n(α) = ( r_n(α) cos θ_n(α),  r_n(α) sin θ_n(α) ),
    r_n(α) = √n cos α + √(1 + n cos² α),
    β_n(α) = arcsin( √(n/(n+1)) sin α ),
    θ_n(α) = π + n α − (n+1) β_n(α).
```

This is a verbatim rendering of Serret's 1846 construction with the parameter `n` made a
P-constructible input rather than an integer. It is the smallest possible addition because a
single real parameter is exactly what is needed to hit every modulus `k² = n/(n+1)`, and no
algebraic family can (§C.3).

### C.5 The construction in full

Write `c` for the target parameter (`c = k²` in the projection's notation) and put

```
n := c/(1−c)  > 0,        k := √c = √(n/(n+1)).
```

`n` and `k` are P-constructible from `c` (field operations and `Real.sqrt`), and `√n`, `√(n+1)`
are P-constructible, so `serret n` is a P-constructible curve and every `γ_n(α)` has
P-constructible coordinates for P-constructible `α`.

**Arc length [symbolic + numeric, `R2-01`, `R2-05`].** By (A.5),

```
speed (γ_n) (α) = √n / √(1 − k² sin² α) = √n / √(1 − c sin² α),
arcLengthOf γ_n 0 α = √n · F(α, k) = √n · ellipticF c α.
```

So `γ_n` is exactly the curve whose arclength function is `F(·, c)` up to the scale `√n`.

**Injectivity and the complementary arc [numeric, `R2-05`].**
`γ_n` is injective on `[0, π]` (grid check, minimum pairwise distance positive for
`n ∈ {0.5, 1, 1.7, 2, 3}`); the only special point is the node at `α = π/2` for `n = 1`, hit
once. Also `F(π−α, k) = 2K − F(α, k)` to 40 dps, and `θ_n(−α) = 2π − θ_n(α)` (reflection in the
focal axis). Hence the arc `Γ_a := γ_n([0, a])` and the "opposite" arc
`Γ'_a := γ_n([a, π])` cover `γ_n([0, π])`, meet only at `γ_n(a)`, and have lengths

```
len Γ_a = √n F(a, k),        len Γ'_a = √n (2K − F(a, k)),        (C.1)
```

with `2K = F(π, k)` the length of the half-curve.

**Reduction to `[0, K]`.** As for `ellipticEAm`, periodicity and reflection reduce a general
`u` to `[0, 2K]` and then to `[0, K]`. The two identities are `F(α + π) = F(α) + 2K` and
`F(π − α) = 2K − F(α)`, giving `am(u + 2K) = am(u) + π` and `am(2K − u) = π − am(u)`; this
mirrors `jacobiAm_add_int_mul` and `ellipticE_pi_sub`.

**Abutting arcs [construction].** Let `L := √n · u` and suppose first `0 ≤ L ≤ √n K`
(the reduction above handles the rest). Then:

1. `L` and `R := √n·2K − L` are P-constructible: the half-curve arclength
   `arcLengthOf γ_n 0 π = √n·2K` is the length of the arc between the two P-constructible
   endpoints `γ_n(0) = (√n+√(n+1))·(−1,0)` and `γ_n(π) = (√(n+1)−√n)·(1,0)`, so it is
   P-constructible by `PConstructible.arc_length`, and `2K` is that over `√n`.
2. `A :=` the arc laid out by `arc_of_length` along `serret n` from `γ_n(0)` with length `L`;
   by (C.1) its far endpoint is `γ_n(a)`, where `a := am(L/√n, k) = am(u, c)`.
3. `B :=` the arc laid out from the *other* end `γ_n(π)` with length `R` (travelling backwards);
   its far endpoint is again `γ_n(a)`.
4. By the injectivity of `γ_n` on `[0,π]`, `A ∩ B = {γ_n(a)}`, so `inter_x A B` and
   `inter_y A B` are P-constructible.
5. From the point `(x, y)` of `γ_n(a)` recover `a`: `r = √(x²+y²)` and, by (A.2),
   `cos a = (r²−1)/(2√n r)`. Both are P-constructible, and `a` lies in the known range, so
   `a = am(u, c)` is P-constructible.

This is the exact analogue of `ellipticEAm_Pconstructible_of_mem_Icc`, with the ellipse replaced
by `serret (c/(1−c))` and `E` by `F`. Since `c` and `u` were arbitrary, `jacobiAm c u` is
P-constructible for every P-constructible `c < 1` and `u`, and then `sn`, `cn`, `dn` follow from
`jacobiSn/Cn/Dn_Pconstructible_of_am`.

### C.6 Notes for the Lean implementation (not done here — Defs is the user's call)

* `γ_n`, `r_n`, `β_n`, `θ_n` are elementary combinations of `Real.sqrt`, `Real.cos`,
  `Real.sin`, `Real.arcsin`; no new imports beyond what `Defs.lean` already carries.
* The one genuinely new analytic lemma is `speed (γ_n) = √n/√(1−c sin²·)`; its proof is
  `field_simp`/`ring` after `linear_combination` with `(1)` and `(3)` above, exactly as
  `speed_ellipseParam_eq` is proved.
* Injectivity of `γ_n` on `[0,π]` should be handled *locally*, as in
  `ellipseArc_PConstructibleCurve`, not as a global statement, to avoid the node.
* The only structural difference from the ellipse development is that the new base family is
  analytic for irrational `n`; no algebraic equation is ever used, so the existing
  `PConstructibleCurve` schema (base families given by explicit point-set predicates) is
  unchanged.
* `pi_Pconstructible`, `int_Pconstructible`, `arccos_Pconstructible_of_mem_Icc` and the
  periodicity lemmas are all already available in `Jacobi.lean`/`Basic.lean`.

---

## Verification index

| script | what it checks | tag |
|---|---|---|
| `R2-01-serret.py` | Serret rederivation (A.1)–(A.5); `speed²(1−k²sin²α)=n`; `Δ²+(r²−(2n+1))²=4n(n+1)`; `arc=√n F(α,k)` for 5 values of `n` | symbolic + 30 dps |
| `R2-02-cassini.py` | Cassini differential `ds=b²√u du/√((P−u²)(u²−Q))` | symbolic |
| `R2-03-affine-lemniscate.py` | affine lemniscate `1/speed²` is degree 16/12, not quartic; only uniform scaling keeps `k=1/2` | symbolic |
| `R2-04-cassini-arclength.py` | Cassini quarter-perimeter `=(b²/√α₀)∫(1−k²sin²φ)^{−1/4}dφ`; hyperelliptic, not `−1/2`; lemniscate limit `=(√2/2)K(1/2)` | 21–30 dps |
| `R2-05-serret-geometry.py` | `n=1` is the focus-`(1,0)` lemniscate; `F(π−a)=2K−F(a)`; injectivity of `γ_n` on `[0,π]`; `θ(−a)=2π−θ(a)`; half-length `=√n·2K` | 40 dps |

## Final independent arithmetic re-check

Performed after writing the body (script `R2-06-recheck.py`), recomputing the headline constants
from scratch with independent methods:

* `K(1/2) = 1.8540746773013719184…` (mpmath `ellipk`) and
  `∫₀^{π/2}(1−½sin²)^{-1/2} = 1.8540746773013719184…` (quadrature) — agree to 40 dps.
* lemniscate quarter `∫₀^{π/4}dθ/√(cos2θ) = 1.3110287771460599… = K(1/2)/√2` — agree to 25 dps.
* `n = c/(1−c)` for `c = 1/2, 1/3, 2/3, 0.9` gives `k² = n/(n+1)` equal to `c` to 40 dps.
* the recommended arc identity `arc(0→α) = √n F(α, √(n/(n+1)))` rechecked at `n = c/(1−c)`,
  `c = 0.7`, `α = 1.2`, to 30 dps.
