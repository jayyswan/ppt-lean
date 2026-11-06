# NOTES-jacobi-X3 — classical geometric mechanisms for the amplitude

Task `PLAN-jacobi-X3-classical-mechanisms.md` (X series). **Research only: no `.lean` file
was created, edited or deleted.** Numerics: Python 3.12 + `mpmath`/`numpy` at
`C:\Users\<user>\AppData\Local\Programs\Python\Python312\python.exe`; scripts live in
`archived files/jacobi-scripts/` with the `X3-` prefix. `mpmath`'s `ellipfun(kind,u,m)` and
`ellipf(phi,m)` take the parameter `m = c = k²`; that convention is used here.

Every identity is tagged **[symbolic]** (exact, or reduced to a named theorem) or
**[numeric, N digits]** (script named). Web sources carry URLs in §8.

---

## Plain-language summary (≤10 lines)

1. Eighteenth/nineteenth-century geometers built real ruler-and-conic devices — strings around
   confocal ellipses, hyperbolas, Poncelet tangents — that are *exactly* about "arc length minus
   a straight length", the combination the string tool cannot do alone.
2. Checked numerically, they all split into two kinds: they compute the **second-kind** integral
   `E` (Graves–Chasles, Fagnano) or a **mixture of `E` and first-kind `F`** (MacCullagh/Landen).
3. Graves–Chasles is confirmed to 35 digits: `|PT₁|+|PT₂| + (far inner arc)` is constant; the arc
   is `a(E(φ₂)−E(φ₁))`, and using it backwards inverts **`E`** (`ellipticEAm`), not `F`.
4. MacCullagh/Landen is confirmed to ~30 digits: a hyperbola arc is `(b²/c)F(θ,κ) − c·E(θ,κ) +
   algebraic`; both coefficients are nonzero.
5. Fagnano is the addition theorem for `E` (`E(φ)+E(ψ)−E(μ) = m sinφ sinψ sinμ`, ~33 digits);
   its first-kind analogue (lemniscate/Fagnano doubling) exists only at the **fixed** modulus
   `m = 1/2`.
6. Poncelet's tangent step is an **algebraic** (degree-2) map, not a rotation in the outer angle;
   its natural Jacobi time was not reduced to a standard `F` here (partial result).
7. Lemniscate/AGM/elastica give either fixed modulus, or an infinite process, or a curve that is
   not in `Defs.lean`.
8. **Verdict: negative.** None of the classical conic mechanisms inverts the first-kind map `F`;
   they give forward `E`/`F` values, and at most invert `E`.
9. The only assumptions that would let a construction through are (i) a drawable curve of pure
   **first-kind** arc length (the Serret family, R2) or (ii) a constructor whose curve algebraically
   encodes `F` (the X2 loophole). Neither exists in `Defs.lean`.
10. Useful negative: it closes the "classical geometry" family of routes and names the exact gap.

---

## 0. Mechanism / verdict table

| # | Mechanism | What it computes | Inverts anything? | Verdict | Numeric check |
|---|---|---|---|---|---|
| 1 | **Graves–Chasles** string on confocal ellipses | ellipse arc `a(E(φ₂)−E(φ₁))` = algebraic `L−(|PT₁|+|PT₂|)` | inverts **E** (`ellipticEAm`); not F | **Negative** (2nd kind) | `X3-01` spread `2.4e-35`, `0.0` [numeric, 35] |
| 2 | **MacCullagh / Landen** hyperbola | `(b²/c)F − c·E + algebraic` (mixed) | no (mixed inverse is new, not `am`) | **Negative** | `X3-02` ~30 digits [numeric, 30] |
| 3 | **Fagnano** ellipse arcs / lemniscate | E-addition `m sinφ sinψ sinμ` (algebraic) | E-addition; F-addition only `m=1/2` | **Negative** | `X3-03` `2.4e-33` [numeric, 33] |
| 4 | **Poncelet–Jacobi** two circles | algebraic degree-2 tangent map | none found; step not `F(θ,m)` | **Partial / undetermined** | `X3-04` (unreduced) |
| 5 | **Lemniscate / AGM / pendulum / elastica** | `F` at fixed `m=1/2`, or time `= ∫dθ/Δ` (F) | special arguments only; AGM infinite | **Negative** | X2 / R2 / analytic |
| 6 | **Greenhill/Salmon/Chasles catalogue** | curves with elliptic arclength | same as 1–3 | **Negative** | literature |

---

## 1. Graves–Chasles string theorem — second kind only

**Statement.** Let `E_in` be an ellipse with semiaxes `a>b`, focus distance `f²=a²−b²`, and let
`E_out` be a confocal ellipse with semiaxes `A>B`, `A²−B²=f²`. For `P` on `E_out`, draw the two
tangents to `E_in`, touching at `T₁,T₂`. Then
**[symbolic]**
```
|P T₁| + |P T₂| + arc_far(T₁,T₂)  =  L  (constant),
```
where `arc_far` is the arc of `E_in` on the side of `E_in` away from `P`. Equivalently the inner
arc is an **algebraic** function of `P` plus the constant string length `L`; this is the geometric
form of the addition theorem for the integral of the second kind. Sources: Dinčǎ,
arXiv:0902.1421 §3.2 (exact statement: "the excess between the sum of the lengths of tangents …
and the subtended arc … independent of the point"); Chasles 1843, "Propriétés générales des arcs
d'une section conique dont la différence est rectifiable"; DLMF §19.30(i).

**Numeric check** (`X3-01-graves.py`, runs in <1 s). Inner `a=2, b=√3`, outer `A=2.5,
B=√5.25`; and a second pair `a=3, b=2, A=3.6`. Sampling 24 points `P` around `E_out`, the
quantity `|PT₁|+|PT₂|+arc_far` has **max spread 2.4e-35** (first pair) and **0.0** (second pair)
at 35 dps; `L = 12.21372680579770365825052` for the first pair (perimeter `11.739697674715417244`).
The arc integral `a·(E(φ₂,c)−E(φ₁,c))` with `c=1−b²/a²` agrees with direct quadrature to `0.0`.

**What it pins down, and why it fails.** The measured arc is a difference of **`E`** values, i.e.
pure second kind; the tangent lengths are algebraic. Running the mechanism *backwards* — choosing
the outer point so that the inner arc takes a prescribed value — is an inverse-`E` problem; the
script solves it by bisection and recovers the eccentric angle `θ=1.0471975511965976` to
`1.02e-24`. That is exactly `ellipticEAm` (already a black box in the programme), **not** `am`.
To reach `am` one would need a curve whose own arc length is a pure first-kind `F`; every confocal
ellipse has second-kind arclength, so the assumption that would let Graves through — a confocal
family with first-kind arclength — is false.

## 2. MacCullagh / Landen hyperbola — mixed `E` and `F`

**Statement.** The hyperbola is drawable in `Defs.lean`: `y=1/x` is `power_law(1,−1)` (`x>0`),
and every hyperbola is its affine image under `translate_x/y`, `scale_x/y`, `rotate`. Its arc
length is an elliptic integral. **DLMF §19.30(ii)** reduces it to Carlson's `R_D`, and says "for
`s` in terms of `E(φ,k)`, `F(φ,k)`, and an algebraic term see Byrd–Friedman (1971, p. 3)".
Landen's theorem (1775) expresses a hyperbolic arc through two elliptic arcs; MacCullagh's
"hyperbolic excess" is the arc minus the tangent-to-asymptote length. Sources: DLMF §19.30(ii),
DLMF §19.7.5 and §19.7.7, Mingari-Scarpello–Ritelli, arXiv:1209.4909, Landen,
*Phil. Trans.* **65** (1775) 283–289.

**Exact reduction [symbolic].** With `c²=a²+b²`, `k₀=a/b`, `κ=a/c`, `κ'=b/c`, `sinh t = tan ψ`,
`sin θ = √(1+k₀²)·sin ψ / √(1+k₀² sin²ψ)` (DLMF 19.7.7 imaginary argument + 19.7.5 imaginary
modulus):
```
s(t) = (b²/c)·F(θ,κ) − c·E(θ,κ)
       + (a²/c)·sinθ cosθ / √(1−κ² sin²θ)
       + b·tanψ·√(1+k₀² sin²ψ).
```
**Numeric check** (`X3-02-hyperbola.py`, runs in ~1 s, 30 dps, `a=2, b=1`): `s_formula − s_direct`
is `3.5e-31, 9.9e-31, 3.9e-31, 1.6e-29` at `t = 0.3, 0.8, 1.5, 2.5`.
The two elliptic coefficients are
```
F-coefficient = b²/c = +0.4472135955…      E-coefficient = −c = −2.2360679775…
```
both **nonzero**: a genuine mixture.

**Why it fails.** E-parts *can* be cancelled by combining with an ellipse arc (which contributes
`E` only), but the `F`-part has coefficient `b²/c ≠ 0`, and `F` is not a coefficient an ellipse
can supply. Since no drawable curve has pure first-kind arclength (R1a/R1b/R1c/R2), the `F`-term
has no drawable partner. Inverting the mixed arc gives a new transcendental map, neither `F` nor
`am`: the script solves `s(ψ)=target` and finds `θ = 1.29116745991442`, whereas
`am(target/β) = 2.38807…`. The assumption that would let MacCullagh/Landen through — that the
`E` and `F` parts could be separated into two *curves* (not just two numbers) — is exactly the
Serret requirement, which `Defs.lean` does not meet.

## 3. Fagnano's theorem — the addition theorem for `E`

**Statement.** Fagnano's ellipse theorem (as commonly paraphrased, e.g. Eppstein's usenet
compilation): *two arcs of an ellipse differ by a straight length when their endpoints are
related by the normal condition.* Analytically this is the Euler/Fagnano addition theorem for the
second kind **[symbolic]**: if `F(φ)+F(ψ)=F(μ)` (Jacobi `sn`-addition), then
```
E(φ) + E(ψ) − E(μ) = m·sinφ·sinψ·sinμ,
```
whose right-hand side is algebraic — an arc difference equals a constructible straight length.
Sources: Eppstein junkyard (<https://ics.uci.edu/~eppstein/junkyard/fagnano.html>), Chasles 1843,
MacTutor Fagnano biography.

**Numeric check** (`X3-03-fagnano.py`, ~3 s, 32 dps): worst residual over 9 cases
(`m ∈ {0.3,0.6,0.85}` × 3 pairs) is **`2.4e-33`**. Lemniscate (`m=1/2`) doubling
`sl(2u) = 2·sl(u)·√(1−sl⁴u)/(1+sl⁴u)` matches to `0.0` and `−7.7e-34` at `u=0.3,0.6`; the
general Jacobi `sn`-addition is algebraic for any `m` (residual `~1e-33` at `m=0.7`).

**Why it fails.** Fagnano's geometric realisation is an **`E`-addition** (second kind). The
first-kind analogue is the lemniscate/Fagnano doubling, but the lemniscate integral has the single
fixed parameter `m=1/2`, and R2 showed affine scaling cannot change that modulus, so it realises
only `c=1/2`. The general first-kind addition (`sn(u+v)`, algebraic) exists but *takes `am(u), am(v)`
as input*: it is an addition law, not an inversion. The assumption that would let Fagnano through —
a variable-modulus first-kind curve — is precisely the Serret extension of R2.

## 4. Poncelet–Jacobi for two circles — partial

**Setup and step equation.** Outer unit circle at `O`; inner circle centre `(d,0)`, radius `r`,
`r+d<1`; `P=e^{iθ}`. A chord with unit normal `n=(cosψ,sinψ)` through `P` touches the inner circle
iff `n·(C−P)=±r`, i.e.
```
d·cosψ − cos(ψ−θ) = ±r        (equivalent to MathWorld's  r + d cosφ − cos(φ−θ) = 0),
```
and its two outer intersections have angles `ψ ± arccos(n·P)`, one of which is `θ`, so
`θ' = 2ψ − θ`. Sources: MathWorld *Poncelet's Porism* (tangent equation, Richelot 1830 / Fuss
1792), Jacobi 1828.

**What the numerics show** (`X3-04-poncelet.py`). With `r=0.4, d=0.3` the forward orbit is
`θ = 0, 1.925101, 4.848325, 6.569752, 8.765184, …` (increments `1.925, 2.923, 1.721, 2.195, …`).
1. The map is **algebraic of degree 2**: `θ'` is obtained from a quadratic in `tan(ψ/2)`; it is
   **not** a Möbius rotation. Fitting a Möbius map in `t=tan(θ/2)` from the first three steps
   leaves residuals that grow to `−0.098`, `−8.9` at steps 4 and 7.
2. The step is not constant in `θ` or in the chord-normal angle `ψ`.
3. `F(θ',m) − F(θ,m)` is **not** constant for any `m`: best spread over a 500-point scan in
   `m∈(0,1)` is `≈0.71` (coordinate `θ`) and `≈0.32` (coordinate `ψ`), with the optimum drifting
   to `m→0`. So the **outer angle is not the Jacobi coordinate**, and the natural genus-1
   amplitude was *not* reduced to a standard `F(angle,m)` in this budget.

**Verdict: partial / undetermined.** The exact Jacobi linearisation of the two-circle Poncelet
correspondence (its genus-1 coordinate and modulus as functions of `(r,d)`) was not pinned down.
Independently of the linearisation, the structural obstruction stands: every tangent step and
read-off is **algebraic**, so any *fixed finite number* of steps is an algebraic function of the
start data; a single step can equal `am(u)` only if the step function `Δ(r,d)` can be set to `u`
by constructible `r,d`, and `Δ(r,d)` is the period of a first-kind integral — inverting it is
again `am`. `Δ(r,d)=u` therefore cannot be solved with the allowed moves. To finish this
mechanism one would identify the invariant cross-ratio of the two circles, map it to the Legendre
modulus, and show `Δ` is a complete first-kind integral in that modulus.

## 5. Lemniscate division, AGM, pendulum, elastica — negative

- **Lemniscate / Fagnano division (Gauss–Abel).** Fagnano's division of the lemniscate into `n`
  equal arcs holds for `n = 2^a·(product of Fermat primes)`; it produces only the *special*
  arguments `Ω/n`, never `sl(u)` for a general constructible `u`. The lemniscate integral is a
  `F` at the **fixed** modulus `m=1/2` (R2).
- **Gauss AGM.** The arithmetic–geometric mean computes `sl(u)`/`F` by an *infinite* iteration;
  `Defs.lean` constructions are finite trees, so AGM is not a constructor. (Landen's formula,
  MathWorld *Landen's Formula*.)
- **Pendulum / elastica.** The pendulum phase portrait is drawable, but its **time** is
  `∫dθ/√(2k(cosθ−cosθ₀))`, an `F`-integral, not a Euclidean length; X2 already showed the
  portrait does not remember the time. The rectangular elastica has tangent angle an elliptic
  function of arclength, but its defining ODE is none of `ellipse / rectangle / poly_graph
  (deg ≤ 6) / power_law / exp_two / sine / cubic_bezier`, so it is not a base curve, and no
  closure operation manufactures it.

**Verdict: negative.** Sources: DLMF §19.30(iii), MacTutor Fagnano/Landen, X2 notes,
Greenhill 1892 p. 190.

## 6. Other classical sources

Chasles (1843) "Propriétés générales des arcs d'une section conique dont la différence est
rectifiable"; Serret's first-kind family and the lemniscate (already catalogued in R2); Salmon,
*Higher Plane Curves*; Greenhill, *The Applications of Elliptic Functions* (1892, free at
<https://archive.org/download/applicationselli00greerich/applicationselli00greerich.pdf>),
p. 190 (curves with elliptic arclength). None adds a mechanism beyond the `E`-type (1,3), the
mixed `E`+`F` (2), or fixed-modulus `F` (5). **Verdict: negative.**

---

## 7. The negative claim, stated precisely

**Excluded class.** Any finite construction built from the `Defs.lean` moves whose measured
lengths arise from the classical confocal / Fagnano / MacCullagh–Landen / two-circle Poncelet
configurations, in the sense that they can supply only
(i) `E`-type lengths plus algebraic data (Graves–Chasles, Fagnano ellipse),
(ii) mixed `E`+`F` lengths plus algebraic data (MacCullagh/Landen hyperbola), or
(iii) algebraic maps whose linearising time is a first-kind integral reached only through an
algebraically-defined angle (Poncelet).

None of these yields the **inverse** of the first-kind map `F`: at most they invert `E`
(`ellipticEAm`), and `E`, `F` are already P-constructible *forward*. Because `am` is not
D-finite (X1), a successful measured-length construction must live in the transcendental
fragment, but the classical conic mechanisms are second-kind or fixed-modulus.

**Assumption that would let one through.** A single new constructor producing a **drawable curve
of pure first-kind (Euclidean) arc length** — the Serret generating-triangle family of R2, whose
arc is `√n·F(α,√(n/(1+n)))`, with `n=c/(1−c)` — would let `arc_of_length`/abutting arcs invert `F`
and yield `am` for every P-constructible `c<1`. Equivalently (X2 §6.3), a constructor producing a
curve whose defining equation algebraically encodes `F` would break the claim. Strictly within the
current `Defs.lean` move set, neither exists.

## 8. References (URLs)

- DLMF §19.30 *Lengths of Plane Curves* — <https://dlmf.nist.gov/19.30> (i ellipse, ii hyperbola,
  iii lemniscate).
- DLMF §19.7 *Connection Formulas* — <https://dlmf.nist.gov/19.7> (19.7.5 imaginary modulus,
  19.7.7 imaginary argument).
- I. Dinčǎ, *Thread configurations for ellipsoids*, arXiv:0902.1421 §3.2 — exact Graves statement.
- G. Mingari Scarpello, D. Ritelli, A. Scimone, *The hyperbola rectification from Maclaurin to
  Landen …*, arXiv:1209.4909 — <https://arxiv.org/abs/1209.4909>.
- J. Landen, *Phil. Trans. R. Soc.* **65** (1775) 283–289 (hyperbolic arc via two elliptic arcs).
- M. Chasles, *Propriétés générales des arcs d'une section conique, dont la différence est
  rectifiable* (1843).
- MathWorld, *Poncelet's Porism* — <https://mathworld.wolfram.com/PonceletsPorism.html>
  (tangent equation `r + d cosφ − cos(φ−θ)=0`).
- J. Keane (usenet), *Fagnano's theorem on normals to an ellipse*, arch. Eppstein —
  <https://ics.uci.edu/~eppstein/junkyard/fagnano.html>.
- MacTutor, *John Landen* / *Giulio Fagnano* /
  <https://mathshistory.st-andrews.ac.uk/Biographies/Landen>.
- A. G. Greenhill, *The Applications of Elliptic Functions* (1892), p. 190 —
  <https://archive.org/download/applicationselli00greerich/applicationselli00greerich.pdf>.
- Prior programme notes used: `NOTES-jacobi-R1a/R1b/R1c/R2/R3.md` (drawable arclength catalogue;
  Serret first-kind family), `NOTES-jacobi-X1.md` (`am` not D-finite), `NOTES-jacobi-X2.md`
  (crossings, pendulum time, loopholes).

## 9. Verification index

| script | what it checks | tag |
|---|---|---|
| `X3-01-graves.py` | far-arc string identity constant (`2.4e-35`, `0.0`); arc `=a(E(φ₂)−E(φ₁))`; backward = inverse-E to `1.0e-24` | numeric, 35 |
| `X3-02-hyperbola.py` | DLMF 19.7.5+19.7.7 hyperbola reduction `(b²/c)F−cE+alg` to `1.6e-29`; both coefficients nonzero; mixed inverse ≠ `am` | numeric, 30 |
| `X3-03-fagnano.py` | `E(φ)+E(ψ)−E(μ)=m sinφ sinψ sinμ` to `2.4e-33`; lemniscate doubling `m=1/2`; general `sn`-addition | numeric, 33 |
| `X3-04-poncelet.py` | tangent map degree-2 algebraic; step not constant in `θ,ψ`; best `F`-fit spread `0.71`/`0.32`, `m→0` | numeric, partial |
