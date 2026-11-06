# NOTES-jacobi-X5 — what theory could rule routes out, and where it breaks

Research task `PLAN-jacobi-X5-obstruction-theory.md`. **Research only: no `.lean` file was
created, edited or deleted.** Numerics: Python 3.12 + `mpmath` at 40 dps
(`C:\Users\<user>\AppData\Local\Programs\Python\Python312\python.exe`); script archived as
`archived files/jacobi-scripts/X5-01-theory-checks.py`. Tags: **[symbolic]** (proved or reduced
to a named theorem), **[numeric, N digits]**. Web sources carry URLs in §8.

---

## Plain-language summary (10 lines)

1. A *uniform* construction is one finite recipe that works for all `u` in an interval; it is a
   statement about functions, and §1 gives a precise class `ℱ` of the functions such recipes can
   produce (two sorts: constructible curves `𝒢`, constructible functions `ℱ`).
2. `ℱ` is closed under `+ − × ÷`, elementary composition, differentiation, **integration of the
   speeds of constructible curves** (the `arc_length` move), **unique crossings** (`inter`), and
   the **inverses of those arc lengths** (`arc_of_length`). It is also closed under composition of
   its own elements, which is what defeats most closure theories.
3. **No existing theory excludes `am` from `ℱ`.** Each candidate handles one fragment:
   D-finite theory handles the algebraic fragment only; o-minimality/Pfaffian can never exclude
   `am` because `am = ∫ dn` with `dn` Pfaffian, so `am` is definable in the o-minimal Pfaffian
   closure; differential algebra proves `am` is not elementary but cannot separate it from
   `ellipticEAm`, which is constructible and also non-elementary.
4. The best candidate is **Ax–Schanuel functional transcendence** (Ax 1971; Brownawell–Kubota;
   Bertrand–Pillay) plus the **Hodge "kind" invariant** (first vs second/third kind). It *can*
   prove the corrected transcendence input `(T3)′` for algebraic `M`, and shows `u` and `am(u)`
   are algebraically independent.
5. But Ax–Schanuel only controls **algebraic** relations. It cannot absorb `arc_length`
   integration, `arc_of_length` inversion, offset, or crossings with `sine`/`exp_two`. So it does
   not prove the target either.
6. **The R3 derivative test's input `(T3)` is false as stated**, with the trivial counterexample
   `M = F_c` (`F_c(am_c(u)) = u`, verified to 0.0 residual, §4). The test therefore cannot be applied
   as written; the corrected input must explicitly exclude "first-kind sections", which is exactly
   the object being sought. This is the headline finding.
7. The obstruction has a clean structural form: every `arc_of_length` inversion is the inverse of
   a **Euclidean speed**, and no drawable curve's speed is proportional to `Δ_c` (R1/R2). The
   first-kind inversion `am` would require such a curve; the second-kind inversion `EAm` is what
   the move set can actually do. **§3 gives this as the "kind" criterion.**
8. Ranked holes (§5): (1) `(T3)` false/corrected; (2) parameter-dependent curves `L1`; (3) the
   uniform/non-uniform gap (§6); (4) multi-stage cancellation `L2`; (5) transcendental curve
   crossings; (6) composition closure; (7) CM moduli; (8) model weakness of `Defs.lean`.
9. For **non-uniform** recipes (§6): a single finite tree is real-analytic, so by the identity
   theorem it can equal `am` only on a discrete set. If no uniform tree works on an interval, the
   constructible `u`'s are a **countable** union of discrete sets — consistent with the known dense
   countable `S_c`, and no stronger. The problem is then genuinely pointwise/transcendence.
10. **Outcome: negative/structural.** No theory excludes the class; the best one proves a
    corrected `(T3)′` only under strong algebraic restrictions, and the exact gap is the
    integration/inversion/non-uniformity of items 5–6–9.

---

## 0. What was asked

The brief asks: (Q1) define "uniformly constructible function of `u`" precisely, with the function
operation contributed by every move; (Q2) for each candidate theory (differential algebra,
Ax–Schanuel/functional transcendence, D-finite, o-minimal/Pfaffian) say what it proves about `am`
and which operations it absorbs or not; (Q3) rank the moves the best theory cannot absorb (the
most valuable output); (Q4) say what can be said for non-uniform recipes. This note answers all
four. No `.lean` edits; the script `X5-01-theory-checks.py` supports §2.4, §3.3 and §4.

---

## 1. Q1 — the class of uniformly constructible functions

Fix `c` with `0 < c < 1`, P-constructible, and an open interval `U ⊆ ℝ` on which `u` ranges.

The moves of `Defs.lean` are **two-sorted**: curves are point-sets, numbers/functions are scalars.
A crossing needs a unique intersection of two *curves*; `arc_length` integrates the speed of a
*tracing of a curve*; `arc_of_length` produces a *curve* from a length. A definition that forgets
the curve/function distinction is wrong in a way that matters (it would let the equation
`u = F_c(z)` count as a "crossing" and trivialise the problem — see Remark 1.4). So:

### 1.1 The two sorts

A family of planar point-sets `S = (S(u))_{u∈U}` is a **constructible curve family over `U`** if
it is produced by finitely many applications of:

* **(C0) base.** `S(u)` is the image of a base constructor `ellipse`, `rectangle`, `poly_graph`
  (degree ≤ 6), `power_law`, `exp_two`, `sine`, `cubic_bezier`, all of whose *scalar parameters*
  (centre, semiaxes, coefficients, exponents `a,b`, control points) are functions in `ℱ(U)`
  (defined below). Note the base *functions* themselves (`2^{·}`, `sin`) are fixed; only the
  parameters vary.
* **(C1) affine maps.** `S(u) ↦ A(u)·S(u) + t(u)` with `A(u)` a `2×2` matrix and `t(u) ∈ ℝ²` with
  entries in `ℱ(U)`; this covers `translate_x/y`, `scale_x/y`, and `rotate n` (whole-degree `n`,
  composed with scalings).
* **(C2) restriction.** `S(u) ↦ S(u) ∩ {box}(u)` where the window bounds are in `ℱ(U)`.
* **(C3) offset.** Replace a traced curve `γ_u` by `γ_u + d(u)·unitNormal(γ_u)` with `d ∈ ℱ(U)`.
* **(C4) arc of prescribed length.** Replace a traced curve `γ_u` by its sub-arc laid from a point
  with coordinates in `ℱ(U)` and of length `ℓ(u) ∈ ℱ(U)` (the `arc_of_length` move).

Write `𝒢(U)` for the class of constructible curve families thus generated (the parameter functions
used in C0–C4 are drawn from `ℱ(U)`; the definition is mutual recursion with `ℱ`).

A real function on (an open subinterval of) `U` belongs to the **constructible function class
`ℱ(U)`** if it is produced by finitely many applications of:

* **(F0)** constants (P-constructible reals) and the identity `u ↦ u`;
* **(F1) field and elementary closure.** `+`, `−`, `×`, `÷`, and `√, exp, log, sin, cos, tan,
  arcsin, arccos, arctan` applied to elements of `ℱ(U)` (on their domains);
* **(F2) parametric arc length.** For `S ∈ 𝒢(U)` with a tracing `γ_u : J_u → ℝ²` (injective,
  differentiable, integrable, `speed γ_u > 0`) and `a, b ∈ ℱ(U)` with `a(u) < b(u)`,
  the map `u ↦ arcLengthOf γ_u (a(u)) (b(u)) ∈ ℱ(U)` (this is `arc_length`);
* **(F3) unique crossings.** If `S, T ∈ 𝒢(U)` have a **unique transversal intersection**
  `S(u) ∩ T(u) = {(x(u), y(u))}` for every `u ∈ U` (uniformly in `u`), then `x, y ∈ ℱ(U)`
  (this is `inter_x`/`inter_y`);
* **(F4) black boxes already in the library.** Roots of degree-≤6 polynomials with `ℱ` coefficients,
  `π`, `arccos` on `[−1,1]`, `ellipticF`, `ellipticE`, `ellipticPiInc` (`n>1`) forwards,
  `ellipticEAm`, and the number-level combinators already proved P-constructible — all subsumed by
  F1–F3 plus `Pptc/Jacobi.lean`; listed for completeness.

**Definition 1 (uniform constructibility).** `jacobiAm c ·` is **uniformly constructible over `U`**
if `am_c ∈ ℱ(U)`, i.e. some finite derivation tree in the above grammar has output `am_c` on `U`
with `u` as a free parameter. A **uniform construction** of `am_c` is such a tree.

Every element of `ℱ(U)` is **real-analytic on a dense open subset** (each of F1–F3 is analytic:
F2 is the antiderivative of a real-analytic integrand in a real-analytic family; F3 is the implicit
function of a real-analytic system with `∂/∂z ≠ 0`; `restrict` and case-splits cut `U` into
finitely many analytic pieces). This analyticity is used in §6.

### 1.2 The function operation each move contributes

| move | curve-level effect | function operation contributed to `ℱ` |
|---|---|---|
| base curves with `ℱ` parameters | varies the defining elementary function in `(x,u)` | substitution of an `ℱ` function into an elementary (algebraic/trig/exp) expression; composition with `sin`, `2^{·}`, powers |
| `translate/scale/rotate` | affine substitution `(x,y) ↦ A(u)(x,y)+t(u)` | affine substitution with `ℱ` coefficients |
| `restrict` | intersection with a box | multiplication by a characteristic function, hence **finitely many analytic pieces** (piecewise analytic) |
| `offset` | `γ + d·n` | the speed factor `|1 − d·(v×v′)/|v|³|` (overview F3); an algebraic function of the curve data and its derivatives (still elementary/Pfaffian) |
| `arc_length` | — | the **definite integral** `∫ₐᵤᵇᵘ σ_u(t) dt` of a Pfaffian function `σ_u(t)=speed γ_u(t)` over `ℱ` bounds |
| `arc_of_length` | a sub-arc of prescribed length | the **inverse** of an arc-length function, `u ↦ γ_u(s_u^{-1}(ℓ(u)))` (equivalently the primitives of F2 plus F3) |
| `inter_x/inter_y` | unique crossing | an **implicit function** `u ↦ x(u)` of an analytic system coming from two curve families |

So the class `ℱ` is exactly the closure of the elementary functions under:

> **(op1)** field operations and elementary composition; **(op2)** definite integration of the
> speeds of constructible curves (parametric definite integrals of Pfaffian functions);
> **(op3)** implicit functions defined by unique crossings of constructible curves;
> **(op4)** inversion of the arc lengths appearing in (op2).

This is the answer to Q1's "list the function operations".

### 1.3 Immediate structural properties

* **(P1) `ℱ` is composition-closed.** Construction trees nest: if `f, g ∈ ℱ(U)`, substituting the
  tree of `g` for the input of the tree of `f` gives a tree for `f∘g`. This is the single most
  important obstruction to closure theories: composition closure is what breaks D-finiteness and
  defeats any argument based on a fixed differential equation.
* **(P2) `ℱ` is closed under `d/du`.** Differentiating F0–F3 keeps one inside `ℱ` (derivative of an
  integral is the speed; derivative of an implicit function comes from differentiating the
  analytic system; elementary derivatives stay). So the field generated by `ℱ` is a differential
  field over `ℂ` (or `ℂ(u)`).
* **(P3) `ℱ` is countable.** Finitely many rules and countably many trees (the only scalar seed is
  `1`; cf. X4 F10). Similarly `𝒢` is countable. So "`am_c ∈ ℱ`" is a countable disjunction over
  trees.
* **(P4) `ℱ` is not closed under inversion of an arbitrary element**, only under inversion of
  *arc lengths of constructible curves* (C4+F3). This asymmetry is the whole game.

### 1.4 Remark (why the two sorts matter — the circularity guard)

In `ℱ`, the relation `u = F_c(z)` is **available as an equation between two `ℱ` functions**
(`u ↦ u` and `z ↦ F_c(z)`), but it is **not** a crossing: `inter_x/inter_y` requires the relation
to come from two *constructible curve families* `S,T ∈ 𝒢`, and the graph of `F_c` is not a
constructible curve (`poly_graph` needs rational coefficients; `arc_length` produces numbers, not
curves). Consequently `am_c`, though it is the implicit function of that relation, is not put into
`ℱ` by F3. Equivalently: the statement "`am_c ∈ ℱ`" is exactly the negation of "the class `𝒢` of
constructible curves contains a curve of arc length `α F_c + β`", which is the single-curve route
R1/R2 investigate. **The class definition is therefore tight enough not to trivialise.**

---

## 2. Q2 — candidate theories

Throughout, "absorbs" means: the theory's closure theorems are stable under that operation, so the
fragment built from it is covered by the theory.

### 2.1 Theory table

| theory | core theorem used | what it proves about `am` | absorbs (from §1.2) | cannot absorb |
|---|---|---|---|---|
| **Differential algebra / Liouvillian** (Liouville; Rosenlicht 1968, 1969; Risch; Kolchin Picard–Vessiot) | Liouville's theorem on elementary integrals; the genus-0/log-derivative criterion for elementary integrability | `am_c` is **not elementary**: it inverts `∫dφ/Δ_c`, a nonzero holomorphic 1-form on the genus-1 curve `w²=(1−s²)(1−cs²)` | op1; op2 when the integrand's primitive is elementary or log-derivative; algebraic op3 | op2/op4 in general (`EAm` already non-Liouvillian); cannot distinguish first from second kind |
| **Strongly normal extensions** (Kolchin) | the differential Galois group of an autonomous algebraic ODE; strongly normal ⟺ group is an algebraic group; Liouvillian ⟺ identity component of the *linear* group is solvable | `am` and `ellipticEAm` are both strongly normal with **nonlinear elliptic-curve Galois group**, hence both non-Liouvillian | op1, algebraic op3 | **cannot separate `am` from `ellipticEAm`** — the required separation is not a Galois-theoretic dichotomy |
| **Ax–Schanuel / functional transcendence** (Ax 1971; Brownawell–Kubota; Bertrand–Pillay 2010; Pila–Tsimerman; Mok–Pila–Tsimerman; Blázquez-Sanz–Casale–Freitag–Nagloo) | differential-algebraic independence of `(z, ℘(z), ℘′(z), ζ(z))` over `ℂ`; "normalized" `ζ` independent of `℘` (Bertolin–Waldschmidt) | `u` and `am_c(u)` are **algebraically independent**; the corrected `(T3)′` holds for **algebraic** `M`; no *algebraic* relation encodes `F_c` | algebraic op1/op3; it is the only tool that speaks to first vs second kind (`℘` vs `ζ`) | **op2, op4, and transcendental op3**: Ax–Schanuel controls only *algebraic* relations among finitely many functions; it cannot bound an integral combination or an inverse |
| **D-finite / holonomic** (X1; Stanley; Sattelberger–Sturmfels) | D-finite ⟹ finitely many singularities; closure under `+,−,×,÷`, algebraic substitution, `∫` | `am_c` is **not D-finite** (infinitely many log-branch points, X1 §2.3) | op1 algebraic; op2 with algebraic data; algebraic op3; `offset`; algebraic parameters/endpoints | **transcendental op1** (`sin u`, `2^u`, `EAm`), op2 with transcendental endpoints, op4; the fragment that can produce a non-D-finite length is exactly the target's habitat (X1 §4) |
| **o-minimality / Pfaffian** (Khovanskii 1991; Wilkie 1996; Speissegger 1999) | `dn` is **Pfaffian** (the Weierstrass chain `℘′=q, q′=6℘²−g₂/2` is triangular and `sn,cn,dn` are rational in it), and `am = ∫ dn`; the Pfaffian closure of `ℝ_exp` is o-minimal and closed under integration/implicit functions | **nothing negative**: `am` is definable in the Pfaffian closure, so tameness cannot exclude it | everything in §1.2 — `ℱ` is contained in the Pfaffian closure (op1–op4 are its closure operations), hence o-minimal | cannot exclude `am`; only supplies analyticity and finiteness |
| **Hodge/period "kind" classification** (Griffiths; DLMF 19.30; R1/R2 catalogue) | any meromorphic 1-form decomposes into holomorphic + exact + second + third kind; the inverse of a first-kind integral is periodic (abelian/elliptic), of a second/third-kind integral is quasi-periodic/logarithmic | gives the **correct structural criterion**: `am` would need a drawable curve with `speed = α Δ_c`, i.e. **first-kind arc length**; no drawable curve has one (R1/R2) | explains op2/op4 for the *drawable* catalogue | **no closure theorem**: it classifies single curves, not finite compositions, parameter families, or inversions |

### 2.2 What the best candidate would prove

Rank by usefulness for the target:

1. **Ax–Schanuel + kind criterion** ("best"): it is the only proved theory that (a) makes the
   first-vs-second-kind distinction precise (`℘` vs `ζ`, `z` vs `ζ(z) − (η/ω)z`), and (b) yields
   a genuine non-existence statement — algebraic independence of `u` and `am_c`, hence no finite
   *algebraic* equation `Φ(u, am_c(u)) = 0` exists. The kind criterion (row 6) states exactly which
   geometric object is missing.
2. **Differential algebra (Liouvillian/strongly normal)**: proves non-elementarity of `am` and
   identifies the elliptic-curve Galois group, but is *strictly too coarse* at the only place that
   matters (it also excludes the constructible `EAm`).
3. **D-finite**: correct and rigorous in the algebraic fragment, but that fragment can never
   contain the target (X1).
4. **o-minimal/Pfaffian**: cannot give a negative result; useful only to certify analyticity and
   tameness.

### 2.3 The blunt answer: no theory absorbs `ℱ`

The class `ℱ` is closed under composition (P1), under a genuinely elliptic forward integral, and
under the inversion of that integral (`EAm`), while the target `am` is the *other* inversion of an
integral on the *same* elliptic curve. No standard theory has a closure theorem of the shape
"closed under these inversions but not that one". This is the precise technical reason the
programme is stuck, and it is worth stating at the top of any write-up.

### 2.4 Calibration checks [numeric, 40 digits]

Script `X5-01-theory-checks.py` (all residuals `≤ 6·10⁻⁴⁰`):

* `am` and `EAm` both solve an **autonomous first-order algebraic ODE**: `am′² = 1 − c sin²(am)`,
  `EAm′² = 1/(1 − c sin²(EAm))`. Both associated curves have genus 1 (Riemann–Hurwitz: four simple
  branch points). This is the calibration for the claim that differential algebra alone cannot
  separate them.
* `sn` is **doubly periodic** (`|sn(u+4K)−sn(u)| = 2.9·10⁻⁴¹`), whereas the angle `EAm` is only
  **quasi-periodic** (`EAm(v+2E₀) − EAm(v) − π = 0` to `≤ 5·10⁻⁴¹`). This is the "kind" signature:
  first-kind inversion is periodic, second-kind inversion drifts.
* Jacobi's epsilon `E_c(am_c(u))` is non-affine (second divided differences `−0.114` at `c=0.3`,
  `−0.243` at `c=0.7`), confirming the `EAm` route is circular (R3 §4.5).

---

## 3. The kind criterion, made precise

### 3.1 Every allowed inversion is the inverse of a Euclidean speed

An `arc_of_length` inversion produces `T = T(x)` with `T′(x) = 1/speed γ(T(x))`, where `speed γ` is
built from the curve data and is **elementary/Pfaffian** (no integral, no `am`). Conversely every
function obtained by inverting a drawable arc length is a solution of an autonomous ODE
`y′ = 1/σ(y)` with `σ ∈ 𝒢`-speed. For the ellipse `σ(T)=Δ_c(T)`, giving `EAm`; `am` would need
`σ(T) = α Δ_c(T)`, i.e. a drawable curve whose speed is a constant multiple of `Δ_c`.

### 3.2 The two inversions of the same curve

The forms `dφ/Δ_c(φ)` (first kind, holomorphic) and `Δ_c(φ)dφ` (second kind) live on the **same**
elliptic curve; their integrals are `F_c` and `E_c`. The classification of abelian differentials
(Hodge/kind) says:

* the inverse of a **holomorphic** (first-kind) integral is an **abelian/elliptic function**:
  `sn_c(u+4K)=sn_c(u)`, doubly periodic (§2.4);
* the inverse of a **second-kind** integral is **quasi-periodic**: `EAm` drifts by `π` each `2E₀`
  (§2.4); the inverse of a third-kind integral is logarithmic.

**Kind criterion.** `ℱ` can invert the arc lengths of drawable curves. R1a/R1b/R1c/R2 prove that
every drawable arc-length differential has a nonzero second- or third-kind component or a boundary
term, never a pure holomorphic first-kind class. Therefore no single `arc_of_length` inversion can
produce `am`. The missing object is a drawable curve with `speed = α Δ_c` (the Serret family of
R2), which is not a `Defs.lean` constructor.

### 3.3 `am` vs `EAm` is *not* literally a `℘`-vs-`ζ` independence statement

The brief asks whether "inverse of `E` allowed, inverse of `F` not" is a statement about the
independence of `ζ` from `℘`. **Answer: related, but not the same statement.**

* First-kind inversion is the inverse of the **uniformizer** `z` (so it produces `℘`, `sn`);
  second-kind inversion inverts a **normalized `ζ`**-type map.
* Ax–Schanuel/Brownawell–Kubota and the Bertolin–Waldschmidt conjecture (`trdeg_ℚ ℚ(g₂,g₃,π/ω,
  ℘(u), ζ(u)−(η/ω)u) ≥ 2`) say there is **no unexpected algebraic relation** between `z`, `℘(z)`,
  `℘′(z)`, and the normalized `ζ(z)`. This is what would make a corrected `(T3)′` provable for
  algebraic `M`.
* But the **allowability** of `EAm` is a purely **definitional/move-set** fact (Lean proved
  `ellipticEAm_Pconstructible_of_mem_Icc`); it is not a consequence of any independence theorem.
  Conversely, Ax–Schanuel does not forbid inverting `F`; it only forbids *algebraic* relations. So
  the E/F distinction is a **kind/period** statement (§3.2), supported by transcendence but not
  equivalent to it.

This distinction is worth recording because it is easy to conflate the two in a write-up.

---

## 4. The `(T3)` problem: false as stated, and what the corrected input is

### 4.1 R3's derivative test and its input

R3 §2.3 proves "Lemma 3 (derivative test)" modulo the input

> **(T3)** If `M ∈ 𝒜` and the composite `u ↦ M(am_c(u))` also lies in `𝒜`, then `M(am_c(·))` is
> constant,

where `𝒜` is the allowed class of R3 §1: "constants, the identity, and closure under `+−×÷, √,
sin, cos, tan, arcsin, arccos, arctan, 2^{·}, log, the forward incomplete integrals `F_c, E_c,
ellipticPiInc`, and the inverse `ellipticEAm_c`"; `𝒜` "does not contain `am_c` or any inverse of
`F_c`".

### 4.2 `(T3)` is false

Take `M = F_c`. Then:

* `F_c ∈ 𝒜` by R3's own definition;
* `M(am_c(u)) = F_c(am_c(u)) = u`, and the identity `u ↦ u` is **in** `𝒜`;
* `u` is not constant.

Hence `(T3)` is false. Numerically, `F_c(am_c(u)) = u` to `0.0` residual at `c ∈ {0.3, 0.7, 0.93}`
(script `X5-01`, part 1). This is not a numerical coincidence; it is the definition of `am`.

The same failure occurs for the `M` actually produced in the proof of Lemma 3. There
`M(φ) = speed γ(G^{-1}(φ))·Δ_c(φ)/G′(G^{-1}(φ))` and the proof asserts `M ∈ 𝒜` "because
`G^{-1} ∈ 𝒜`, `speed γ` is drawable data, and `Δ_c` is elementary." If `G = am_c` (so
`G^{-1} = F_c ∈ 𝒜`), then `M = speed γ ∘ F_c ∈ 𝒜` and `M(am_c(u)) = speed γ(u) ∈ 𝒜` is a
nonconstant drawable speed. So **the proof's own closure rule manufactures counterexamples to its
input.** (The instance is circular — it presupposes `G=am_c` — but that is exactly the point: the
hypotheses of Lemma 3 do not exclude the circular instance, so the lemma cannot be used as stated.)

### 4.3 What the corrected input must say

The failure is not "generic transcendence" but a **first-kind section**: `M` contains `F_c` (or
`E_c`, `Π_c`, `EAm_c`) in a way that makes `M∘am_c` land back in `𝒜`. The corrected statement must
forbid exactly that:

> **(T3)′** Let `M` be built from drawable speeds and from `G, G′, G^{-1}` for a reparametrisation
> `G` with `am_c = G∘T`, and suppose `M` does **not** contain a first-kind section, i.e. `M` is not
> of the form `N∘F_c` (equivalently, the construction has not already inverted `F_c`). If
> `M(am_c(·)) ∈ ℱ` then `M(am_c(·))` is constant.

**But `(T3)′` is not an independent "transcendence input": it is essentially the target in
disguise.** If a nonconstant `M∘am_c ∈ ℱ` exists with `M` first-kind-section-free, then the
derivative test's reduction breaks, and conversely, the single-curve route is exactly a
first-kind-section-free way to make `M∘am_c = id`. So the derivative test does not reduce the
problem to a standard transcendence statement; it reduces it to a statement equivalent to the
absence of a first-kind route. This is the single sharpest gap in the R round, and it is ranked
first in §5.

### 4.4 What Ax–Schanuel *can* prove for `(T3)′`

If `M` is **algebraic** over `ℂ(φ)`, then `N := M∘am_c ∈ ℱ` and `M = N∘F_c`; asking that `M` be
algebraic is asking for `N` to be algebraic over `ℂ(u)` when pulled back by `F_c`. Ax–Schanuel for
the elliptic curve states precisely that there is no nonconstant algebraic relation between
`z = F_c(φ)` and `φ = am_c(z)` beyond the curve itself. So **`(T3)′` holds for algebraic `M`**,
modulo the standard Ax–Schanuel statement for the Weierstrass pair `(℘,℘′)` (Ax 1971; the
semi-abelian generalization is Bertrand–Pillay 2010). For non-algebraic `M` (involving `E_c`,
`Π_c`, `EAm_c`, `sin`, `2^{·}`, or another `arc_length`), Ax–Schanuel is silent. Since the target
constructions all use such non-algebraic `M` (loophole L1), this does **not** close the test.

**Conclusion for Q2/Q3:** the best theory proves `(T3)′` only in the algebraic case and never
proves the full target; the exact place it breaks is the non-algebraic `M` of §5.2–§5.5.

---

## 5. Q3 — ranked list of holes the best theory cannot absorb

Ranked by (how likely a construction could hide there) × (how little the best theory says).

### Hole 1 — the corrected derivative-test input `(T3)′` (non-algebraic `M`)

**What the theory cannot absorb:** `M` built from `E_c`, `Π_c`, `EAm_c`, `sin`, `2^{·}`, or a
*second* `arc_length`/`arc_of_length`. Ax–Schanuel bounds only algebraic relations; the corrected
`(T3)′` is the target in disguise (§4.3).
**What a construction exploiting it would look like:** a drawable curve `γ`, a reparametrisation
`G` with `G^{-1} ∈ 𝒜`, and `M(φ) = speed γ(G^{-1}(φ))Δ_c(φ)/G′(G^{-1}(φ))` nonconstant with
`M∘am_c ∈ ℱ`. The natural attempt takes `G^{-1}` containing `E_c`/`EAm_c` and `speed γ` chosen so
the product cancels the second-kind part and leaves a first-kind section. No candidate exists, but
nothing in the move set forbids it.

### Hole 2 — parameter-dependent curves (R3 `L1`)

**What the theory cannot absorb:** differentiating a *family* of arcs in a parameter `p(u)` gives
the extra term `(∂/∂p s_p(T))·p′(u)` (R3 (MT-param)). No closure theory differentiates in the
parameter of a family and stays inside its fragment.
**What a construction exploiting it would look like:** take a drawable family whose complete
integrals `K(p), E(p)` are constructible numbers (they are, for constructible `p`); set `p=p(u)`
so that `∂s/∂p · p′` supplies the missing `F`-dependence and the right side of (MT-param) becomes
an `am_c`-free nonconstant function. This is the same hole X1 §4.1, X2 §6.3(1) and R3 §6 rank
first.

### Hole 3 — the uniform/non-uniform gap (§6)

**What the theory cannot absorb:** it is a theory about a *single* finite tree analytic on an
interval. It says nothing about using a **different tree for each `u`**, which is what the
predicate `∀u, PConstructible(am c u)` permits. The identity-theorem argument (§6) shows each tree
matches `am` only on a discrete set, so the constructible `u`'s can be at most countable — which
they already are — but it does **not** exclude any particular `u`.
**What a construction exploiting it would look like:** a countable family of ad hoc finite trees,
one per constructible `u`, each using `u`'s own derivation (this is exactly how the known
`S_c ⊇ {F_c(φ)}` is built). A proof of the target for all constructible `u` cannot come from a
single analytic object and must exploit the *syntax* of the derivation of `u`.

### Hole 4 — multi-stage / composite cancellation (R3 `L2`)

**What the theory cannot absorb:** compositions of inversions produce a composite derivative
`H = ∂₁L₂·T₁′ + ∂₂L₂` (R3 §2.4 F-ii); no theory controls a nonlinear `L₂` whose `u`-derivative
cancels against the term fed by an earlier stage.
**What a construction exploiting it would look like:** `am_c(w) = G(T₂(w))` with
`T₂ = s_{C₂}^{-1}(L₂(T₁,u))` and `T₁ = s_{C₁}^{-1}(L₁(u))`, choosing `L₂` nonlinear so that `H` is
nonconstant but `am_c`-free. No candidate; R3's collapse shows the test only bites when the stages
keep `F_c`/`am_c` out.

### Hole 5 — crossings with transcendental curves (`sine`, `exp_two`)

**What the theory cannot absorb:** Ax–Schanuel/`℘`-`ζ` tools are about algebraic curves; a crossing
of a `sine` or `exp_two` family with another family is a Pfaffian implicit equation, outside the
algebraic Ax–Schanuel theory. o-minimality applies but cannot exclude anything (§2.1).
**What a construction exploiting it would look like:** a moving crossing whose coordinate satisfies
the *required autonomous* Jacobi field `z′ = dn(z)`; X2 §3.3 tested the natural candidates
(Kepler, scaled sine, pendulum, moving circle, `EAm`) and all failed, but a general impossibility
is not proved. The relevant filter is X2's autonomy test.

### Hole 6 — composition closure itself

**What the theory cannot absorb:** `ℱ` is closed under composition (P1), so any candidate theory
must be stable under composing its fragment with `F_c`, `E_c`, `EAm_c`, `sin`, `2^{·}`. D-finite
theory fails this immediately; Ax–Schanuel has no composition theorem for transcendental inner
functions; differential algebra's Liouvillian predicate is too coarse. There is no known
"composition-stable but `am`-free" class containing the allowed moves.

### Hole 7 — CM / singular moduli (R2, R3 `L11`)

**What the theory cannot absorb:** at `c = 1/2` (lemniscatic), `c = 1/√2` (`K′=K`), and other
singular moduli there are extra `E`↔`F` relations (Landen, Legendre, Schwarz). The generic
arguments do not separate these.
**What a construction exploiting it would look like:** use a first-kind curve whose modulus is a
singular modulus (the lemniscate has `c=1/2`), or an `E`↔`F` identity valid only there, to invert
`F`. Even a success would cover only countably many `c` (R2 §A.3), but it would be a genuine
partial positive. R2's Serret catalogue is the natural place to check.

### Hole 8 — model weakness of `Defs.lean` (X4)

**What the theory cannot absorb:** `Defs.lean` has no union/concatenation of strokes, no wrapping a
string past `2π` (the `hinj` bound), no chaining `arc_of_length` from its own far endpoint, and
`offset` demands `C¹`. A negative result inside `Defs.lean` therefore does **not** immediately
exclude the drawing program (X4 "weaker than the program"). These holes weaken impossibility
proofs rather than enable constructions, so they rank last for *finding* a route but first for
*trusting* a negative.

### Not holes (for the record)

* **Single-curve route (`L0`/`L8`)** is the positive target, not a hole.
* **Mixed `E`/`F` at different or the same angle (`L3`/`L4`)** and **third kind (`L5`)** are closed
  to the precision tested (R3 §4.2–4.4; X1 §5).
* **Definitional circularity (`L10`)** is excluded by the two-sorted definition (§1.4), but must be
  audited if new primitives (polar plotting, a "Jacobi curve") are added.
* **o-minimality (`§2.1`)** can never be part of a negative result, since `am = ∫ dn` is definable
  in the Pfaffian closure.

---

## 6. Q4 — non-uniform constructions

### 6.1 What "recipe changes with `u`" can and cannot mean

* **Within one tree:** a tree is a fixed finite object. Its parameters may be `ℱ` functions of `u`,
  and `restrict`/case-splits can cut `U` into finitely many pieces, but on each piece the output is
  a **single real-analytic function** of `u`. So a single tree is always "uniform on each analytic
  piece"; it cannot change its formula non-analytically inside a piece.
* **Across trees:** the predicate `PConstructible(am c u)` allows a *different* finite derivation
  for each `u`. Nothing in the class definition forbids this. Since there are countably many trees
  and all real numbers are not countably needed (the constructible `u`'s are themselves countable),
  countability is not by itself an obstruction.

### 6.2 The identity-theorem upgrade (a precise, limited result)

**Proposition (uniform failure ⟹ discrete). [symbolic]** Fix `c`. Suppose **no** uniform tree
computes `am_c` on any interval (i.e. `am_c ∉ ℱ(U)` for every nonempty `U`). Then for every finite
tree `τ` whose output `h_τ` is real-analytic on its (open) validity set `V_τ ⊆ ℝ`, the set
`{u ∈ V_τ : h_τ(u) = am_c(u)}` is **discrete** (has no accumulation point in `V_τ`).

*Proof.* `am_c` is real-analytic with `am_c′ = dn_c > 0`, so it is real-analytic on `ℝ`. On each
connected component of `V_τ`, `h_τ` is real-analytic (F1–F3 are analytic; `restrict` cuts into
finitely many components). If `h_τ − am_c` had an accumulation point of zeros in a component, the
identity theorem would force `h_τ ≡ am_c` there, i.e. a uniform construction on an interval,
contradicting the hypothesis. Hence the zero set is discrete. ∎

**Corollary.** If uniform non-constructibility holds, then for every bounded interval the set
`{u : PConstructible(am c u)}` is a **countable union of discrete sets**, hence countable (and so
of measure zero and meager). This is consistent with — and cannot improve on — the known
`S_c` of R3 §5, which is already a countable dense subgroup containing `{F_c(φ)}` and the dyadic
multiples `rK`.

### 6.3 What this does and does not say

* It **rules out** any positive answer that would need `am_c` constructible on a set with an
  accumulation point, in particular on an interval or a positive-measure set. So no non-uniform
  recipe can "patch" analytic pieces into `am` on an interval.
* It **does not rule out** `am_c(u₀)` constructible at a single generic `u₀`, nor at countably
  many special `u₀`. The programme's target is `∀` constructible `u`, but the uniform theory only
  ever sees one tree at a time; the remaining question is exactly the **pointwise/transcendence**
  question the brief already declared hopeless with current mathematics.
* Consequence for the R/X programme: a "useful negative" from this theory must be phrased as "no
  **uniform** construction", and the honest statement of the remaining gap is "for each generic
  constructible `u`, whether some ad hoc finite tree computes `am_c(u)` is a transcendence
  question". This is the sharpest formulation available.

### 6.4 Example of the gap

The known positive facts (R3 §5) are all of the "presented" form `u = F_c(φ)` with `φ`
constructible, or finite combinations and halvings. Each such `u` has its own short tree. A proof
of the full target would have to show that the *entire* countable set of constructible `u`'s lies
in `S_c`; the present theory shows only that `S_c` cannot contain an interval. The two are far
apart, and that distance **is** the obstruction Q4 identifies.

---

## 7. What a future proof would have to do

A complete proof cannot be a pure transcendence theorem about the number `am_c(u₀)` (hopeless) and
cannot be a pure closure theorem (none exists, §2.3). The surviving program is:

1. **Prove the corrected `(T3)′` for the geometric class** — i.e. show that a nonconstant
   `M∘am_c ∈ ℱ` with `M` first-kind-section-free is impossible. By §4.3 this is essentially the
   single-curve statement, so it must be attacked through the **kind criterion** (§3.2), not
   through transcendence alone.
2. **Close the parameter-dependent hole** by a theorem that controls `∂/∂p` of a family of abelian
   integrals (a Picard–Fuchs/Gauss–Manin statement) and shows the second-kind part cannot cancel to
   a first-kind section under the allowed `p(u)`.
3. **Reduce the target to the uniform statement** via the *syntax* of the derivation of `u` (Hole
   3) — e.g. an induction showing each rule that builds `u` preserves membership in `S_c`, which is
   exactly the programme's `L`-tasks. This is the only route that can bridge the countable/pointwise
   gap.

Items 1–2 are open research problems; item 3 is partially done (`Pptc/JacobiAddition.lean`).

---

## 8. Sources

**Elliptic functions and integrals.**

* DLMF §22.16 — amplitude, `am = arcsin sn`, periodicity, Jacobi epsilon.
  <https://dlmf.nist.gov/22.16>
* DLMF §22.4 — poles of `dn`, period lattice. <https://dlmf.nist.gov/22.4>
* DLMF §19.30 — lengths of plane curves (kind classification of elliptic arclengths).
  <https://dlmf.nist.gov/19.30>
* DLMF §23.2 — Weierstrass `℘`, `ζ`; `ζ` is quasi-periodic, not elliptic.
  <https://dlmf.nist.gov/23.2> ; Wolfram `WeierstrassZeta` ("not periodic and therefore not
  strictly an elliptic function"), <https://reference.wolfram.com/legacy/language/v13.2/ref/WeierstrassZeta.html>

**Differential algebra / differential Galois theory.**

* M. Rosenlicht, *Liouville's theorem on functions with elementary integrals*, Pacific J. Math. 24
  (1968) 153–161.
* M. Rosenlicht, *On the explicit solvability of certain transcendental equations*, Publ. Math.
  IHÉS 36 (1969) 15–22. <https://eudml.org/doc/103891>
* M. Bronstein, R. Corless, J. Davenport, D. Jeffrey, *Algebraic properties of the Lambert W
  function from a result of Rosenlicht and Liouville*, Integral Transforms Spec. Funct. 19 (2008)
  709–712. <https://doi.org/10.1080/10652460802332342> (a worked non-elementarity proof of an
  implicitly defined function, the closest classical analogue).
* Overview of Liouville's theorem and Liouvillian extensions:
  <https://en.wikipedia.org/wiki/Liouville%27s_theorem_(differential_algebra)>
* Kolchin's strongly normal extensions / the Picard–Vessiot Galois correspondence (including the
  characterization of PV extensions as strongly normal with linear algebraic group):
  T. Crespo, Z. Hajto, *Algebraic Groups and Differential Galois Theory*, AMS GSM 122, Ch. "The
  Galois correspondence". <https://www.ams.org/bookstore/pspdf/gsm-122-prev.pdf>
* Liouville's theorem and the genus criterion used for non-elementarity:
  R. C. Churchill, *Liouville's Theorem on Integration in Terms of Elementary Functions* (2006).
  <https://ksda.ccny.cuny.edu/PostedPapers/liouv06.pdf>

**Functional transcendence (Ax–Schanuel).**

* J. Ax, *On Schanuel's conjectures*, Ann. of Math. 93 (1971) 252–268.
* J. Pila, *Functional transcendence via o-minimality*, LMS lecture notes — differential-field
  Ax–Schanuel statement and the semi-abelian references. <https://people.maths.ox.ac.uk/pila/LMSNotes.pdf>
* D. Bertrand, A. Pillay, *A Lindemann–Weierstrass theorem for semi-abelian varieties over function
  fields*, J. Amer. Math. Soc. 23 (2010) 491–533.
* J. Pila, J. Tsimerman, *Ax–Schanuel for the j-function*, Duke Math. J. (2016); Mok–Pila–Tsimerman,
  *Ax–Schanuel for Shimura varieties*, Ann. of Math. (2019).
  <http://www.math.hku.hk/imrwww/IMRPreprintSeries/2018/IMR2018-15.pdf>
* D. Blázquez-Sanz, G. Casale, J. Freitag, J. Nagloo, *A differential approach to Ax–Schanuel, I*,
  arXiv:2102.03384 (Ax–Schanuel with derivatives for uniformizers).
* M. Waldschmidt, *Conjectures and open problems* (elliptico-toric Schanuel; Bertolin's conjecture
  `trdeg_ℚ ℚ(g₂,g₃,π/ω, ℘(u), ζ(u)−(η/ω)u) ≥ 2`). <https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/AWSLecture5.pdf>
* C. Bertolin, M. Waldschmidt, *Variations on Schanuel's Conjecture for elliptic and quasi-elliptic
  functions*. <https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/Semi-Elliptic-Schanuel.pdf>

**D-finite / holonomic.**

* X1 notes and references therein; A.-L. Sattelberger, B. Sturmfels, *D-Modules and Holonomic
  Functions*, arXiv:1910.01395; <https://en.wikipedia.org/wiki/Holonomic_function>.

**o-minimality / Pfaffian.**

* A. Khovanskii, *Fewnomials*, AMS Transl. Math. Monogr. 88 (1991).
* A. J. Wilkie, *Model completeness results for expansions of the ordered field of real numbers by
  restricted Pfaffian functions and the exponential function*, J. Amer. Math. Soc. 9 (1996)
  1051–1094.
* P. Speissegger, *The Pfaffian closure of an o-minimal structure*, J. Reine Angew. Math. 508
  (1999) 189–211.
* L. van den Dries, A. Macintyre, D. Marker, *The elementary theory of restricted analytic fields
  with exponentiation*, Ann. of Math. 140 (1994) 183–205.
* Pfaffian functions are closed under composition, differentiation, integration and implicit
  functions (Wilkie lecture notes, Berlin 2007), so `am = ∫ dn` is definable in the Pfaffian
  closure and o-minimal tools cannot exclude it.
  <https://modnet.imj-prg.fr/resources/lecture%20notes/Wilkie%20-%20An%20introduction%20to%20o-minimality%20%28Berlin%2C%202007%29.pdf>

**Internal programme.**

* `PLAN-jacobi-X0-overview.md`, `PLAN-jacobi-X5-obstruction-theory.md`.
* `NOTES-jacobi-R1a/R1b/R1c.md` (drawable-speed catalogue), `NOTES-jacobi-R2.md` (Serret first-kind
  family, moduli), `NOTES-jacobi-R3.md` §2 (derivative test, `(T3)`), §4 (mixed `E`/`F`,
  third kind, epsilon).
* `NOTES-jacobi-X1.md` (D-finite), `NOTES-jacobi-X2.md` (crossings, autonomy filter),
  `NOTES-jacobi-X3.md` (classical mechanisms), `NOTES-jacobi-X4.md` (constructor audit).
* `pptc/Pptc/Defs.lean`, `pptc/Pptc/Jacobi.lean`, `pptc/Pptc/ThirdKind.lean`.

---

## 9. Verification index

| item | claim | tag | where |
|---|---|---|---|
| `(T3)` counterexample | `F_c(am_c(u)) = u`, identity in `𝒜` | [symbolic] + [numeric, 40] | §4.2, `X5-01` part 1 |
| non-separation | `am`, `EAm` both solve autonomous genus-1 ODEs | [symbolic] + [numeric, 40] | §2.4, `X5-01` part 2 |
| kind signature | `sn` `4K`-periodic; `EAm` drifts by `π` per `2E₀` | [numeric, 40] | §2.4, §3.2, `X5-01` part 3 |
| circularity | epsilon `E_c(am_c)` non-affine | [numeric] | §2.4, `X5-01` part 4 |
| genus criterion | both associated curves genus 1 (Riemann–Hurwitz) | [symbolic] | §2.4, §3.2 |
| class definition | two-sorted `𝒢`/`ℱ`; composition-closed; analytic | [symbolic] | §1 |
| identity upgrade | no uniform tree ⟹ zero set discrete ⟹ countable `S_c` | [symbolic] | §6.2 |

`X5-01-theory-checks.py` runs in under 5 s at `mp.dps = 40`; all residuals reported are `≤ 6·10⁻⁴⁰`
except the (intentionally nonzero) divided differences. No claim in this note rests on a single
script.
