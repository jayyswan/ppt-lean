# NOTES-jacobi-X2: the amplitude as a crossing

Task `PLAN-jacobi-X2-crossings.md`. Research only: **no `.lean` file was created, edited or
deleted.** Numerics use Python 3.12 + `mpmath`/`sympy`/`numpy`
(`C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`); scripts are archived in
`archived files/jacobi-scripts/` with the `X2-` prefix. `mpmath`'s `ellipfun(kind,u,m)` and
`ellipf(phi,m)` take the **parameter** `m = c = k²`; that convention is used throughout.

Every identity is tagged **[symbolic]** (exact, by `sympy`) or **[numeric, N digits]**.
Web sources are given with URLs in §9.

---

## Plain-language summary (≤10 lines)

1. A crossing is `inter_x`/`inter_y`, the coordinate of the **unique** intersection of two
   constructible curves, so it can only solve an equation that a constructible curve already
   encodes.
2. `(sn,cn,dn)` is a Pfaffian chain (`sn'=cn·dn`, …), so "Pfaffian vs. not" does **not** by
   itself separate `am` from what crossings produce. The useful filter is different.
3. The right filter is **autonomy**: a crossing whose parameters depend on `u` produces a
   coordinate `z(u)` satisfying an ODE `z'=R(z,u)`; for `z=am(u)` the ODE must be the
   *autonomous* Jacobi field `am'=dn=√(1−c sin²am)`.
4. The pendulum phase portrait is drawable, but its **time** is the action integral
   `∫dθ/√(2k(cosθ−cosθ₀))`, an `F`-integral, not the Euclidean arc length the constructors can
   measure; the portrait as a time-independent set does not remember the time. (Checked.)
5. The exact equation for `am` is `u = F(am,c)`, and `F` is not a finite trig/polynomial
   expression (checked), so all "Kepler-like" finite equations are only approximations.
6. The one crossing construction that genuinely works in this language is the abutting-arcs
   crossing, and it inverts `E` (giving `ellipticEAm`), not `F`. It is the calibration by which
   the failure for `F` is measured.
7. **Conclusion.** Crossings solve exactly the equations whose defining curves are drawable;
   inverting `F` needs a curve that *encodes* `F`, and every route to that is blocked in
   `Defs.lean` (R1a/R1b/R1c/R2). Useful negative, with the loophole named in §6.3.
8. The only assumptions that would let a construction through are (i) a drawable curve of
   arc length `F` (Serret, R2's proposed extension) or (ii) a constructible curve whose
   defining equation encodes `F` (the "implicitly elementary `F`" loophole, §6.3).

---

## 1. The move language, and what a crossing actually is

Recall the constructors of `pptc/Pptc/Defs.lean` (read in full for this task). A
`PConstructible` *number* comes from `1`, `+ − × ÷`, `inter_x`/`inter_y`, and
`arc_length`. A `PConstructibleCurve` *set* comes from the bases `ellipse`, `rectangle`,
`poly_graph` (degree ≤ 6, rational coefficients), `power_law` (`a,b ∈ ℚ`), `exp_two`
(`y=2^x`), `sine` (`y=sin x`), `cubic_bezier` (constructible control points), closed under
`translate_x/y`, `scale_x/y` (independent factors), `rotate` (integer degrees),
`restrict` (axis-aligned window), `arc_of_length`, and `offset`.

A crossing supplies `PConstructible x` (resp. `y`) *only* given a proof
`h : S ∩ T = {(x,y)}` (`Defs.lean:126,131`). So the constructor is: two curves, a
**singleton** intersection, read a coordinate. The singleton hypothesis is the side condition
every candidate must discharge (typically by `restrict`-ing one curve, or by using arcs that
meet only at a shared endpoint).

`arc_of_length` (`Defs.lean:324`) is the only constructor that turns a length into a curve.
Its far endpoint is deliberately *not* required to be constructible; the arc is `γ '' Icc a b`
with `arcLengthOf γ a b = x`, so the endpoint is `γ(s^{-1}(x))` where `s` is the traced arc
length. This is how inverse arc-length information enters a curve, and hence a crossing.

The two prior X-round results this note leans on:

* **R1a/R1b/R1c/R2** classify the arc lengths of the drawable class. The only non-elementary
  one available at *general* parameter `c` is the ellipse's, `E`; `sine` gives
  `√2·E(·,1/2)` (fixed modulus `1/2`), `exp_two` is genus 0 (elementary), and the algebraic
  curves (`poly_graph`, `power_law`, `cubic_bezier`) and all offsets give `E`/third-kind
  combinations **plus an unavoidable boundary term**, never a pure first-kind `F`. No drawable
  curve has arc length `F`. (See `NOTES-jacobi-R1a/R1b/R1c/R2.md`.)
* **R3** shows that `am` is not reachable from the "allowed class" `𝒜` of functions
  (elementary + forward `F, E, Π` + the one available inverse `ellipticEAm`), with the
  parameter-dependent-curve loophole L1 left open (`NOTES-jacobi-R3.md` §6).

---

## 2. Question 1 — the class of equations a crossing can solve

### 2.1 Curve-equation shapes

Write a planar curve as the zero set of a real-analytic function. The bases give:

| base | defining equation | nature |
|---|---|---|
| `ellipse` | `((x−cx)/a)² + ((y−cy)/b)² = 1` | polynomial (degree 2) |
| `rectangle` | linear pieces `x∈[..] ∧ y = c` etc. | linear/inequalities |
| `poly_graph p` | `y = p(x)`, `p ∈ ℚ[x]`, deg ≤ 6 | polynomial |
| `power_law a b` | `y = a xᵇ`, `a,b∈ℚ`, `x>0` | algebraic/rational power |
| `exp_two` | `y = 2ˣ` | exponential |
| `sine` | `y = sin x` | trigonometric |
| `cubic_bezier` | image of a degree-3 polynomial map | algebraic (degree ≤ 3) |

The closure operations act on the *defining equations* as follows.

* `translate_x/y`, `scale_x/y`, `rotate(n)`: substitute an affine change of the variables,
  `(x,y) ↦ (a x + b y + e, c x + d y + f)` with constructible coefficients. The equation shape
  is preserved; coefficients become constructible numbers, possibly depending on `u`.
* `restrict(xmin,xmax,ymin,ymax)`: intersect with a box (linear inequalities). No new
  functional forms.
* `offset`: if the arc is traced by `γ` with velocity `v`, the offset point is
  `γ(t) + d·(−v_y, v_x)/|v|`. Substituting this into the base equation gives an equation that
  is **algebraic over the base data** in `x,y,d` and the velocity; it involves
  `1/√(x'²+y'²)` (and after iterating, `1/(x'²+y'²)^{3/2}`). No new transcendence: offsets
  add rational functions of the base equation and its derivatives (R1a's (F3)).
* `arc_of_length`: replaces a curve by a sub-arc; the sub-arc's endpoints are
  `γ(s^{-1}(L))`. So a curve obtained this way, if read through a crossing endpoint, supplies
  `s^{-1}(L)` — the **inverse arc length** of a drawable curve — at a constructible `L`.

### 2.2 The equational form of a crossing

A crossing of `S`, `T` is the system

    F(x,y) = 0,   G(x,y) = 0,

whose coefficients are constructible numbers (possibly functions of `u`). Eliminating one
variable locally (implicit function theorem) gives a single relation `Φ(z,u) = 0` for the
coordinate `z` we read off. Hence:

> **The crossing solvable class.** A crossing can produce the unique number `z(u)` defined
> by a finite system whose entries lie in the class generated by `{polynomials, sin, 2^{·},
> rational powers}` under `+ − × ÷`, `√`, affine changes of variables with constructible
> coefficients, offsets, and `arc_of_length` endpoints. Without `arc_of_length` this is the
> exponential–trigonometric–algebraic class, whose implicit functions include genuinely
> non-elementary ones (the Kepler solution below is the model). With `arc_of_length` the only
> *new* functions available are inverses of drawable arc lengths; at general parameter `c` the
> only non-elementary one is `E^{-1} = ellipticEAm`.

### 2.3 The calibration sentence

If a crossing produces `am(u)`, then reading off the coordinate and differentiating along the
solution forces the level set to be an integral curve of `φ' = dn(φ) = √(1−c sin²φ)`, whose
solutions are `u = F(φ) + C`. So the crossing's defining relation must be equivalent to
`u = F(φ)`; see §6.1 for the precise statement. This is why "does a drawable curve encode
`F`?" is the whole question.

---

## 3. Question 2 — Pfaffian chain, pendulum, and the autonomy filter

**Script:** `X2-01-basics.py`, `X2-02-crossings.py`.

### 3.1 The Pfaffian chain is real — and is not a separator

`(sn,cn,dn)` satisfies the autonomous polynomial system

    (sn,cn,dn)' = ( cn·dn,  −sn·dn,  −c·sn·cn ).                              (P)

Finite differences at 40 dps give worst residuals `3.9·10⁻²², 4.0·10⁻²², 4.9·10⁻²²` at
`c = 0.3, 0.7, 0.93`. **[numeric, 21 digits]** `am` is not in this chain, but
`am = atan2(sn,cn)` (checked to `9.2·10⁻⁴¹`) **[numeric, 40 digits]**, so the amplitude *is* a
function of the position `(sn,cn)`. The brief is right that Pfaffian-ness does not separate
`am` from `sin`/`exp`: all obey (P)-type systems, and Khovanskii's fewnomial theory treats
them uniformly ([Khovanskii 1991]; see §9).

The chain has a geometric reading relevant here: `(sn,cn,dn)` lies on

    sn² + cn² = 1,        c·sn² + dn² = 1,

the intersection of two quadrics, an algebraic (elliptic) curve. Its projection to the
`(sn,cn)`-plane is the **unit circle**. So the *trajectory is an algebraic curve* — exactly the
kind of object a crossing can see. What the crossing cannot see is the **time**: the map
`u ↦ (sn u, cn u)` winds the circle infinitely often, and the algebraic locus carries no
labelling by `u`. (The Lean invariants are `jacobiSn_sq_add_jacobiCn_sq` and `jacobiDn_sq`,
`Pptc/Jacobi.lean:216,221`.)

### 3.2 The pendulum phase portrait: drawable shape, hidden time

The pendulum `θ″ = −k sin θ` has energy `θ′² = 2k(cos θ − cos θ₀)`, so the phase portrait
`p² = 2k(cos θ − cos θ₀)` is a transformed cosine graph — a drawable-looking closed curve.
Its **time** of flight from `θ` to `θ₀` reduces to a first-kind integral,

    t = ∫_θ^{θ₀} dφ/√(2k(cosφ − cosθ₀))
      = k^{−1/2} ( K(s²) − F(ψ, s²) ),   s = sin(θ₀/2),  sinψ = sin(θ/2)/s.     (T)

At 40 dps, quadrature of the left side equals the right side to **18 digits**. **[numeric, 18
digits]** But the drawing language can only measure the **Euclidean arc length** of the
portrait, `σ = ∫√(1 + (dp/dθ)²) dθ`, a different integral: at `k=1, θ₀=1.2` the ratios
`t/σ = 0.9582, 0.9833, 1.0321` for `θ = 0.2, 0.6, 1.0`, and at `k=2` they are `≈0.53`.
**[numeric, 18 digits]** So (a) the portrait's geometric length is not the time, and (b) even
if it were, a crossing returns a *position*, not a *time*.

**This closes the literal pendulum route for crossings:** to read `am(u)` off the portrait we
would have to select the point at time `u`, i.e. invert (T). Inverting (T) is precisely solving
an `F`-integral, so the pendulum gives the same circularity as the original problem. (This is
the same `F`-integral that R2's non-drawable Serret curve would invert; R2 is the precise
statement that no *drawable* curve plays that role.) DLMF §22.19 is the standard reference for
the pendulum/`am` correspondence [DLMF 22.19].

### 3.3 The autonomy filter (the operational test)

Suppose a family of curve pairs is parametrised by constructible functions `p(u)` and has
unique intersection `(X(u),Y(u))`; read a coordinate `z(u)`. Differentiating the defining
system in `u` expresses `z'` as a constructible function of the configuration:

    z' = R(z; p(u), p'(u)).                                                  (AF)

For `z = am(u,c)` the required function is **autonomous**:

    z' = dn(z) = √(1 − c sin²z),     z(0)=0.                                 (J)

So a necessary condition for a candidate crossing is that it reproduces (J). We tested it at
`c = 0.3, 0.7, 0.93`, on several `u`; `X2-02` prints `max |z'² − (1−c sin²z)|`:

| candidate crossing (parameter depending on `u`) | worst residual | verdict |
|---|---|---|
| Kepler: `sin(z−u) = a z` crossed with `y=a x`, `a∈{0.2,0.5}` | `0.83 … 3.74` | fail |
| scaled sine: `sin(z/u) = a z` | `1.00` | fail |
| pendulum portrait crossed with `p=p₀+u` | `9.45 … 9.56` | fail |
| ellipse arc endpoint angle `= EAm(u)` | `0.36 … 1.97` | fail |
| moving circle `(x−u)²+sin²x=1` crossed with `y=sin x` | `0.15 … 0.50` | fail |

**[numeric]** None reproduces the Jacobi field. The pendulum/Kepler families are the
"most competent" elementary crossings available and they miss (J) badly; the EAm candidate
reproduces `z'=1/dn`, the reciprocal of the required field — which is exactly why it inverts
`E`, not `F`.

### 3.4 Why the test is not circular

The filter does not assume `am` is hard: it is a numerically testable identity. It also has a
**positive calibration** (a genuine crossing that passes a related test): see §7.

---

## 4. Question 3 — Kepler-like reformulations and the addition theorem

**Script:** `X2-01-basics.py`, `X2-03-selfref.py`.

### 4.1 The exact equation, and why every finite version fails

The exact equation is `u = F(φ,c)`. The underlying reason a crossing cannot capture it is that
`F` is not a finite expression in the curve-equation class. Quantitatively:

* expanding the integrand, `F(φ) = φ + (c/4+…)φ − (c/8+…)sin 2φ − …`; fitting
  `u = aφ + b sin2φ` to the exact `F` leaves residuals `1.4·10⁻⁴, 1.7·10⁻³, 2.2·10⁻²` at
  `c = 0.1, 0.3, 0.7`; adding `sin4φ, sin6φ` gives `4.1·10⁻⁸, 5.7·10⁻⁶, 8.0·10⁻⁴`, still
  nonzero. Least-squares fitting `F` by `Σ_{k=0}^{N} a_k cos 2kφ` leaves `5.8·10⁻³` at
  `N=12, c=0.7`, with all coefficients nonzero. **[numeric]** So the "most elementary-looking"
  equation is only the one-sine Kepler approximation.
* The exact statement is `F(am(u),c) = u` to `2.3·10⁻⁴¹` modulo `4K`. **[numeric, 40 digits]**

Hence the honest answer to Question 3 is: the exact equation for `am` is a *differential*
relation `(φ')² = 1 − c sin²φ` (equivalently the integral `u=F(φ)`), and crossings solve
*finite* equations; the finite equations that do exist (addition theorem, duplication) are
relations among `am` at several arguments, not a single relation determining `am(u)` from `u`.

### 4.2 Addition-theorem fixed points give only torsion

The addition theorem makes `(sn,cn,dn)(u+v)` an algebraic function of the two points
(R3, `jacobiCn_add`). A crossing can implement that algebraic map. Its fixed points,
e.g. `sn(2u)=sn(u)`, are the 2-torsion solutions (`u ∈ {0,2K,…}` plus finitely many others per
period) — isolated values, not a construction of `am(u)` for variable `u`. The known
constructible set `S_c` is a countable dense subgroup containing the dyadic multiples `rK`
(R3 §5); nothing about addition supplies the missing inverse of `F`.

### 4.3 The clean circularity demonstration for moving curves

Take the moving line `y = a x + p(u)` crossed with the unit circle `x²+y²=1`. The intersection
angle `θ` satisfies `sinθ = a cosθ + p`, i.e.

    p = sinθ − a cosθ.

Therefore **the parameter that forces `θ=am(u)` is `p(u) = sn(u) − a·cn(u)`** — an expression
that already contains the amplitude. Numerically, with this `p(u)`, the crossing reproduces
`am(u)` to `1.1·10⁻⁴¹, 5.7·10⁻⁴², 1.1·10⁻⁴¹` at `c = 0.3, 0.7, 0.93` **[numeric, 40
digits]**; with the plain constructible `p(u)=u` the Jacobi test fails by `1.19`
(`X2-03`, part 4). This is the general shape of the parameter-dependent loophole: a crossing
can be *tuned* to `am`, but the tuning data is `am` itself.

---

## 5. Question 4 — self-referential crossings

**Script:** `X2-03-selfref.py`.

### 5.1 Unknown / equation count

Let `A₁(u), A₂(u)` be arcs of constructible curves `C₁, C₂`, laid to constructible lengths
`L₁(u), L₂(u)`, and let `P(u)` be the crossing point.

* **Unknowns:** `(x,y)` : 2. **Equations:** `P∈C₁`, `P∈C₂` : 2. Generically the solution set is
  0-dimensional (isolated points), as required by `inter_x`/`inter_y`.
* The lengths enter in only two ways: (i) they decide which sub-arc is present, and (ii) they
  fix the sub-arc **endpoints**. Consequently either

  (i′) `P` is the **fixed geometric intersection** of `C₁` and `C₂` (algebraic, independent of
  `L₁,L₂`), or
  (ii′) `P` is a **shared endpoint**, in which case the "self-reference" is the single scalar
  relation `s₁^{-1}(L₁(u)) = s₂^{-1}(L₂(u))` between the two drawable arc lengths.

  Either way, no free parameter remains to bend a coordinate into a moving `am(u)`. To obtain
  `u`-dependence one must move a curve with a parameter `p(u)` — and that is §3.3 / §4.3.

### 5.2 Case (i′): length-invariant, so useless for a moving target

For two *fixed* drawable curves the crossing set is fixed. Example (in `X2-03` part 3): the unit
circle and the line `y=x` meet at `(±1/√2, ±1/√2)`, fixed; the arc lengths to that point are
`π/4` and `√2−1` respectively, independent of `u`. A varying pair `(L₁(u),L₂(u))` can only make
the endpoints coincide at the single `u` where they hit the fixed values; the crossing
coordinate never moves. **[numeric, printed exactly]**

### 5.3 Case (ii′): the shared endpoint reduces to a drawable arc-length relation

In the shared-endpoint configuration, the output is `γ₁(s₁^{-1}(L₁(u)))`. If `L₁(u)` is
constructible then `s₁^{-1}(L₁(u))` is constructible whenever `s₁` is a drawable arc length
appearing in the language:

* `s₁ = E` (ellipse): this is `ellipticEAm(L₁(u))` — constructible (Lean: line 602).
* `s₁` elementary (circle, line, `2^x`): constructible.
* `s₁ = E + boundary` (algebraic curves/offsets): the inverse is a new function, but it inverts
  `E + boundary`, not `F`.

For the output to equal `am`, we would need `s₁ = F` (so that `L₁(u)=F(am u)=u` is the
constructible input and `s₁^{-1}(L₁)=am`). No drawable `s₁` is `F` (R1a/R1b/R1c/R2). This is
the precise reduction of Question 4 to the single-curve obstruction.

### 5.4 What a self-referential "positive" would have to do

A positive construction would need a constructible curve `C*` with `arcLengthOf γ* = αF(φ,c)+β`
(so that `arc_of_length`/abutting arcs invert `F`). Its construction tree would be

    (number c) → n := c/(1−c) → serret-family curve γ_n        [NOT a Defs.lean constructor]
    (number u) → L := √n·u → arc_of_length γ_n from γ_n(0) length L
    (arc)      → arc_of_length γ_n from γ_n(π) length √n·2K−L
    → inter_x/inter_y of the two arcs (unique) → point γ_n(α), α=am(u,c)
    → recover α from (x,y) by an algebraic relation (A.2 of R2).

R2's Serret curve `γ_n` is the required `C*`; it is *not* drawable (degree ≥ 4, or analytic
for irrational `n`). If a new constructor for it were added, this crossing would prove
`PConstructible (am c u)`. Absent that constructor, every crossing reduces to the cases above.
This is also the exact analogue of `ellipticEAm_Pconstructible_of_mem_Icc`.

---

## 6. Synthesis: what is excluded, and what would let a construction through

### 6.1 The main statement (per-coordinate, single effective equation)

Let `Φ(z,u)` be the relation obtained by eliminating the other coordinate from a crossing
system, with `Φ` built in the curve-equation class of §2.1. Suppose `Φ(am(u),u)=0` with
`Φ_z ≠ 0`. Differentiating, `Φ_z·dn + Φ_u = 0`, whose characteristics are `u = F(z)+C`; since
the coefficient `dn` depends on `z` alone, the general `C¹` solution is `Φ = Ψ(u − F(z))`. So
`Φ` **contains `F`**. Therefore a successful single-equation crossing must encode `F`.

**[symbolic/analytic; the numeric content is the calibration and the failure table above]**

### 6.2 The class excluded

> **Excluded class.** Crossings (and abutting-arc configurations) of constructible curves
> whose parameters are constructible *without* `am`/`F`, where no curve used has arc length
> `α F(φ,c)+β` and no curve equation is `y=F(x)` up to affine change. In this class the
> intersection coordinate is obtained from constructible data by algebraic operations,
> elementary functions, and inverses of drawable arc lengths (`ellipticEAm` and its relatives);
> it cannot be `am(u,c)` for `0<c<1`.

### 6.3 The loopholes (assumptions that would let a construction through)

1. **Multi-equation cancellation (R3's L1, the top one).** A crossing is a 2×2 system; after
   differentiation the extra unknown `w'` can absorb conditions, so §6.1's single-equation
   argument is *not* airtight for 2×2 systems. Concretely, one could try to drive a moving
   intersection along the Jacobi circle. Our tests (§3.3, §4.3) show the natural families fail
   or are circular, but a general impossibility is not proved. This is the same open loophole
   as R3's L1.
2. **A drawable curve of arc length `F`** (Serret/Kiepert; R2 §C). Any such constructor would
   immediately give a positive crossing construction (the tree in §5.4).
3. **An `F`-encoding curve equation (implicitly-elementary `F`).** If some constructible curve
   had defining equation equivalent to `y = F(x)` (or if the graph of `F` lay on an
   elementary/`E`-definable curve), a crossing could read `am` directly. This is the
   Lambert-`W`-style loophole: an implicit elementary equation can define a non-elementary
   function. R3 §4.3 shows no *E/elementary* relation for `F` at the same angle (the only
   fitting case `c'=c` is circular epsilon), which closes the concrete instances, but a general
   transcendence proof is not in hand.
4. **Special/CM moduli** (`c=1/2`, singular moduli): not separated from the generic tests here;
   R3 §6 ranks it low. Nothing in the crossing analysis is modulus-sensitive beyond the
   generic failure, but a dedicated check at `c=1/2` is the natural next test.

No impossibility of `PConstructible (jacobiAm c u)` is claimed. Only the class in §6.2 is
excluded.

---

## 7. Positive calibration: the abutting-arcs crossing inverts `E` (not `F`)

**Script:** `X2-02-crossings.py` part (a). This is the model crossing construction, and the
demonstration that the method is sound.

**Construction tree (in the `Defs.lean` move language).** Fix `c<1`, `b=√(1−c)`, and
`0<L<E(π/2,c)`.

1. `ellipseParam b` is the tracing `t ↦ (sin t, b·cos t)`; its speed is `√(1−c sin²t)`, so
   `arcLengthOf (ellipseParam b) 0 φ = ellipticE c φ` (Lean: `speed_ellipseParam_eq`
   `Pptc/Basic.lean:3389`, `arcLengthOf_ellipseParam` `Pptc/Basic.lean:3396`).
2. `arc_of_length` on the ellipse gives arc `A` from `(0,b)` of length `L`; its far endpoint is
   at `φ = ellipticEAm c L`.
3. `arc_of_length` on the co-parametrisation `t ↦ (cos t, b·sin t)` from `(1,0)` of length
   `E(π/2,c)−L` gives arc `B`; its far endpoint is again `(sin φ, b cos φ)`.
4. `A ∩ B = {(sin φ, b cos φ)}` (unique: on `[0,π/2]`, `sin` is injective, and a common point
   forces the two angle parameters to be `φ`). Hence `inter_y` is legal, and `φ` is recovered
   by `arccos`/`arcsin`.

**Numerical checks.** For `c ∈ {0.3, 0.7, 0.93}` and lengths `L/K ∈ {0.2, 0.55, 0.9}`
(`K=E(π/2,c)`): quadrature of the two arc lengths and the reconstruction of `φ` agree to
`2.3·10⁻⁴¹`. **[numeric, 40 digits]**. The side conditions (unique crossing, injectivity,
regularity) hold on `[0,π/2]`. This reproduces the known Lean theorem
`ellipticEAm_Pconstructible_of_mem_Icc` and is the calibration for the negative: crossings
*can* invert a drawable arc length, and the drawable arc length they trip over is `E`, not `F`.

---

## 8. Verification index

| script | what it checks | tag |
|---|---|---|
| `X2-01-basics.py` | Pfaffian chain (P); `am=atan2(sn,cn)`; `F(am)=u`; `F` not a finite cos-2k polynomial; Kepler-fit residuals; pendulum time `=` `F`-integral and `≠` Euclidean portrait length | numeric 18–40 digits |
| `X2-02-crossings.py` | abutting-arc crossing reproduces `EAm` at 3 moduli × 3 lengths; Jacobi-ODE failure table for Kepler/scaled/pendulum/EAm candidates; circularity `v=a·am−sin am` | numeric 6–41 digits |
| `X2-03-selfref.py` | unknown/equation count; moving circle × sine ODE fail; fixed intersection is length-independent; moving line × circle circularity `p=sn−a cn` | numeric 6–41 digits |

Scripts run in under 3 s each (all well under the 30 s cap).

---

## 9. References

* DLMF §22.14 Integrals, https://dlmf.nist.gov/22.14 (derivatives `am'=dn`, `F`,`E`).
* DLMF §22.16 Related functions, https://dlmf.nist.gov/22.16 (`am=arcsin sn`; nome/Fourier
  series — an *infinite* series, not a finite composition).
* DLMF §22.19 Physical applications (pendulum), https://dlmf.nist.gov/22.19.
* Wolfram MathWorld, *Elliptic Integral*, https://mathworld.wolfram.com/EllipticIntegral.html.
* Wolfram Functions, *JacobiAmplitude*,
  https://functions.wolfram.com/introductions/PDF/JacobiAmplitude.pdf
  (`am` is the inverse of `F`).
* Wikipedia, *Pfaffian function*, https://en.wikipedia.org/wiki/Pfaffian_function
  (Khovanskii's chains; trigonometric functions are Pfaffian on bounded intervals).
* A. G. Khovanskii, *Fewnomials*, Translations of Mathematical Monographs 88, AMS 1991,
  https://bookstore.ams.org/MMONO/88 (Pfaffian systems, fewnomial Bezout bound).
* Internal: `pptc/Pptc/Defs.lean` (constructors), `pptc/Pptc/Jacobi.lean`
  (`ellipticEAm`, line 602; `ellipseParam_ellipticEAm_Pconstructible`, line 636),
  `pptc/Pptc/JacobiAddition.lean` (near-zero reduction, line 313),
  `NOTES-jacobi-R1a/R1b/R1c/R2/R3.md`.

---

## 10. Open loopholes, ranked

1. **Multi-equation (2×2) cancellation / moving intersections** — §6.3(1). The one place the
   crossing formalism escapes the single-equation argument; no candidate, not excluded.
2. **A drawable curve of arc length `F`** — §6.3(2); R2's recommended constructor. Would make
   the §5.4 tree a proof.
3. **Implicitly-elementary `F`** — §6.3(3). Concrete instances (`E`/elementary relations) are
   closed by R3 §4.3; a general transcendence statement is not proved.
4. **Special/CM moduli** — §6.3(4). Generic failure only.

**Not loopholes.** Time-independent crossings of fixed curves (fixed, length-invariant);
the literal pendulum portrait (time is not the Euclidean length and positions are periodic);
finite Kepler-type equations (approximations of a non-finite `F`); addition/duplication fixed
points (only torsion).
