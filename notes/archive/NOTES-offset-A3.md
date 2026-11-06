# NOTES-offset-A3 — offset × offset, self-crossings, cusps

Task A3 of the parallel `offset` research programme. Repo root `C:\dev\Powerpoint\lean`.
Scripts: `archived files/offset-scripts/A3-*.py`. Log: `HANDOFF-offset-A3.md`.
Evidence tags: `[Lean]`, `[symbolic]`, `[numeric, N digits]`, `[Jacobian rank …]`,
`[parameter count…]`. Anything not proved in Lean is marked `[symbolic]`/`[numeric]`.

## 0. Summary (≤12 lines)

1. **Offset × offset of two cubic pairs has genuine elimination degree 92.** The four-equation
   system (two offsets, two square roots) has elimination polynomial in `t₁` of degree 96,
   which factors **structurally** as `q₁(t₁)·f₉₂(t₁)`, where `q₁ = u₁²+v₁²` is the **cusp
   locus of the first base curve** (the spurious `w₁=w₂=0` component); `f₉₂` is the genuine
   factor, **irreducible over ℚ**. `[symbolic, mod-p Gröbner on 3 instances]`
2. The structural reason there are **no sign-branch factors**: the implicit equation of a cubic
   pair's offset depends on `d²`, so `±d` are the *same* algebraic curve; the `±d₁,±d₂` sign
   branches are not separate components.
3. **Galois group of `f₉₂` is `S₉₂`** (irreducible, contains a 47-cycle and an 89-cycle, and
   odd permutations). Hence a real root is a **degree-92 number outside every tower of degree
   ≤ 6** — the first degree ≥ 20 number with full-symmetric Galois group from an offset.
4. A real crossing is verified to **45 digits** (mpmath, independent of the resultant), with
   distances exactly `1`, perpendicularity residuals `~1e-60`, Jacobian determinant `267.86`
   (transverse, so `restrict` isolates it and `inter_x/inter_y` apply).
5. **Self-crossings of one offset (bitangent circles) have genuine degree 32** (36 with the
   spurious `q₁`), `f₃₂` irreducible over ℚ but with **imprimitive** Galois group (the `t↔s`
   involution gives blocks of size 2). The bitangent-circle **centre has degree 16**.
6. **Cusp verdict: NOT extractable.** The evolute is a rational curve but is *not* a legal
   curve (offsets are constant-distance only), no constructible curve is *forced* through a
   cusp, and `inter` cannot manufacture a transverse crossing at a singular point. The
   degree-12 curvature equation is not usable: no engine covers degree 12.
7. Special cases: offset×**line** `= 10` (A2 F1, calibration); offset×**circle** `= 16` finite
   (Bézout 20, 4 at the circular points); offset×**parabola** is exact (PH, no squaring, ≤ 60);
   `γ₁=γ₂` on two windows `= 32`.
8. The recovery quintic means **every** offset-crossing parameter is in `K`; the crossing is
   always the hard part, the recovery never is.

## 1. Mechanism table

| mechanism | legal extraction? | degree | dimension | coverage | real feasibility |
|---|---|---|---|---|---|
| offset₁ × offset₂, two cubic pairs | yes (`crossing_Pconstructible`) | **92** genuine (96 incl. `q₁`) | ≤15 params `[parameter count]` | one irreducible degree-92 family; no low-degree factor generically | 12 real / 96 (cf1, `d₁=d₂=1`) |
| offset × line (A2 F1, sanity) | yes | 10 | 7 of 10 (`Basic`/`Offset`) | codim 3 | some real |
| offset × circle (or ellipse) | yes | **16** finite (Bézout 20) | – | – | real |
| offset × parabola (PH, rational) | yes | ≤ 60 exact | – | – | real |
| offset self-crossing (two windows) | yes | **32** genuine (36 incl. `q₁`) | ≤9 params | imprimitive degree-32 family | real for `d≥2` (none for `d=1`) |
| cusp / evolute point | **no** | 12 (curvature) | – | – | – |

Ratings: "yes" means the `Defs.lean` moves literally realize it with side conditions discharged
below. Dimension entries are parameter counts, not verified Jacobian ranks (see §4.3).

## 2. Offset × offset: the elimination

### 2.1 The system

Write `γᵢ(tᵢ) = (xᵢ(tᵢ), yᵢ(tᵢ))` for two cubic pairs, `uᵢ = xᵢ'`, `vᵢ = yᵢ'`,
`qᵢ = uᵢ²+vᵢ²`, `wᵢ = √qᵢ`. Equating the offset points
`γ₁ + d₁N₁ = γ₂ + d₂N₂`, `Nᵢ = (−vᵢ, uᵢ)/wᵢ`, and clearing `w₁w₂` gives the four equations

```
E₁ = a·w₁w₂ − d₁v₁·w₂ + d₂v₂·w₁ = 0 ,      a = x₁−x₂,  b = y₁−y₂
E₂ = b·w₁w₂ + d₁u₁·w₂ − d₂u₂·w₁ = 0 ,
F₁ = w₁² − q₁(t₁) = 0 ,    F₂ = w₂² − q₂(t₂) = 0 .
```

`wᵢ` is free with `wᵢ²=qᵢ`, so **both signs of each offset are present at once**: `wᵢ<0`
traces `offset(−dᵢ)`. Since `−dᵢ` is `PConstructible` whenever `dᵢ` is, all four sign
combinations are legal. `[symbolic]`

### 2.2 Eliminating `t₂, w₁, w₂`

* From `E₁, E₂` (linear in `w₂`), the `w₂`-resultant is `−d₂w₁·(w₁Q + d₁J)` with
  `Q = a u₂ + b v₂` and `J = u₁v₂ − v₁u₂`; dividing by `−d₂w₁` (a unit on the solution set)
  gives `w₁Q + d₁J = 0`.
* Substituting `w₁ = −d₁J/Q` into `F₁` gives `G = d₁²J² − q₁Q² = 0`.
* Substituting `w₁` into `E₁` gives `w₂ = −d₂v₂J/(aJ+v₁Q)`, and `F₂` gives
  `H = d₂²v₂²J² − q₂(aJ+v₁Q)² = 0`.
* `Resultant_{t₂}(G,H)` over ℚ factors as `c · f₄² · f₁₆⁴ · f₂₀² · f₉₂` (degrees
  4,16,20,92; total 204), but this includes the `Q=0` spurious locus. The honest elimination
  is the Gröbner elimination below.

**Clean elimination.** `GroebnerBasis[{E₁,E₂,F₁,F₂}, {t₂,w₁,w₂,t₁}, Lex, Modulus→p]` over
`GF(p)` has a single univariate element in `t₁`. Its degree is **96** for three random
instances (different integer cubics) and two primes (`1000003`, `999983`).
`[symbolic, mod p]` It is **generically irreducible over `GF(p)` after removing a factor of
degree 4**; over ℚ the same computation (via `FactorList` of `Resultant(G,H,t₂)`, then a
divisibility test against the mod-p Gröbner element) shows

```
elimination polynomial  =  q₁(t₁) · f₉₂(t₁) ,   deg q₁ = 4,  deg f₉₂ = 92,
q₁ = u₁²+v₁² = 45t₁⁴ − 24t₁³ + 148t₁² − 92t₁ + 29  (instance cf1),
f₉₂ irreducible over ℚ  (FactorList length 2),
```

and both `q₁` and `f₉₂` divide the mod-p elimination element, so `q₁·f₉₂` is the elimination
polynomial. `[symbolic]` The factor `q₁` is exactly the spurious `w₁=w₂=0` component: at a
root of `q₁`, `u₁=v₁=0`; with `w₁=w₂=0`, `E₁=E₂` vanish identically and `F₂` needs `q₂(t₂)=0`,
so these are the "both base curves at a cusp" corner solutions, not offset intersections.

### 2.3 Bézout bookkeeping

The offset of a cubic pair as a plane algebraic curve has degree **10** (`Offset.lean`'s
line-crossing polynomial `offsetCrossPoly` has degree 10; the implicit resultant
`Res_t[(X−x)u+(Y−y)v, (X−x)²+(Y−y)²−d²]` has total degree 10). `[symbolic]` Two degree-10
curves meet in `10² = 100` points. The parametrized elimination sees `96` affine points,
of which `4` are the cusp spurious component (`w₁=w₂=0`, not intersections at all) and `92`
are genuine; the remaining `8` of the Bézout count sit at infinity / are shared circular
points (both degree-10 offset curves pass through the two circular points). `[symbolic, numeric]`

**Structural factorization answer (PLAN Q1):** the only structural factor is `q₁` (a `w=0`
component); there are no sign-branch factors, because the offset curve is even in `d`.

### 2.4 Galois group of `f₉₂` = `S₉₂`

501 primes were sampled and `f₉₂` factored mod each. `[numeric, exact mod p; Galois inference]`

* `f₉₂` is **irreducible over ℚ** ⇒ transitive.
* 80 primes produce a factor degree of a **prime > 46**; e.g. `q=1223` gives factor degrees
  `{1,3,89}` (an 89-cycle), `q=1289` gives `{1,1,6,6,9,22,47}` (a 47-cycle).
* 248 primes give an **odd** permutation (`n − #cycles` odd), e.g. `q=1283` gives a single
  degree-92 factor (a 92-cycle, odd).

A transitive group containing a `p`-cycle with `p > n/2` is primitive (no block system can
survive a cycle of length `> n/2`); with `p = 47 ≤ n−3 = 89`, Jordan's theorem gives
`A₉₂ ⊆ G`; the odd element gives `G = S₉₂`. **Verdict: `Gal(f₉₂/ℚ) = S₉₂`.** `[symbolic]`

Consequence: every root has degree 92 over ℚ, and the smallest index of a proper subgroup of
`S₉₂` is 92, so no tower of steps of degree ≤ 6 can reach a root. `[symbolic]`

### 2.5 Recovery: both parameters land in `K`

The crossing point `(X,Y) ∈ K` by `crossing_Pconstructible`
(`offsetCubicPair_cross_point_Pconstructible`, `Offset.lean:547`). The displacement from
`γ₁(t₁)` to `(X,Y)` is along the normal, so `offsetParam_normal_eq_zero` gives

```
(X − x₁(t₁))·u₁(t₁) + (Y − y₁(t₁))·v₁(t₁) = 0 ,
```

a **quintic** in `t₁` whose coefficients are built from `X,Y` and the cubic coefficients by
`+ − ×` alone, hence lie in `K` (`normalEq_eq_quinticVal`, `Offset.lean:578`). Its leading
coefficient is `−3(c₃²+e₃²) ≠ 0` for a genuine cubic. Therefore
`root_Pconstructible_le_six_coeffs` gives `t₁ ∈ K`; likewise `t₂`. `[Lean, existing lemma]`
So the full data `(X, Y, t₁, t₂)` of an offset×offset crossing is P-constructible.

## 3. Explicit new number: a real degree-92 offset×offset crossing

### 3.1 Construction tree (all parameters rational, `d₁=d₂=1`)

1. `γ₁(t) = (2t³−3t²+5t+7, t³+4t²−2t+1)`, `γ₂(t) = (3t³+t²−4t+2, −t³+2t²+6t−5)`.
   Both are cubic polynomials; write each as a cubic Bézier on `[0,1]` (rational control
   points), then apply the rational affine reparametrisation `t = αs+β` (`α,β ∈ ℚ`) that puts
   the crossing parameter in `(0,1)`. Apply `cubic_bezier` → constructible curves `S₁, S₂`.
2. Use `exists_rat_window_cubicPair` to pick a short rational window on each where the arc is
   injective, regular (`speed ≠ 0`), `C¹`. Apply `PConstructibleCurve.offset` with `d=1` →
   constructible offset arcs `O₁, O₂` (`offsetCubicPairArc_PConstructibleCurve`,
   `Offset.lean:275`).
3. Restrict `O₁, O₂` to small coordinate windows around `(11.4021856741…, 6.8334367955…)`.
   The crossing is transverse: Jacobian determinant `267.857637…` `[numeric, 30 digits]`; by
   continuity a small window isolates exactly one point, so `O₁ ∩ O₂ = {P}` after restriction.
4. `inter_x`, `inter_y` → `P = (X,Y) ∈ K` (via `crossing_Pconstructible`).
5. Recover `t₁, t₂ ∈ K` from the two quintic normal equations (§2.5).

Side conditions checked: arcs regular and injective (short rational windows); `d=1` ∈ K;
crossing isolated/transverse; both signs of `d` legal. `[Lean for the engine; numeric for
transversality and the explicit instance]`

### 3.2 Numerical certificate `[numeric, 45 digits]`

```
t₁ = 1.22231179911457674266169305600314168498362206
t₂ = 1.64943883635326178031270697615901139391043872
P  = (11.4021856741030028189257978281836538860928064,
      6.83343679556988366929415468845972471682396063)
|P − γ₁(t₁)| = 1.0 (exactly, to 45 digits)
|P − γ₂(t₂)| = 1.0
normal-equation residuals ≈ 3.7e−60 and 4.4e−60
speed γ₁(t₁) = 13.93862978987233672929144331009301814828
speed γ₂(t₂) = 24.19481405533477685648885116778446061015
```

12 real solutions of the 4-variable system exist for cf1 (`d₁=d₂=1`; NSolve, precision 25);
one of these is the above, and its `t₁` is a root of the irreducible degree-92 `f₉₂`.
`f₉₂` itself was not printed in full (the shared Wolfram service timed out on the ~93-term
integer coefficient vector); the defining system, the factorization `q₁·f₉₂`, the
irreducibility and the Galois evidence are recorded, and `f₉₂` is reconstructible from the
system in §2.1–2.2 with `Resultant`/`GroebnerBasis`. `[symbolic]`

**"Genuinely new" checklist (§4 of the overview):**
* degree over ℚ: **92**; minimal polynomial over ℚ is `f₉₂`, irreducible of degree 92;
* not a root of degree ≤ 8 (`root_Pconstructible_le_eight`), not in the nonic family
  (`nonicVal_root_Pconstructible`), not a septic with a non-real root, not in the codim-3
  decic family (degree 92 ≠ 10);
* Galois evidence `S₉₂` puts the root outside every tower of degree-≤6 steps.

## 4. Self-crossings of one offset (bitangent circles)

### 4.1 Degree

Two disjoint windows of the *same* arc give two constructible offset arcs `O` and `O'`; their
crossing is a **bitangent circle centre**: a point at distance `|d|` from `γ(t)` and from
`γ(s)` with `t≠s`, the circle of radius `|d|` tangent at both. Saturating the `t↔s` diagonal
by the Rabinowitsch variable (`r(s−t)=1`) and eliminating `(s,w₁,w₂,r)` gives a univariate in
`t` of degree

```
36 = q₁(t) · f₃₂(t),      f₃₂ irreducible over ℚ, deg 32,
```

confirmed on **two instances** (cf1 `d=1`; cf1 `d=2`; second cubic `d=2`). `[symbolic]`
`36 = (10−1)(10−2)/2` is the maximal node count of a degree-10 plane curve; 4 of the 36 are
the spurious cusp component `q₁`.

### 4.2 Real feasibility and the centre

For cf1, `d=1` there are **no** real self-crossings; for `d=2` there is one genuine one
(the other near-diagonal numerical hits are cusps, `t≈s`). `[numeric]`

```
t = 0.599337433861129445146424851688373373150798571
s = 0.0476717005369934433997256730706413981860966541
centre X = 7.87715009600341450889889780106580084769897677
centre Y = 2.80686039268423686425593528826127510749194291
|centre − γ(t)| = |centre − γ(s)| = 2.0 (to 45 digits),  perp residuals ≈ 1e−61,
Jacobian determinant 6.1035618… (transverse)
```

The self-crossing polynomial for cf1, `d=2` (explicit, `[symbolic]`):

```
f₃₂(t) = 4939757637440419476137
 − 171567311174953282243812 t
 + 1900683705607606447866846 t²
 − 12154245401968565785795800 t³
 + 53119940708167982013346845 t⁴
 − 173189567550564902939960304 t⁵
 + 444430450023364820723563342 t⁶
 − 933948657131460024605959916 t⁷
 + 1655747772048120320104701094 t⁸
 − 2533193265633398598123925052 t⁹
 + 3400000803543540764985399930 t¹⁰
 − 4054805821497820973702777104 t¹¹
 + 4340525391749983862662859939 t¹²
 − 4198723592418233813197778120 t¹³
 + 3696868282512422443768636266 t¹⁴
 − 2969881197094243482713535172 t¹⁵
 + 2190480727730476025175509482 t¹⁶
 − 1481065452765798410214073532 t¹⁷
 + 924268187610186057862631074 t¹⁸
 − 529064553603668626882788472 t¹⁹
 + 280403697767276095898692675 t²⁰
 − 135783772031881110665569536 t²¹
 + 61016372781990194047128786 t²²
 − 24794404092649268865468756 t²³
 + 9379780546977357257348694 t²⁴
 − 3139473745961717584794660 t²⁵
 + 986767022135220688023750 t²⁶
 − 261866451689349969924000 t²⁷
 + 67003001824974808168125 t²⁸
 − 12949524126861832125000 t²⁹
 + 2620933629659040093750 t³⁰
 − 288034083207368437500 t³¹
 + 44499647686531640625 t³²
```

### 4.3 The parameter degree is 32, the centre degree is 16

`f₃₂` is irreducible, so `t` (and `s`) have degree 32 over ℚ. But the self-crossing system is
symmetric under `t↔s`, so `f₃₂` has an involution on its roots, and **all** factor degrees mod
every sampled prime are even (`{8,8,16}`, `{4,6,6,8,8}`, `{2,4,4,11,11}`, …) — the group is
**imprimitive with blocks of size 2**, not `S₃₂`. The centre is the fixed point of the
involution (`X₊(t) = X₊(s)`), so its Galois orbit is a block: the centre has degree **16**.
This is confirmed by the elimination for the centre coordinate: `Res_t(q₁(X−x)² − d²v₁², f₃₂)`
has degree 64 and factors as `(deg 16)² · (deg 32)`. `[symbolic]` So the self-crossing
mechanism gives a *degree-16* new number and a *degree-32* parameter, but its Galois group is
imprimitive, not full symmetric.

**Degree-halving observation:** a symmetric configuration (two windows of one curve) halves
the degree of the symmetric output relative to the parameter. This is a general way to get
smaller, possibly more useful, numbers out of a high-degree mechanism.

### 4.4 Isolation hypothesis (PLAN Q2)

The two windows can always be chosen with rational endpoints near a transverse self-crossing:
the crossing is an isolated point of the analytic self-intersection locus, and a small product
of coordinate windows around it contains no other crossing, so `restrict` yields a unique
intersection. Formally, `exists_rat_window_cubicPair` supplies rational windows where each arc
is injective/regular, and transverse isolation is an open condition on the windows. `[symbolic]`

## 5. Cusp / evolute verdict (PLAN Q3)

**Verdict: no legal extraction reaches a generic cusp or evolute point, and the degree-12
curvature equation is not usable.**

Reasoning:

1. A cusp of `O_d` occurs at `t₀` with `d = 1/κ(t₀)`; the cusp point is the evolute point
   `E(t₀) = γ(t₀) + (1/κ(t₀))N(t₀)`.
2. The **evolute is a rational curve**: `κ = (u v' − v u')/q^{3/2}` (with `γ'=(u,v)`,
   `γ''=(u',v')`), so `(1/κ)N = (q/W)(−v,u)` with `W = u v' − v u'` a cubic, and
   `E(t) = γ(t) + (q/W)(−v,u)` is rational. But **it is not a legal `PConstructibleCurve`**:
   `offset` only produces constant signed distance `d`; `arc_of_length` produces a length, not
   a variable-distance offset; `cubic_bezier` is degree 3 only; `poly_graph` is a graph of a
   polynomial ≤ 6 and `E` is not such a graph. No move draws the evolute.
3. `inter_x`/`inter_y` need two constructible curves meeting in exactly one point. A cusp is a
   **singular point** of `O_d` (two branches meet there), and no other legal curve is *forced*
   through a generic cusp. A line or circle through it would need the cusp coordinates already
   (which is what we are trying to construct); choosing its parameters requires knowing `t₀`.
   Crossing `O_d` with `O_{d'}` fails because the two offsets are everywhere separated by
   `|d−d'|`, so they never meet.
4. The cusp parameter `t₀` is a root of the **degree-12** curvature equation
   `(u v' − v u')² d² = q³`. Roots of degree 12 over `K` are reachable only if some engine
   covers degree 12. The available engines are degree ≤ 8, the special nonics, septics with a
   non-real root, the codim-3 decic family, and now the codim-76 degree-92 offset×offset
   family — **none** is an all-degree-12 engine. So `t₀` is not generally in `K`.
5. What a construction would have to break: either find a constructible curve through the cusp
   determined *without* knowing its coordinates (none is known), or obtain a genuine degree-12
   engine. The cusp is a **limit** (`E` is the envelope of the offset family as `d` varies),
   and limits are not moves.

This excludes the class: any finite tree of `Defs.lean` moves whose target is a cusp of an
offset or an evolute point, except in non-generic coincidences where the cusp already lies on
a curve placed by `K`-data.

## 6. Other metric problems (PLAN Q4)

* **Points equidistant from two curves at distance `r` (medial-axis points).** Same as
  offset×offset with `d₁=d₂=r`: degree 92 for two distinct cubics, 32 for two windows of one
  cubic. No triangular reduction.
* **Circles of given radius `r` tangent to a curve and a line.** Equals
  `offset(curve, r) × (line shifted by r)`: A2's F1 with the line's `C` shifted. Degree **10**
  in the parameter (because the offset of a line is a parallel line). Not triangular (10 > 6),
  but a single univariate degree-10 equation; recovery quintic.
* **Circles of given radius `r` through a point and tangent to a curve.** Equals
  `offset(curve, r) × circle(centre=point, radius=r)`: substituting the offset parametrisation
  into the circle and clearing `w` gives `q₁·A² − B²` with `deg A = 6`, `deg B = 5`, i.e.
  **degree 16** finite (Bézout 20, 4 at the circular points). `[symbolic]` No triangular solve.
* **Triangular solves.** The only near-triangular case is when the second curve's offset is a
  line (tangent to a line): then the crossing is a single univariate degree-10 whose parameter
  is recovered by a quintic. Everything with a genuine second offset is degree ≥ 16.

## 7. Parameter growth as `k` offsets are chained (PLAN Q5)

Heuristic `[symbolic/numeric]`. By (O3), consecutive offsets along the same normal collapse
to one offset; growth needs a non-similarity affine map (`scale_x`/`scale_y`) between steps.

* **Degree.** For a curve with a rational parametrisation of degree `N`, the offset has
  implicit degree `4N−2` (verified `N=3 → 10`; this is the standard Farouki–Neff count). A
  chain that repeatedly offsets then applies an affine degree-preserving map multiplies the
  parametrisation degree by a constant each step, so the implicit degree grows at least
  linearly and typically multiplicatively in `k`. The reachable degrees are therefore
  **unbounded**.
* **Dimension.** Each added cubic pair contributes `≤ 16` coefficients (18 counting `d`), and
  each offset step adds `O(1)` parameters. So the family dimension grows **linearly** in `k`,
  while the degree grows at least linearly and usually multiplicatively, and the coefficient
  space grows at least as fast. The family stays a low-dimensional (high-codimension)
  subvariety of the space of degree-`N` polynomials. **Coverage of whole degrees does not
  follow from a parameter count** — exactly the warning of §4 of the overview. What does
  follow is that `K` contains elements of unbounded degree (the engine property plus the
  recovery quintic).
* A concrete next degree: offset a degree-6 `poly_graph` (valid tracing `(t, p(t))`), whose
  offset has implicit degree `4·6−2 = 22`, and cross it with the degree-10 cubic offset:
  Bézout `22·10 = 220`, minus shared circular points. This would lift the headline degree from
  92 into the low hundreds and is the cheapest route to a still-higher Galois group.

## 8. Side discoveries

* **The `±d` offsets of a curve are one algebraic curve.** The implicit equation of the
  `d`-offset is even in `d` (it sees only `d²`), so `offset(+d)` and `offset(−d)` are two real
  branches of a single degree-`(4n−2)` complex curve. Hence no sign-branch factors appear in
  the elimination, and `d` and `−d` are never independent parameters.
* **Cusp-locus spurious factors.** Whenever a crossing system is rationalised with `wᵢ`, the
  cusp locus `qᵢ = uᵢ²+vᵢ²` of the base curve enters the elimination polynomial as a spurious
  factor (`q₁` in offset×offset, `q₁` in self-crossing). The factor is exactly the
  `wᵢ=0` component. Any future rationalised system should expect it and divide it out.
* **Self-crossing count saturates Bézout.** The offset of a cubic realizes the maximum
  `(10−1)(10−2)/2 = 36` nodes of a degree-10 curve (less the 4 spurious ones), so the offset
  curve is a maximally nodal degree-10 curve.
* **Degree-halving by symmetry** (§4.3): the `t↔s` involution halves the degree of the
  symmetric output (centre: 16 vs parameter: 32).
* **A cheap degree-16 engine with a full-symmetry question.** Offset×circle is degree 16; it
  would be worth checking whether its Galois group is `S₁₆` (a smaller, more tractable
  candidate for "full symmetric" than `f₉₂`).

## 9. Leads for other tasks

* **B1 (totally real septic).** `f₉₂` has only 12 real roots out of 92; the offset×offset
  family is **far from totally real** and will not cover totally real targets. A totally real
  engine needs a mechanism whose real-root count is high (e.g. crossing near an extremum), not
  offset×offset.
* **A2/A4 (families/rational offsets).** The explicit self-crossing polynomial `f₃₂` and the
  offset×offset system are available for cofactor experiments. The PH case (parabola, PH
  cubics) gives exact polynomial equations with no squaring; offsetting a PH cubic and
  crossing two such offsets is a promising exact high-degree mechanism.
* **Z synthesis.** The strongest claim here is `Gal(f₉₂) = S₉₂` and the degree-92 real
  constructible number; verify the `f₉₂` coefficients with a fresh Wolfram session and store
  them, then rerun the Galois sampling on the exact polynomial.
* **B4 (legality formalisation).** The reusable Lean lemma is: "the crossing data
  `(X,Y,t₁,t₂)` of two offset cubic arcs is P-constructible". The only missing formal input is
  the finiteness bound for the specific second offset; a Lean proof would factor the
  rationalised system and bound the `t₁`-degree (`≤ 96`), then feed
  `offsetCubicPair_cross_root_Pconstructible`.
* **Cusp route.** To reach cusps one needs a new constructor (variable-distance offset / the
  evolute) or a genuine degree-12 engine. The evolute is rational, so if a "offset by a rational
  function of the parameter" move were added, the evolute and its cusps would become legal —
  a concrete specification for a future constructor.
