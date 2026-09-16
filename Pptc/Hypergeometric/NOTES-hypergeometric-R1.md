# NOTES-hypergeometric-R1

**Origin problem for `power_law`; hyperelliptic route to a new `Γ` (B1, B6).**

Research note, wave 0, task R1. No `.lean` file was edited, created or deleted.
Every identity below is labelled:

* **[NC n]** numerically checked to `n` significant digits (scripts in
  `archived files/hypergeometric-scripts/`, run with `py R1-*.py`);
* **[SY]** proved symbolically here (the proof is written out);
* **[CL]** classical (from the literature, not re-derived here);
* **[SP]** speculative / not established.

Sources read: `AGENTS.md`, `PLAN-hypergeometric-00-overview.md` (§2 V4/V5/V6/V7,
§4 H6, §5 B1/B6, §7), `Pptc/Defs.lean` (all base curves and closure operations),
`Pptc/Basic.lean` lines 3300–4010 (the `ellipticF` construction), and the wave-0
HANDOFFs.

Scripts (all in `archived files/hypergeometric-scripts/`):

| script | contents |
|---|---|
| `R1-q1-origin-complete-period.py` | Q1 (A)–(F) |
| `R1-q2-b1-gauss-second.py`  | Q2 (1)–(7) |
| `R1-q3-hyperelliptic-periods.py` | Q3 (A)–(F) |
| `R1-q4-newgamma-cm.py` | bonus CM/Chowla–Selberg probe |

---

## 0. Answers in brief

1. **The `x = 0` restriction cannot be removed by any of the current primitives for
   non-integer `b`.** For integer `b ∈ {1,…,6}` (i.e. `m = 2b−2 ∈ {0,2,4,6,8,10}`)
   the origin *is* already reachable, because `poly_graph` draws `y = x^n` through
   `(0,0)`; so H6's `m = 6, 8, 10` are fine from the origin. For non-integer `b` no
   drawable curve shares the length density `√(1+Cx^m)` and reaches `x = 0`: the only
   such *graphs* are the same power law, `offset` changes the density, a rectangle edge
   is a straight segment, and a cubic Bézier's density is a quartic (genus ≤ 1). More
   importantly, even removing `x = 0` would not give a *complete period*: the arc length
   is a **second-kind** integral `∫√(1+x^m)dx`, which diverges at `x = ∞`, whereas the
   Beta-value complete periods are **first-kind** integrals `∫dx/√(1+x^m)`. The two are
   different periods, and every closed drawable curve has genus ≤ 1.

2. **B1 frontier.** `₂F₁(a,1−a;1;½) = √π / (Γ((1+a)/2) Γ(1−a/2))` (Gauss's second
   theorem) **[NC 50]** for every tested `a`, including `a = ⅕, ⅛`. The four reachable
   signatures `a ∈ {½,⅓,¼,⅙}` are exactly the Schwarz *algebraic* ones (reducible to `K`
   by the quadratic/quartic/cubic/sextic transformations). The H6 arc-length family is
   `₂F₁(−½, 1/m; 1+1/m; z)`, whose parameter identity `c = a+b+3/2` fails every standard
   quadratic transformation, so **H6 cannot reach `a ∉ {½,⅓,¼,⅙}`**. A new `a` would need
   a mechanism outside the Schwarz list; none is available.

3. **B6.** The complete first-kind periods of `y² = 1+x^m` are
   `(1/m)·B(p/m, ½−p/m)`. For `m = 6, 8` every Γ argument is already in the
   denominator-24 family of `Gamma.lean`; for **`m = 10` the arguments `1/10, 1/5, 3/10,
   2/5` are new**, so `B(1/10,2/5) = Γ(1/10)Γ(2/5)/√π` would be a genuinely new Γ product
   (denominators 10 and 5). But **no drawable construction closes it**: the arclength is
   the wrong (second-kind) integral, it needs `x = ∞`, and the genus-1 integration-by-parts
   trick that the repo uses for `ellipticF` has no genus-2 analogue.

4. **Strongest candidate** (§4): the genus-2 first-kind period `B(1/10,2/5)` at `m = 10`,
   equivalently `Γ(1/10)Γ(2/5)`. It is genuinely new (§3.2) and the curve is drawable, but
   it is *not* closable with the current primitives; the missing piece is a primitive that
   produces the *first-kind* differential `dx/√(1+x^m)` over a finite arc (or a closed
   genus-2 curve). This is a negative result, not a construction.

---

## 1. Q1 — the `power_law` origin / complete-period problem

### 1.1 The length density **[SY]**

`power_law a b` is the set `S_{a,b} = {(x,y) : 0 < x ∧ y = a x^b}` (`Defs.lean:197–199`).
Parametrize the graph by `x` and write `y(x) = a x^b`. Then

```
ds/dx = √(1 + y'(x)²) = √(1 + a²b² x^{2b−2}) =: √(1 + C x^m),
        C = a²b²,   m = 2b − 2.
```

Both `a` and `b` are rational, so `C` and `m` are rational; `C > 0` and `m` can have either
sign. In this note `m > 0` (the interesting case).

### 1.2 V4 and what `arc_length` actually returns **[SY]** + **[NC 45]**

With `m > 0`, expanding `(1+u)^{1/2} = Σ_k (½ choose k) u^k`, `u = Cx^m`, and using
`(1/m)_k / (1+1/m)_k = 1/(mk+1)`:

```
∫₀^X √(1+Cx^m) dx = X · ₂F₁(−½, 1/m; 1+1/m; −C X^m) =: G(X).
```

**Proof (symbolic, one line).** The `k`-th term of the series is
`(½ choose k) C^k X^{mk+1}/(mk+1)`, and
`(½ choose k) = (−1)^k (−½)_k / k!`, while `C^k = (−1)^k (−CX^m)^k`; collecting
`(−½)_k (1/m)_k / ((1+1/m)_k k!) (−CX^m)^k X` gives exactly the `₂F₁` series.

`R1-q1` (A) confirms the closed form against adaptive quadrature to 45+ digits for
`m = 2, 3, 4, 6, 7, 7/2, 8, 10, 1/2` (worst deviation `< 2·10^{-46}`, most are `0` at 45 dps).

Now `PConstructible.arc_length` (`Defs.lean:148–161`) integrates `speed` over a bounded
parameter interval `[a,b]`, requires `γ '' Icc a b ⊆ S`, and requires **both** endpoints
`γ a, γ b` to be P-constructible *points*. Taking `γ(t) = (t, a t^b)` on `[x₀, X]` gives

```
PConstructible (G(X) − G(x₀)),   with x₀ > 0 the image of a P-constructible point,
```

and `(0,0) ∉ S_{a,b}` because the primitive's defining formula carries `0 < x`. So the
only available values are *differences* `G(X) − G(x₀)` with `x₀ > 0`. `R1-q1` (B) checks
`G(X)−G(x₀)` against the numeric integral `∫_{x₀}^{X}` for `m = 6, X = 0.5, x₀ = 0.2`
(identical to 32 digits).

Note `G(0) = 0` algebraically (the `X` prefactor), so the obstruction is *purely* that
`(0,0)` is not on the curve — but see §1.6: even that is not the real obstruction to a
*complete period*.

### 1.3 Integer exponents: the origin is already reachable **[SY]** + **[NC 45]**

For `b = n ∈ {1,…,6}`, `y = x^n` is a polynomial of degree `n ≤ 6`, so
`PConstructibleCurve.poly_graph (X^n : Polynomial ℚ)` draws it, *including* `(0,0)`
(`Defs.lean:195–196`). The arc-length constructor then applies with `γ(t) = (t, t^n)`,
`a = 0`, `b = X`: both endpoints `(0,0)` and `(X, X^n)` are P-constructible, so `G(X)`
itself is P-constructible. Here `m = 2n−2 ∈ {0,2,4,6,8,10}`.

`R1-q1` (C) checks the four hyperelliptic cases:

```
n = 4 (m = 6):  G(0.5) = 0.5086511106620370580395797   (diff vs quadrature 0)
n = 5 (m = 8):  G(0.5) = 0.5026787251709954479237950   (diff 0)
n = 6 (m = 10): G(0.5) = 0.5007953703123245360412293   (diff 0)
```

So **H6's `m = 6, 8, 10` are obtainable from the origin without any new device.** The
`x = 0` problem in the plan's §4 is therefore a problem *only* for non-integer `b`, i.e. for
`m ∉ {0,2,4,6,8,10}`.

### 1.4 A curve sharing the density `√(1+Cx^m)` is the same power law **[SY]** + **[NC 45]**

Suppose a real `C¹` injective arc is parametrized by `x` (so it is a graph `y = f(x)`).
Then `ds/dx = √(1+f'(x)²)`, and `ds/dx = √(1+Cx^m)` for all `x` on the arc forces

```
f'(x)² = C x^m   ⇒   f(x) = ± (2√C/(m+2)) x^{m/2+1} + const,
```

i.e. `f` is a power law with exponent `b = m/2 + 1` — the *same* functional form up to a
vertical translation (`√C = |ab|` is rational, so the leading coefficient is rational).
`R1-q1` (D) checks `f'(x)/x^{m/2} = b` is constant for `m = 3, 5, 6, 7, 1/2`.
For `b = m/2+1` to be an integer in `[1,6]` we need exactly `m ∈ {0,2,4,6,8,10}`; otherwise
the only carrier is `power_law`, whose set omits `x = 0`.

If the arc is not a graph (`x` not monotone on it), the length element cannot be written
as a single-valued `√(1+x^m)dx` without double-counting, so the same conclusion holds for
the density on an injective arc.

**Conclusion.** No drawable graph curve sharing the `√(1+Cx^m)` density includes `x = 0`
unless `m/2+1 ∈ {1,…,6}`.

### 1.5 The other primitives do not help **[SY]** + **[NC 45]**

* `offset`: for a graph, `|γ_d'(x)| = (1 + d·κ(x))·√(1+Cx^m)` with curvature
  `κ = y''/(1+y'²)^{3/2}`. If this were `√(1+C'x^m)` then `(|\gamma_d'|²−1)/x^m` would be
  constant. `R1-q1` (E), for `m = 6, n = 4, C = 16, d = 0.17`, gives
  `561.97, 43.61, 16.52, 16.04` at `x = 0.3, 0.6, 1.1, 1.6` — not constant. So the offset
  density is a genuinely different differential; in particular it is not a power-law one.
* `rectangle` + `restrict` + `arc_length`: a rectangle edge is a straight segment; its
  length is a difference of P-constructible coordinates, i.e. an ordinary P-constructible
  number. Cropping with `restrict` changes nothing about the length element. No Γ value
  arises.
* `cubic_bezier`: coordinates are cubic in `t`, so `speed² = (quadratic)² + (quadratic)²`
  is a **quartic**. `R1-q3` (D) fits the quartic exactly (residual `1.7·10^{-14}` on a
  random P-constructible-control-point Bézier). `∫√(quartic) dt` is a **genus-1** integral,
  so a Bézier cannot even locally reproduce the genus-2/3/4 density `√(1+Cx^m)` for
  `m ≥ 6`. (The same holds for any rotation/translation/scaling of a Bézier, which only
  change the coefficients of the quartic.)
* `rotate`/`scale_x`/`scale_y`/`translate_x`/`translate_y` are **image maps**
  (`S ↦ f '' S`). Applying one to `power_law a b` produces a set that still does **not**
  contain the image of the excluded point `(0,0)`, and its length density is the same
  `√(1+Cx^m)` in the pre-image parameter. So no rigid motion or scaling re-introduces
  `x = 0`.

### 1.6 Why no drawable curve yields a *complete period* **[SY]** + **[CL]** + **[NC 40]**

The plan's B6 calls `B(i/m, j/m)` the "complete periods" of `y² = 1+x^m`. Two distinct
differentials are involved:

* **first kind (holomorphic)**: `∫ dx/y = ∫ dx/√(1+x^m)`. This *is* finite over `[0,∞)`
  and equals `(1/m)B(1/m,½−1/m)`. `R1-q3` (A) verifies
  `∫₀^∞ x^{p−1}/(1+x^m)^{1/2} dx = (1/m)B(p/m,½−p/m)` to 40 digits for all admissible
  `p` at `m = 6,8,10`.
* **second kind (arc length)**: `∫ y dx = ∫ √(1+x^m) dx`. This **diverges**:
  `∫₀^U √(1+x^m) dx = (2/(m+2))U^{m/2+1} + O(1)`. `R1-q3` (C) confirms
  `m=6: 2501.05, 2.5·10^7, 2.5·10^{11}` at `U = 10,100,1000`; `m=8,10` likewise.

So the arc-length value is the *second-kind* integral, which has **no finite complete
version at all**; the Beta value is a first-kind quantity. They are different periods,
related (in genus 1) only by a Legendre relation with a divergent piece. **`R1-q1`/`R1-q3`
(F)** show numerically that the incomplete arclength `G(X)` never equals the Beta period:
e.g. at `m = 10`, `(1/10)B(1/10,2/5) = 1.1905798216…`, while
`G(0.5)=0.50002, G(0.9)=0.91368, G(1.0)=1.04090, G(1.2)=1.43020, G(2.0)=11.651`.

Independently, **no closed drawable curve has genus ≥ 2.** The closed base curves are the
ellipse (genus 1) and the rectangle (rational); the arclength double cover of a cubic Bézier
is genus 1 by the quartic argument; `offset`, `scale`, `rotate`, `translate`, `restrict`,
`arc_of_length` all preserve the underlying function field. A `poly_graph` of degree ≤ 6
*does* have genus up to 4 (`R1-q3` (D): `speed²` has degree `2(d−1)`, so `d = 4,5,6` give
genus `2,3,4`), but it is an **unbounded graph**, so only open arcs of it are ever drawn. A
complete first-kind period needs a cycle; the real locus of `y² = 1+x^m` is two unbounded
arcs (m even) or two unbounded arcs meeting at `(−1,0)` (m odd) — no bounded cycle.

**Why the repo's genus-1 trick does not generalise [CL].** `ellipticF_Pconstructible`
(`Basic.lean:3977`) gets the first-kind `ellipticF` from a Bézier arclength (second kind)
using two integration-by-parts identities (`Basic.lean:3870, 3909`). These work because a
genus-1 curve has a one-dimensional space of holomorphic differentials, so the second-kind
arclength is determined by the first-kind period plus boundary terms and a known
coefficient `m²`. In genus `g ≥ 2` there are `g` independent holomorphic differentials and
`2g` second-kind periods, so one arclength integral no longer determines the holomorphic
periods. This is the precise structural reason the construction cannot be transplanted to
`m = 6, 8, 10`.

### 1.7 Q1 verdict

For **non-integer** `b` the current primitives cannot reach `x = 0` on a curve sharing the
density, and — more decisively — the arclength is the wrong kind of period and no drawable
closed curve has the requisite genus. The claim "some drawable curve sharing
`√(1+x^m)` removes the limitation" is **false for the current primitives**.

**Loopholes (stated explicitly).**

* A *coincidental* identity making some finite `G(X)` equal a Beta value. We found no such
  identity and no mechanism produces one; but the project cannot rule it out, in line with
  §7's "do not claim non-P-constructibility outright".
* A future primitive that produces a **closed genus-2 curve**, or an arc carrying the
  **first-kind** differential `dx/√(1+x^m)` (not the arclength differential), would change
  the conclusion. Adding only "reaching `x = ∞`" is *not* enough, because the arclength
  density still diverges there.
* `arc_of_length` + `inter_x/inter_y` can synthesise new numbers from known lengths, but
  every input length is already P-constructible; there is no mechanism turning one
  incomplete second-kind integral into a first-kind complete period.

---

## 2. Q2 — B1's frontier: for which `a` is `₂F₁(a,1−a;1;½)` reachable?

### 2.1 Gauss's second theorem **[CL]** + **[NC 50]**

```
₂F₁(a, 1−a; 1; ½) = √π / ( Γ((1+a)/2) · Γ(1−a/2) ).
```

`R1-q2` (1) verifies this to 50 digits for
`a = ½, ⅓, ¼, ⅙, ⅕, ⅛, 3/10, 2/5, 3/7, 3/8, 0.37, 0.123` (deviation `0` at 50 dps, or
`< 3·10^{-51}`). Since `√π` and `Γ` are P-constructible when their arguments are, reaching
the value `₂F₁(a,1−a;1;½)` makes `Γ((1+a)/2)Γ(1−a/2) = √π / ₂F₁(…)` P-constructible by
division. **This is the B1 bridge.**

### 2.2 The four reachable signatures **[NC 50]**

| `a` | route to `K` | `Γ` product | `Gamma.lean` |
|---|---|---|---|
| `½` | V6 quadratic, `₂F₁(½,½;1;z) = ₂F₁(¼,¼;1;4z(1−z))` | `Γ(¾)²` | have (denom 4) |
| `¼` | V7 quartic, verified at `z = 1/5` | `Γ(5/8)Γ(7/8)` | have (denom 8) |
| `⅓` | cubic signature (R2) | `Γ(2/3)Γ(5/6)` | have (denom 6) |
| `⅙` | sextic signature (R2) | `Γ(7/12)Γ(11/12)` | have (denom 12) |

Checks (`R1-q2` (2)).

* `a = ½`, `z = ½`: `₂F₁(½,½;1;½) = ₂F₁(¼,¼;1;1) = (2/π)K(1/2) = √π/Γ(¾)²`, all equal to
  50 digits. (`mpmath` uses the parameter `m = k²`, so `(2/π)·ellipk(1/2)`.)
* `a = ¼`, `z = 1/5`: `₂F₁(¼,¾;1;1/5) = (1+√(1/5))^{−1/2} ₂F₁(½,½;1; 2√(1/5)/(1+√(1/5)))`,
  both `1.04226813278780864028011135919`, deviation `2.7·10^{-51}`.
* `a = ⅓`, `a = ⅙`: Gauss-second value equals `₂F₁` LHS to 50 digits
  (`1.1595952669639283657699920515700209`, `1.0984306968398620689429351616086988`). The
  cubic/sextic *reductions* are R2's deliverable; they do not change the value reached.

These four `a` are exactly the classical **Schwarz algebraic signatures**: the Legendre
function `P_{−a}` is algebraic (equivalently the family reduces to `K`) only for
`a ∈ {½,⅓,¼,⅙}` (up to the degenerate limits). [CL]

### 2.3 The H6 family cannot reach B1 **[SY]** + **[NC 50]**

H6 gives the family `(−½, 1/m; 1+1/m; z)` for `z ∈ (−1, 0]`. Its defining feature is

```
c = a + b + 3/2     (a = −½, b = 1/m, c = 1+1/m).
```

Every standard quadratic transformation relates `c` to `a, b` by `c = a − b + 1`,
`c = (a+b+1)/2`, or `c = a+b+½`; none is `a+b+3/2`, so none applies to the H6 family
(each forces `m < 0`, or is inconsistent). The
Pfaff/Euler transformation maps the family to `(1−z)^{1/2} ₂F₁(−½, 1; c; z/(z−1))`, again
with `(a,b) = (−½,1)`, which is not `(A,1−A)` (that would need `−½ = A` and `1 = 1−A`
simultaneously). The contiguous class of H6 moves `c` by integers, so `c = 1` needs
`1/m ∈ ℤ_{>0}`; even then `a+b = 1` has no integer solution for the shifts.
`R1-q2` (4) confirms the Euler transform numerically at interior points: e.g.
`₂F₁(−½,⅙;7/6;−½) = (3/2)^{1/2} ₂F₁(−½,1;7/6;1/3)` to 50 digits (deviation `0`).

So the H6 hyperelliptic arc lengths, and their contiguous classes, land **outside** the
Legendre `(a,1−a;1)` family. Heuristically this is the genus mismatch of §1.6 (an algebraic
hypergeometric transformation preserves the local monodromy up to commensurability, and a
genus-2 period is not commensurable with the genus-1 Legendre family) **[SP]**; the
parameter algebra above is the rigorous part **[SY]**.

### 2.4 A verified generalisation that does *not* help **[NC 50]**

Bailey's `z = ½` summation (attribution uncertain; verified here) reads

```
₂F₁(a, 1−a; c; ½) = Γ(c/2) Γ((c+1)/2) / ( Γ((c+a)/2) Γ((c+1−a)/2) ).
```

`R1-q2` (6) verifies it over **172** `(a,c)` pairs to 50 digits (worst `1.07·10^{-50}`; it
reduces to Gauss's second theorem at `c = 1`). It shows that *any* reachable
`₂F₁(a,1−a;c;½)` — not only `c = 1` — gives a Γ product. But the H6 transform produces
`₂F₁(−½,1;c;½)` (i.e. `b = 1 ≠ 1−a = 3/2`), to which this does not apply, and our only
reachable hypergeometric arguments are negative (`z = −CX^m ≤ 0`), whereas the summation
needs `z = ½`. So the generalisation is a useful fact for the programme but does not widen
B1 here.

### 2.5 Frontier table and what a new `a` requires

| `a` | `₂F₁(a,1−a;1;½)` | `Γ` product | status |
|---|---|---|---|
| `½` | 1.1803405990160962260453379 | `Γ(¾)²` | reachable (V6) |
| `⅓` | 1.1595952669639283657699921 | `Γ(2/3)Γ(5/6)` | reachable (R2 cubic) |
| `¼` | 1.1339155597260827324401565 | `Γ(5/8)Γ(7/8)` | reachable (V7) |
| `⅙` | 1.0984306968398620689429352 | `Γ(7/12)Γ(11/12)` | reachable (R2 sextic) |
| `⅕` **[NC 50]** | 1.1137746646208464520265199 | `Γ(3/5)Γ(9/10)` | **unknown** |
| `⅛` **[NC 50]** | 1.0771499089006602942508828 | `Γ(9/16)Γ(15/16)` | **unknown** |

A new `a` (e.g. `⅕`, `⅛`) requires a mechanism that produces `₂F₁(a,1−a;1;½)` **without**
reducing to `K`. The value itself is no harder to *state* — Gauss's second theorem gives it
to 50 digits — the difficulty is entirely one of *construction*. Per §1–§2, none of the
current primitives supplies it: the elliptic machinery stops at the four Schwarz
signatures, and the non-elliptic source (H6) has the wrong parameters and wrong argument
range. Note that `Γ(3/5)Γ(9/10)` (a `= ⅕`) and `Γ(9/16)Γ(15/16)` (a `= ⅛`) are *new*
against `Gamma.lean`'s denominator-24 family (`9/16 = 13.5/24`, `15/16 = 22.5/24`).

### 2.6 Q2 verdict

The correspondence is clean and verified; the frontier is exactly the Schwarz list
`{½,⅓,¼,⅙}`. H6 does not cross it. B1's last row remains **open and blocked** by the
current primitives.

---

## 3. Q3 — B6: hyperelliptic periods of `y² = 1+x^m`, `m = 6, 8, 10`

### 3.1 The complete first-kind periods **[CL]** + **[NC 40]**

For `y² = 1+x^m` the holomorphic differentials are `x^{k}dx/y`, `k = 0,…,m−2`. With
`p = k+1`, the substitution `u = x^m` gives

```
∫₀^∞ x^{p−1} / √(1+x^m) dx = (1/m) B(p/m, ½ − p/m),   1 ≤ p ≤ m/2 − 1.
```

`R1-q3` (A) verifies this to 40 digits for every admissible `p` at `m = 6, 8, 10`
(deviations `0` or `< 2.3·10^{-41}`).

### 3.2 Which of these are new Γ products **[NC 40]**

| `m` | periods `B(p/m,½−p/m)/m` | Γ arguments | denominators |
|---|---|---|---|
| 6 | `B(1/6,1/3)/6` | `Γ(1/6)Γ(1/3)` | 6, 3 — **have** |
| 8 | `B(1/8,3/8)/8` | `Γ(1/8)Γ(3/8)` | 8 — **have** |
| 8 | `B(1/4,1/4)/8` | `Γ(1/4)²` | 4 — **have** |
| 10 | `B(1/10,2/5)/10` | `Γ(1/10)Γ(2/5)` | 10, 5 — **NEW** |
| 10 | `B(1/5,3/10)/10` | `Γ(1/5)Γ(3/10)` | 5, 10 — **NEW** |

`Gamma.lean` reaches `Γ(k/24)`, `k ∈ ℤ`, i.e. arguments `1/24,2/24,…`; the m=6 and m=8
arguments are integer multiples of `1/24`, but `1/10 = 2.4/24`, `1/5 = 4.8/24`,
`3/10 = 7.2/24`, `2/5 = 9.6/24` are **not**. So **`m = 10` is the one place a genuinely
new Γ product (denominator 5 and 10) could appear.** Numerically
`B(1/10,2/5)/10 = 1.1905798216203709653197821695`, `B(1/5,3/10)/10 = 0.7748481388736765147810976916`.

### 3.3 Why no drawable construction closes them **[SY]** + **[NC]**

Identical to §1.6 and stated here for the record:

* the arclength is `∫√(1+x^m)dx` (second kind), which diverges at `x = ∞`;
* the Beta value is the first-kind integral `∫dx/√(1+x^m)` (a different period);
* `arc_length` integrates over a bounded interval of a *finite* arc with P-constructible
  endpoints, so it can never take `X = ∞`;
* no closed drawable curve has genus ≥ 2 (`R1-q3` (D));
* genus `g` has `g` holomorphic periods, so the genus-1 IBP reduction (`Basic.lean:3870`)
  has no `g ≥ 2` analogue.

### 3.4 Loopholes, explicitly

1. **Coincidence.** A finite `G(X)` could in principle equal a Beta value at some special
   algebraic `X`. No identity or mechanism that produces such an `X` was found, and
   `G(X)` is a strictly increasing continuous function of `X` (it is an integral of a
   positive density), so an equality would be a single isolated `X`; the primitive offers
   no way to *select* it.
2. **New primitive.** A closed genus-2 constructible curve, or an arc carrying the
   first-kind differential `dx/√(1+x^m)` (e.g. via a parametric curve whose `speed`
   equals `1/√(1+x^m)`, i.e. `ds = dx/y`), would close the period. Note that a real
   parametrization of such an arc requires `x'(t)² + y'(t)² = 1/(1+x(t)^m)`, which is
   non-algebraic for `m>0` unless the curve is not a graph — this is *not* currently a
   primitive.
3. **Bootstrap.** `arc_of_length` + `inter_x/inter_y` only rearrange known
   P-constructible lengths; they do not manufacture a first-kind complete period.
4. **Analytic continuation.** Not a primitive; the plan's §3 junk-value trap forbids
   stepping outside `|z|<1` ad hoc.
5. **Complex/other cycles.** The complex cycles of `y²=1+x^m` have imaginary periods; only
   real primitives exist.

### 3.5 Q3 verdict

**No complete hyperelliptic period `B(i/m,j/m)` is closable with the current primitives.**
The prize if it were closable is the `m = 10` product `Γ(1/10)Γ(2/5)` (new denominator 5
and 10). The obstruction is not merely "the graph is unbounded": it is that the arclength
is the **second-kind** differential, which has no finite complete value, while the Beta
value is **first-kind**.

---

## 4. The strongest candidate for a new drawable construction (with numeric evidence)

**Target.** The `m = 10` first-kind period

```
(1/10) B(1/10, 2/5) = Γ(1/10) Γ(2/5) / (10 √π) = 1.1905798216203709653197821695…
```

would make `Γ(1/10)Γ(2/5)` (hence a Γ product at denominators 5 and 10) P-constructible.
**Evidence that it is new** (`R1-q3` (B)): the arguments `1/10, 2/5` are not of the form
`k/24` (`1/10 = 2.4/24`, `2/5 = 9.6/24`), so neither `Γ` is in the `Gamma.lean`
denominator-24 family. **Evidence of the obstruction** (`R1-q3` (C),(F)): the drawable
arc `y = x^6` from `(0,0)` has `G(X) = ∫₀^X √(1+x^{10})dx`, which is a second-kind
incomplete period; it takes the values `0.5000, 0.9137, 1.0409, 1.4302` at
`X = 0.5,0.9,1.0,1.2` and grows like `X^6/6`, never equalling the Beta value `1.19058`.

**The missing piece, precisely.** A primitive that lays a *first-kind* hyperelliptic
differential along a bounded arc — e.g. a parametric curve `γ` with `speed γ(t) = 1/√(1+x(t)^m)`
— would close the period. Among the current six base curves, none has a length density of
this shape (the graph density is `√(1+Cx^m)`, the Bézier density is `√(quartic)`), and no
closed curve has genus ≥ 2.

**Runner-up (B1, `a = ⅕`).** `₂F₁(1/5,4/5;1;½) = 1.1137746646208464520265199… =
√π/(Γ(3/5)Γ(9/10))` (`R1-q2` (1), 50 digits). Also new (denominators 5 and 10), but
reaching it needs an entirely new transcendental mechanism outside the Schwarz list, which
is a taller order than the "close a period" gap above.

**Bonus probe (speculative, [SP]).** A CM/Chowla–Selberg route to `Γ(1/5)` via the
elliptic primitive was tested: `K(τ)` at `τ = i√5` (discriminant −20) is
`1.5763903948025924763237575552608632…`, but no algebraic relation with
coefficients `≤ 10^6` and degree `≤ 6` to products of `Γ(k/5)` or `Γ(k/20)` exists
(`R1-q4`). The method is validated on `d = −4` (`K(i)·4√π/Γ(1/4)² = 1` exactly, residual
`1.6·10^{-61}`) and `d = −3` (`K(k₃) = 3^{1/4}Γ(1/3)³/(2^{7/3}π)`, residual `1.6·10^{-61}`).
This does **not** establish that `Γ(1/5)` is out of reach of the elliptic machinery — only
that the elementary `Γ(k/5)`/`Γ(k/20)` guess fails; a full Chowla–Selberg computation
(which gives Γ-products with exponents beyond ±1) is open.

---

## 5. Label ledger

| statement | label |
|---|---|
| V4 / density formula (§1.1–1.2) | [SY] + [NC 45] |
| piece `= G(X)−G(x₀)`, `x₀>0` (§1.2) | [SY] (definition of the primitive) + [NC 32] |
| integer `b` reaches origin via `poly_graph` (§1.3) | [SY] + [NC 45] |
| density-sharing graph is a power law (§1.4) | [SY] + [NC 45] |
| offset density ≠ power-law (§1.5) | [SY] + [NC 45] |
| Bézier density quartic / genus 1; poly_graph genus up to 4 (§1.6, §3.3) | [SY] + [NC 14] |
| first-kind period `= (1/m)B(p/m,½−p/m)` (§1.6, §3.1) | [CL] + [NC 40] |
| second-kind arclength diverges (§1.6, §3.3) | [SY] + [NC 22] |
| genus-1 IBP has no `g≥2` analogue (§1.6) | [CL] (Riemann surface theory) |
| Gauss's second theorem (§2.1) | [CL] + [NC 50] |
| V6 at `z=½`, V7 at `z=1/5` (§2.2) | [CL] + [NC 50] |
| four Schwarz signatures are the reducible ones (§2.2) | [CL] |
| H6/quadratic parameter algebra (§2.3) | [SY] + [NC 50] (Euler transform); genus-mismatch heuristic [SP] |
| Bailey `z=½` formula (§2.4) | [NC 50] over 172 pairs (attribution [SP]) |
| m=10 Γ arguments are new (§3.2) | [NC 40] (arithmetic) |
| CM/Chowla–Selberg probe (§4) | [SP] (method validated on `d=−4`, [NC 50]) |

No `sorry`, no Lean file touched.

Scripts: `archived files/hypergeometric-scripts/R1-q1-origin-complete-period.py`,
`R1-q2-b1-gauss-second.py`, `R1-q3-hyperelliptic-periods.py`, `R1-q4-newgamma-cm.py`.
