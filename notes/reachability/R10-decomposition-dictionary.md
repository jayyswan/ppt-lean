# R10 — the Route-I decomposition dictionary

**Stream:** R10 of `notes/reachability/PLAN-routes.md` (waves 1–2, math positive).
**Deliverable:** this file. Research only: **no `.lean` edit, no `lake` command, no commit.**
**Status:** first catalogue. Positive constructions are stated under A (R12 §2.5), but every one
below is B-legal (B0 shape data, affine value), so it is also a B-claim. The negative list is B.
**Sources read:** `PLAN-routes.md` §0–§3 (R10 section), `R12-convention.md` §0–§3, `R7-dzero.md`,
`R8-missing-curve-audit.md` §1–§3, `R3-separation.md` §2–§3, `R5-named.md` §0–§1,
`R9-singularity-spectrum.md` §0–§1, `Pptc/Defs.lean`, `Pptc/Basic.lean`
(`linearMap_PConstructibleCurve`).

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**.
**Backend:** Wolfram Language MCP, 25–60 digit working precision; cells in §9. No Python.

---

## 0. Verdicts

1. **Eight graph-function entries, plus affine/`restrict` closure.** The catalogue is: (E1)
   exp-drift, the R7 family; (E2) lines; (E3) polynomial graphs; (E4) power laws, including
   negative exponents; (E5) log-drift, the other orientation of `exp_two`; (E6) the offset of the
   exponential, which brings the `√(1+z²)`-type algebraic term and one log point; (E7) sine shears;
   (E8) conic branches. Every entry has an exact `g(u)` or `h(x)` and a stated asymptotic type
   (§1). All are built from `Defs` constructors without `arc_of_length`.

2. **The `d=0` parabola is the first instance of the first entry, E1, with
   `(k,A,B)=(2,1/8,1/4)` and `(−2,1/8,−1/4)`.** It is exactly R7's construction, not a new one:
   the two summands are affine images of `exp_two`, and the family is one `inter_x` at output
   depth 1. The restatement in §2 checks the matrices against R7. [Proof, R7; rechecked Wolfram]

3. **Hits, all at output depth 1:** the `d=0` parabola; every finite exponential sum of at most
   **two** distinct rates (plus linear drift); every trig polynomial of degree ≤2 (plus linear
   drift); every branch of a conic, in particular algebraic functions of degree ≤2 (the explicit
   `√(1+u²)` split is in §5); every rational power law `a u^b`, including `b<0`; and the
   clothoid's `a√(2ψ)` as a power law. Constructions are in §§2–5 and §8.

4. **Misses in the two-summand catalogue:** three distinct exponential rates, trig polynomials of
   degree ≥3, and mixed sums with ≥3 independent atoms. The invariant is **atom count** — one
   exponential rate or one trig frequency per catalogue graph function, so a difference has at
   most two. This is a **[Heuristic]** classification of the reachable class, not a theorem; the
   constructions could be broken by a reachable curve carrying two rates. The named rows that
   *are* excluded have separate proofs (§6).

5. **The general pattern.** A difference of two catalogue graph functions is a sum of at most two
   generators. R7's example is the **odd part** of one generator: if `g` is drawable, then
   `g(u) − g(−u)` is a graph difference, and so is the even part
   `g(u) + g(−u) = g(u) − (−g(−u))`. This gives `sinh(ku)`, `cosh(ku)`, R7's two-rate odd
   function, and the sine/shear examples in one stroke (§7). [Proof sketch; the reflection is
   `scale_x(−1)` and `scale_y(−1)`.]

6. **The R5 named rows are not graph differences** for the reasons already proved elsewhere:
   `tan x = λx` (`1/log`, R9), the gear involute, rhumb, beam continuous interpolation and Biot
   (infinite finite log points, R3/R8), the tractrix (`−ln|sin ψ|`, R3), the elastica
   (non-elementarity), and the `l=0` well (`δlogδ`, R9). The goat is a single target, not a
   family; the separatrix is an identity, not an equation; the `tan x = x` quartic route uses
   *other* missing curves. The negative list is §6.

7. **At least one hit is Lean-able in principle.** The `d=0` hit (H1) is the recommended first
   formalisation: the identity is `Real.sinh_eq` plus algebra, the uniqueness is
   `F₀' = cosh²u > 0`, and the construction is two `linearMap` images of `exp_two`, a
   `translate_y`, and one `inter_x`. The algebraic `√(1+u²)` hit (H4) is a second candidate.
   No Lean is attempted here.

8. **No Route-O claim changes.** Every hit is a cheaper depth-1 construction and a new `R` entry;
   it says nothing about the B1 span condition for `tan`, and nothing about the discrete beam
   spectra (R11/C). [Proof for each hit; the misses are marked as above.]

---

## 1. The graph-function catalogue

### 1.1 Convention

`u` is the **unknown**, `x` is the **value** (the family parameter). A **graph function** is
either

- `h(u)`: the ordinate of the curve at abscissa `u` (R7's orientation; the curve is
  `{(u,h(u))}`), or
- `g(u)`: the abscissa of the curve at ordinate `u` (the same class by the affine swap
  `(X,Y)↦(Y,X)`).

R3 Definition 2.2 and Lemma 2.3 allow both. The **constructions in §§2–5 and §8 use the
`h`-orientation**: the curves are graphs over the abscissa, the value enters as
`translate_y(C₂,x)`, and the intersection gives `x = h₁(u) − h₂(u)`. This is exactly R7's
convention. In the `g`-orientation the value would enter as `translate_x(C₂,x)`; the identity is
the same after swapping the axes, and the catalogue table uses whichever form is natural for the
entry. In the propositions below, `g_i` is a generic symbol for a graph function; where the
construction is `h`-orientation (all of §§2–5 and §8), read `g_i` as `h_i`.

All entries are built **without `arc_of_length`**. `depth` in the catalogue table is **curve depth**
(R3 Definition 4.1: base curves 0; affine, `restrict`, translations and arithmetic free; `offset`
+1); a readout (`inter_x`/`box`) adds 1, and the hit tables below quote the output depth.

### 1.2 The catalogue

| id | `Defs`-level curve | exact graph function (orientation) | asymptotic type | depth |
|---|---|---|---|---|
| **E1** | `exp_two` → `scale_x(ln2/k)` → `linearMap` | `h(u)=A e^{ku}+B u+C`, `k∈ℚ\{0}` (`g` is the swap) | exponential at the `k`-end, linear at the other | 0 |
| **E2** | `poly_graph` degree 1 + affine | `h(u)=αu+β` (or the `g`-swap) | linear | 0 |
| **E3** | `poly_graph p`, `p∈ℚ[X]`, `deg p≤6` | `h(x)=p(x)`; on a monotone branch `g=p⁻¹` | polynomial; algebraic `u^{1/n}` | 0 |
| **E4** | `power_law a b`, `a,b∈ℚ` | `h(x)=a x^b`; `g(u)=(u/a)^{1/b}` | power `u^{1/b}`; pole if `b<0` or `1/b<0` | 0 |
| **E5** | `exp_two` → `linearMap` | `g(u)=A log u+B u+C` (natural `g`; the `h`-form is the inverse) | linear with a log; log point at `u=0` | 0 |
| **E6** | `offset` of `(t,e^t)` | `g_d(u)=log z−u z+z²`, `u=z+d/√(1+z²)` (natural `g`) | `log u−d+O(1/u²)`; log point at `u=d` | 1 |
| **E7** | `sine` → `linearMap` → translations | `h(u)=αu+β sin(ωu+φ)+γ` (`g` is the swap) | linear plus bounded oscillation | 0 |
| **E8** | `poly_graph` / `power_law` / `ellipse` + affine/`restrict` | conic branch `h(u)=a u²+bu+c`, or `αu+β+γ√(q(u))`, or a bounded ellipse arc | quadratic; linear plus `√`; bounded | 0 |
| **E9** | affine/`restrict` closure of E1–E8 | same class | rescaled, ends possibly swapped | unchanged |

E1 is the R7 family; the `d=0` parabola is the first instance. E9 is not a new formula: it records
that every affine image and every restriction of an entry is again drawable (R3 §1.3), and that the
parameters may be any P-constructible numbers, not only rationals, whenever the construction uses
`scale_x`/`scale_y`/`translate`/`linearMap`.

### 1.3 The entries in detail

**E1 (exp-drift, the R7 family).** Start from `exp_two = {(t,2^t)}`. Scale the abscissa by
`ln2/k`: `{( (ln2/k)t, 2^t )} = {(τ, e^{kτ})}` with `τ=(ln2/k)t`. Apply the linear map
`(a,b,c,d)=(1,0,B,A)`, i.e. `(X,Y) ↦ (X, B X + A Y)`:
```
(τ, e^{kτ}) ↦ (τ, Bτ + A e^{kτ}) = (u, h(u)) .
```
Thus `h(u)=A e^{ku}+B u`. Adding `C` is a `translate_y` (a vertical shift of the graph). For
`k<0` the scale `ln2/k` is negative, which `scale_x` allows. For `k=0` the entry degenerates to
E2. This is exactly R7's curve with `(k,A,B)=(2,1/8,1/4)` and `(−2,1/8,−1/4)`: R7's matrices
`(ln2/2,0,ln2/8,1/8)` and `(−ln2/2,0,ln2/8,1/8)` are this construction after substituting
`τ=(ln2/k)t`. The `g`-form `g(u)=A e^{ku}+B u` is the affine swap.

**E2 (lines).** `poly_graph` of a degree-1 rational polynomial, then `rotate`/`scale`/`translate`.
Both orientations are the same line. Asymptotic: linear at both ends.

**E3 (polynomial graphs).** `poly_graph p` is `{(x,p(x))}`. In the `h`-orientation it is
`h(x)=p(x)`. In the `g`-orientation, on a branch where `p` is monotone, `g=p⁻¹`, an algebraic
function (Puiseux at the critical points, `u^{1/n}` at infinity). `poly_graph` allows degree ≤6
and rational coefficients; affine images extend the coefficient set for the low-degree targets
used here (a quadratic has enough free scaling/translation parameters to fit any P-constructible
coefficients). The target families in this note are at most quadratic, so this is not a
restriction in practice.

**E4 (power laws).** `power_law a b` is `{(x,a x^b): x>0}` (and the origin when `b>0`; the origin
is omitted when `b≤0`, per the constructor). In the `h`-orientation, `h(x)=a x^b`. In the
`g`-orientation, `g(u)=(u/a)^{1/b}` on a branch. Asymptotic: `u^{1/b}`; a negative exponent gives
a pole at `u=0` and an open end at the origin, exactly the `power_law` convention. The `y=1/x`
case (`a=1,b=−1`) is the rectangular hyperbola used in H4.

**E5 (log-drift).** Apply `linearMap(A ln2, B d, 0, d)` with `d≠0` to `(t,2^t)`:
```
(t,2^t) ↦ (A ln2·t + B d·2^t, d·2^t) .
```
Let `u=d·2^t`; then `t=log₂(u/d)` and the abscissa is
`A ln2·log₂(u/d)+B u = A log(u/d)+B u`. So `g(u)=A log u+B u+const`. Asymptotic: `B u` dominates
as `u→∞`; `A log u→−∞` as `u→0⁺`, a log point at `0`. This is the second orientation of the same
`exp_two` curve; it is the source of the `log` summands in R9's `β=0` case.

**E6 (offset of the exponential).** Take `(t,e^t)`, which is `scale_x(ln2)` applied to `exp_two`,
and offset by `d` (R3 §1.5):
```
P_d(t) = ( t − d z/√(1+z²),  z + d/√(1+z²) ),        z=e^t .
```
Put `u=y=z+d/√(1+z²)`. Then `d/√(1+z²)=u−z`, so
```
g_d(u) = x = log z − d z/√(1+z²) = log z − z(u−z) = log z − u z + z² ,
```
where `z=z(u)` solves `u=z+d/√(1+z²)`, equivalently the quartic `(u−z)²(1+z²)=d²`. This is the
entry that brings the `√(1+z²)`-type algebraic term. Asymptotic: `z=u−d/u+O(u⁻³)`, hence
`g_d(u)=log u−d+O(1/u²)`. At `z→0⁺`, `u→d` and `g_d→−∞`: one finite log point at `u=d`. Depth 1
(the `offset` step). The numerical check is in §9 cell 4. `d=0` degenerates to `(t,e^t)`, whose
graph function is `log u`, a special case of E5.

**E7 (sine shears).** Start from `sine = {(t,sin t)}`. The linear map
`(a,b,c,d)=(1/ω, 0, α/ω, β)` gives
```
(t,sin t) ↦ ( t/ω,  (α/ω)t + β sin t ) .
```
Translate the abscissa by `−φ/ω`, so the new abscissa is `u=(t−φ)/ω`, i.e. `t=ωu+φ`; translate
the ordinate by `γ−αφ/ω`. The result is `{(u, αu+β sin(ωu+φ)+γ)}`, i.e.
`h(u)=αu+β sin(ωu+φ)+γ` (the `h`-orientation, matching R7). Asymptotic: linear drift plus a
bounded oscillation. `α=0` gives the pure sine/cosine graphs; a phase `φ=π/2` turns `sin` into
`cos`. The shear `x+sin x` is the case `α=1,β=1,ω=1,φ=0`.

**E8 (conic branches).** A branch of a conic is a graph function:
- parabola: after a rotation, `g(u)=a u²+bu+c`, from `poly_graph`;
- hyperbola: `g(u)=αu+β+γ√(q(u))` with `q` quadratic, an affine image of `power_law(1,−1)`
  (every nondegenerate hyperbola is an affine image of `xy=1`);
- ellipse: a bounded arc from `ellipse` plus `restrict`,
  `g(u)=c_x ± (w/2)√(1−((u−c_y)/(h/2))²)`.
The formulas are written in the orientation natural to each branch; the other orientation is the
affine swap, and the table records only the type. Asymptotic types: quadratic, linear plus `√`,
bounded. Depth 0. The explicit `√(1+u²)` branch is the hyperbola `y²−2uy=1`, which is
`linearMap(1/2,−1/2,1,0)` applied to `(w,1/w)`; see H4.

**E9 (closure).** Affine maps and `restrict` preserve every entry (R3 §1.3); they may swap the two
ends (a negative `scale_x`) and may restrict the domain to a monotone branch. `offset` of an entry
is a new entry of the same tower type (R3 §1.4); its graph function is algebraic in the entry's
parameter plus at most the log summand of E5/E6. This is why E6 is the prototype of every
"single offset" curve in the scope.

**Single offsets of the other entries.** If the base is algebraic (E2/E3/E4/E8), its offset is
algebraic in the same parameter: the normal correction is `d·y'/√(x'²+y'²)`, a square root of an
algebraic function, so the graph function stays algebraic (no log). If the base is E7 (trig), the
offset is algebraic in `(sin t,cos t)` plus the linear drift, so the graph function stays in the
trig tower (no log). If the base is E1/E5 (exp), the offset is E6 or its log-drift analogue: it
adds one algebraic correction and at most one log summand. Thus a **single offset** never leaves
the catalogue; it raises the curve depth to 1 (so a readout at depth 2), and the asymptotic type is
the base type plus an algebraic (or one-log) correction. Repeated offsets stay in the same tower
type but can nest square roots; they are not needed for any hit below. [Proof, R3 §1.4 + R9 §1.2]

---

## 2. Hit 1: the `d = 0` parabola (R7 restated)

### 2.1 The identity

> **Proposition 2.1 [Proof, R7; rechecked Wolfram].**
> ```
> F₀(u) := ¼ sinh 2u + u/2 = (e^{2u}/8 + u/4) − (e^{−2u}/8 − u/4) .
> ```

Set `g₁(u)=e^{2u}/8+u/4` and `g₂(u)=e^{−2u}/8−u/4`. Both are E1:
`g₁ = E1(k=2,A=1/8,B=1/4)`, `g₂ = E1(k=−2,A=1/8,B=−1/4)`. The expansion is immediate:
`(e^{2u}−e^{−2u})/8+u/2 = ¼ sinh 2u+u/2`. §9 cell 1 returns residual `0`.

### 2.2 The construction is exactly R7's

R7's matrices are
```
M₁ = ( ln2/2, 0,  ln2/8, 1/8) ,      M₂ = (−ln2/2, 0,  ln2/8, 1/8) ,
C₁ = M₁ '' exp_two ,                 C₂ = M₂ '' exp_two ,
u  = inter_x C₁ (translate_y C₂ x) .
```
These are E1's construction with the stated `(k,A,B)`: `M₁(t,2^t) = (u, e^{2u}/8+u/4)` and
`M₂(t,2^t) = (u, e^{−2u}/8−u/4)`. So the catalogue entry is not a new decomposition; it is R7's,
re-indexed. [Proof; the matrices are R7 §2.2 verbatim.]

### 2.3 Legality and depth

`F₀'(u)=cosh²u>0`, `F₀(0)=0`, `F₀(u)→±∞` as `u→±∞`; hence `F₀:ℝ→ℝ` is a strictly increasing
bijection and the intersection is unique for every P-constructible `x∈ℝ`. The construction is
`exp_two` (depth 0) → two `linearMap`s (free) → `translate_y` by `x` (free) → one `inter_x`
(depth 1). Output depth **1**. This is B0 shape data plus affine value, so it is B-legal as well
as A-legal.

### 2.4 Lean-ability

The formal shape is short:
```
F₀ u = Real.sinh (2*u)/4 + u/2
g₁ u = Real.exp (2*u)/8 + u/4
g₂ u = Real.exp (-(2*u))/8 - u/4
F₀_eq : ∀ u, F₀ u = g₁ u - g₂ u        -- Real.sinh_eq; ring
F₀_strictMono : StrictMono F₀          -- deriv F₀ = cosh² > 0
```
Then `inter_x` on `C₁ = M₁ '' exp_two` and `translate_y C₂ x`; `linearMap_PConstructibleCurve`
(Basic.lean) supplies the curve side, and the singleton-intersection hypothesis follows from
`F₀_strictMono` and `F₀_eq`. The only analytic input is `F₀' = cosh² > 0`; the rest is the exp
identity and set algebra. This is the recommended first Lean target.

---

## 3. Exponential targets

### 3.1 One and two rates: hits

> **Proposition 3.1 [Proof].** Let `k₁≠k₂` be rational and let
> `F(u)=A₁e^{k₁u}+A₂e^{k₂u}+B u+C`. Then `F=g₁−g₂` with
> ```
> g₁(u)=A₁e^{k₁u}+B₁u+c₁ ,      g₂(u)=−A₂e^{k₂u}+B₂u+c₂ ,
> B₁−B₂=B ,   c₁−c₂=C .
> ```
> Both `g_i` are E1, hence drawable graph functions. The construction has depth 1.

[Proof: expand; §9 cell 5 gives residual `0` with sample coefficients.] If `A₂=0` the target is a
single rate and `g₂` is a line; if `k₁=k₂` combine the coefficients first. If one rate is `0`, the
corresponding term is the linear drift and is absorbed in `B`.

**Defs-level.** For each `i`,
`C_i = translate_y (linearMap(1,0,B_i,A_i) '' (scale_x(ln2/k_i) '' exp_two)) c_i`.
The second curve is translated vertically by `x`; `inter_x` returns
`u=F⁻¹(x)`. If `F` is not globally injective (opposite signs of `k_i` can make it non-monotone),
`restrict` to a branch on which it is; the target family is defined on that branch anyway.

### 3.2 Three rates: a miss in the catalogue

> **Claim 3.2 [Heuristic].** No decomposition `F=g₁−g₂` with both `g_i` in the catalogue E1–E9
> is known for a sum of **three** distinct exponential rates. The invariant is the **number of
> exponential rates at an end**: each catalogue graph function carries at most one rate, so a
> difference carries at most two.

The reason is structural. E1 carries one rate. E2/E3/E4/E8 are algebraic (zero rates). E5 is the
other orientation of E1: it carries the same single rate, seen as a log in the graph function. E6
is E5 plus an algebraic correction, still one rate. E7
is trig (no real exponential rate). E9 preserves the count. A difference therefore has at most two
distinct rates. For `F(u)=A₁e^{k₁u}+A₂e^{k₂u}+A₃e^{k₃u}+Bu+C` with three distinct `k_i`, matching
the three independent exponentials would require three summands. **This is not a theorem about all
tower curves**: a reachable curve with two rates in one coordinate would break it. It is a
statement about the catalogue E1–E9 and is labelled accordingly. [Heuristic]

**What would break it.** A constructor that adds curves pointwise, or an offset/composition that
turns a single `z=e^{ku}` into a polynomial `z+z²` in the graph function. Neither is in `Defs`;
`offset` changes `A_i` algebraically but does not square `z`, and there is no curve-addition
constructor. If a future construction produces such a curve, Claim 3.2 is withdrawn and three-rate
sums become hits.

---

## 4. Trig targets

### 4.1 Degree ≤2: a hit

> **Proposition 4.1 [Proof].** Let
> `F(u)=c₀+a₁cos u+b₁sin u+a₂cos 2u+b₂sin 2u`. Then `F=g₁−g₂` with
> ```
> g₁(u)=c₀/2+a₁cos u+b₁sin u ,      g₂(u)=−c₀/2−a₂cos 2u−b₂sin 2u .
> ```
> Both are E7 (frequency 1 and frequency 2 respectively), hence drawable. Depth 1.

[Proof: expand; §9 cell 2 returns `0` symbolically.] Write each pair as a single phase-shifted sine:
`a_j cos(ju)+b_j sin(ju)=R_j sin(ju+φ_j)`. Then `g₁=c₀/2+R₁ sin(u+φ₁)` and
`g₂=−c₀/2−R₂ sin(2u+φ₂)`. The frequency-2 summand is E7 with `ω=2`; the construction is the E7
matrix `(1/ω,0,α/ω,β)` with `α=0, β=−R₂, ω=2`, plus the phase translation. If the target has a
linear term `αu`, put it on `g₁`: E7 allows a drift and one frequency, so
`F=αu+trig` is still a difference of two E7 functions (the linear term is free).

**Legality.** A degree-≤2 trig polynomial need not be injective on all of `ℝ`. The target family
is only defined on a branch where `F` is injective; `restrict` the curves to that window. For a
pure `sin`/`cos` (degree 1) a half-period window always exists; for degree 2 one chooses a
monotone branch (if the coefficient `a₂,b₂` is so large that no branch covers the desired range,
the construction solves the branch on which the target is posed, not a larger one). This is the
same legality caveat as R12 §2.3 condition 3.

### 4.2 Degree ≥3: a miss in the catalogue

> **Claim 4.2 [Heuristic].** A trig polynomial with three distinct frequencies (in particular
> degree ≥3) has no decomposition with two catalogue graph functions. The invariant is the
> **number of frequencies**: each E7 summand carries one, so a difference carries at most two.

Same status as Claim 3.2: a statement about E1–E9, not a theorem about all tower curves. A single
`sin` curve with a phase gives both `sin` and `cos` of **one** frequency; it does not give two
frequencies. A degree-2 polynomial uses exactly two summands (frequencies 1 and 2); a degree-3
needs a third. [Heuristic]

**Mixed sums.** A linear drift is free on either E7 summand, so `linear + one frequency` is a hit.
`linear + two frequencies + one exponential rate` has three atoms (two frequencies + one rate) and
is a miss in the catalogue; `linear + one frequency + one rate` is a hit (put the rate on one
summand and the frequency on the other; the drift on either). [Heuristic, same atom count.]

---

## 5. Algebraic targets

### 5.1 Conic branches: hits

Here "algebraic degree ≤2" means the defining polynomial has total degree ≤2, i.e. a branch of a
conic. Every branch of a conic is a graph function (E8), so the trivial decomposition `F=F−0`
already works, with `h₂` a line (the axis). Depth 1. The interesting point is that the split can
also be made with two **nonconstant** summands, which is what the dictionary records.

> **Proposition 5.1 [Proof].** `F(u)=√(1+u²)` is a difference of two E8 graph functions:
> ```
> h₁(u)=u+√(1+u²) ,      h₂(u)=u .
> ```
> `h₁` is the hyperbola branch `y²−2uy=1`, i.e.
> `C₁ = linearMap(1/2,−1/2,1,0) '' power_law(1,−1)`; `h₂` is the line `poly_graph(X)`.
> The construction is one `inter_x`, depth 1.

[Proof: `h₁−h₂=√(1+u²)`; §9 cell 3 returns `{0,0}`. The hyperbola check:
`(w,1/w) ↦ ((w−1/w)/2,w)`; with `w=u+√(1+u²)`, the abscissa is `u`. The numerical point
`w=2` gives `(3/4,2)` and `3/4+√(1+9/16)=2`, §9 cell 3.]

Here the curves are used in the `h`-orientation (graphs over the abscissa): `h₁(u)=u+√(1+u²)`,
`h₂(u)=u`; `translate_y` by `x` gives `h₁(u)=h₂(u)+x`, i.e. `√(1+u²)=x`. On the branch `u≥0`,
`x≥1`, the intersection is unique. For `x<1` there is no real point; the target's range is
`x≥1`, so that is correct. The conjugate branch `−√(1+u²)` is obtained by `scale_y(−1)`.

**General conic.** A quadratic polynomial is E3/E8; a hyperbola branch is an affine image of
`power_law(1,−1)`; an ellipse arc is `ellipse` plus `restrict`. The decomposition `F=F−0` is
always available, and a nonconstant split is obtained by writing `F=(F+L)−L` for any line `L`
(affine images of conics are still conics). In every case the depth is 1.

### 5.2 Power laws, including negative exponents: hits

> **Proposition 5.2 [Proof].** Let `F(u)=a u^b` with `a,b∈ℚ`, `a≠0`, `b≠0`, on `u>0`. Then
> `F=h₁−h₂` with `h₁(u)=a u^b` (E4, `power_law a b` in the h-orientation) and `h₂(u)=0` (the line
> `poly_graph(0)`). Depth 1.

`power_law(a,b)` is already `{(u,a u^b)}`, so no swap is needed. If `a` is P-constructible but not
rational, use `scale_y(a) '' power_law(1,b)` (the constructor's rational `a` is only the base case).
The second curve is the `x`-axis; `translate_y` by
`x` gives the horizontal line at height `x`; `inter_x` returns `u=(x/a)^{1/b}`. For `b<0` the
curve is open at `u=0` (the `power_law` convention) and `F` has a pole there; restrict to `u>0`
and note the omitted origin is not part of the family. For `b=0` the curve is the horizontal ray
`y=a` (`x>0`), and the target is constant; exclude it (the target is not injective). Depth 1.

**Clothoid.** The clothoid's `d=0` family is `x=a√(2ψ)`, i.e. `F(ψ)=a√2·ψ^{1/2}`: E4 with
`b=1/2`. This is a hit, though the family is already `R` by the radical collapse of R5 §2.4. The
same remark applies to any `aψ^b` target that is already solvable by radicals; the dictionary
records the cheaper Route-I construction, not a new number.

**Neile `d=0` is a near-miss.** `F(u)=⅓cosh³u` expands as
`(e^{3u}+3e^u+3e^{−u}+e^{−3u})/24`, i.e. **four** exponential rates. It is not a difference of
two catalogue graph functions (atom count 4 > 2). But Neile is already `R` by the `arccos`
collapse of R5 §2.4, so this miss costs nothing. [Heuristic for the graph-difference part;
`R` for the target.]

---

## 6. The R5 named rows: the negative list

The table records, for each named row, the target form, the obstruction, and the invariant. The
row numbers are R5's. Convention B is in force for the exclusions (R12 §2.5). For the rows already
settled in R3/R8/R9, the proof is cited rather than repeated.

| # | target | target form in `u` | decomposition? | obstruction / invariant | status |
|---|---|---|---|---|---|
| 6 | `tan x = λx` | `sinh u − λ gd u = λkπ`; or `λ=h(u)=sinh u/(gd u+kπ)` | **no** | uniform-in-`λ`: `1/log` (R9); fixed-`λ` continuous interpolation: infinite log (R3); fixed-`λ` discrete-in-`k`: C/R11 | **I-excluded (B)** for the continuous family |
| 7 | gear involute `tan α−α=k` | `sinh u − gd u = k` | **no** | infinite finite log points from `gd` (R3 Lemma 3.2/3.3) | **I-excluded** |
| 8 | cantilever beam | `x + gd x = (2m+1)π` | continuous interpolation **no**; discrete [Open] | `gd` infinite log for the interval; discrete needs C/R11 arithmetic | **mixed** |
| 9 | clamped–clamped | `x − gd x = 2mπ` (or `x+gd x`) | as row 8 | as row 8 | **mixed** |
| 10 | rhumb (fixed `k`) | `u − k gd u = c` | **no** | `gd` infinite log (R3) | **I-excluded** |
| 13 | tractrix | `−ln|sin ψ| − dψ = x` | **no** | `−ln|sin ψ|` has log points at every `ψ=kπ` (R3) | **I-excluded** |
| 14 | Euler elastica | `F(ψ/2|m) − dψ = x` | **no** | non-elementary elliptic integral (R8 §3.5) | **I-excluded** [standard] |
| 15 | spherical well `l=0` | algebraic relation between `sinh u` and `gd u` | **no** | `δlogδ` at `iπ(m+½)` (R9) | **I-excluded (B)** |
| 16 | Biot `x tan x=Bi` | `sinh u·(gd u+kπ)=Bi` | **no** | infinite finite log points (product linear in `gd`; R8) | **I-excluded** |
| 12 | goat | `tan β−β=(π/2)sec β` | not a family | single target S; `tan`/`sec` not reachable graph functions; legality open | **S-open** |
| 11 | separatrix | `θ=gd t` | identity | not an equation; pointwise `R` | **R** |
| 19 | `tan x=x` quartic | quartic/involute/quadratrix route | other curves | needs a missing curve outside E1–E9; not excluded | **open, different class** |
| 4 | Neile `d=0` | `x=⅓cosh³u` (see §5.2) | **no** (4 rates) | atom count, but already `R` | **R** |
| 5 | clothoid `d=0` | `a√(2ψ)=x` | **yes** | E4 power law | **R** |

### 6.1 `tan x = λx` (row 6)

For fixed `λ` the function `F(u)=sinh u−λ gd u` has infinitely many finite log branch points at
`u=iπ(m+½)` (`gd u=2 arctan(e^u)−π/2`, R3 Lemma 3.2), so it is **not** a difference of two drawable
graph functions: the continuous interpolation in `u` is excluded. The uniform-in-`λ` form is
`h(u)=sinh u/(gd u+kπ)`, which has a `1/log` singularity at each `iπ(m+½)` (R9 §0.2); R9 excludes
the continuous-in-`λ` family. The fixed-`λ` discrete-in-`k` spectrum is **C/R11**, not covered by
either function argument. The row's `I-excluded (B)` verdict refers to the continuous-in-`λ`
family; the Route-O catenary sufficiency is untouched.

### 6.2 Gear involute, rhumb, beams, Biot

The involute is the `λ=1` slice of the same `gd` equation; the rhumb is `u−k gd u`; the beam
continuous interpolation is `x±gd x`; Biot is `sinh u·(gd u+kπ)`. Each contains `gd` linearly, so
each has infinitely many finite log branch points. The log coefficient is a nonzero constant, so R3's
finite-log count applies. For the beams the **discrete**
spectrum `c=(2m+1)π` is not covered: R3's argument needs an interval, and a difference of graph
functions can pass through infinitely many prescribed points (the `sin` example of R12 §0.7).
That is R11/C's arithmetic question, not a graph-difference question. The natural candidate
`x+π/2` minus a `gd`-correction fails because `gd` is not in the class; no other candidate is
known. [Proof for the continuous interpolation; Open for the discrete spectrum.]

### 6.3 Tractrix, elastica, `l=0`, Biot

The tractrix has `−ln|sin ψ|`, which has a log branch point at every `ψ=kπ`; infinitely many
finite log points, so no graph difference (R3/R8). The elastica's incomplete elliptic integral is
non-elementary; a graph function of a tower curve without `arc_of_length` is elementary (R8 §3.5,
standard non-elementarity). The `l=0` well reduces to `coth u·gd u ~ −i ζ log ζ` at
`u₀=iπ(m+½)`, a `δlogδ` singularity excluded by R9's classification. Biot's product is linear in
`gd`, so it has infinitely many finite log points. All four are negative under B; the tractrix,
Biot, `l=0` and elastica are B-only (R12 §4.3), while the involute and rhumb are A-robust (real log
monodromy).

### 6.4 Goat, separatrix, quartic

The goat is a **single target**, not a family: Route I's uniformity question does not apply. If one
tries to read it as a graph difference, `tan β` and `sec β` are not graph functions of any E1–E9
curve (there is no pointwise-combination constructor; `sine` gives `sin`/`cos`, not `tan` or
`sec`). The Route-O construction is formal but has a pole/fold; its legality is R13's question.
[Open] The separatrix `θ=gd t` is an identity, solved pointwise by `arctan`/`exp`; it is `R`, not
an equation family. The `tan x=x` quartic/involute/quadratrix routes are Route-I constructions
with **other** missing curves (R5 §2.18); they are outside the catalogue E1–E9 and are not
excluded by anything here.

---

## 7. The general pattern: atom count and reflection

### 7.1 Atom count

Call an **atom** one of: an algebraic generator (E2/E3/E4/E8); an exp generator, either the
exp-drift E1 (rate `k`) or its log orientation E5; an offset correction of a single-rate curve
(E6); or one trig frequency `ω` (E7). A catalogue
graph function carries at most one atom; a difference of two carries at most two. This is the
pattern behind the hits and misses:

| target | atoms | verdict |
|---|---|---|
| quadratic polynomial | 0 (algebraic) | hit (E3/E8; `F−0`) |
| conic branch / `√(quadratic)` | 0 (algebraic) | hit (E8; H4) |
| `a u^b` | 0 (algebraic) | hit (E4; H5) |
| `A e^{ku}+Bu` | 1 rate | hit (E1) |
| `A₁e^{k₁u}+A₂e^{k₂u}+Bu` | 2 rates | hit (H2) |
| three distinct rates | 3 rates | miss [Heuristic] |
| `c₀+a₁cos u+b₁sin u` | 1 frequency | hit (E7) |
| degree-2 trig | 2 frequencies | hit (H3) |
| degree-3 trig | 3 frequencies | miss [Heuristic] |
| `linear + 1 frequency + 1 rate` | 2 atoms | hit |
| `linear + 2 frequencies + 1 rate` | 3 atoms | miss [Heuristic] |

The distinction between polynomials and exponential sums is important: a polynomial is a **base
family** (`poly_graph`), so its many monomials do not count as many atoms; an exponential sum is
not a base family, so its rates do count. This is why `u⁶` is a hit but `e^{u}+e^{2u}+e^{3u}` is a
miss in the two-summand catalogue.

**Invariant glossary.** Each miss in this note names one of four invariants:
- **growth** — polynomial vs exponential vs bounded oscillation (separates E1/E3/E7, and the
  rate-count miss is its sharp form at an end);
- **singularity type** — finite log, `1/log`, `δlogδ`, elliptic (the negative list of §6);
- **parity** — the reflection/odd-even structure of §7.2 (R7 is the odd part of one generator);
- **number of rates/frequencies** — the atom count above.
The first three are R3/R9 invariants (with R12's A/B caveats); the fourth is the catalogue's
positive/negative boundary and is the one labelled **[Heuristic]** when used as a miss.

### 7.2 The reflection trick

For any drawable graph function `g`, the reflected function `u↦g(−u)` is drawable: `scale_x(−1)`
reflects the curve in the ordinate axis, and `scale_y(−1)` reflects it in the abscissa axis. Hence
for any P-constructible `a,b`,
```
F(u) = a g(u) + b g(−u) = g₁(u) − g₂(u) ,
g₁ = a g ,      g₂ = −b g(−u) ,
```
is a graph difference of two drawable graph functions. In particular the odd and even parts of `g`
are graph differences:
```
½(g(u) − g(−u)) = ½g(u) − ½g(−u) ,
½(g(u) + g(−u)) = ½g(u) − (−½g(−u)) .
```
R7 is the odd part of `g(u)=e^{2u}/8+u/4`: `g(−u)=e^{−2u}/8−u/4`, and
`g(u)−g(−u)=¼sinh 2u+u/2`. The same trick gives
```
sinh(ku) = ½e^{ku} − ½e^{−ku} ,      cosh(ku) = ½e^{ku} − (−½e^{−ku}) ,
```
both hits with two E1 summands (rates `k` and `−k`); §9 cell 6 returns `{0,0}`. For the sine
family, `sin(ωu)` is already E7; `cos(ωu)=sin(ωu+π/2)` is an E7 translate; and any
`αu+β sin(ωu+φ)` is E7, so its reflection span is again a graph difference. This is the precise
sense in which "the sine curve and its shears are the oscillatory examples": the shear is the
generator, and the reflection/translation produces the companion phase (`cos` from `sin`).

### 7.3 What the pattern does not cover

The reflection trick produces sums of a function and its reflection, not arbitrary two-generator
sums. The degree-2 trig hit uses two **different** frequencies, not a reflection; it is a
two-generator hit of the more general form `F=g₁−g₂` with independent `g_i`. The atom-count table
is the general bookkeeping; the reflection trick is the clean sufficient condition that explains
R7 and the sinh/cosh examples. Neither is a theorem about *all* tower curves: they classify the
catalogue E1–E9. [Heuristic for the classification; Proof for the constructions.]

---

## 8. `Defs`-level constructions and output depth

All matrices are in R7's convention: `(a,b,c,d)` acts by `(X,Y)↦(aX+bY,cX+dY)`. `x` is the
P-constructible family parameter. `translate_y` by `x` is free (depth unchanged); `inter_x` adds 1.

### H1 — `d=0` parabola (depth 1)

```
C₁ = linearMap( ln2/2, 0,  ln2/8, 1/8) '' exp_two
C₂ = linearMap(−ln2/2, 0,  ln2/8, 1/8) '' exp_two
u  = inter_x C₁ (translate_y C₂ x)
```
`g₁=e^{2u}/8+u/4`, `g₂=e^{−2u}/8−u/4`, `g₁−g₂=F₀`. Unique for all `x∈ℝ`. **Depth 1.**

### H2 — one or two exponential rates (depth 1)

For each `i=1,2`:
```
E_i = scale_x(ln2/k_i) '' exp_two
C_i = translate_y (linearMap(1, 0, B_i, A_i) '' E_i) c_i
```
The first curve is `C₁`; the second is translated vertically by `x`:
```
u = inter_x C₁ (translate_y C₂ x)
```
`h₁−h₂=A₁e^{k₁u}−A₂e^{k₂u}+(B₁−B₂)u+(c₁−c₂)`. To represent the target
`F=F₁e^{k₁u}+F₂e^{k₂u}+Bu+C`, set `A₁=F₁`, `A₂=−F₂`, `B₁−B₂=B`, `c₁−c₂=C` (Prop. 3.1). If a rate
is absent, use a line for that summand. **Depth 1.**

### H3 — trig polynomial of degree ≤2 (depth 1)

For `j=1,2`, with `R_j` and `φ_j` the amplitude and phase of `a_j cos(ju)+b_j sin(ju)`, set
`α_j=0`, `β_1=R₁`, `β_2=−R₂`, `ω_j=j`, and
```
C_j = translate_y (translate_x (linearMap(1/ω_j, 0, α_j/ω_j, β_j) '' sine) (−φ_j/ω_j))
        (γ_j − α_j φ_j/ω_j)
```
with `γ₁=c₀/2`, `γ₂=−c₀/2`. Then `h_j(u)=γ_j+β_j sin(ω_j u+φ_j)` and
`h₁−h₂=F`. The outer `translate_y` by `x` is applied to `C₂`; `inter_x` returns `u` on a monotone
window. **Depth 1.**

### H4 — `√(1+u²)` (depth 1)

```
C₁ = linearMap(1/2, −1/2, 1, 0) '' power_law(1, −1)
C₂ = poly_graph(X)                         -- the line y = x
u  = inter_x C₁ (translate_y C₂ x)
```
`C₁={((w−1/w)/2,w)}`, so `h₁(u)=u+√(1+u²)`; `h₂(u)=u`; the intersection is
`h₁(u)=h₂(u)+x`, i.e. `√(1+u²)=x`. Unique on `u≥0`, `x≥1`. **Depth 1.**

### H5 — `a u^b` (depth 1)

```
C₁ = power_law(a, b)                              -- {(u, a u^b)}
C₂ = poly_graph(0)                                -- the x-axis, {(u,0)}
u  = inter_x C₁ (translate_y C₂ x)
```
The intersection is `a u^b=x`; unique on the monotone branch `u>0`. **Depth 1.** The clothoid is
`a'=a√2`, `b=1/2`.

### Depth summary

| hit | curves | active steps | output depth |
|---|---|---|---|
| H1 | two E1 | 2 `linearMap` + 1 `translate_y` + 1 `inter_x` | **1** |
| H2 | two E1 | `scale_x`/`linearMap` free + 1 `inter_x` | **1** |
| H3 | two E7 | `linearMap`/translations free + 1 `inter_x` | **1** |
| H4 | E8 + E2 | `linearMap` free + 1 `inter_x` | **1** |
| H5 | E4 + E2 | base curves free + 1 `inter_x` | **1** |
| E6-based target (if any) | E6 + E2 | 1 `offset` + 1 `inter_x` | **2** |

The last row is included for completeness: if a future target needs the offset-exp graph function
E6, the curve depth is 1 and the construction depth is 2, still below Route O's 3.

---

## 9. Wolfram cells

All values are Wolfram Language MCP evaluations. Residual `0` is exact (symbolic `Simplify`); the
numerical table uses 60-digit working precision and displays 20 digits. No Python.

| cell | check | result |
|---|---|---|
| 1 | `((E^(2u)/8+u/4) − (E^(−2u)/8−u/4)) − (Sinh[2u]/4+u/2)` | `0` |
| 2 | `(c₀/2+a₁Cos[u]+b₁Sin[u]) − (−c₀/2−a₂Cos[2u]−b₂Sin[2u]) − (c₀+a₁Cos[u]+b₁Sin[u]+a₂Cos[2u]+b₂Sin[2u])` | `0` |
| 3 | `((u+Sqrt[1+u²])−u)−Sqrt[1+u²]`; `((w−1/w)/2 /. w→u+Sqrt[1+u²])−u`; the point `w=2` | `{0,0}`; `{3/4,2,2}` |
| 4 | E6: solve `u=z+½/√(1+z²)` at `u=10,100,1000`; compare `log z−u z+z²` with `log u−½` | differences `−2.5·10⁻³`, `−2.5·10⁻⁵`, `−2.5·10⁻⁷` (the `O(1/u²)` term) |
| 5 | two-rate general identity with `(A₁,A₂,k₁,k₂,B₁,B₂,c₁,c₂,u)=(2,−3,½,5/2,7,1,4,−2,13/10)` | `0` |
| 6 | `(½e^{ku}−½e^{−ku})−sinh(ku)`; `(½e^{ku}−(−½e^{−ku}))−cosh(ku)` | `{0,0}` |

Cell 4 is the asymptotic check for E6: the graph function is `log u−d+O(1/u²)`, not `log u`; the
difference tends to zero like `1/u²`. Cell 3 also checks the hyperbola parametrisation used in H4.

---

## 10. Summary table

| target | family | decomposition or obstruction | depth | status |
|---|---|---|---|---|
| `d=0` parabola | continuous B0 | `(e^{2u}/8+u/4)−(e^{−2u}/8−u/4)` (E1, H1) | **1** | **R** [Proof, Wolfram] |
| one exponential rate | continuous | `F−0` (E1) | **1** | **R** |
| two exponential rates | continuous | one rate per summand (E1, H2) | **1** | **R** |
| three exponential rates | continuous | rate count 3 > 2 | — | **miss** [Heuristic] |
| trig degree ≤2 | continuous | frequencies 1 and 2 (E7, H3) | **1** | **R** |
| trig degree ≥3 | continuous | frequency count ≥3 | — | **miss** [Heuristic] |
| algebraic degree ≤2 | continuous | conic branch is E8; `√(1+u²)` split (H4) | **1** | **R** |
| power law `a u^b`, `b∈ℚ\{0}` | continuous | E4; `power_law` in h-orientation (H5) | **1** | **R** |
| clothoid `a√(2ψ)` | continuous | E4 with `b=1/2` | **1** | **R** (already R) |
| Neile `d=0` | continuous | `⅓cosh³u` has four rates | — | **R** (arccos collapse, not graph diff) |
| `tan x=λx` | hybrid B1×C | `1/log` / infinite log (R9) | — | **I-excluded (B)** |
| gear involute | continuous B0 | `gd` infinite log (R3) | — | **I-excluded** |
| beams (continuous) | continuous B0 | `gd` infinite log (R3) | — | **I-excluded**; discrete [Open] |
| rhumb | continuous B0 | `gd` infinite log (R3) | — | **I-excluded** |
| tractrix | continuous B0 | `−ln|sin ψ|` infinite log (R3) | — | **I-excluded** |
| elastica | continuous B0 | non-elementary (R8 §3.5) | — | **I-excluded** [standard] |
| Biot | continuous B0 | `gd` product infinite log (R8) | — | **I-excluded** |
| `l=0` well | continuous B0 | `δlogδ` (R9) | — | **I-excluded (B)** |
| goat | single S | not a family; `tan`/`sec` not reachable; legality | — | **S-open** |
| separatrix | single | identity `θ=gd t`, pointwise `R` | — | **R** |
| `tan x=x` quartic | single | other missing curves (R5 §2.18) | — | **open, different class** |

---

## 11. Open items

1. **Prove the atom-count classification.** The constructions are proofs; the claim that every
   reachable graph function (without `arc_of_length`) carries at most one exponential rate or one
   trig frequency is a **[Heuristic]** / **[Proof sketch]** based on R3's normal form and the
   absence of a pointwise-combination constructor. The missing lemma is: the algebraic functions
   `A_i` produced by iterated `offset`s of `exp_two` cannot turn `z=e^{ku}` into a polynomial
   `z+z²` in the graph function. If this is false, the three-rate and degree-3 trig misses become
   hits.
2. **Three-rate and degree-3 targets.** Either prove the atom-count invariant or find a reachable
   curve with two rates/frequencies. The reflection trick does not produce them; a new constructor
   (or a clever offset composition) would.
3. **Discrete beam spectra.** R3's log count is silent on a discrete set; the graph-difference
   question is R11/C. The natural `gd` candidate fails, but no arithmetic obstruction is proved
   here.
4. **Lean.** Formalise H1 first (§2.4). H4 is a second candidate: the identity is `ring`, the
   hyperbola is an affine image of `power_law`, and the uniqueness is monotonicity on `u≥0`. The
   remaining hits are algebraically easier but need the monotonicity/`restrict` bookkeeping.
5. **The goat.** The open question is legality (R13), not graph-difference existence; `tan`/`sec`
   are outside E1–E9, so a new curve would be needed even for a single-target intersection.
6. **The `tan x=x` quartic route.** Its quartic/involute/quadratrix curves are outside the
   catalogue; adding them is a separate missing-curve question, not a decomposition in E1–E9.
7. **E6 targets.** No named target in this note uses the offset-exp graph function; it is
   catalogued because it is the prototype of a "single offset" curve and the source of the
   `√(1+z²)` term. If a target needs it, the construction is depth 2, still cheaper than Route O.
8. **No Route-O claim changes.** The B1 span condition for `tan` (R12 §3.3) and the discrete
   spectra (R11) are untouched. The dictionary only adds depth-1 `R` entries and the negative
   list above.
