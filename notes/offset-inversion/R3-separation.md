# R3 — separation theorems: intersections, boxes, and the parabola family

**Stream:** R3 of `PLAN-offset-inversion.md`. **Deliverable:** this file.
**No `.lean` file was edited and no `lake` command was run.**

Sources read: `PLAN-offset-inversion.md` §0, §1, §R3; `notes/sheared-sine-intersections.md` §3b;
`notes/offset-inversion/R0-foundations.md`; `R1-whewell-base.md`; `R2-tower.md` (Q2, Q3);
`Pptc/Defs.lean` (constructors, lines 216–445); `Pptc/Offset.lean`; `Pptc/BoxOffset.lean`.

R2's rigidity theorem (`ρ = A + B sec²ψ` / `A + secψ`, i.e. "same solution for all `x`
⟺ parallel curves") is used as an **input** and is not re-derived here.

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. Every numerical value was
produced by **Wolfram Language** in the three evaluator cells reproduced in §6.

---

## 0. Verdicts

1. **Q1: the normal form is correct, and the plan's `offset` warning is a false alarm.**
   The offset of `(t, e^t)` in the constructor's own parameter is
   `(t − d e^t/√(1+e^{2t}), e^t + d/√(1+e^{2t})) = (αt + A₁(e^t), βt + A₂(e^t))` with
   `α = 1, β = 0, A₁(z) = −dz/√(1+z²), A₂(z) = z + d/√(1+z²)`, both algebraic. The `ln u`
   in the plan's warning appears only after the **reparametrisation** `u = e^t`, i.e.
   `t = ln u`; the normal form is stated in the inherited parameter and is closed under
   `offset` there. [Proof + Wolfram] See §1.5. The normal form is **necessary but not
   sufficient** for the separation: the catenary `(t, cosh t)` is of the exp form, exactly as
   R2 warned, so Q1 alone does not prove Q3. §1.6.

2. **Q2: a single intersection solves a *difference of two graph functions*; a single box
   solves a *piecewise-affine* function of `x`.** Precisely: write `g_C(u)` for the abscissa
   of a drawable curve `C` at ordinate `u` (a "graph function"). One intersection of `C₁, C₂`,
   with `x` entering only through P-constructible affine data, forces
   `F(u) = g_{C₁}(u) − g_{C₂}(u)` on an interval. A box of a tower curve with affine
   `x`-dependence gives a piecewise-affine function of `x`. The `S, κ, ψ` dictionary is in
   §2.4. [Proof]

3. **Q3: PROVED, and by a sharper invariant than §3b's.** The separation is *not* proved by
   accumulation of zeros (a continuous family has no accumulation); it is proved by
   **monodromy at finite logarithmic branch points**:
   - `F(u) = sinh(2u)/4 + u/2 − d·gd u = sinh(2u)/4 + u/2 − 2d arctan(e^u) + const` has
     **infinitely many** finite logarithmic branch points, at `u = iπ(m + ½)`, `m ∈ ℤ`
     [Proof + Wolfram];
   - every graph function of a drawable tower curve has only **finitely many** finite
     logarithmic branch points: none for algebraic or trig curves, at most two per branch for
     the exp tower (§3.3) [Proof + Wolfram].
   Hence **for `d ≠ 0`, no single intersection** (any pair of tower types, any `exp_two`
   partner) and **no single box with affine `x`-dependence** solves the parabola family.
   §3.4–§3.5; the two residual readout generalisations are listed as gaps in §3.9. The
   degenerate `d = 0` case is `[Open]` and is genuinely different: there `F_0` is of the exp
   normal form (§3.9 item 4).
   **This holds for every tower type, including `exp_two`**; the essential singularity of
   `exp` is at `z = 0`, i.e. `u = ∞`, and therefore does **not** obstruct — it pushes all
   parametrisation log-monodromy to infinity, away from the discriminating finite points.
   §3.7.

4. **Q4: separation survives at depth ≤ 2 and fails only at depth 3, where it fails for the
   *right* reason.** Depth counts the four active steps `offset`, `arc_of_length`,
   `intersection`, `box`; affine maps, `restrict` and arithmetic are free. No step except
   `arc_of_length` adds a transcendental atom; therefore any number of intersections and
   boxes stays inside the finite-log-branch-point class, and the §3 argument applies
   uniformly. `arc_of_length` is the one step that integrates, and at depth 2 it produces a
   *curve*, not a number, so a readout is still needed: the offset-inversion construction has
   depth 3 (`offset → arc_of_length → box`). A two-step `intersection → intersection`
   construction does **not** escape. §4.

---

## 1. Q1 — the tower normal form

### 1.1 Statement

Define three classes of parametrised plane curves. Throughout `t` is a real parameter on an
interval, `λ ≠ 0` is real, and an **algebraic function** means a real function satisfying a
polynomial equation with real coefficients (equivalently, a branch of a real algebraic
function of the stated variables).

- **(A) Algebraic.** `S` is contained in a real algebraic curve `P(x,y) = 0`.
- **(E) Exp tower.** `γ(t) = (αt + A₁(e^{λt}), βt + A₂(e^{λt}))`, `α, β ∈ ℝ`,
  `A₁, A₂` algebraic.
- **(T) Trig tower.** `γ(t) = (αt + A₁(sin t, cos t), βt + A₂(sin t, cos t))`,
  `α, β ∈ ℝ`, `A₁, A₂` algebraic in two variables, and **bounded** on the circle
  `sin² + cos² = 1`.

Let `𝔗 = A ∪ E ∪ T` (as point sets: a set is in the class if *some* tracing of it has the
stated form).

> **Theorem 1.1 [Proof].** `𝔗` is closed under the curve constructors of `Defs.lean`:
> `translate_x/y`, `scale_x/y`, `rotate`, `restrict`, `offset`, and `arc_of_length`
> (which only cuts a sub-arc).

The subtlety — and the only place the plan's warning could bite — is `offset`; it is treated
in §1.4. Note that `arc_of_length` does *not* create a new curve: it returns
`γ '' Icc a b`, a subset of a curve already in `𝔗`. `intersection` is not a curve
constructor; it returns a *number* (`PConstructible.inter_x/inter_y`), so it is Q2's subject,
not Q1's.

### 1.2 Base curves

| constructor | coordinates | class | why |
|---|---|---|---|
| `poly_graph p` | `(t, p(t))` | A | polynomial graph |
| `power_law a b` | `(t, a t^b)`, `b ∈ ℚ` | A | `y^q = a^q x^p` for `b = p/q`, a semialgebraic (hence algebraic) curve |
| `ellipse` | `(cx + (w/2)cos t, cy + (h/2)sin t)` | A | conic |
| `rectangle` | four segments | A | union of lines |
| `cubic_bezier` | cubic polynomials in `t` | A | polynomial image of `ℝ` |
| `exp_two` | `(t, 2^t)` | E | `α=1, β=0, λ=ln2, A₁=0, A₂(z)=z` |
| `sine` | `(t, sin t)` | T | `α=1, β=0, A₁=0, A₂(z,w)=z` |

`rotate` by `n` degrees uses `cos(nπ/180)`, `sin(nπ/180)`, which are algebraic numbers; so it
is an affine map with algebraic coefficients and preserves all three classes. [Proof]

### 1.3 Affine and `restrict`

**Affine [Proof].** Let `A(x,y) = (a x + b y + c, e x + f y + g)`.
- On A: an invertible affine image of an algebraic curve is algebraic.
- On E: `a(αt+A₁(z)) + b(βt+A₂(z)) + c = (aα+bβ)t + (aA₁(z)+bA₂(z)+c)`, and the bracket is
  algebraic in `z = e^{λt}`. Same for the second coordinate. The parameters `α, β` change;
  `λ` and the class do not.
- On T: identical, with `z = (sin t, cos t)`; boundedness is preserved because
  `aA₁ + bA₂ + c` is bounded on the circle.

**`restrict` [Proof].** `restrict` intersects with an axis-aligned box: a subset of a curve in
`𝔗`. A subset of an algebraic set is algebraic; a subset of an E- or T-curve is traced by the
same parametrisation restricted to the preimage of the box. (The preimage may be a union of
intervals; each component is again of the same form.) ∎

### 1.4 The `offset` step

Let `γ(t) = (αt + A₁(z), βt + A₂(z))`, where either `z = e^{λt}` (E) or
`z = (sin t, cos t)` (T). Write `A_{i,z}` for the derivative with respect to `z`
(and `A_{i,z}·z'` in the trig case, componentwise).

The velocity is
```
x'(t) = α + λ z A₁'(z)        (E),      x'(t) = α + A₁_s cos t − A₁_c sin t   (T),
y'(t) = β + λ z A₂'(z)        (E),      y'(t) = β + A₂_s cos t − A₂_c sin t   (T).
```
In both cases `x'` and `y'` are **algebraic functions of `z`** (for T, of `(sin t, cos t)`;
`A₁_s, A₁_c` are the partials). Hence
```
s(z) := √(x'(z)² + y'(z)²)
```
is algebraic in `z` (a square root of an algebraic function is algebraic — it satisfies
`W² = x'² + y'²`). It is nonzero on the regular window by the constructor's `hreg`.

By R0 (2.1), `P_d(t) = γ(t) + d·n(t)` with
```
P_d(t) = ( αt + A₁(z) − d·y'(z)/s(z),   βt + A₂(z) + d·x'(z)/s(z) ).
```
Define
```
A₁*(z) := A₁(z) − d·y'(z)/s(z),        A₂*(z) := A₂(z) + d·x'(z)/s(z).
```
Both are algebraic in `z` (algebraic operations on algebraic functions). Therefore
```
P_d(t) = ( αt + A₁*(e^{λt}),  βt + A₂*(e^{λt}) )        (E),
P_d(t) = ( αt + A₁*(sin t,cos t),  βt + A₂*(sin t,cos t) )   (T),
```
with the **same** `α, β, λ`. This is the same class. Boundedness in T is preserved because
`|n| = 1`, so each `A_i*` differs from a bounded `A_i` by at most `|d|`.

> **So `offset` preserves `𝔗`, and it adds no new transcendental atom.** It only changes the
> algebraic functions `A_i` and keeps the linear drift `(α, β)` and the frequency `λ`.
> [Proof + Wolfram: for a general E-curve the clearing identities
> `((P_d)_1 − αt − A₁(z))²(x'²+y'²) − d²y'² = 0` and its `y` analogue are identically `0`
> (§6, cell 1, first line); the specific `(t,e^t)` and `(t,sin t)` cases and the affine case
> are also `{0,0}`.]

### 1.5 The `(t, e^t)` warning, resolved

The plan asks: for `(t,e^t)` the offset is
```
P_d(t) = ( t − d e^t/√(1+e^{2t}),   e^t + d/√(1+e^{2t}) ).
```
With `u = e^t` this is `(ln u − d u/√(1+u²), u + d/√(1+u²))`, which contains `ln u`. Does that
break the normal form?

**No — it is a reparametrisation artefact, not an induction failure.** The normal form is a
statement about the tracing produced by the constructors, and the constructors never
reparametrise: `offset` differentiates the given tracing and adds `d·n`. In the inherited
parameter `t`,
```
P_d(t) = ( t + A₁(e^t),  0·t + A₂(e^t) ),    A₁(z) = −dz/√(1+z²),  A₂(z) = z + d/√(1+z²),
```
which is exactly an E-curve with `α = 1, β = 0, λ = 1`. Both `A_i` are algebraic:
`A₁²(1+z²) = d²z²` and `(A₂−z)²(1+z²) = d²`. [Wolfram: the identity in `t` has residual
`{0,0}`, and `B₁²(1+z²) − d²z² = 0`; §6 cell 1.]

The `ln u` is what one gets by *choosing a different tracing* `t = ln u`. That is also a legal
tracing of the same point set, but it is not the one the constructor produces, and the normal
form is existential over tracings. The honest statement of the plan's warning is therefore:

> **If the normal form were required to hold in the `u`-parametrisation, it would fail at the
> first offset.** Read in the constructor's parameter, it holds. The set is unchanged either
> way, which is what matters for the separation. [Proof]

There is a genuine limitation hidden here, and it is the one Q3 must respect: the normal form
is *not invariant under arbitrary reparametrisation*. It is a statement about a particular
tracing. Q3 therefore does **not** use Q1's coordinate form directly; it uses a
reparametrisation-invariant invariant (§3.1).

### 1.6 What the normal form does *not* give

R2's warning is confirmed: the exp class E contains the catenary,
```
(t, cosh t) = ( t + 0,  0·t + ½(e^t + e^{−t}) ),
```
so **the normal form does not exclude the missing curves**, and it cannot prove Q3 by itself.
Likewise the trig class T contains bounded perturbations of lines, which is a large class.
Q1 is a closure theorem, not a separation theorem. Q3 needs an invariant that is preserved by
`offset`, `affine`, `restrict`, `arc_of_length` and violated by `F`; that invariant is the set
of finite logarithmic branch points of the graph function (§3).

---

## 2. Q2 — the intersection class

### 2.1 The uniform convention, formalised

PLAN §1 says: one configuration solves a family if it works for all values of the family
parameter, "changing only P-constructible data that does not depend on the unknown root."
For R3 I use this in the following explicit form.

> **Definition 2.1 (uniform convention).** Let `F : J → ℝ` be injective, `U = F⁻¹`, and let
> `s` be a construction term (a finite word of `Defs.lean` constructors). We say `s` **solves
> `F` on `J`** if for every `x ∈ J` the term, instantiated with
> (i) all fixed curve data and
> (ii) P-constructible parameters that are functions of `x` only, built from `x` by the same
> constructive vocabulary,
> produces a P-constructible number `u(x)` with `F(u(x)) = x`, and no parameter depends on
> `u` or on `F`. Algebraic post-processing of the output is allowed through the derived
> rule `root_Pconstructible_le_six_coeffs` (this is how L2 recovers `w` from the quartic).

Two clarifications matter for the separation.

- **Why `x` may enter at all.** With *fixed* curves, a single intersection is a fixed finite
  set and a single box is a fixed number; neither can vary with `x`. So `x` must enter as
  P-constructible data. Under Definition 2.1 the only admissible entrance is through affine
  data (`translate_x/y`, `scale_x/y`) or, at higher depth, through an `arc_of_length` length.
- **What "solves" does *not* mean.** It does **not** mean "has the same roots as `F`". By R2's
  rigidity theorem, an offset curve parallel to the parabola has the same solution function up
  to a shift of `d`; so "same roots" is *not* a separating condition inside the offset class.
  The separation is against the **intersection/box** class, and it must use a stronger
  invariant than the root set. This is the point of §3.

### 2.2 One intersection: the reduction to a difference of two graph functions

> **Definition 2.2 (graph function).** For a drawable curve `C` and a branch, let
> `g_C(u)` be the abscissa of the point of `C` with ordinate `u`, where the branch is a graph
> over the ordinate axis. If the branch is a graph over the abscissa axis instead, use
> `h_C(x)`; swapping axes is an affine map, so it preserves every class in §1.

> **Lemma 2.3 (reduction) [Proof, under the readout hypothesis below].** Let `C₁, C₂` be
> drawable tower curves. Suppose a construction with exactly one `inter_x`/`inter_y` step,
> all other steps affine or `restrict`, and `x` entering through P-constructible affine data,
> produces for each `x` in an interval a point `p(x) ∈ C₁ ∩ C₂(x)` whose **ordinate** is
> `u(x) = U(x)`. Then, on that interval,
> ```
> F(u) = g_{C₁}(u) − g_{C₂}(u).                                      (2.3.1)
> ```

**Proof.** Write the affine `x`-dependence of the second curve as a translation (a general
affine dependence is the same computation after composing with the fixed linear part). Say
`C₂(x) = C₂ + (φ(x), 0)`. The point `p(x) = (a(x), u(x))` satisfies
`p(x) ∈ C₁`, i.e. `a(x) = g_{C₁}(u(x))`, and `p(x) − (φ(x),0) ∈ C₂`, i.e.
```
a(x) − φ(x) = g_{C₂}(u(x)).
```
Subtracting, `φ(x) = g_{C₁}(u(x)) − g_{C₂}(u(x))`. If `φ` is the identity (`x` used directly
as the translation), then `x = F(u(x))` gives (2.3.1). If `φ` is a non-identity P-constructible
map, replace `F` by `φ ∘ F`; this is the form used in §3.4. For a translation in the `y`
direction the roles of abscissa and ordinate swap, and (2.3.1) still holds with `g` replaced
by `h`; by Definition 2.2 that is the same class. ∎

Three remarks.

- **Readout hypothesis.** Lemma 2.3 assumes the output is the ordinate `u` itself. If the
  construction outputs an algebraic function `A` of the point's coordinates, then on the
  branch where `C₁` is a graph the point is determined by `u`, so the output is `Ã(u)` with
  `Ã` algebraic, and `F` is replaced by `F ∘ Ã`. If the output is the *other* coordinate (the
  abscissa), swap the roles of abscissa and ordinate as in Definition 2.2; the right-hand side
  becomes a difference of `h`-graph functions and the conclusion is identical. Since `Ã` is
  nonconstant (otherwise `u` is
  constant and cannot solve a varying family), `F ∘ Ã` has the same *kind* of branch set as
  `F` (infinitely many finite log branch points; §3.2). This is the form stated in Theorem
  3.4. A fully general bookkeeping where the output uses both coordinates and `C₁` is not a
  graph over either axis is [Open] (§3.9), but a tower curve is locally a graph except at
  finitely many vertical/horizontal tangents, so restricting to a sub-arc covers the
  generic case.
- **`x` used twice.** If both curves are translated by functions of `x`, the same subtraction
  gives `φ₁(x) − φ₂(x) = g_{C₁}(u) − g_{C₂}(u)`; an invertible P-constructible `φ₁ − φ₂`
  composes with `F` as above and changes nothing structurally.
- **What the equation looks like in `S, κ, ψ`.** See §2.4.

### 2.3 One box

> **Lemma 2.4 (single box) [Proof, for affine `x`-dependence].** Suppose a construction has
> exactly one `box_xmax`/`box_ymax` step, applied to a drawable curve built from base curves by
> affine maps, `restrict` and `offset` only (**no `arc_of_length`**), with `x` entering only
> through `translate_x/y` and `scale_x/y` by `x` or by constants. Then the box output is a
> **piecewise-affine** function of `x`.

**Proof.** The curve being boxed is `A_x(C₀)` where `C₀` is fixed and `A_x` is affine with
entries affine in `x`. The box is
```
box_xmax(A_x(C₀)) = max_{p ∈ C₀} (a(x)p₁ + b(x)p₂ + c(x)).
```
The set `C₀` is compact and fixed, so the maximizing point `p*` is locally constant in `x`
except at finitely many parameter values where two extremal branches exchange. On each
subinterval, the value is `a(x)p₁* + b(x)p₂* + c(x)`, affine in `x`. ∎

Two consequences.

- `U(x) = F⁻¹(x)` is **not** affine: `F'(u) = cosh²u − d sech u` is nonconstant, so `U` has a
  nonconstant second derivative wherever `F' ≠ 0`. Hence a single box cannot equal `U`, and
  cannot determine `U` by an affine relation either.
- The **positive** construction L2 is *not* a single box in this sense: its box is applied to
  an `arc_of_length` stroke whose *length is `x`*, so the curve being boxed already encodes
  `x` nonlinearly. That is a depth-3 construction (§4), and it is exactly the mechanism the
  separation is designed to leave standing.

### 2.4 `S`, `κ`, `ψ` vocabulary

R1/R2's dictionary, specialised to what Q2–Q3 use. With `w = tan ψ = sinh u`, `u = gd⁻¹ψ`,

```
S(u) = ds/du = ρ(ψ) sech u,        ρ = 1/κ = R'(ψ),        dψ/du = sech u.
```

For the **parabola** `y = x²/2` (R1 row 1), with `w` the slope parameter:

```
κ = (1+w²)^{-3/2},   ρ = (1+w²)^{3/2} = sec³ψ,   R = ½(w√(1+w²) + asinh w) = ¼sinh 2u + u/2,
F(u) = R(w) − dψ = ¼sinh 2u + u/2 − d·gd u,        w = sinh u.          (2.4.1)
```

In the `w`-variable, `F(w) = ½(w√(1+w²) + asinh w) − d arctan w`; in the `u`-variable it is
(2.4.1). The two are related by `w = sinh u`, which is where the exponential structure enters.

**A single intersection, in this vocabulary.** A tower curve's graph function `g_C` is a
function of the *ordinate*. The tower constraints are on `κ, ψ, S`, not on `F`; the offset
atom `−dψ` is linear in the angle. So a single intersection can produce any equation of the
form "difference of two tower graph functions", i.e. any relation built from
`αu + A(e^{λu})` or `αu + A(sin u, cos u)`. It cannot produce `gd u = arctan(sinh u)`,
because `gd` is not algebraic in `e^{λu}` or in `(sin u, cos u)` — this is the R1/R2 atom
count made into a branch-point statement in §3.

---

## 3. Q3 — separation (headline)

**Standing hypotheses.** Fix `d ≠ 0` (the plan's cusp-free regime is `|d| < 1`, but nothing
below uses it: the argument is local in `u` and works on any interval where `F` is injective,
and on the complex plane away from the branch locus). The target is
`F(u) = sinh(2u)/4 + u/2 − d·gd u`, `U = F⁻¹`. All analytic statements are about the complex
extension; the real interval `J` of Definition 2.1 is contained in the domain of a branch.
**The case `d = 0` is degenerate and is discussed separately in §3.9 item 4**: there the `gd`
term is absent, `F(u) = ¼sinh 2u + u/2` *is* of the exp normal form, and the branch-point
invariant does not separate it.

### 3.1 The invariant: finite versus infinite logarithmic monodromy

Let `f` be a function analytic on a domain `Ω ⊂ ℂ` minus a discrete set. A point `u₀` is a
**logarithmic branch point** of `f` if, in a local coordinate `ζ = u − u₀`, `f` contains a
term `c·log ζ` with `c ≠ 0`; equivalently, analytic continuation around `u₀` changes `f` by a
nonzero additive constant. A **finite log branch point** is one with `u₀ ∈ ℂ`.

> **Lemma 3.1 (invariance) [Proof].** (a) Algebraic operations (`+`, `−`, `×`, `÷`,
> composition with a nonconstant algebraic function) preserve the property "at most finitely
> many finite log branch points", and the image of a finite set under a nonconstant algebraic
> map is finite. (b) Passing from a tower curve `C` to its graph function `g_C` does not create
> log branch points beyond those of the parametrisation. (c) Each active constructor either
> leaves the atom set alone or adds only *finitely much* branch data: `offset` and affine steps
> only change the algebraic `A_i` (§1.4); `restrict` restricts the domain; `arc_of_length`
> integrates a tower speed, so it can add only the finitely many residues of that abelian
> differential; `intersection` and `box` are locally analytic readouts (implicit function
> theorem / one extremal branch).

Part (c) is the depth bookkeeping of §4; the substantive content is (a)–(b), proved in §3.3.
The phrase "finitely much" is essential: `arc_of_length` *can* add log branch points (that is
how the positive construction works), but only finitely many, so it cannot manufacture `F`'s
infinite set by itself.
The key contrast is:

```
F has infinitely many finite log branch points   (§3.2),
every tower graph function has finitely many     (§3.3).
```

### 3.2 The branch points of `F`

Write
```
gd u = arctan(sinh u) = 2 arctan(e^u) − π/2,        (identity, [Proof + Wolfram])
F(u) = sinh(2u)/4 + u/2 − d·gd u.
```
Since `d ≠ 0`, the only non-entire ingredient is `arctan(e^u)`. The function `arctan z` has
logarithmic branch points at `z = ±i` (its derivative is `1/(1+z²)`, with nonzero residues
`∓i/2`). Therefore `arctan(e^u)` has a log branch point wherever `e^u = ±i`, i.e.
```
u₀ = iπ(m + ½),   m ∈ ℤ.                                            (3.2.1)
```
Near such a point `e^u ∓ i` has a simple zero, so the branch point is genuinely logarithmic
(coefficient `≠ 0` because `d ≠ 0`). There are **infinitely many** of them, spaced by `iπ`
along the imaginary axis.

> **Lemma 3.2 [Proof + Wolfram].** `F` has infinitely many finite logarithmic branch points,
> exactly at (3.2.1). Its monodromy around `u₀` is a nonzero multiple of `2πd`.

[Wolfram: `Solve[Sinh[u]==I,u]` and `Solve[Sinh[u]==−I,u]` give
`u = iπ(½ + 2k)` and `u = iπ(−½ + 2k)`, union `iπ(m+½)`; `Residue[1/(1+z²),{z,i}] = −i/2`,
so the monodromy of `arctan` is `2πi·(−i/2) = π`; a 40-digit contour integral around `z=i`
gives `π − 2.9·10⁻⁵⁵ i`, i.e. `π`; §6 cell 2.]

**Why this is the right invariant, not a coordinate artefact.** In the `w = sinh u` variable
`F(w) = ½(w√(1+w²)+asinh w) − d arctan w` has only *two* finite log branch points, at
`w = ±i`. The infinite set (3.2.1) is created by the change of variable `w = sinh u`, which is
the *target* variable of the family: the construction must output `u`, not `w`. The
construction's own parameters are free, but the equation it solves is `F(u) = x`, and `u` is
the output; so the relevant analytic continuation is in `u`. This is exactly the point where
"same roots on a window" and "same function" diverge, and why R2's rigidity (which is stated
in `ψ`) is not by itself enough: rigidity compares offset equations in `ψ`, while Q3 compares
*any* readout function to `F` in `u`. [Proof; the `w`-form is R1's, and the `u`-form is
(2.4.1).]

### 3.3 Tower graph functions have only finitely many finite log branch points

> **Lemma 3.3 [Proof + Wolfram].** Let `C` be a curve in `𝔗` and `g_C` a branch of its
> abscissa-as-a-function-of-ordinate. Then `g_C` has at most finitely many finite
> logarithmic branch points.

**Case A (algebraic).** `g_C` is an algebraic function; algebraic functions have no
logarithmic branch points (their monodromy is finite). [Proof: a global branch of an algebraic
function has finite monodromy around every point, while a log branch point has infinite
monodromy.]

**Case T (trig).** `C` is `(αt + A₁(sin t,cos t), βt + A₂(sin t,cos t))` with `A_i` bounded.
On a branch where `C` is a graph over the ordinate, `u = βt + A₂(sin t,cos t)`. If `β ≠ 0`,
then `t = (u − A₂)/β` with `A₂` bounded, so `g_C(u) = αt + A₁ = (α/β)u + O(1)`; the
parametrisation is analytic in `t` with no logarithm anywhere (`A_i` are algebraic in
`sin,cos`, and the boundedness hypothesis rules out poles on the circle, so they are analytic
there), so no log branch points. If `β = 0`, `u` is bounded,
so the branch is defined on a bounded interval and has no log branch points. [Proof] The
same argument shows the graph of a T-curve is a bounded perturbation of a line: a **stripe**
`|y − (β/α)x| ≤ M` when `αβ ≠ 0`, a bounded `x`-range when `α = 0, β ≠ 0`, and a bounded
ordinate when `β = 0`. These are the cruder forms used in §3.4.

**Case E (exp).** `C` is `(αt+A₁(e^{λt}), βt+A₂(e^{λt}))`. Put `z = e^{λt}`, so
`t = log z / λ` and
```
X(z) = (α/λ) log z + A₁(z),        Y(z) = (β/λ) log z + A₂(z).        (3.3.1)
```
The parametrisation is by `z ∈ ℂ*` (or the algebraic Riemann surface of `A_i`). Solve
`Y(z) = u` for `z` and put `g_C(u) = X(z(u))`.

- If `β ≠ 0` (`Y` carries the log term): as `z → 0` or `z → ∞`, `Y(z) → ∞`; so the
  logarithmic monodromy of the parametrisation sits at `u = ∞`, not at a finite `u`. At a
  finite `u`, `z(u)` is finite and nonzero and `Y` is analytic or algebraic there; hence
  `g_C(u)` is analytic or algebraic at finite `u`, with **no** finite log branch point.
- If `β = 0` (`Y = A₂(z)` algebraic): `z(u)` is an algebraic function of `u`, and
  `g_C(u) = (α/λ) log z(u) + A₁(z(u))`. A log branch point can occur only where `z(u) = 0`
  or `z(u) = ∞`. Since `A₂` is algebraic, these occur only at the finite values
  `u = lim_{z→0} A₂(z)` and `u = lim_{z→∞} A₂(z)` (when those limits are finite); otherwise
  `z(u) = 0,∞` corresponds to `u = ∞`. So there are **at most two** finite log branch points
  per branch.

[Wolfram: for the sample `c' ≠ 0` curve `(log z + z, log z + 2z)`, `Solve[Y==u,z]` gives a
single inverse branch and `Y → −∞` as `z → 0`, confirming that the log monodromy is at
`u = ∞`; for `exp_two`, `x = log y`, whose only finite log branch point is `y = 0`; §6 cell
2.] ∎

**The essential singularity.** In the case `β ≠ 0` the parametrisation (3.3.1) has an
essential singularity at `z = 0`, which is the `exp_two` point the plan flags. It is exactly
because the singularity is at `z = 0` that it maps to `u = ∞` and **cannot** create a finite
log branch point. So it does not obstruct the argument; it is the reason the argument is
clean. If one instead tried the §3b "accumulation of zeros at the end of the window" route,
the essential singularity would be fatal (see §3.6). [Proof]

### 3.4 Theorem: no single intersection

> **Theorem 3.4 (separation, one intersection) [Proof].** Let `C₁, C₂` be drawable tower
> curves. Let `s` be a construction whose only non-affine, non-`restrict` step is a single
> `inter_x` or `inter_y`, with `x` entering only through P-constructible affine data, and whose
> output is `u = U(x)` (possibly after an algebraic readout, Definition 2.1). Then `s` does not
> solve `F` on any interval: there is no such construction.

**Proof.** By Lemma 2.3 (and the readout remark), on an interval
```
G(u) := F(u)  (or F(Ã(u)) with Ã algebraic nonconstant)  =  g_{C₁}(u) − g_{C₂}(u).   (3.4.1)
```
By Lemma 3.2, `F` has infinitely many finite log branch points at `iπ(m+½)`. A nonconstant
algebraic `Ã` pulls these back to infinitely many finite points (each `Ã⁻¹(iπ(m+½))` is finite
and nonempty for all but finitely many `m`; the log branch survives composition unless
`Ã' = 0`, which happens at finitely many points, so infinitely many survive). Hence the left
side of (3.4.1) has infinitely many finite log branch points. By Lemma 3.3 each `g_{C_i}` has
only finitely many, so the right side has only finitely many. Contradiction. ∎

**Scope note.** The theorem covers every combination of tower types (A/A, A/E, A/T, E/E, E/T,
T/T): the right side is always a difference of two functions each with finitely many finite
log branch points. It does **not** cover a construction that first builds an `arc_of_length`
curve and then intersects it; that is depth 2, §4.

### 3.5 Theorem: no single box

> **Theorem 3.5 (separation, one box) [Proof, affine `x`-dependence].** A construction whose
> only non-affine step is a single `box_xmax`/`box_ymax`, applied to a curve built from base
> curves by affine maps, `restrict` and `offset` only (no `arc_of_length`), with `x` entering
> only through `translate_x/y` and `scale_x/y` by `x` or constants, does not solve `F` on any
> interval.

**Proof.** By Lemma 2.4 the box output is piecewise affine in `x`. On any subinterval it is
`a x + b`. But `U = F⁻¹` is not affine: `F'(u) = cosh²u − d sech u` is nonconstant
(`F''(u) = 2 cosh u sinh u + d sech u tanh u`, not identically zero for `d ≠ 0`; and even for
`d = 0`, `F' = cosh²u` is nonconstant). Hence `U(x) = a x + b` fails on every interval.
∎

**Why this does not contradict L2.** L2's box is applied to an `arc_of_length` stroke of length
`x`; the stroke's shape depends on `x` nonlinearly, so its box is not piecewise affine. The
`arc_of_length` step is precisely what Theorem 3.5 excludes by hypothesis.

### 3.6 Relation to the §3b accumulation argument

`sheared-sine-intersections.md` §3b proves a separation by: (i) writing the intersection
condition as an analytic function `R(θ)`, (ii) using the discrete root family `tan t = t`,
whose roots accumulate at `π/2`, (iii) clearing poles and concluding `R ≡ 0` from accumulating
zeros.

That mechanism **does not transfer directly**, for a precise reason: the parabola family
`F(u) = x` has a *continuous* parameter `x`, so its roots `u(x)` form an interval, not a
discrete set accumulating at a boundary. There is no accumulation point to feed the
identity theorem.

The correct adaptation is to use the other half of the §3b toolkit — **poles**, not zeros. In
§3b the function `R` is rational in `tan θ` and the pole at `θ = π/2` is what forces `R ≡ 0`
after clearing. Here the corresponding local datum is the **logarithmic monodromy** at a
finite branch point: `F` has a pole of `dF` with nonzero residue at `u₀`, while a tower graph
function has none. The identity theorem is replaced by analytic continuation around a small
loop, and "accumulating zeros" is replaced by "infinitely many finite branch points". This is
the same analytic-continuation idea in its monodromy form. [Proof]

**Consequence for the plan's phrasing.** The plan's `[Heuristic]` ("single intersections
cannot solve equations that need `u` and `gd u` together") is now a theorem **for the
intersection/box class**, but the proof is not the §3b zero-accumulation proof; it is a
branch-point count. Both are instances of "an analytic function with too much local structure
must be identically zero"; only the local structure used differs.

### 3.7 `exp_two`: the essential singularity, and why it does not bite

The plan warns that the §3b argument has an essential singularity at `exp_two`, so exp-type
partners need separate treatment. Here is the resolution.

- The parametrisation (3.3.1) has its essential singularity at `z = 0` (`t → −∞`), and its
  logarithmic monodromy there maps to `u = ∞` when `β ≠ 0`.
- `F`'s discriminating branch points are at the **finite** points `u = iπ(m+½)`.
- At a finite `u`, an E-curve's graph function is analytic or algebraic (Lemma 3.3), whether
  `β ≠ 0` or `β = 0`.

So `exp_two` and all its affine images are covered by the same branch-point count, with no
separate case. The one place where a separate check is needed is the `β = 0` sub-case, where
`Y = A₂(z)` is algebraic and `g_C` can have up to two finite log branch points; these are
still finite in number, so they cannot match `F`'s infinite set. [Proof + Wolfram]

**What remains `[Open]` for exp-type partners** is not the graph-function lemma but the
*composition* case at depth ≥ 2: a composition of two E-graph functions can in principle
produce a richer branch set, and the composition bookkeeping is only partly done (§4, §5.2).
For a *single* intersection the exp case is closed.

### 3.8 The cusp caveat

R0 §3.4 shows that laying an arc across an offset cusp changes the right-hand side by the
P-constructible constant `2Φ(t₀) − Φ(a)` and keeps the **same** functional form
`R(ψ) − dψ = x + const`. So a cusp:

- does not create a new equation family;
- shifts the RHS by a constant, which does not change the branch-point set of `F` (it only
  translates the target `x`, not the function `u ↦ F(u)`);
- may be the only way to reach the far branch when `d > 1` (R0 §5.2), but that is a readout
  question, not a separation question.

Hence the cusp caveat neither weakens nor strengthens Theorems 3.4–3.5. [Proof, citing R0
§3.4]

### 3.9 Gaps

1. **General readout using both coordinates.** Lemma 2.3 is stated for the output equal to one
   coordinate (up to an algebraic function of that coordinate). If a construction uses *both*
   coordinates of the intersection in a way that is not a function of one of them, the
   reduction to (3.4.1) needs the extra step "a tower curve is locally a graph over either
   axis". This is true except at finitely many vertical/horizontal tangents, and restricting
   to a sub-arc avoids them, but the formal bookkeeping is `[Open]`. **Expected answer:** the
   same branch-point count, after restricting to a graph branch.
2. **Box with non-affine `x`-dependence.** Theorem 3.5 assumes `x` enters through
   `translate/scale` by `x` or constants. If `x` enters through an arbitrary P-constructible
   tower function `g(x)`, the box output is `g(x) + const`; then `U` would have to be a tower
   function of `x`. `U(x) ~ ½ log(8x)` [Wolfram: `F(3) = 51.1926…` with `d = ½`, and
   `e^6/8 = 50.4286…`, difference `0.7640…`; §6 cell 3], which is not exp-algebraic, but the
   full "`U` is not a tower function" statement is `[Open]`. **Expected answer:** no.
3. **`d`-varying uniformity.** Theorem 3.4 fixes `d`. If `d` is allowed to vary with the
   family parameter (R2 Q3.4), the target function changes and the branch-point argument must
   be run family-wise. This is `[Open]` and is R2's open item 2, not new here.
4. **The degenerate case `d = 0`.** At `d = 0` the target is `F_0(u) = ¼sinh 2u + u/2`, which
   is **of the exp normal form**:
   `F_0(u) = u/2 + (e^{2u} − e^{−2u})/8`, i.e. the graph `{(u,F_0(u))}` is an
   E-curve with `α = 1, β = ½, λ = 2, A₂(z) = (z − z^{-1})/8`. So Lemma 3.2 fails (F_0 is
   entire, with no log branch points at all) and Theorem 3.4 gives nothing. Whether F_0 is
   *drawable* — i.e. whether the specific `A₂` is reachable from `exp_two` by the constructors,
   as opposed to merely lying in the normal-form class — is a constructor-reachability
   question, not a separation question. `[Open]`. This is the honest boundary of the
   branch-point method: it separates `F` from the *whole* normal-form class only when the
   `gd` atom is present, i.e. `d ≠ 0`. The programme's positive result (L2) holds at `d = 0`
   too, so `d = 0` is not a counterexample to the programme, only to a normal-form-based
   separation.

---

## 4. Q4 — what remains possible: composition depth

### 4.1 Definition of depth

> **Definition 4.1 (depth).** For a construction term, `depth` counts the **active** steps
> and ignores the free ones:
> - base curve: `0`;
> - `translate_x/y`, `scale_x/y`, `rotate`, `restrict`, arithmetic on P-constructible
>   numbers, and linear change of variable: `depth` unchanged;
> - `offset`: `+1`;
> - `arc_of_length`: `+1`;
> - `inter_x`/`inter_y`: `max(depth of the two curves) + 1`;
> - `box_xmax`/`box_ymax`: `depth(curve) + 1`.
>
> The **output depth** of a construction is the maximum depth along the term that produces
> the output number.

For orientation: the parabola offset inversion of L2 is `offset` (1) → `arc_of_length` (2) →
`box_xmax` (3), so it has output depth **3**.

### 4.2 What each extra step can add

| step | what it adds | new transcendental atom? | new finite log branch points? |
|---|---|---|---|
| affine / `restrict` | algebraic reparametrisation | no | finitely many (algebraic image of a finite set) |
| `offset` | changes `A_i` in the normal form (§1.4) | **no** | **no** |
| `intersection` | one algebraic elimination between two tower curves | **no** | **no** (algebraic elimination) |
| `box` | a maximum, locally one branch | **no** | **no** |
| `arc_of_length` | one abelian integral of a tower speed; the length `x` enters | **yes** (an integral) | **finitely many** (poles/residues of the abelian differential), plus the `dψ` term if an offset precedes it |

The table is the whole content of Q4. **Only `arc_of_length` integrates.** Every other step is
algebraic (elimination, extremum, affine change) and therefore preserves the branch-point
class of §3. This is the precise reason "more steps ≠ more power": an intersection of two
intersections is still an algebraic elimination, and a box of a box is still an extremum.

**Cross-check against R2's combination list.** R2 §Q2.3 proves that a tower word carries *at
most one bare `arctan`*, of the form `arctan(M·tan ψ)` with `M` a partial product of linear
parts, plus weighted elliptic terms `σ₁E(φ_j|k_j)` with independent moduli, plus the algebraic
coordinate. Read in the `u`-variable, each of those ingredients is a tower graph function of
the types in Lemma 3.3, so each contributes only finitely many finite log branch points. R2's
list therefore *confirms* the table: no number of offsets, affines or intersections adds the
`gd` atom, and only `arc_of_length` changes the analytic character.

### 4.3 Separation at bounded depth

> **Theorem 4.2 (depth ≤ 2) [Proof, modulo the reduction lemma].** No construction of output
> depth ≤ 2 solves `F` on an interval.

**Proof sketch.** A depth-≤2 output is one of:

1. **One intersection or one box** (depth 1): Theorems 3.4–3.5.
2. **`intersection` then `intersection`** (depth 2). The first intersection produces a
   P-constructible number `u₁(x)` which, by Lemma 2.3, is a difference of two graph functions
   (or a graph function). The second intersection uses `u₁(x)` as a parameter in a tower curve
   and produces `u₂(x)`. Composing, `u₂` is obtained from `u₁` by the same operation; the
   branch-point set of the composite is the union of the branch points of the outer graph
   function (finitely many) pulled back along `u₁` (finitely many each) and the branch points
   of `u₁` (finitely many). So `u₂` has finitely many finite log branch points, while `F`
   (or `F ∘ Ã`) has infinitely many. Contradiction.
3. **`box` then `intersection`**, or `intersection` then `box`: the same composition
   argument; the first output has finitely many finite log branch points and the second step
   is algebraic/extremal, so the composite has finitely many.
4. **`offset` then `intersection` / `box`**: `offset` adds no atom or branch point (§1.4), so
   this reduces to cases 1–3.
5. **`arc_of_length` as the first step, then a readout**: `arc_of_length` produces a *curve*,
   not a number. To get a number one needs a `box` or an `intersection` afterwards, which is
   depth 3. A depth-2 output cannot consist of `arc_of_length` plus a readout.
   (`arc_of_length` followed by nothing is a curve, not an output number.)

Hence depth ≤ 2 cannot solve `F`. ∎

**The honest caveat.** Case 2's "composite has finitely many branch points" uses the fact that
the outer graph function has finitely many finite log branch points. This is Lemma 3.3. The
bookkeeping of how the inner branch points pull back is elementary for a *single* composition
but has not been written out in full for arbitrary nesting, so Theorem 4.2 is `[Proof sketch]`
for the nested case. The conclusion is nevertheless secure for depth 2 because at depth 2
there is at most one composition, which is covered by Lemma 3.1(a).

### 4.4 The positive construction sits at depth 3

The separation does **not** survive at depth 3, and that is correct: L2's construction
```
parabola → offset(d) → arc_of_length(x) → box_xmax
```
is exactly depth 3 and solves `F` for P-constructible `d < 1`, `x ≥ 0`. The reason is that
`arc_of_length` introduces the one operation that inverts `F`: it lays the length `x` along
the offset, and the box reads the endpoint. In the language of §4.2, `arc_of_length` is the
only step that adds an integral, and the parabola's offset is the unique tower curve whose
integral *is* `F` (R1 row 1, R2 rigidity).

So the verdict on Q4 is:

> **A two-step construction does not escape; the separation survives at depth ≤ 2. It fails at
> depth 3, but it fails because `arc_of_length` is the offset-inversion mechanism itself, not
> because intersections gained expressive power.** [Proof for depth ≤ 2 modulo §4.3's caveat;
> the depth-3 positive statement is L2.]

---

## 5. Exact statements, gaps, and what would break separation

### 5.1 The theorems as proved

**Theorem 1.1 (tower normal form).** *The class `𝔗 = A ∪ E ∪ T` of §1.1 is closed under
`translate_x/y`, `scale_x/y`, `rotate`, `restrict`, `offset`, and `arc_of_length`. In
particular the offset of an E-curve is again an E-curve with the same `λ` and the same linear
drift `(α,β)`, and the `ln u` in the plan's `(t,e^t)` example is a reparametrisation artefact.*
[Proof + Wolfram]

**Lemma 2.3 (intersection reduction).** *One intersection of two tower curves, with `x`
entering through affine data and the output equal to one coordinate (up to an algebraic
function of it), forces `F(u) = g_{C₁}(u) − g_{C₂}(u)` on an interval.* [Proof]

**Theorem 3.4 (no single intersection).** *For `d ≠ 0`, no construction whose only active step
is one `inter_x`/`inter_y`, with `x` entering through P-constructible affine data and an
algebraic readout, solves `F(u) = x` on any interval, for any pair of drawable tower curves.*
[Proof]

**Theorem 3.5 (no single box).** *No construction whose only active step is one
`box_xmax`/`box_ymax`, applied to a curve built without `arc_of_length` and with `x` entering
only through `translate/scale` by `x` or constants, solves `F(u) = x` on any interval.*
[Proof]

**Theorem 4.2 (depth ≤ 2).** *No construction of output depth ≤ 2 solves `F` on an interval.*
[Proof, modulo the nested-composition bookkeeping of §4.3]

**Positive control (L2, cited).** *At depth 3, `offset → arc_of_length → box` does solve `F`
for P-constructible `d < 1`, `x ≥ 0`.* [R0 §5.3, L2]

### 5.2 Precise gaps

1. **General two-coordinate readout** (§3.9 item 1). The reduction to a single graph branch is
   [Open] in full generality; the local-graph argument covers the generic case.
2. **Box with non-affine `x`-dependence** (§3.9 item 2). The statement "`U` is not a tower
   function of `x`" is [Open]; only the affine case is proved.
3. **Nested composition bookkeeping** (§4.3). Depth 2 is covered; the general statement for
   arbitrary nesting is [Proof sketch].
4. **`d` varying with the family parameter** (§3.9 item 3), inherited from R2 Q3.4. Not needed
   for Q3 (d fixed) but needed for a fully general "uniform in the family".
5. **The degenerate case `d = 0`** (§3.9 item 4). `F_0(u) = ¼sinh 2u + u/2` is of the exp
   normal form, so the branch-point method is silent; whether the corresponding E-curve is
   drawable is [Open] and is a constructor-reachability question.
6. **The `w`-versus-`u` variable.** Lemma 3.2 uses `u`. If a construction is allowed to output
   `w` and recover `u` by a *non-algebraic* operation, the branch-point count changes back to
   two. But recovering `u` from `w` is `u = asinh w`, which is not an algebraic operation and
   is not available to `PConstructible`; the only allowed recovery is algebraic
   (`root_Pconstructible_le_six_coeffs`). So the gap is closed by the convention, and this is
   worth stating explicitly. [Proof, given Definition 2.1]

### 5.3 What would break the separation

1. **A new base curve whose graph function has the `gd` atom.** The cleanest break: a drawable
   curve `y = F(x)` (the graph of the offset-inversion function) or any curve with
   `ρ = sec³ψ` and a `gd`-type parametrisation. A horizontal line at height `x` would then
   intersect it at `u = U(x)` in one step. This is the precise sense in which the missing
   curve is the obstruction.
2. **`arc_of_length` (already present).** The depth-3 construction already breaks it, and that
   is the intended positive result.
3. **A construction allowed to use the unknown root as data** (non-uniform). Excluded by
   Definition 2.1; this is the convention's whole job.
4. **A `box` applied to an `arc_of_length` stroke** — this is (2) in different clothing.
5. **A base curve with an essential singularity at a finite point** (not `exp_two`, whose
   essential singularity is at `z = 0 ↦ u = ∞`). Such a curve could have infinitely many
   finite log branch points and break Lemma 3.3.

### 5.4 `[Open]` items for R4

1. **Carry the branch-point invariant through arbitrary nesting.** Prove Lemma 3.1(a) for
   arbitrary finite compositions of graph functions, giving Theorem 4.2 without the caveat.
   This is the main technical gap.
2. **The two-coordinate readout.** Formalise "a tower curve is locally a graph" and close
   §3.9 item 1.
3. **`U` is not a tower function.** Prove the box case with `x` entering through an arbitrary
   tower function of `x` (§3.9 item 2). Expected: `U(x) ~ ½log(8x)` is not exp-algebraic.
4. **The `d`-varying uniformity.** R2's open item 2; the branch-point method should adapt, but
   the family is then two-parameter.
5. **Named-problem transfer.** The same invariant should separate the beam/`tan x = λx`
   families from the intersection class (R2 did the offset-class version via parallelism).
   The `u`-variable branch points of `x + gd x` are at `x = iπ(m+½)` shifted, so the argument
   should go through verbatim; not written out here.
6. **Lean.** The branch-point/monodromy argument is not in `Pptc` and would need complex
   analysis (residues, analytic continuation) well beyond the current library. The Lean
   headline (L2) is the *positive* side and does not need it. A formal separation would be a
   separate large project; the useful formalizable fragment is the algebraic part of Q1
   (closure of the normal form), which is mostly polynomial algebra.

---

## 6. Wolfram reproducibility

Four evaluator calls, grouped into three blocks (the fourth is a short follow-up confirming
the corrected `w`-form of `F'`). Residuals are `numeric − closed form`; `0. 10^-k` means zero
at the working precision.

**Cell 1 — Q1 closure.** [Wolfram]
- general E-curve clearing identities
  `((P_d)_1 − αt − A₁(z))²(x'²+y'²) − d²y'²` and the `y` analogue: `{0, 0}`;
- `(t,e^t)` offset against `(t + B₁(e^t), B₂(e^t))`: `{0, 0}`;
- the same in the `u = e^t` coordinate against `(ln u − du/√(1+u²), u + d/√(1+u²))`:
  `{0, 0}` (confirming the `ln u` is only the reparametrised form);
- `B₁(z)²(1+z²) − d²z²`: `0` (algebraicity of `B₁`);
- trig offset identity: `{0, 0}`;
- `|A₁| ≤ |d|`: `True`; `max |A₂|` at `d = 1`: `2.000000…` (= `1 + |d|`);
- affine closure: `{0, 0}`;
- R0's offset-derivative identity: `0`.

**Cell 2 — Q3 branch structure.** [Wolfram]
- `F'(u) − (cosh²u − d sech u)`: `0`; in the `w = sinh u` form the correct relation is
  `F'(u) = cosh u·(√(1+sinh²u) − d/(1+sinh²u))`, residual `0`;
- `gd` identity `arctan(sinh u) − (2 arctan(e^u) − π/2)`: `0` under `u ∈ ℝ`, and
  `0. × 10⁻⁸⁹` numerically at `u = 7/10`;
- `Solve[Sinh[u]==I,u]` ⟹ `u = iπ(−½ + 2k)`; `Solve[Sinh[u]==−I,u]` ⟹
  `u = iπ(½ + 2k)` and `iπ(3/2 + 2k)`; union `iπ(m + ½)`;
- `Residue[1/(1+z²),{z,i}] = −i/2`; `2πi·Residue = π`;
- 40-digit contour integral around `z = i`, radius `1/10`: `π − 2.920…×10⁻⁵⁵ i`;
- residues of `dF = ½ dz/z + 2d dz/(1+z²)` at `0, i, −i`: `{½, −id, id}`; the ratio
  `res(i)/res(0) = −2id = −i` at `d = ½` (not rational, so the two logs are
  incommensurable);
- count of `iπ(m+½)` with `|u| < 10`: `6` (for `m = −20…20`), i.e. infinite in the limit;
- `exp_two` graph function: `x = log y`, one finite log branch point at `y = 0`;
- sample `c' ≠ 0` E-curve `(log z + z, log z + 2z)`: one inverse branch, `Y → −∞` as
  `z → 0`, so its log monodromy is at `u = ∞`.

**Cell 3 — Q2 sample and readout.** [Wolfram]
- `sin x = 2^x` root near `−10`: `x = −9.42623148317411980283242777898`
  (an example of a single-intersection equation of the tower class);
- L2 readout quartic residual: `0`; roots at `d = ½, e = 1`:
  `{−0.0590… ± 0.9983…i, 0.7104…, 1.4076…}`, the valid root `1.40760987206315754870082364129`;
- `F(3) = 51.1926371720112106605170316648` at `d = ½`, against `e^6/8 = 50.4286…`
  (difference `0.7640…`), confirming `F(u) ~ e^{2u}/8` and hence `U(x) ~ ½log(8x)`.

**Backend.** All values in this note are Wolfram Language, 30–50 digit working precision, in
the three cells above. No Python/mpmath fallback was used.
