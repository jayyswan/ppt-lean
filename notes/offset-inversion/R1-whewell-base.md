# R1 — Whewell functions of the base curves and their affine images

**Stream:** R1 of `PLAN-offset-inversion.md`. **Deliverable:** this file. No `.lean` file was
edited and no `lake` command was run.

Sources read: `PLAN-offset-inversion.md` §0/§1/§R1; `notes/offset-inversion-tangent-angle.md`;
`notes/offset-inversion/R0-foundations.md` §2, §6; `notes/offset-inversion/R5-named.md`;
`notes/offset-inversion/atlas.wl`; `notes/offset-inversion/W0.md`; `Pptc/Defs.lean`
(constructors, lines 214–340); `Pptc/ThirdKind.lean` (the residue/kind section, lines 267–317).

Labels: **[Proof]** argument written out here; **[Wolfram]** checked in Wolfram Language at
20–40 digit working precision — **every number in this note is from Wolfram** (§14 lists the
residuals); **[Heuristic]**; **[Open]**.

**Scope.** R5 owns the *named-problem* catalogue (catenary, log-cosine, tractrix, elastica,
goat, beam, rhumb, involute). This note is the *curve* catalogue: for each base curve of
`Defs.lean` and each affine image, the Whewell function `R`, its elementary status, its genus
and kind, the equation `R(ψ) − dψ = x`, and whether that equation collapses.

**Standing hypotheses.** Everything below is on a window where `R0` §2 applies: `γ` is
(pointwise) C², `speed γ ≠ 0`, and `1 − dκ > 0` if the offset arc is to be read by a box
(R0 §5.1). Where `κ = 0` the `ψ`-parametrization itself fails (Lemma 1.5); that is flagged per
row. The offset *equation* `R(ψ) − dψ = x` is meaningful even when the box readout is not, so
the rows are stated for the equation, with readout remarks where they differ.

---

## 0. Verdicts

Every base curve of `Defs.lean` has a Whewell function that is the antiderivative of the
radius of curvature in the angle variable, `R'(ψ) = 1/κ(ψ)` (Lemma 1.1). Four consequences
organise the whole catalogue, and they are the reason this note is short where R0 and R5 were
long.

1. **`d` never changes the genus.** The offset element is `(1 − dκ)·s dt = s dt − d·(dψ/dt)dt`,
   and for every rationally parametrized curve `dψ/dt` is a *rational* function of the
   parameter. So the equation is `(an abelian integral of the base curve) − d·(an elementary
   function) = x` (Lemma 1.3). The ψ term is therefore never a new transcendent and never
   raises the genus; it is exactly the elementary (logarithmic/third-kind) summand.
2. **The genus is read off `z² = speed²`.** For a polynomial graph of degree `p` it is `p − 2`;
   for a power law `y = x^p` it is `num(p − 1) − 1`. The two rules agree on `y = x^d`, and both
   are invariant under every nondegenerate affine map (Lemmas 1.4, 4.2, 5.6).
3. **Elementarity is exactly genus 0.** Polynomial graphs: degree ≤ 2 (a cubic is *always*
   genus 1 over ℝ — the exceptional cubics exist only over ℂ, §4.3). Power laws: `p − 1 = 1/n`
   — this is Chebyshev's criterion, and the source note's stated form is correct but
   redundant (§5.1). The two genus-0 base curves are the parabola (degree 2, conic) and
   `exp_two`, whose `z² = speed²` is a conic in `y = 2^t` rather than in `x` (§8.2).
4. **"Absorbed" has a precise answer, and it is the same for the Bézier, the ellipse and the
   sheared sine.** The ψ term is absorbed in the sense that the equation stays one abelian
   integral on one curve, of unchanged genus; it is *not* absorbable into a single standard
   `E` or `F`, because it is not a multiple of `dR` and it survives as the third-kind
   (log/arctan) part (§6.3, §7.5, §9.4).

Curve by curve: **parabola** — one genuinely new family, elementary but irreducible; it is the
*simplest* member of the class "elementary `R` containing an explicit `gd⁻¹ψ = u` term", a class
that also contains the odd-`n` power laws (§5.6), and it is the right headline (L2) because its
`R = ¼sinh 2u + u/2` is the two-term minimum and its geometry (a `poly_graph`, a vertex, a
quartic readout) is the cleanest formalization target. **Cubic graph, cubic Bézier, ellipse,
sheared sine** — elliptic, genus 1, one new family each; none collapses.
**Quartic/quintic/sextic graphs, and power laws with `num(p − 1) ≥ 3`** — hyperelliptic of genus
≥ 2, no closed form, a family in principle and nothing usable in practice. **`exp_two`** —
elementary (genus 0) but irreducibly transcendental in ψ, and the "junk term" is unavoidable
under every affine map (§8.4). **Rectangle and lines** — trivial: the mechanism degenerates and
no equation is solved (§10).

---

## 1. The frame: five lemmas every row uses

Throughout, `γ` is C² on a window, `s = speed γ`, `κ` is the signed curvature (R0 §1),
`ψ` is a tangent angle with `ψ' = κ s`, `w = tan ψ`, `u = asinh w`, `gd u = ψ`,
`ρ := 1/κ` (signed radius of curvature), and `R` is the Whewell function `s = R(ψ)`.

### 1.1 Lemma (the angle-derivative of `R`). `R'(ψ) = ρ(ψ) = 1/κ`. [Proof]

`R(ψ(t)) = s(t)` by definition, so differentiating in `t` and using `ψ' = κ s`,

```
dR/dψ = (ds/dt)/(dψ/dt) = s/(κ s) = 1/κ . ∎
```

Thus **the Whewell function is the antiderivative of the radius of curvature, in the angle
variable**. Every closed form in this note is an instance of this one line, and every genus
statement is a statement about `∫ρ dψ`.

### 1.2 Lemma (the `u` coordinate). [Proof]

With `w = tan ψ = sinh u` we have `dψ/du = sech u`, hence

```
S(u) := ds/du = ρ(ψ(u))·sech u ,        A(u) := ∫ S du ,
```

and the equation `R(ψ) − dψ = x` becomes `A(u) − d·gd(u) = x + const`. Also
`x = ∫ S sech u du`, `y = ∫ S tanh u du` recover the curve from `S` (source note §2; immediate
from `dx/ds = cos ψ`, `dy/ds = sin ψ`, `dψ/du = sech u`).

### 1.3 Lemma (the ψ term is elementary, and adds no elliptic content). [Proof]

Let `γ` be rationally parametrized, `γ(t) = (N₁(t)/D(t), N₂(t)/D(t))`. Then

```
κ s = ψ' = (x'y'' − y'x'')/(x'² + y'²) ,
```

a **rational function of `t`** (numerator and denominator are polynomials). Therefore

```
(1 − dκ)·s dt = s dt − d·(dψ/dt) dt ,                                       (1.3.1)
```

the first term is the base arc element `ds` (an abelian differential of the second kind on the
algebraic curve `z² = speed²`), and the second is `d` times an **exact** differential. Hence

```
R(ψ) − dψ = [second-kind abelian integral on z² = speed²] − d·[elementary function] .   (1.3.2)
```

Since an elementary antiderivative of a rational function is rational plus logarithms plus
arctangents, and logs/arctangents are the third-kind pieces, the honest bookkeeping is:

> **`R` is second kind; the `ψ` term is third kind (logarithmic) or rational; `d` mixes the
> two but changes neither the curve nor the genus.**

Two corollaries used constantly below.

* `d` is a *coefficient*, never a deformation: the reachable set for fixed `γ` and varying `d`,
  `x` is the two-parameter family `{R(ψ) − dψ = x}` on one curve.
* The ψ term is **not** absorbable into a single `E`/`F`: `dψ` is exact but not a multiple of
  `ds` (unless the curve is a circle), so `R − dψ` is not `c·E(amplitude|modulus)` for any
  standard `E`. It is one abelian integral, not one *standard* integral. This is the precise
  answer to the Bézier/ellipse question posed in §R1.

**Caveat.** (1.3.1) needs `speed ≠ 0` but *not* `κ ≠ 0`. Where `κ = 0` the ψ-parametrization
fails (Lemma 1.5) while the arc element is still fine, so the `t`-form of (1.3.1) is the
safe one.

### 1.4 Lemma (genus bookkeeping). [Proof]

Suppose the arc element can be written `ds = √(Q(t)) dt` with `Q` a polynomial of degree `n`
having distinct roots. Then `R = ∫√Q dt` lives on the hyperelliptic curve `z² = Q(t)`, whose
genus is

```
g = ⌊(n − 1)/2⌋ .
```

* **Polynomial graph** `y = p(x)`, degree `p = p_deg`, under a linear map
  `(x,y) ↦ (ax + by, cx + ey)`: the tangent is `(1, p')`, so
  `speed² = (a + bp')² + (c + ep')² = A + B p'(x) + C p'(x)²`, a polynomial of degree
  `2·deg p' = 2(p_deg − 1)`. Hence `g = p_deg − 2` for every affine image. [Proof]
* **Power law** `y = a x^p`: put `p − 1 = A₀/B₀` in lowest terms and `x = τ^{B₀}`. Then
  `speed = τ^{B₀−1}√(B₀² + a²(A₀+B₀)²τ^{2A₀})`, so `ds` lives on `z² = B₀² + c τ^{2A₀}`, of
  degree `2A₀`: `g = A₀ − 1 = num(p − 1) − 1`. [Proof] (Same computation after any linear map,
  §5.6.)
* **Genus 0 ⟺ elementary** for these integrals: `g = 0` means `z² = Q` is a conic, which is
  rationally parametrized, so `∫√Q dt` is elementary. Conversely a genus-`g ≥ 1` hyperelliptic
  integral of the second kind is not elementary (Liouville; standard). [Proof, modulo the
  standard Liouville theorem]

### 1.5 Lemma (inflections break the ψ-parametrization). [Proof]

At a point with `κ = 0`, `R'(ψ) = 1/κ` is infinite: `ψ` is stationary in `s`, so `R` is not a
`C¹` function of `ψ` there (it has a vertical tangent). The equation `R(ψ) − dψ = x` must then
be read on each branch `κ > 0` / `κ < 0` separately — exactly R0 §6.3's remark that "when `κ`
changes sign `R` is not a single-valued function of `ψ`". Odd-degree graphs (including
`y = x³`, §4.4) and general Béziers have such points; the parabola, the ellipse and
`exp_two` do not.

---

## 2. Master table

`w = tan ψ`, `u = asinh w`, `p_deg = deg p`, `A₀/B₀ = p − 1` in lowest terms, `e² = 1 − b²/a²`
for the ellipse. "Collapses" means: reduces to a *single* equation `Φ(ψ) = αψ + β` with `Φ` one
elementary function, hence within reach of one intersection of two drawable curves — the sense
in which the source note calls Neile's parabola a collapse.

| # | curve | `R` in the clean coordinate | elementary? | genus / kind | equation `R − dψ = x` | collapses? |
|---|---|---|---|---|---|---|
| 1 | parabola `y = x²/2`, all affine images | `½(w√(1+w²) + asinh w) = ¼sinh 2u + u/2 = ½(secψ tanψ + gd⁻¹ψ)`, scale `p` and shift `ψ₀` | **yes** | genus 0; elementary, transcendental in ψ | `p·½(sec φ tan φ + gd⁻¹φ) − dψ = x`, `φ = ψ − ψ₀` | **no** (even for `d = 0`: two independent terms) |
| 2 | `poly_graph`, degree `p_deg ≤ 6` | `∫√(A + Bp' + Cp'²)dx` (`A,B,C` from the linear map); plain graph: `∫√(1+p'²)dx` | iff `p_deg ≤ 2` | `g = p_deg − 2`: 3 → 1, 4 → 2, 5 → 3, 6 → 4 | `∫√Q − dψ = x` | no (except `p_deg = 1`) |
| 3 | power laws `y = a x^p`, `p ∈ ℚ` | `S = (n/p^n)cosh²u(sinh u − m)^{n−1}`, `n = 1/(p−1)`; `A = (n/(2p^n))·B(tanh²u; n/2, −(n+1)/2)` | iff `p − 1 = 1/n` | `g = A₀ − 1 = num(p−1) − 1` | `A(u) − d·gd u = x` | at `d = 0` iff `n` is even (`R` a polynomial in `sec ψ`); `n = 2` is Neile |
| 4 | cubic Bézier | `∫√Q₄(t)dt`, `Q₄ = γ'·γ'` | **no** | genus 1; second kind (+third kind from `ThirdKind`'s `Π`) | `∫√Q₄ − dψ = x`, `ψ` elementary | no |
| 5 | ellipse | `R = a[E(m) − E(π/2 − φ(ψ); m)]`, `m = e² = 1 − b²/a²` | **no** | genus 1; second + third kind | `s(φ) − dψ(φ) = x` | only the circle `a = b` (`R = aψ`) |
| 6 | `exp_two` `y = 2ˣ`, affine images | `R = (1/ln2)(secψ − ln(1+secψ) + ln tanψ)` for `b = 1` | **yes** | genus 0 (conic); elementary | `R(ψ) − dψ = x` | no (elementary but irreducible) |
| 7 | sheared sine `(−bt + sin t, at)` | `Λ(t) + …`, `Λ = ∫√((cos t − b)² + a²)dt`: `E`, `F`, `Π` | **no** | genus 1; second + third kind | `Λ − d·arctan(a/(cos t − b)) = x` | no (`a = 0` degenerate) |
| 8 | rectangle, line segments | none: `ψ` constant on each side | — | — | degenerates | **completely** |

---

## 3. Row 1 — the parabola and every affine image

### 3.1 `R` in the three coordinates. [Proof + Wolfram]

Parametrize `γ(w) = (w, w²/2)`, the `poly_graph` with `p = X²/2`. Then
`γ' = (1,w)`, `s = √(1+w²)`, `κ = 1/(1+w²)^{3/2}`, `ψ = arctan w`, `w = tan ψ`, and by Lemma
1.1

```
R'(ψ) = 1/κ = sec³ψ ,     R(ψ) = ∫ sec³ = ½(sec ψ tan ψ + ln(sec ψ + tan ψ)) = ½(secψ tanψ + gd⁻¹ψ).
```

In `w`: `R = ½(w√(1+w²) + asinh w)`; in `u` (`w = sinh u`, `√(1+w²) = cosh u`):

```
R = ¼ sinh 2u + u/2 .                                                     (3.1)
```

[Wolfram] `D[R(w),w] − √(1+w²) = 0`; `D[R(w) − d·arctan w, w] − (√(1+w²) − d/(1+w²)) = 0`;
`R(2) − ∫₀²√(1+x²)dx = 0``39.5. The `ψ` form is exact because `asinh(tan ψ) = gd⁻¹ψ`
[Wolfram: `ArcSinh[Tan p] − Log[Sec p + Tan p] = 0` under `−π/2 < p < π/2`; `FullSimplify`
does not do it unaided, which is worth knowing for L2].

`κ > 0` everywhere, so Lemma 1.5 does not bite: `R` is a global `C^∞` function of `ψ` on
`(−π/2, π/2)`.

### 3.2 Why every affine image gives the same family. [Proof]

**Claim.** If `A` is an invertible affine map and `γ` is a parabola with vertex radius of
curvature `p` and vertex tangent angle `ψ₀`, then `Aγ` is a parabola and

```
R_{Aγ}(ψ) = p·½(sec φ tan φ + gd⁻¹φ) + const ,      φ = ψ − ψ₀ .          (3.2)
```

*Proof.* An invertible affine map takes a parabola to a parabola (a conic of eccentricity 1 to
a conic of eccentricity 1, since eccentricity is an affine invariant of conics). All parabolas
with the same `p` are similar, and for the standard parabola `ρ(ψ) = p sec³(ψ − ψ₀)` — this is
`κ = 1/(1+w²)^{3/2}` with `w = tan(ψ − ψ₀)` and `p = ρ` at the vertex. Hence `R' = ρ` is
(3.2)'s derivative, and `R` is determined up to a constant, i.e. up to the choice of arc-length
origin. ∎

**The equation family is unchanged.** Replacing `(p, d, x)` by `(1, d/p, x/p)` and `ψ` by
`ψ + ψ₀` is a bijection of the data `(d, x)` — and `d`, `x` are free P-constructible
parameters, `ψ₀` a P-constructible shift. So for every affine image the reachable set is
literally the same two-parameter family as for `y = x²/2`, up to rescaling `d` and `x` and
shifting the unknown. **Nothing new appears.** [Proof]

**Warning, and a trap I fell into.** The vertex of the *image* is not the image of the vertex:
an affine map does not preserve the extremal points of `κ` unless it is conformal. For
`A = [[2,1],[1,3]]` applied to `(t,t²/2)` the image's curvature is extremal at `t = −1/2`, not
at `t = 0`, so the naive `p = 1/|κ(0)| = √5` is **wrong**; the correct value is
`p = 1/|κ(−1/2)| = √(5/2)/2`. This matters for any Lean statement that identifies "the
vertex" after an affine map.

### 3.3 Numerical confirmation of (3.2). [Wolfram]

Two non-similar affine maps, checking `s(t) − s(t_v) = p[F(ψ − ψ₀) − F(0)]` at four
parameters each (working precision 35, `F = ½(sec tan + gd⁻¹)`):

| `A` | vertex `t_v` | `p` | `ψ₀` | max residual |
|---|---|---|---|---|
| `[[2,1],[1,3]]` | `−1/2` | `√(5/2)/2 = 0.790569…` | `−arctan(1/3) = −0.321751…` | `0``34.85` |
| `[[3,0],[1,1]]` | `−1/2` | `9/2` | `0` | `0``34.60` |

### 3.4 The equation, and why it does not collapse. [Proof]

For `d < 1` (cusp-free, R0 §5.3) and `x ≥ 0` the equation `Φ(w) = R(w) − d arctan w = x` has a
unique solution `w ≥ 0` with `Φ' = (s³ − d)/s² > 0`; this is R0 §5.3 and L2's content.
**Collapse:** even at `d = 0` the equation is `secψ tanψ + gd⁻¹ψ = 2x`, a sum of two
independent elementary functions of `ψ`. One intersection can solve `Φ(ψ) = αψ + β` for a
*single* `Φ`; it cannot solve a sum of `sec tan` and `gd⁻¹` unless one eliminates `ψ` between
them, which is exactly the transcendence the construction is built on. So no collapse —
consistent with the source note, which never claimed one.

---

## 4. Row 2 — polynomial graphs of degree `≤ 6`

### 4.1 The general shape. [Proof]

For `y = p(x)`, `ψ = arctan p'(x)` and `ds = √(1+p'²)dx`, so

```
R = ∫ √(1 + p'(x)²) dx          (as a function of x),       R'(ψ) = ρ = (1+p'²)^{3/2}/p'' .
```

Under a linear map `A = [[a,b],[c,e]]` the tangent `(1,p')` goes to `(a + bp', c + ep')`, so

```
speed² = (a + bp')² + (c + ep')² = A + B p'(x) + C p'(x)² ,                 (4.1.1)
```

with `A = a² + c²`, `B = 2(ab + ce)`, `C = b² + e² > 0`. This is a polynomial in `x` of degree
`2(p_deg − 1)`, so by Lemma 1.4 the genus is `p_deg − 2` **for every affine image**. In
particular (4.1.1) is exactly the shape quoted in `ThirdKind.lean` line 279, and the residue
argument there (the expansion in `1/p' ~ 1/t²`) applies to all of them.

Also `R' = 1/κ` blows up at an inflection; by Lemma 1.5 the ψ-form must be read branchwise
there. For even-degree `p` there is no real inflection; for odd degree ≥ 3 there is one.

### 4.2 Genus table. [Proof + Wolfram]

| `p_deg` | `deg speed²` | genus | Wolfram classification of `∫√(1+p'²)dx` |
|---|---|---|---|
| 1 | 0 | 0 | elementary |
| 2 | 2 | 0 | elementary |
| 3 | 4 | 1 | `EllipticF` |
| 4 | 6 | 2 | `Hypergeometric2F1` |
| 5 | 8 | 3 | hypergeometric (no elliptic reduction) |
| 6 | 10 | 4 | hypergeometric (no elliptic reduction) |

[Wolfram] `Integrate[Sqrt[1+(d x^{d−1})²], x]` for `d = 1,…,6` returns: elementary,
elementary, `EllipticF`, `Hypergeometric2F1`, hypergeometric, hypergeometric. Explicitly for
the representatives:

```
p = x²   :  R = ½x√(1+4x²) + ¼ asinh(2x)
p = x³   :  R = [(3(x + 9x⁵) − 2(−1)^{1/4}√(3+27x⁴)·EllipticF[i asinh((1+i)√(3/2)x), −1])] / (9√(1+9x⁴))
p = x⁴   :  R = x·Hypergeometric2F1[−1/2, 1/6, 7/6, −16x⁶]
```

(These are Wolfram's own outputs, quoted to show the *class*; the `x³` line is elliptic with an
imaginary modulus, which is the standard real form after a Möbius reduction.)

### 4.3 Special cubics: none over ℝ; a family over ℂ. [Proof + Wolfram]

A repeated root of `1 + p'²` at `x₀` needs `p'(x₀)² = −1` and hence `2p'(x₀)p''(x₀) = 0`, i.e.
`p'(x₀) = ±i` **and** `p''(x₀) = 0`. For real (in particular rational) coefficients `p'(x₀)` is
real, so `p'(x₀)² = −1` is impossible:

```
[Wolfram] Reduce[∃x, 1 + (u x² + v x + w)² = 0 ∧ (2ux + v) = 0]  with u,v,w real  ⟹  False.
```

Hence **every cubic with rational coefficients is genuinely genus 1; there is no exceptional
cubic.** Over ℂ there is a two-parameter family, `p'(x) = a(x − c)² ± i`, where the double root
occurs at `x = c` and the genus drops to 0; it is not reachable from `poly_graph`'s rational
coefficients. This is the precise answer to "what about the special cubics": the only special
ones are complex, and `poly_graph` cannot draw them.

One further remark: `p_deg = 0` or a constant `p'` is a line, §10.

### 4.4 Representative worked rows.

**(a) `p = X²` (degree 2).** Speed `√(1 + 4x²)`; slope `w = 2x`; `ψ = arctan(2x)`;
`R = ½(w√(1+w²) + asinh w)/2` after rescaling — literally Row 1 with `p = 1/2` in the graph
`y = x²/(2p)`. Genus 0, elementary, no collapse. This is why "degree ≤ 2" and "the parabola"
are the same row up to scale.

**(b) `p = X³` (degree 3).** `speed² = 1 + 9x⁴`, genus 1; Wolfram's antiderivative contains
`EllipticF` with imaginary modulus. Inflection at `x = 0` (`κ = 6x/(1+9x⁴)^{3/2}`), so the
ψ-form has a vertical tangent at `ψ = 0` and the equation must be stated branchwise
(Lemma 1.5). Not elementary; no collapse.

**(c) `p = X⁴` (degree 4).** `speed² = 1 + 16x⁶`, genus 2 (a genuine hyperelliptic curve, not
reducible to elliptic). Not elementary; no collapse; **no standard closed form exists**, which
is the honest statement: Wolfram returns a `₂F₁`, not an `E`.

**(d) `p = X⁶` (degree 6).** `speed² = 1 + 36x^{10}`, genus 4. Nothing usable.

**Affine images** of (a)–(d) change only `A`, `B`, `C` in (4.1.1) and hence the specific
differential on the same genus; the genus is unchanged (Lemma 1.4), the elementarity is
unchanged (genus 0 ⟺ elementary), and the ψ term remains elementary by Lemma 1.3. So for
polynomial graphs the affine direction adds **no new cases at all** beyond a three-parameter
family of differentials on a fixed genus — the opposite of the power-law case (§5.6), where the
affine direction does add a parameter (the exponent denominator is fixed but the branch points
move).

---

## 5. Row 3 — power laws `y = a x^p`

Write `n := 1/(p − 1)`, so `p = 1 + 1/n`; the models are `y = x^{1+1/n}` and its y-shear
`y = x^{1+1/n} + m x`. Below, `a = 1` and the constant `a` is restored by rescaling `x`
(`x ↦ a^{−1/p}x`), which does not change the exponent or the class.

### 5.1 Chebyshev's criterion, verified. [Proof + Wolfram]

`ds = √(1 + p²x^{2p−2})dx` is the binomial integral

```
∫ x^0 (1 + c x^N)^q dx ,      N = 2p − 2 ,   q = 1/2 ,   c = p² .
```

Chebyshev's theorem: for `q, N ∈ ℚ` this is elementary iff one of `q`, `(m+1)/N`,
`(m+1)/N + q` is an integer, where `m` is the exponent of `x^m` outside the bracket. Here
`m = 0`, so

```
q = 1/2 ∉ ℤ ;
(m+1)/N = 1/(2p−2) ∈ ℤ   ⟺   p − 1 = 1/(2k) ;
(m+1)/N + q = 1/(2p−2) + 1/2 ∈ ℤ   ⟺   p − 1 = 1/(2k−1) .
```

The union is `{1 + 1/n : n ∈ ℤ \ {0}}`, i.e. **`R` is elementary exactly when `(p − 1)^{-1}`
is an integer**. [Proof]

**Verdict on the source note's phrasing.** The note says "elementary exactly for `p = 1 + 1/n`
and `p = 1 + 1/(2k−1)`". That is *correct but redundant*: if `n` ranges over the integers,
`1 + 1/n` already covers even and odd `n` and both signs, so the second clause is contained in
the first; if `n` is restricted to positive integers, the second clause is exactly what supplies
`p < 1` (e.g. `k = 0` gives `p = 0`). The clean statement is `(p−1)^{-1} ∈ ℤ`. [Proof]

[Wolfram] `Integrate[√(1 + (p x^{p−1})²), x]` classified at 20–40 digit working precision:

| `p` | `1/(p−1)` | elementarity (Wolfram) | criterion | match |
|---|---|---|---|---|
| `1/2` | `−2` | elementary | yes | ✔ |
| `4/3` | `3` | elementary | yes | ✔ |
| `5/4` | `4` | elementary | yes | ✔ |
| `3/2` | `2` | elementary | yes | ✔ |
| `2` | `1` | elementary | yes | ✔ |
| `5/3` | `3/2` | elliptic-hypergeometric | no | ✔ |
| `7/4` | `4/3` | elliptic-hypergeometric | no | ✔ |
| `3` | `1/2` | elliptic-hypergeometric | no | ✔ |

The `p = 3` entry is Row 2's `y = x³` and the `p = 7/4` entry is genus 2: the criterion and the
genus formula of §5.6 agree on every tested point.

### 5.2 The source formula `S ∝ cosh²u (sinh u − m)^{n−1}`, verified. [Proof + Wolfram]

With `p = 1 + 1/n` and `y = x^p + m x`:

```
w = tan ψ = p x^{1/n} + m   ⟹   x = ((w − m)/p)^n ,   dx/dw = n(w − m)^{n−1}/p^n ,
S(u) = ds/dw · dw/du = √(1+w²)·n(w−m)^{n−1}/p^n · cosh u
     = (n/p^n)·cosh²u·(sinh u − m)^{n−1} ,      w = sinh u .                     (5.2.1)
```

[Wolfram] symbolic residual `0` for `n = 2` and `n = 3` (with `m` and `u` symbolic; the only
non-cancelling factor is `√(cosh²u) = cosh u`, which vanishes as a difference because `cosh u >
0`); numeric residual `0``6024` (i.e. zero at the 40-digit working precision, reported with a
6000-digit accuracy marker) for `n = 1/2, 5/3, 7/4` at `u = 7/10`, `m = 3/10`.

**Three structural readings of (5.2.1):**

* `n = 1` (`p = 2`, the parabola): the exponent is `0`, so the `m`-dependence **drops out
  entirely**: `S ∝ cosh²u`. This is Row 1's "all parabolas are similar", recovered from the
  formula — a good consistency check on both. [Proof]
* `n = 2` (`p = 3/2`, Neile): `S ∝ cosh²u(sinh u − m)`, and the source note's
  `cosh³u/3 − m(sinh2u/4 + u/2)` is the integral. [Wolfram] residual against `∫₀^u` is
  `−1/3` for every tested `m` — the constant `−cosh³(0)/3`, i.e. the formula is
  `A = cosh³u/3 − 1/3 − m(sinh 2u/4 + u/2)` exactly. [Proof + Wolfram]
* `n ≠ 1`: the shear `m` moves the branch point in `S` from `0` to `m` and is **not** undone by
  any reparametrization of `u`; this is what "shears matter" means, made precise in §5.4.

### 5.3 The incomplete-Beta form for non-elementary `p`. [Proof + Wolfram]

`S = (n/p^n)cosh²u sinh^{n−1}u`, so

```
A(u) − A(0) = (n/p^n)∫₀^u cosh²v sinh^{n−1}v dv .                              (5.3.1)
```

Put `σ = sinh v`, then `ζ = tanh²v`: `dζ = 2σ/(1+σ²)² dσ`, `σ^{n−1}√(1+σ²)dσ =
½ ζ^{n/2−1}(1−ζ)^{−(n+3)/2}dζ`, hence

```
∫₀^u cosh²v sinh^{n−1}v dv = ½ B(tanh²u ; n/2, −(n+1)/2) ,                     (5.3.2)
A(u) = A(0) + (n/(2p^n))·B(tanh²u ; n/2, −(n+1)/2) ,
```

with `B(z;a,b) = ∫₀^z t^{a−1}(1−t)^{b−1}dt` the incomplete Beta function. The second parameter
is negative, which is harmless on `0 ≤ z < 1` (the integrand is `t^{n/2−1}(1−t)^{−(n+3)/2}`,
integrable at `t = 1`). [Proof]

[Wolfram] (5.3.2) residual `0``40.3`, `0``40.4`, `0``40.5` at `u = 7/10` for `n = 3/2, 5/3, 2`.
This is the "incomplete-Beta form for the non-elementary `p`" requested in §R1; note it covers
the elementary cases too, where the Beta degenerates to a polynomial in `sinh u` (n even) or to
`sinh u·√(1+sinh²u)` plus `asinh` (n odd).

**Genus in this form.** (5.3.2) is an integral on `z² = 1 + τ^{2A₀}` after `σ = τ^{A₀}` (where
`p − 1 = A₀/B₀`; §5.6), so the genus is `A₀ − 1`. This is visible directly in the Beta: the
denominator `A₀` of `n = B₀/A₀` is the exponent whose `τ ↦ τ^{A₀}` substitution produces the
degree-`2A₀` polynomial.

### 5.4 Affine images I: shears, and how they "mix families". [Proof + Wolfram]

A y-shear `(x,y) ↦ (x, y + mx)` sends `w = p x^{1/n}` to `w = p x^{1/n} + m`, which is exactly
the model used in (5.2.1). So:

* **the shear is absorbed into `m`** and the whole one-parameter family `{y = x^p + mx}_m` has
  the single formula (5.2.1);
* **for `n = 1` the family collapses** (`m` disappears) — parabolas again;
* **for `n ≠ 1` the family is genuinely one-parameter**: different `m` give different curves
  (not similar: `y = x^{3/2} + x` is not similar to `y = x^{3/2}`), and different `S`.

So "shears matter" is precisely: *the y-shear is the one affine direction that keeps the
explicit Beta formula, at the price of a new parameter `m`; every other affine direction loses
the formula* (§5.6). [Proof]

### 5.5 Affine images II: the Möbius action of a non-conformal stretch. [Proof + Wolfram]

For `A = [[a,b],[c,e]]` the tangent `(1, w)` goes to `(a + bw, c + ew)`, so

```
tan ψ' = (c + e·tan ψ)/(a + b·tan ψ) ,        w' = (c + ew)/(a + bw) .          (5.5.1)
```

[Wolfram] `(c + ew)/(a + bw) − (A·(1,w))₂/(A·(1,w))₁ = 0` identically.

`A` is a similarity iff `AᵀA = λI`; a pure rotation has `b ≠ 0` and `c ≠ 0`, so **the Möbius map
is non-affine already for a rotation**. That is consistent, because a rotation does not change
the curve at all: `R` is intrinsic, and (5.5.1) is a change of the *angle variable*, not of the
curve. The correct reading of (5.5.1) is therefore:

* **similarity** (`AᵀA = λI`): `R_{Aγ}(ψ) = λ R_γ(ψ − ψ_rot) + const`. Same function.
  [Proof]
* **y-shear + stretch** (`b = 0`): `w' = (c + ew)/a` is *affine* in `w`, so `x` is a pure power
  of an affine function of `w'`, `dx/dw' ∝ (w' − m')^{n−1}`, and `S ∝ cosh²u'(sinh u' −
  m')^{n−1}`: the Beta presentation survives with a moved `m'`. [Proof]
* **genuine Möbius** (`b ≠ 0`): `dx/dw'` is a fractional power of a Möbius function of `w'`,
  hence **not** a pure power, and the presentation (5.2.1) is lost. [Proof]

### 5.6 The genus is affine-invariant, and what that does and does not say. [Proof]

Let `p − 1 = A₀/B₀` in lowest terms and put `x = τ^{B₀}`, so `w = p τ^{A₀}`. For
`A = [[a,b],[c,e]]`,

```
speed² = (a + bw)² + (c + ew)² = quadratic in w = quadratic in τ^{A₀} ,
```

a polynomial of degree `2A₀` in `τ` with distinct roots generically. Hence

```
g(R_{Aγ}) = A₀ − 1 = num(p − 1) − 1       for every nondegenerate A.           (5.6.1)
```

[Wolfram] the genus table for `p ∈ {4/3, 5/3, 7/4, 8/5, 7/3, 3, 4}` matches (5.6.1) exactly
(`0,1,2,2,3,1,2`), and each entry with `g ≥ 1` is classified elliptic/hypergeometric while the
`g = 0` entry is elementary.

So the answer to "does `R` stay in the same Beta/elliptic family?" is a two-level one:

* **genus and kind: always the same** — `A₀ − 1`, second kind, with the ψ term adding the
  third-kind piece (Lemma 1.3);
* **the explicit Beta (or `E`/`F`) presentation: only for `b = 0`** (similarity or
  y-shear-plus-stretch). For a genuine stretch such as `A = [[2,1],[1,3]]` applied to
  `y = x^{5/3}` one gets `w = (5/3)τ²`, `x = τ³`, `√(quadratic in τ²)dτ` — a different genus-1
  differential, expressible in `E`/`F` but not in Beta form. [Proof]

**Consequence for the catalogue.** The affine direction over a power law adds a four-parameter
family of *differentials* on a fixed genus; it adds **no new elementary/elliptic dichotomy and
no new named equation family**. The only genuinely new equation families in Row 3 are:

* `n` even, `d = 0`: `R = Φ(sec ψ)` with `Φ` a polynomial, so the equation is `Φ(secψ) = x` —
  Neile's collapse, and its `n = 4` sibling `sec⁵ψ/5 − sec³ψ/3 = x`. [Proof]
* `n` odd, `d = 0`: `R = P(tanψ)·secψ + c·gd⁻¹ψ` with `P` a polynomial — two independent
  elementary functions, no collapse. [Proof, from `∫(1+σ²)^{1/2}σ^{n−1}dσ` with `n−1` even]
* `d ≠ 0`: `R − dψ` is never a single tower function (the linear `dψ` is independent of the
  `sec`/`tan`/`gd⁻¹` content), so **nothing collapses once `d ≠ 0`**. [Proof]

This is the sharp form of the source note's Neile sentence: the collapse is a `d = 0`, `n` even
phenomenon, and the smallest non-collapsing deformation is `d ≠ 0`.

---

## 6. Row 4 — the general cubic Bézier

### 6.1 The differential data. [Proof]

Let `Γ(t) = Σᵢ Bᵢ(t) pᵢ`, `t ∈ [0,1]`, with control points `p₁,…,p₄`. Then `Γ'` is *quadratic*
in `t`, so

```
Q(t) := |Γ'(t)|²  is a quartic ,        N(t) := x'y'' − y'x''  is a quadratic ,
κ = N/Q^{3/2} ,      dψ/dt = κ·speed = N/Q  —  a RATIONAL function of t .
```

(By Lemma 1.3 this rationality is the whole story of the ψ term.) Also

```
(1 − dκ)·speed·dt = (√Q − d·N/√Q)dt = (Q − dN)/√Q · dt ,                        (6.1.1)
```

a **second-kind differential on `z² = Q(t)` with a quartic numerator**, for every `d`.

### 6.2 A worked Bézier. [Wolfram]

Control points `(0,0), (1,2), (3,1), (4,0)` (deliberately asymmetric so that `Q` is *not* even):

```
Q(t) = 45 − 180t + 432t² − 396t³ + 117t⁴ ,     deg Q = 4 ,  deg N = 2 ,  Q not even .
```

* `dψ/dt − N/Q = 0` identically. ✔
* `∫√Q dt` is classified elliptic (`EllipticE`/`EllipticF` combination): genus 1. ✔
* the offset identity `∫(1 − ⅓κ)s dt = ∫s dt − ⅓Δψ` holds to `0``38.99` on `[0,1]`. ✔

### 6.3 Verdict: the ψ term is *not* a new independent function. [Proof]

This settles the question posed in §R1. `dψ = (N/Q)dt` is rational, so as a function of `t`
**`ψ` is elementary** (an arctangent of a rational function of `t`). Therefore

```
R(ψ) − dψ = ∫√Q dt − d·ψ(t)  =  [second-kind elliptic integral] − d·[elementary] .   (6.3.1)
```

Three things follow, and they are the same three that hold for the ellipse and the sheared
sine:

1. **No new transcendendent.** There is one elliptic curve `z² = Q(t)`, not two functions.
2. **No genus change.** `d` never appears under the root; (6.1.1) is a second-kind differential
   on the same curve. Kind: second, plus the exact (third-kind/log) contribution of `dψ`.
3. **Not absorbable into a single `E` or `F`.** `dψ` is not a constant multiple of `ds`, so
   `R − dψ` cannot equal `c·E(amplitude|modulus)`; the ψ term survives as the
   arctangent/logarithmic summand. It is one abelian integral, not one *standard* one.

### 6.4 Relation to `ThirdKind.lean`. [Proof, citing that file]

`ThirdKind.lean` (lines 267–317) proves that a **general** cubic Bézier's arc length needs an
incomplete third-kind integral `Π(n; φ, c)` with `n = 1 + h² = sec²ψ₀ > 1`, and that the
symmetric Bézier used for `F` in `Pptc.Basic` has `n = 1` (no `Π`). So for a generic Bézier `R`
is already **second + third kind** before the offset is taken. The ψ term adds a further
third-kind (exact) summand of a different origin: `ThirdKind`'s `Π` comes from the pole of
`dt/√Q` at the Bézier parameter's infinity, while `dψ`'s contribution is the pole of `dψ/dt` at
`Q = 0`, i.e. at `speed = 0`. They are on the same curve but are not the same differential, and
there is no reason for them to merge. **Whether they can be made to merge by a choice of `d`
is [Open]** (§13, item 6).

### 6.5 Collapse. [Proof]

No. The equation is `(elliptic of genus 1) − dψ = x`, and an elliptic integral of the second
kind is not a tower function; no single intersection reaches it. Inflections (`κ = 0`, common
for Béziers) force the branchwise reading of Lemma 1.5.

---

## 7. Row 5 — the ellipse

### 7.1 The parametrization and the angle. [Proof + Wolfram]

`γ(φ) = (a cos φ, b sin φ)`, `a > b > 0`, eccentric anomaly `φ`. Then

```
γ' = (−a sin φ, b cos φ) ,   Q := |γ'|² = a² sin²φ + b² cos²φ = a²(1 − e² cos²φ) ,   e² = 1 − b²/a² ,
κ = ab/Q^{3/2} > 0 ,          tan ψ = y'/x' = −(b/a)cot φ .
```

The `tan ψ` relation determines `ψ` only modulo `π`; on `φ ∈ (0,π)` the velocity has `x' < 0`
and `y' > 0`, so `ψ ∈ (π/2, π)` and

```
ψ(φ) = π − arctan((b/a)cot φ) .                                                (7.1.1)
```

[Wolfram] at `φ = 7/10` both sides give `2.9495973053…`. (This corrects the branch of the
`arctan((b/a)cot φ)` written in §R1: with `γ` traversed counterclockwise and the `Defs.lean`
normal, it is `π` minus that arctangent, not the arctangent.)

`κ` is never zero and is maximal at `φ = π/2`, where `κ = a/b²`. Hence the offset is cusp-free
on the whole ellipse iff `d < b²/a`; for `a = 2, b = 1` that is `d < 1/2`.

### 7.2 `R` as an incomplete `E`, with the exact modulus. [Proof + Wolfram]

```
s(φ) = ∫₀^φ √Q dφ = a[E(e²) − E(π/2 − φ | e²)] ,                              (7.2.1)
```

where `E(m) = E(π/2|m)` is the complete integral and `E(·|m) = ∫₀^· √(1 − m sin²θ)dθ`; the
modulus parameter is **`m = e² = 1 − b²/a²`**. Equivalently `s = b·E(φ | 1 − a²/b²)`.
[Wolfram] both forms differentiate to `√Q` exactly (residual `0`); `dψ/dφ − ab/Q = 0`.

Composing (7.2.1) with (7.1.1), and inverting (7.1.1) as `φ(ψ) = arctan(−(b/a)cot ψ)` (plus the
`π` branch of (7.1.1)),

```
R(ψ) = a[E(e²) − E(π/2 − φ(ψ) | e²)] ,        φ(ψ) = arctan(−(b/a)cot ψ) .     (7.2.2)
```

So **`R` is an incomplete elliptic integral of the second kind with modulus `k = e`** (parameter
`m = e²`), evaluated at the amplitude `π/2 − φ(ψ)` where `φ` is a Möbius (cotangent) function of
`ψ`. [Proof + Wolfram]

### 7.3 The offset element. [Proof + Wolfram]

```
(1 − dκ)·√Q = √Q − d·ab/√Q = (Q − d·ab)/√Q .                                    (7.3.1)
```

The numerator is a *quadratic* in `sin φ`, the denominator `√Q` is the same quadratic: so the
offset arc is a second-kind differential minus `d·(ab/Q)·√Q` — and `ab/Q = dψ/dφ`, so the
second piece is exactly the exact differential `dψ`. [Wolfram] the identity holds to `0``39.6`
on `[0.2,1.2]`.

### 7.4 One worked root. [Wolfram]

`a = 2`, `b = 1`, `d = 1/2`, `x = 1/2`: the equation `s(φ) − ½ψ(φ) = 1/2` has

```
φ = 1.3685688391454295592860627030… ,    ψ = 3.0394344751432346019141740820… ,
s(φ) = 2.0197172375716173009570870410… ,   residual 0``28.4 .
```

### 7.5 Verdict: does the ψ term combine with `E`? [Proof]

**No, and here is exactly why.** Both `∫√Q dφ` and `∫dψ` live on the same elliptic curve
(genus 1), so `R − dψ` is one abelian integral. But `dψ = (ab/Q)dφ` and `ds = √Q dφ` are
different differentials: their ratio is `ab/Q^{3/2} = κ`, not a constant. Consequently

```
R(ψ) − dψ = a[E(e²) − E(π/2 − φ|e²)] − d·ψ(φ)
```

cannot be written as `c₁E(amplitude|m) + c₀` for any amplitude and modulus: the `E` part has
coefficient `1` and the `ψ` part coefficient `d`, and they are independent functions of `φ`.
The genus stays 1, the kind is **second (from `E`) plus third (from `ψ`)** — the `ψ` piece is
`arctan`, i.e. a logarithm with imaginary argument. What *does* combine is the two `E`'s of
(7.2.1) into one incomplete `E` plus a constant; that is the standard reduction, not the ψ
term.

### 7.6 Collapse: only the circle. [Proof]

If `a = b` then `Q ≡ a²`, `s = aφ`, and `φ = ψ − π/2` up to a constant, so `R(ψ) = aψ + c` and

```
R − dψ = (a − d)ψ + c = x     ⟹   ψ = (x − c)/(a − d) ,
```

a **linear equation**: total collapse. (`d = a` makes the offset degenerate to a point,
R0 §3.3(d).) For `a ≠ b` the equation is elliptic and does not collapse. This is the only
collapse in Rows 4–7.

---

## 8. Row 6 — `exp_two` and its affine images

### 8.1 `R` is elementary, with the source note's junk term. [Proof + Wolfram]

`exp_two` is `y = 2^x`, i.e. `γ(t) = (t, 2^t)`. Then `w = tan ψ = y' = 2^t ln 2`, so
`ψ ∈ (0, π/2)` and `dx/dw = 1/(w ln 2)`:

```
R = (1/ln2)∫ √(1+w²)/w dw = (1/ln2)[ √(1+w²) − ln((1 + √(1+w²))/w) ] .          (8.1.1)
```

In the angle, using `√(1+w²) = sec ψ`, `w = tan ψ`:

```
R(ψ) = (1/ln2)[ sec ψ − ln(1 + sec ψ) + ln tan ψ ] .                            (8.1.2)
```

[Wolfram] `D[R,w] − √(1+w²)/(w ln2) = 0`; (8.1.2) residual `0`; `R` against `∫₀^{13/10} speed`
residual `0``34.7`. So the source note's junk term `√(1+w²) − ln(1+√(1+w²))` is precisely
`sec ψ − ln(1+sec ψ)`, and it is **elementary**. The third term `ln tan ψ` is what makes `R`
look non-junk: `ln tan ψ = ln w = t ln 2`, i.e. a multiple of the parameter.

### 8.2 Why every affine image is elementary: the curve is a conic. [Proof + Wolfram]

For `A = [[a,b],[c,e]]`, `Aγ' = (a + b L y, c + e L y)` with `y = 2^t`, `L = ln 2`, so

```
speed² = (a + bLy)² + (c + eLy)² = α + βy + γy² ,    α = a²+c² , β = 2L(ab+ce) , γ = L²(b²+e²) ,
s = (1/L)∫ √(α + βy + γy²) dy/y ,                                               (8.2.1)
```

an integral of a square root of a **quadratic** over `y`: the algebraic curve `z² = α+βy+γy²`
is a **conic, genus 0**. So `R` is elementary for every affine image. [Proof]

[Wolfram] the general antiderivative is

```
√(α+βy+γy²) + 2√α·artanh( √γy/√α − √(α+βy+γy²)/√α )
             − (β/(2√γ))·log( β + 2γy − 2√γ√(α+βy+γy²) ) ,
```

classified elementary. At `β = 0` (the un-sheared `exp_two`) this collapses to
`√(1+w²) − ln(1+√(1+w²))`, i.e. (8.1.1): **the junk term is the `β = 0` slice of the general
artanh/log term.** [Proof + Wolfram]

### 8.3 Is the junk term unavoidable? [Proof + Wolfram]

**Yes, in a precise sense — but it is *not* an obstruction.**

* *Unavoidable*: the coefficient of the `artanh` in (8.2.1) is `2√α` with
  `α = a² + c² > 0` for every invertible `A`. It never vanishes, so the antiderivative always
  carries a logarithm/artanh of an algebraic function of `y`. [Wolfram] (general `α,β,γ`,
  symbolic); [Proof] (`α > 0`).
* *Not removable by `d`*: the equation is `R(ψ) − dψ = x`; `dψ` contributes a term **linear in
  `ψ`**, while the junk term is a logarithm of an algebraic function of `ψ`. A linear function
  cannot cancel a logarithm, for any `d`. [Proof]
* *But elementary*: unlike the Bézier and the ellipse, nothing here is elliptic. So `exp_two`
  produces a **new elementary family**, not a new elliptic one. The source note's word "junk" is
  fair as a description of the *shape* of the antiderivative, but the term is not an
  obstruction to decidability of the equation — it is an ordinary log.

This is consistent with `ThirdKind.lean` line 283: `exp_two` "does have a residue — but its
curve is rational, and that is where `log` came from rather than anything elliptic".

### 8.4 Collapse. [Proof]

No. At `d = 0` the equation is `secψ − ln(1+secψ) + ln tanψ = x ln2`, a mix of four independent
elementary functions of `ψ`; at `d ≠ 0` a fifth, `ψ`, joins. A single intersection solves
`Φ(ψ) = αψ + β` for one `Φ`; it cannot solve this mix. This is not a proved negative: the mix
of `sec`, `ln sec`, `ln tan` and `ψ` is exactly the pattern R3 must exclude, so it is recorded
here as a **separation-theorem obligation** (§13 item 7) and labelled [Open], not claimed.

---

## 9. Row 7 — sheared sines

### 9.1 The data. [Proof + Wolfram]

Normal form `γ(t) = (−bt + sin t, at)` (this is `atlas.wl`'s `shearedSineCurve[a,b]`). Then

```
γ' = (cos t − b, a) ,   Q := speed² = (cos t − b)² + a² ,   tan ψ = a/(cos t − b) .
```

`ψ` needs the same care as the ellipse: when `cos t < b` the velocity has `x' < 0`, so
`ψ ∈ (π/2, π)` and `ψ = π + arctan(a/(cos t − b))`. [Wolfram] `tan ψ − a/(cos t − b) = 0`;
`dψ/dt − a sin t/Q = 0` — again **rational**, hence elementary.

### 9.2 `Λ` and its closed form. [Proof + Wolfram]

```
Λ(t) := ∫√((cos t − b)² + a²) dt ,        R(ψ(t)) = Λ(t) + const .
```

*Genus 1.* With `u = tan(t/2)`: `√Q = √(Q₄(u))/(1+u²)` and `dt = 2du/(1+u²)`, so
`Λ = 2∫√(Q₄(u))/(1+u²)² du` — a **quartic under the root**, genus 1. The double pole at
`u = ±i` (from `(1+u²)²`) is the source of a third-kind term. [Proof]

[Wolfram] for `a = 1, b = 1/2` the antiderivative is an `E`/`F`/`Π` combination with
`k² = −63/65 + 16i/65` and `Π`-parameter `n = 1/13 + 8i/13`; the derivative check is exactly
`0`. So:

> **`Λ` is elliptic, genus 1, of mixed second and third kind; in the `tan(t/2)` variable
> Wolfram's closed form is `E`, `F` and `Π` at the complex modulus above.**

The complex modulus is an artefact of `tan(t/2)`; a real Möbius reduction would give a real
modulus and a real `n`. The structural content — genus 1, and a genuine `Π` — is
representation-independent.

### 9.3 The equation and the ψ term. [Proof + Wolfram]

```
Λ(t) − d·arctan(a/(cos t − b)) = x ,        (1 − dκ)√Q = (Q − d·a sin t)/√Q .
```

[Wolfram] the offset identity holds to `0``34.7` on `[0.2,1.2]` at `d = 1/2`; `a = 1, b = 1/2`,
`d = 1/2`, `x = 1` gives

```
t = 1.9741207383643481115035625062… ,   ψ = 2.2994401446775155570361934492… ,   residual 0``25.3 .
```

### 9.4 Verdict on the ψ term. [Proof]

Identical in structure to §6.3/§7.5: `dψ/dt` is rational, so `ψ` is elementary in `t`; the
equation is one second-kind elliptic integral minus `d` times an elementary function, on the
same genus-1 curve; and `dψ` is not a multiple of `ds`, so it is not absorbable into a single
`E`. The source note's form `R = Λ − d·arctan(a/(cos t − b))` is exactly this.

### 9.5 Degenerate cases and collapse. [Proof + Wolfram]

* `a = 0`: `speed = |cos t − b|`, elementary; the equation collapses to quadrature.
* `b = 0`: the pure sine `(sin t, at)`; [Wolfram] `∫√(cos²t + 1)dt` is still elliptic. So
  `b = 0` does **not** collapse.
* `b ≠ 0, a ≠ 0`: genus 1, no collapse.

---

## 10. Row 8 — rectangle and line segments

### 10.1 A line segment. [Proof]

For a segment, `κ ≡ 0`, so `ψ` is **constant** and `R'(ψ) = 1/κ = ∞`: `R` does not exist as a
function of `ψ` (it is a step, `R ≡ s₀` on the branch, with `ψ` fixed). The offset by `d` is a
congruent parallel segment, and laying an arc of length `x` along it is a pure translation by
`x` in the fixed direction `ψ`. Formally `R(ψ) − dψ = x` degenerates to `s₀ − dψ = x`, which
determines the *arc-length origin* `s₀` given `(d, ψ, x)`, never `ψ`. So:

> **No equation is solved. `d` has no effect on the endpoint, and the unknown `ψ` is not
> recoverable from `x`. Everything collapses — the mechanism is vacuous, not merely
> redundant.**

### 10.2 The rectangle. [Proof]

The rectangle is four segments; `ψ` takes four values and jumps by `π/2` at each corner. So
`R(ψ)` is a four-valued step function and is not a function of `ψ` at all. Along one side the
same degeneracy as §10.1 applies. Across a corner the tracing is not differentiable in the sense
required by `arc_of_length`'s `hdiff` (R0 §3.1), and `speed` is not continuous; so the arc cannot
be laid across a corner within the constructor's hypotheses. Therefore the rectangle adds
**nothing** to the catalogue, and is recorded here only so that the table is complete.

(One could `restrict` to a single side and then lay an arc; that is §10.1 again, and it solves
no equation.)

---

## 11. Synthesis: which curves give genuinely new equation families

Two base curves give a new family at genus 0. The parabola is the important one: `R = ½(secψ tanψ
+ gd⁻¹ψ)` is elementary, so no elliptic machinery is needed, yet the equation `R(ψ) − dψ = x`
contains an explicit `u` (the `gd⁻¹ψ` term) alongside `gd u`, and is irreducible — two independent
elementary functions plus the linear term. That is the whole reason the offset-inversion mechanism
is interesting, and it is why L2 is a parabola theorem and not an ellipse theorem. Four further
curves give one new family each, all at genus 1 and all in the same shape "second-kind elliptic
integral minus `d` times an elementary angle": the cubic polynomial graph, the cubic Bézier, the
ellipse and the sheared sine. They differ only in the differential (a quartic with a quadratic
numerator; a quartic with a quartic numerator plus `ThirdKind`'s `Π`; a quadratic with a constant
numerator; a quartic over `(1+u²)²` with a `Π`), not in the mechanism — so R2/R4 may treat them as
one class and R3 as one separation target. `exp_two` is the second genus-0 curve and the odd one
out: elementary, with no elliptic content at all, yet with an unavoidable logarithm, so it gives a
new *elementary* family that a separation theorem must handle separately. Power laws contribute a
clean two-parameter grid: genus `num(p−1) − 1`, elementary iff that is `0`, and a collapse only in
the even-`n`, `d = 0` corner (Neile and its `sec⁵` sibling); their odd-`n` members are the only
other curves whose `R` contains an explicit `u`, which is why they are the parabola's nearest
relatives among the power laws. Everything of degree ≥ 4 — polynomial graphs, power laws with
`num(p−1) ≥ 3` — is hyperelliptic of genus ≥ 2 and has no usable closed form, so it is a family on
paper only. Lines and rectangles contribute nothing. In one sentence: **the catalogue is one
elementary irreducible family (parabola) with its odd-`n` power-law relatives, four elliptic
families that share a single mechanism, one elementary-but-logarithmic family (`exp_two`), a
hyperelliptic tail with no closed form, and a degenerate floor.**

---

## 12. Missing curves, and the Whewell function each would supply

A curve is determined up to congruence by its Whewell function `R` with `R' > 0`
(reconstruction: `x = ∫R'(ψ)cosψ dψ`, `y = ∫R'(ψ)sinψ dψ`). [Proof: differentiate; the tangent
angle of the result is `ψ`.] So "which curve is missing" and "which `R` do I want" are the same
question, and the list below is exactly the list of `R`s not supplied by any `Defs.lean`
constructor or its affine images. (R5 already owns the named-problem side; this table is the
curve side.)

| missing curve | `R(ψ)` | `R'(ψ) = ρ` | what it unlocks (R5 rows) |
|---|---|---|---|
| catenary `y = a cosh(x/a)` | `a tan ψ` | `a sec²ψ` | `tan x = λx`, `j₁` zeros, gear involute (R5 6, 7) |
| log-cosine `y = ln sec x` | `gd⁻¹ψ = ln(secψ + tanψ)` | `sec ψ` | beam spectra, rhumb line, pendulum separatrix (R5 8–11) |
| tractrix | `−ln(−sin ψ)` (drawn branch) | `−cot ψ` | tractrix-with-length (R5 13) |
| Euler elastica | `F(ψ/2; m)` (first kind, genus 1) | `1/√(1−m sin²(ψ/2))`-type | elastica, rectangular elastica (R5 14) |
| goat curve | `tan ψ − (π/2)sec ψ` | `sec²ψ − (π/2)secψ tanψ` | goat grazing (R5 12), with the pole/fold obstruction |
| clothoid (Euler spiral) | `a√(2ψ)` | `a/√(2ψ)` | already collapsible: `R − dψ = x` is a quadratic in `√ψ` (R5 5) |
| circle involute | `aψ²/2` | `aψ` | collapses: quadratic in `ψ` |
| *any prescribed `R`* | `R` | `R'` | by Whewell's reconstruction, one curve per `R` |

The first five are the R5 "**M**" curves. The last two are worth recording because they are the
*positive* control: both are missing from `Defs.lean`, and both would add nothing, since their
`R` is a power of `ψ` and the equation collapses to a polynomial. This is a useful sanity check
on the catalogue: **a missing curve only matters if its `R` is not a polynomial in a single
function of `ψ`.**

---

## 13. Open items for R2 and R4

1. **[Open] Affine-after-offset (R2 §1).** `L_{A(P_d)} = ∫|Aγ'| − d∫(|Aγ'|/|γ'|)dψ`. The second
   term is a *weighted* angle integral. By Lemma 1.3 it is no longer exact, so it is the first
   place where the ψ term can raise the genus. Determine its genus for a polynomial graph and
   for the ellipse, and whether it is ever elementary. **This is the most likely place for a
   genuinely new family** and R1 does not settle it.
2. **[Open] Two-angle equations (R2 §2).** After affine-after-offset, one equation carries
   `arctan(slope)` and `arctan(Möbius(slope))`. §5.5 gives the Möbius map; whether the pair is
   independent for every non-similarity `A`, or only for `b ≠ 0`, is not settled.
3. **[Open] Genus of the tower (R2 §4).** §1.4 gives the genus for a single base curve. The
   genus of `R` for an arc that has been offset and then affinely mapped is not computed here;
   item 1 is the first case.
4. **[Open] Feeding parameters forward (R4 §1).** R1's Lemma 1.3 shows `d` is a coefficient and
   not a deformation, which is the R1-side input to R4's collapse argument. Whether outputs used
   as *new affine data* (§5.5) escape the one-equation class is R4's question.
5. **[Open] Can a two-step construction synthesise a missing `R`?** §12 says every missing
   curve is a missing `R`. R4 should test the five `M` rows against two-step constructions
   (offset of an offset, offset then affine, two offsets with independent `d`s).
6. **[Open] Bézier: do the two third-kind pieces merge?** `ThirdKind`'s `Π` (pole at the Bézier
   parameter's infinity) and the ψ term's log (pole at `speed = 0`) are different differentials
   on the same curve. Whether some `d` makes the combined differential have a single residue
   class is a concrete computation on the explicit quartic of §6.2, not done here.
7. **[Open] `exp_two`'s separation.** §8.4 says the equation mixes `sec`, `ln sec`, `ln tan` and
   `ψ`. That `R − dψ` is outside the single-intersection class is *not* proved here; it is an
   R3 obligation of exactly the same shape as the parabola's. Note that this row is *elementary*,
   so R3's analytic-continuation argument (which uses poles/accumulation of zeros of the angle
   function) must be adapted: there are no elliptic poles, only logarithmic ones.
8. **[Open] The goat curve's pole/fold (R5 §2.11).** R1 records the goat `R` in §12 but does not
   settle whether a legal arc can reach `β`. That is R4's item.

---

## 14. Numbers: backend and residuals

Backend: **Wolfram Language** via `wolfram_WolframLanguageEvaluator`, kernel `WorkingPrecision`
20–40 (checks at 25–40, symbolic identities exact). No mpmath was used.

**One deviation from the one-call rule, forced by the harness.** `atlas.wl` cannot be `Get`-ed
from the evaluator (W0 §0: no mount of `C:` in the sandbox), and a single cell containing all of
Rows 1–7 exceeded the MCP gateway's HTTP timeout (504). The computation was therefore run as
**six self-contained cells**, each redefining `speed`, `curvature`, `ψ` and the classifier at the
top, so no session state is relied on. `atlas.wl`'s conventions (`ψ = ArcTan[x',y']`, left
normal, `offsetArc` integrating `|1−dκ|·speed`) are reproduced exactly in those helpers; the
parabola self-test of W0 §2 is subsumed by Row 1's checks.

| check | where | residual |
|---|---|---|
| `D[R(w),w] − √(1+w²)`, `R = ½(w√(1+w²)+asinh w)` | §3.1 | `0` |
| `D[R(w) − d arctan w, w] − (√(1+w²) − d/(1+w²))` | §3.1 | `0` |
| `R(2) − ∫₀²√(1+x²)dx` | §3.1 | `0``39.53` |
| `ArcSinh[Tan p] − Log[Sec p + Tan p]` | §3.1 | `0` (under `−π/2<p<π/2`) |
| affine parabola `A = [[2,1],[1,3]]`, `p = √(5/2)/2`, `ψ₀ = −arctan(1/3)` | §3.3 | `0``34.85` |
| affine parabola `A = [[3,0],[1,1]]`, `p = 9/2`, `ψ₀ = 0` | §3.3 | `0``34.60` |
| `Reduce[∃x, 1+(ux²+vx+w)²=0 ∧ (2ux+v)=0]` real | §4.3 | `False` |
| `∫√(1+(d x^{d−1})²)dx`, `d = 1,…,6` | §4.2 | elementary, elementary, `EllipticF`, `₂F₁`, hypergeom., hypergeom. |
| `(5.2.1)` symbolic, `n = 2, 3` | §5.2 | `0` |
| `(5.2.1)` numeric, `n = 1/2, 5/3, 7/4` | §5.2 | `0``6024` at wp 40 |
| `(5.3.2)` Beta form, `n = 3/2, 5/3, 2` | §5.3 | `0``40.31`, `0``40.37`, `0``40.49` |
| Neile shear `cosh³u/3 − m(sinh2u/4+u/2)` | §5.2 | `−1/3` exactly (= the `−cosh³0/3` constant) |
| Möbius `(c+ew)/(a+bw)` | §5.5 | `0` |
| genus table `p = 4/3,5/3,7/4,8/5,7/3,3,4` | §5.6 | `0,1,2,2,3,1,2`, all matching `num(p−1)−1` |
| Bézier `Q = 45−180t+432t²−396t³+117t⁴`, `dψ/dt − N/Q` | §6.2 | `0` |
| Bézier offset identity, `d = 1/3`, `[0,1]` | §6.2 | `0``38.99` |
| ellipse `D[a(E(m)−E(π/2−φ;m)),φ] − √Q`, `m = 3/4` | §7.2 | `0` |
| ellipse `D[b E(φ;−3),φ] − √Q` | §7.2 | `0` |
| ellipse `dψ/dφ − ab/Q` | §7.2 | `0` |
| ellipse offset identity `[0.2,1.2]`, `d = 1/2` | §7.3 | `0``39.61` |
| ellipse root `d=1/2, x=1/2` | §7.4 | `0``28.40` |
| `exp_two` `D[R,w] − √(1+w²)/(w ln2)`, and `R(ψ)` form | §8.1 | `0`, `0` |
| `exp_two` `R` vs `∫ speed` on `[0,13/10]` | §8.1 | `0``34.70` |
| affine `exp_two`: `∫√(A+By+Cy²)/y dy` | §8.2 | elementary (`artanh` + `log`) |
| sheared sine `tanψ − a/(cos t−b)`, `dψ/dt − a sin t/Q` | §9.1 | `0`, `0` |
| sheared sine offset identity `[0.2,1.2]`, `d = 1/2` | §9.3 | `0``34.75` |
| sheared sine root `a=1,b=1/2,d=1/2,x=1` | §9.3 | `0``25.30` |
| sheared-sine `Λ` closed form derivative | §9.2 | `0` |

