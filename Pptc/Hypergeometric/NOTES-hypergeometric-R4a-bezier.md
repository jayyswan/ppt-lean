# NOTES-hypergeometric-R4a — cubic Bézier arc length as ₂F₁?

Research note, wave 2, task **R4a** of `PLAN-hypergeometric-00-overview.md` (inbound survey,
§6 "Worth adding: an inbound survey (R4)"). No `.lean` file was created, edited or deleted;
no `lean-lsp` tool and no `lake` command was used.

Every identity is labelled:

* **[NC n]** numerically checked to `n` significant digits, with the Wolfram kernel
  (`wolfram_WolframLanguageEvaluator`); the script is
  `archived files/hypergeometric-scripts/R4a-bezier-checks.wl`;
* **[SY]** proved symbolically here (proof written out);
* **[CL]** classical (from the literature, not re-derived here);
* **[SP]** speculative / not established.

Sources read: `AGENTS.md`, `PLAN-hypergeometric-00-overview.md` (§1, §2, §4 H6, §5 B1/B6,
§6 R4), `NOTES-hypergeometric-R1.md`, `Pptc/Defs.lean` (`speed`, `arcLengthOf`,
`bezierParam`, `cubic_bezier`), `Pptc/ThirdKind.lean` (whole file), and the relevant slices
of `Pptc/Basic.lean` (`firstKindQuartic`/`firstKindCurve`/`bezierParam_firstKind`,
`ellipticFIntegrand`, `thirdKindMaster`/`thirdKindCubic`/`thirdKindCubicDeriv`/
`thirdKindAnti`/`ellipticPiAux`, `integral_thirdKindMaster`, `ellipticF_Pconstructible`).

---

## 0. Answers in brief

1. **A general cubic Bézier contributes no new ₂F₁ value or family.** Its arc length is a
   **genus-1** integral (R1 §1.6, reproduced below) whose reduction is
   `algebraic + α·F + β·Π + γ·(E, elementary)` in *incomplete* elliptic integrals. Per
   PLAN §1, incomplete `F`/`E`/`Π` are Appell `F₁`/`F_D`, **not** ₂F₁; only the *complete*
   integrals are ₂F₁. `Pptc/ThirdKind.lean` already lands this as a P-constructible result
   (`ellipticPiInc_Pconstructible_gt_one`), but it is a third-kind/Appell result, not a ₂F₁
   one. Script check `1f` confirms the full reduction to 99 digits at a concrete rational
   Bézier.

2. **The only ₂F₁ values a Bézier yields are degenerate, and both are already landed:**
   * graph of a cubic `y = C x³` — `speed² = 1 + 9C²t⁴`, so `m = 4`, giving
     `₂F₁(−½, ¼; 5/4; −9C²X⁴)` — inside **`hyp_graphFamily_class_Pconstructible`**
     (`m = 2n−2 = 4`, i.e. `n = 3`), check `4a`;
   * the `h = 0` / ellipse limit — the complete `K(c) = (π/2) ₂F₁(½,½;1;c)` at
     `c = 1 − m²` — inside **`hyp_elliptic_class_Pconstructible`** (`i=j=k=0`), check `4b`.
   Both parameter identities are the ones the programme already owns (H6's
   `c = a+b+3/2` for `m=4`, and Legendre's `(a, 1−a; 1)`), so there is no new parameter
   identity either.

3. **A closed / periodic Bézier never reduces to a complete elliptic integral [SY].**
   `speed² = x'² + y'²` is a sum of two real squares of quadratics, so every real zero of
   `Q` has multiplicity ≥ 2: `√Q` has **no real branch point**. A complete `K`/`E`/`Π` over
   a real Bézier arc would require integrating between simple real roots of `Q`. For the
   concrete closed cubic Bézier (`p₁ = p₄`) the quartic is `9(1 − 8t + 26t² − 36t³ + 18t⁴)`,
   whose four roots are all non-real (check `3`). The finite Bézier arc `t ∈ [0,T]` also has
   `Q > 0` throughout, so nothing is completed.

4. **Affine images (`translate_x/y`, `scale_x/y`, `rotate`) add nothing.** The Bernstein form
   is affine-invariant, so an affine image of a cubic Bézier is a cubic Bézier with the
   transformed control points; `Q` becomes `γ'ᵀ AᵀA γ'`, still a quartic, still genus ≤ 1.
   The classification and the reduction are unchanged, and P-constructible affine data keeps
   the control points P-constructible.

**Verdict: no new ₂F₁ source. Obstruction: the general Bézier's arc length is an incomplete
elliptic integral of mixed first/second/third kind (Appell `F₁`/`F_D`), and only its
degenerate sub-families collapse to a single ₂F₁ — both already landed.**

---

## 1. The arc-length integral and its classification

### 1.1 Setup **[SY]**

Write the general cubic Bézier in Bernstein form (`Defs.lean:83`) as
`γ(t) = (x(t), y(t))`, `x, y` cubics in `t`. Then `x', y'` are quadratics and

```
speed(t)² = x'(t)² + y'(t)² =: Q(t),
```

a quartic. (This is the explicit `speed` of `Defs.lean:68`; it is deliberately not
`‖deriv γ t‖`, whose product norm would be the supremum norm.) Hence

```
arcLengthOf γ a b = ∫_a^b √Q(t) dt.
```

R1 §1.6 already recorded the quartic/genus-1 fact; check `1a`–`1b` below reproduce the
algebraic content at a concrete Bézier.

### 1.2 Classification of `∫ √Q dt` **[CL]** + **[SY]**

For a quartic `Q(t) = q₄t⁴ + q₃t³ + q₂t² + q₁t + q₀`:

* **`Q` has a repeated root, or `deg Q ≤ 3`.** The projective closure of `y² = Q(t)` is
  rational (genus 0); `√Q dt` is an Abelian differential of the third kind on `ℙ¹`, so
  `∫√Q dt` is **elementary** (rational functions plus logs/arctans, i.e. `asinh`, `log`).
  *In particular, if `Q` is a perfect square the integrand is a polynomial.* **[CL]**
* **`Q` has four distinct roots** (real or complex). `y² = Q(t)` has genus **1**; the
  holomorphic differential is `dt/√Q`. The general theory of elliptic integrals
  (Legendre / Hermite reduction) gives
  `∫ R(t) dt/√Q = elementary + Σ c_ν ∫ dt/((t−ν)√Q)`, and the residues of `dt/√Q` at its
  poles classify the result:
  - `∫ dt/√Q` — **incomplete first kind** `F(φ, c)`;
  - `∫ t² dt/√Q` (after reduction) — **incomplete second kind** `E(φ, c)` plus elementary;
  - `∫ t dt/√Q` — **incomplete third kind** `Π(n, φ, c)` (nonzero residue). **[CL]**
* **Degree ≥ 5.** Would be hyperelliptic; irrelevant here since `speed²` is exactly a
  quartic. **[SY]**

`Pptc/ThirdKind.lean` makes the genus-1 reduction explicit and *constructive* for the
Bézier class: `integral_sqrt_quartic` states

```
∫₀^T √Q = [quarticArcAnti(T) − quarticArcAnti(0)]
          + ∫₀^T (α + β t + γ t²)/√Q dt,
α = 2q₀/3 − q₃q₁/(24q₄),   β = q₁/2 − q₃q₂/(12q₄),   γ = q₂/3 − q₃²/(8q₄).
```

Checks `1a` (moment reduction, **[NC 60]**) and `1b` (pullback to the Legendre angle,
**[NC 60]**) confirm it at the ThirdKind Bézier `m = 2`, `h = ½`, `T = ½`, whose control
points are the rational points

```
p₁ = (0, 0),  p₂ = (1/6, 0),  p₃ = (7/24, 1/8),  p₄ = (29/96, 5/16),
```

and whose quartic factors as
`Q(t) = (1 − t + 5t²/4)(1 − t + 17t²/4) = 1 − 2t + (13/2)t² − (11/2)t³ + (85/16)t⁴`.

### 1.3 The third-kind reduction, reproduced **[SY]** + **[NC 60–99]**

`ThirdKind.lean` substitutes `t = sin ψ / (cos ψ + h sin ψ) =: thirdKindTan h ψ` (which is
`tan ψ` when `h = 0`), where the quartic is
`thirdKindQuartic m h t = ((1−ht)² − mt²)² + ((1+m)(1−ht)t)²`. The Bézier with those
control points is `bezierParam_thirdKind`:

```
bezierParam (0,0) (T/3,0) (2T/3 − hT²/3, (1+m)T²/6)
           (T − hT² + (h²−m)T³/3, (1+m)(T²/2 − hT³/3)).
```

Under the substitution, with `Δ(ψ) = √(1 − c sin²ψ)`, `c = 1 − m²`, `D(ψ) = cos ψ + h sin ψ`:

```
√Q = Δ(ψ)/D(ψ)²,   dt/dψ = 1/D(ψ)²  ⇒  speed dψ = Δ(ψ)/D(ψ)⁴ dψ,
D·(cos ψ − h sin ψ) = 1 − (1+h²) sin²ψ   ⇒   n := 1 + h².
```

So the third-kind factor `1 − n sin²ψ` appears with `n = 1 + h² = sec²ψ₀`, and — by
`integral_inv_sqrt_thirdKindQuartic`, `thirdKindMoment_one`, `thirdKind_sum_key` — the
arc length reduces to `algebraic + α·F + β·Π + γ·(F, E, thirdKindAnti)`, with `Π` the
**incomplete** third-kind integral at `n = 1 + h²`. Numerically at the concrete Bézier
above (`m = 2`, `h = ½`, `φ = arctan(2/3)`, `c = −3`, `n = 5/4`):

| identity | check | label |
|---|---|---|
| moment reduction `∫√Q = alg + ∫(α+βt+γt²)/√Q` | diff `0·10⁻⁶⁰` | **[NC 60]** |
| pullback `t = sinψ/(cosψ+h sinψ)` to `∫ (α+βt+γt²)/Δ dψ` | diff `0·10⁻⁶⁰` | **[NC 60]** |
| `∫₀^{thirdKindTan h φ} dt/√Q = F(φ, c)` | diff `0·10⁻⁵⁹` | **[NC 59]** |
| `thirdKindMoment_one`: `∫ t dt/√Q = ∫ sinψcosψ/((1−n sin²ψ)Δ)dψ − h·A(n,φ)` | diff `0·10⁻⁶⁰` | **[NC 60]** |
| `Π(n,φ,c) = F(φ,c) + n·A(n,φ)` | diff `0·10⁻⁵⁹` | **[NC 59]** |
| `thirdKind_sum_key` symmetrised in `±h` | diff `0·10⁻⁹⁹` | **[NC 99]** |

(Here `A = ellipticPiAux`, and `∫√Q` is the pullback of the actual Bézier arc; the
sum check integrates `√Q` and `√(Q(h↦−h))` directly.)

---

## 2. The ₂F₁ verdict

### 2.1 Incomplete `F`/`E`/`Π` are not ₂F₁ **[CL]**

PLAN §1 (verified table, V3 to ≥ 68 digits) records:

```
ellipticF c φ       = sin φ · F₁(½; ½, ½; 3/2; sin²φ, c sin²φ)        — Appell F₁
ellipticE c φ       = sin φ · F₁(½; ½, −½; 3/2; sin²φ, c sin²φ)       — Appell F₁
ellipticPiInc       = F_D in three variables                          — Lauricella F_D
ellipticPi c n      = (π/2) F₁(½; 1, ½; 1; n, c)                      — Appell F₁
```

Only the **complete** cases collapse to ₂F₁:
`K = ellipticF c (π/2) = (π/2) ₂F₁(½,½;1;c)` and
`E = ellipticE c (π/2) = (π/2) ₂F₁(−½,½;1;c)` (§2 V1–V2). At a general upper limit the
elementary boundary term of the master identity does not vanish, and the incomplete `Π`
system does not close on itself (`ellipticPiAux_interchange` in `ThirdKind.lean`). **So the
general Bézier arc length is not a ₂F₁.**

*Exception to keep honest:* the H6 power-law/graph family is a *special* quartic with a
single nonconstant monomial, where the binomial expansion telescopes into one ₂F₁
(`(1/m)ₙ/(1+1/m)ₙ = 1/(mn+1)`); a general quartic has four parameters and its binomial
expansion is a genuine double sum, i.e. Appell, not ₂F₁. This is exactly why H6 works and
the general Bézier does not.

### 2.2 Is there a parameter identity? **

The only parameter identities the Bézier supplies are the degenerate ones, and both are
already in the programme's families:

* **`m = 4` (graph of a cubic).** `c = a + b + 3/2` for the H6 family
  `(−½, 1/m; 1+1/m; z)` becomes `−½ + ¼ + 3/2 = 5/4` ✓. No new identity.
* **`h = 0` (ellipse / first kind).** The complete parameter `(½, ½; 1)`, Legendre's
  `a = ½`, `1 − a = ½`, `b = ½`. No new identity.

`PLAN §5 B1` and R1 §2 already showed the H6 parameter identity fails every standard
quadratic transformation, and the Legendre family stops at the four Schwarz signatures; the
Bézier adds nothing here.

### 2.3 Complete-arc / closed Bézier **[SY]** + **[NC 20]**

A complete elliptic integral over a real Bézier arc would have to integrate between two
**simple real roots** of `Q` (branch points of `√Q`). But

```
Q(t) = x'(t)² + y'(t)²
```

is a sum of two real squares of real quadratics. If `Q(r) = 0` then `x'(r) = y'(r) = 0`, so
`r` is a common root of the two quadratics and `Q` has a root of multiplicity **≥ 2** at
`r`. Therefore `Q` has **no simple real root**: `√Q` is real-analytic on all of `ℝ`, and no
finite real Bézier arc terminates at a branch point. Equivalently:
`Q(0) = |3(p₂−p₁)|²`, `Q(1) = |3(p₄−p₃)|²`, both squares, zero only for a degenerate
(cusp) Bézier, and a cusp gives a double root, hence elementary. Numerically the concrete
closed cubic Bézier `p₁ = p₄ = (0,0)`, `p₂ = (1,0)`, `p₃ = (0,1)` has

```
Q(t) = 9(1 − 8t + 26t² − 36t³ + 18t⁴),  Q(0) = Q(1) = 9,
roots 0.26429… ± 0.16667i, 0.73570… ± 0.16667i   (all non-real),
total length = 1.4401600646980917069485848124017690949141733840234…,
```

so even a closed Bézier realises no real period of the elliptic curve. **[NC 20]** for the
roots, **[NC 59]** for the length.

The only complete ₂F₁ in the picture is the `h = 0` family's forced completion,
`K(c) = (π/2) ₂F₁(½,½;1;c)` with `c = 1 − m²`; `c` is P-constructible whenever `m` is, and
the value is already in the elliptic class (check `4b`). The finite Bézier arc reaches only
the *incomplete* `F(c, arctan T)`, which is an Appell value, not ₂F₁.

---

## 3. Specialisations, explicitly

1. **Degenerate control points → straight segment [SY].** If `p₂ = p₁ + (p₄−p₁)/3` and
   `p₃ = p₁ + 2(p₄−p₁)/3` (equivalently, the control points are equally spaced and
   collinear), `bezierParam_eq_segmentParam` (`Basic.lean:771`) makes the curve the segment
   `[p₁, p₄]`. Then `Q` is a perfect square, `√Q = |p₄ − p₁|`, and the arc length is the
   P-constructible distance `|p₄ − p₁|` — elementary, no ₂F₁.

2. **Graph of a quadratic → elementary [SY] + [NC 49].** A cubic Bézier with `x` linear,
   `y` quadratic is a parabola (a degree-2 `poly_graph`). Then `x'` is constant and `y'` is
   linear, so `Q = x'² + (a t + b)²` is a quadratic in `t`, and
   `∫√Q dt` is elementary. The closed form (for `x' = 1`, `y' = 2at+b`) is
   `∫ √(1 + (2at+b)²) dt = (1/4a)[ u√(1+u²) + asinh u ]` with `u = 2at+b`, verified to 49
   digits (check `5`, `a = 3/7`, `b = −2/5`, `T = 4/3`). In the graph-family language this
   is the `m = 2` (asinh) case of H6 — already elementary.

3. **Graph of a cubic `y = C x³` → `m = 4`, graph class [SY] + [NC 59].** Take the Bézier
   with `x(t) = T t` and `y(t) = C T³ t³`, i.e. control points
   `(0,0), (T/3,0), (2T/3,0), (T, C T³)`. Then `speed² = 1 + 9C²T⁴ t⁴`, a quartic with only
   the `t⁰` and `t⁴` terms. By V4 (`m = 4`, `b = 3`):
   `∫₀^X √(1 + 9C²x⁴) dx = X · ₂F₁(−½, ¼; 5/4; −9C²X⁴)`.
   Check `4a` (`X = 3/5`, `C = 2/7`) agrees to **[NC 59]**. This is exactly
   `hyp_graphFamily_class_Pconstructible` at `n = 3` (`m = 2n−2 = 4`, `i=j=k=0`), so it is
   **already covered**.

4. **The `h = 0` branch → ellipse / first kind [SY] + [NC 50].**
   `thirdKindQuartic_zero` (`ThirdKind.lean:432`) gives
   `thirdKindQuartic m 0 t = firstKindQuartic m t = (1 − mt²)² + ((1+m)t)²
   = (1+t²)(1+m²t²)`, and `thirdKindCurve_zero` shows the curve is `firstKindCurve`. The
   control points are exactly `bezierParam_firstKind` (`Basic.lean:3627`):
   `(0,0), (T/3,0), (2T/3,(1+m)T²/6), (T − mT³/3, (1+m)T²/2)` — a symmetric "sail". Its arc
   length is
   the incomplete first-kind integral: `∫₀^{tan φ} dt/√((1+t²)(1+m²t²)) = F(φ, 1−m²)`,
   verified to 50 digits at `m = 3`, `φ = 1/3` (check `2`). This is the family that
   `Basic.lean` used to construct `ellipticF`; the complete limit is `K`, i.e. the elliptic
   class. **Already covered.**

   The third-kind parameter here is `n = 1 + 0² = 1` (the degenerate `sec²0`), and the
   master identity's boundary term is what makes `F` come out with no `Π` term — this is the
   sentence at the top of `ThirdKind.lean`.

**Summary of coverage.** The general Bézier lands in *incomplete* Appell territory (not a
₂F₁ at all). Every Bézier sub-family that *does* produce a ₂F₁ does so through the already
landed classes:

| Bézier specialisation | ₂F₁ form | landed class |
|---|---|---|
| graph `y = Cx³` | `(−½, ¼; 5/4; −9C²X⁴)` | `hyp_graphFamily_class_Pconstructible`, `n = 3`, `m = 4` |
| `h = 0` / ellipse complete | `(½, ½; 1; 1−m²)` | `hyp_elliptic_class_Pconstructible` (`i=j=k=0`) |
| straight segment | elementary | — |
| graph of a quadratic | elementary (`asinh`, `m = 2`) | — |
| general Bézier | incomplete `F`/`E`/`Π` (Appell), **not ₂F₁** | `ThirdKind.lean`, out of the ₂F₁ programme |

---

## 4. Affine images add nothing **[SY]**

The maps `translate_x`, `translate_y`, `scale_x`, `scale_y`, `rotate` act on point-sets as
`S ↦ f '' S` (`Defs.lean`), and on a parametrized Bézier by post-composition. The Bernstein
basis is affine-invariant, so an affine `A(t) = M t + b` sends
`bezierParam p₁ p₂ p₃ p₄` to `bezierParam (A p₁) (A p₂) (A p₃) (A p₄)` — the image is a
cubic Bézier again, with P-constructible control points when the originals and the affine
data are P-constructible (rational integer rotations/scalings stay rational; `rotate n°`
with integer `n` and P-constructible scales give P-constructible coordinates).

Under an invertible linear part `M`, the new speed-squared is
`Q_M(t) = γ'(t)ᵀ MᵀM γ'(t)`, still a quadratic form in the two velocity quadratics, hence
still a quartic in `t`; translation leaves `Q` unchanged. Therefore:

* the integral stays genus ≤ 1 (`speed²` remains a quartic);
* the reduction to incomplete `F`/`E`/`Π` is unchanged (the moment reduction
  `integral_sqrt_quartic` applies to the transformed coefficients verbatim);
* the two degenerate ₂F₁ cases map into the same landed classes (the graph class is closed
  under `scale_x`/`scale_y`/`translate`, and the elliptic class is closed under affine
  images of the ellipse by construction).

Rotations by non-integer angles are not asserted by the primitive anyway (`rotate` takes
`n : ℤ` degrees), and per PLAN §1 combining `rotate` with `scale_x`/`scale_y` gives every
P-constructible angle — but even a full arbitrary rotation only changes the coefficients of
the same quartic. **No affine image of a Bézier yields a new ₂F₁.**

---

## 5. Label ledger

| statement | label |
|---|---|
| `speed²` of a cubic Bézier is a quartic; `∫√Q` genus 1 (§1.1–1.2) | [SY] + [CL]; R1 §1.6 |
| general quartic classification (elementary / elliptic F,E,Π / hyperelliptic) (§1.2) | [CL] (Legendre/Hermite reduction) |
| moment reduction `integral_sqrt_quartic` at a concrete Bézier (§1.2, check 1a) | [SY] + [NC 60] |
| pullback `t = sinψ/(cosψ+h sinψ)` to Legendre form (§1.3, check 1b) | [SY] + [NC 60] |
| moment 0 `= F(φ,c)` (§1.3, check 1c) | [SY] + [NC 59] |
| `thirdKindMoment_one`: third-kind piece at `n = 1+h²` (§1.3, check 1d) | [SY] + [NC 60] |
| `Π = F + n·A` (§1.3, check 1e) | [SY] + [NC 59] |
| `thirdKind_sum_key` symmetrised in `±h` (§1.3, check 1f) | [SY] + [NC 99] |
| incomplete `F`/`E`/`Π` are Appell `F₁`/`F_D`, not ₂F₁ (§2.1) | [CL] + PLAN §1 (V3, ≥68 digits) |
| complete `K`, `E` are ₂F₁ (§2.1) | [CL] + PLAN §2 (V1–V2) |
| H6 exception is a one-monomial quartic (§2.1) | [SY] + PLAN §2 V4 |
| no simple real root of `Q = x'²+y'²` (§2.3) | [SY] |
| concrete closed Bézier roots non-real, length (§2.3, check 3) | [SY] + [NC 20]/[NC 59] |
| degenerate straight-segment Bézier is elementary (§3.1) | [SY] (Basic `bezierParam_eq_segmentParam`) |
| quadratic-graph Bézier is elementary (§3.2, check 5) | [SY] + [NC 49] |
| cubic-graph Bézier `m = 4` is the graph family (§3.3, check 4a) | [SY] + [NC 59] |
| `h = 0` branch is the ellipse first-kind family (§3.4, check 2) | [SY] + [NC 50] |
| affine image of a Bézier is a Bézier; classification invariant (§4) | [SY] (Bernstein affine invariance) |
| "no new ₂F₁ source" (§0) | **negative result**, with the listed loophole |

**Loophole, stated explicitly (per PLAN §7).** The project cannot prove
non-P-constructibility, and a *coincidence* is not excluded: some special rational Bézier
might have a finite arc length equal to a new ₂F₁ value at a special algebraic endpoint, by
an identity no mechanism here produces. What is established is that the *general* reduction
is incomplete-Appell and that every forced ₂F₁ is already landed. The genuinely new object
the Bézier does deliver — the incomplete third kind at `n > 1` — is already in
`ThirdKind.lean` and is not a ₂F₁, so it belongs to the third-kind side of the repo, not to
the ₂F₁ inbound map.

No `sorry`, no Lean file touched.

---

## 6. Scripts

| script | contents |
|---|---|
| `archived files/hypergeometric-scripts/R4a-bezier-checks.wl` | checks `1a–1f`, `2`, `3`, `4a`, `4b`, `5` above, run with the Wolfram kernel |

All numeric work in this note was produced by the Wolfram kernel through the
`wolfram_WolframLanguageEvaluator` MCP tool. No `py`/`mpmath` fallback was needed; `sympy`
was not used.
