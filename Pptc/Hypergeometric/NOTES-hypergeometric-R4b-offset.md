# NOTES-hypergeometric-R4b — offset-curve arc length as ₂F₁?

Research note, wave 2, task **R4b** of `PLAN-hypergeometric-00-overview.md`.
No `.lean` file was created, edited or deleted; no `lean-lsp` or `lake` call was made.

Every identity is labelled:

* **[NC n]** numerically checked to `n` significant digits (script
  `R4b-offset-checks.wl`, run on the Wolfram kernel);
* **[SY]** proved symbolically here (the proof is written out);
* **[CL]** classical (cited, not re-derived here);
* **[SP]** speculative / not established.

Sources read: `AGENTS.md`; `PLAN-hypergeometric-00-overview.md` (§1, §2, §4 H6,
§5 B1/B6, §6 R4); `NOTES-hypergeometric-R1.md` (§1.5, the offset-density
paragraph); `Pptc/Defs.lean` (`speed`, `arcLengthOf`, `unitNormal`, `offsetParam`,
the `offset` constructor); `Pptc/Offset.lean`; `Pptc/ThirdKind.lean` (head).

Script: `archived files/hypergeometric-scripts/R4b-offset-checks.wl` (backend:
**Wolfram Language kernel** throughout; no Python was used).

---

## 0. Answers in brief

1. **The offset never yields a new ₂F₁ family.** For any curve traced with
   continuous non-vanishing velocity, `speed(offsetParam γ d ·) = |1 − d·κ(·)| · speed γ`,
   and since `κ·speed = dφ/dt` (φ = tangent angle), the offset arc length is

   > **`arcLengthOf (offsetParam γ d) a b = arcLengthOf γ a b − d·(φ(b) − φ(a))`.**

   The offset is the base curve plus `d` times its **total turning angle** — the
   classical parallel-curve length element `ds_d = ds − d·dφ` — and the turning
   angle of every curve in the constructor language is an explicit elementary
   function (`atan2` of the velocity, an algebraic/trigonometric/exp expression).
   So the non-elementary content of the offset arc length is *exactly* that of the
   base arc length. Adding an elementary function to a fixed integrand cannot
   manufacture a hypergeometric family outside the base's.

2. **Per base curve, nothing new:**
   * **line** — κ = 0, Δφ = 0, offset length = base length (elementary);
   * **circle** — κ = 1/R, Δφ = the central angle, offset length = `(R − d)Δθ`
     (elementary);
   * **ellipse** — base length `a·E(c,φ)`, extra term `d·(1/(ab))·arctan((a/b)tanθ)`;
     **offset length = (second-kind E) + elementary. No Π appears**, contrary to
     the task's hypothesis (numerically confirmed to 60 digits, §2.3);
   * **monomial graph `y = Cxⁿ`** — base length is the V4 ₂F₁, extra term
     `d·arctan(nCx^{n−1})`; **offset length = (H6 ₂F₁) + arctan**. Curvature
     corrected (§2.4);
   * **cubic pair (Offset.lean)** — base length is the incomplete third-kind
     machinery of `ThirdKind.lean`, extra term `d·arctan`; **offset length =
     (incomplete Π) + elementary**. No complete special case lowers Π to a ₂F₁.

3. **Already-covered verdict.** The hypergeometric content is inherited from the
   base: for the ellipse's complete arc it is `(−½, ½; 1)` ∈ the elliptic class
   `(½+ℤ, ½+ℤ, 1+ℕ)`; for monomial graphs it is exactly the H6 family
   `(−½+ℤ, 1/m+ℤ, 1+1/m+ℕ)`. The offset's only new term, `arctan`, is itself the
   *elementary* ₂F₁ `₂F₁(½,1;3/2;−z²) = arctan z / z` (H1, landed).

4. **Affine invariance.** `translate_x/y`, `scale_x/y`, `rotate` are image maps;
   the identity above holds verbatim for the image curve, whose turning angle is
   still `atan2(elementary, elementary)`. So the classification is invariant: the
   offset of any affine image is its base length plus an elementary term.

**Verdict: no new ₂F₁ source.** The hope that the parallel-copy constructor
"leaves the curve" and so raises the hypergeometric degree is false for *arc
length*; the degree-raising happens only for *intersections* (`Offset.lean`'s
degree-10 roots), which is not R4's question. This closes the `offset` branch of
the R4 inbound survey negatively.

---

## 1. The offset arc-length integral

### 1.1 Definitions and sign convention **[SY]**

Write `γ(t) = (x(t), y(t))`, `w := speed γ t = √(x'² + y'²)`, and
`t̂ = (x'/w, y'/w)`. `Defs.lean` defines

```
unitNormal γ t = (−y'/w, x'/w) = R₉₀ t̂ ,   R₉₀(a,b) = (−b,a),
offsetParam γ d t = γ t + d · unitNormal γ t .
```

`unitNormal` is the velocity turned a quarter turn **counterclockwise** (the
*left* normal), and positive `d` pushes the point to the left of the direction of
travel. Take the signed curvature **paired with that normal**,

```
κ := (x'y'' − y'x'') / w³      (left-turning positive).
```

Then `n = R₉₀ t̂` gives `n' = R₉₀ t̂' = κ w R₉₀ n = −κ w t̂`, so

```
Γ' := (offsetParam γ d ·)' = γ' + d n' = w t̂ − d κ w t̂ = (1 − dκ) w t̂ ,
```

> **`speed (offsetParam γ d t) = |1 − d·κ(t)| · speed γ t` .** **[SY]**, residual
> identically `0` in script (A).

This is the task's item 1 with the sign made explicit: with the *standard*
(left-positive) κ and the left unit normal the factor is `1 − dκ`. The task's
`1 + dκ` is the same statement after redefining `κ` by a sign (equivalently
`d ↦ −d`, both available since `d` is a signed P-constructible distance).

### 1.2 The turning-angle form **[SY]** + **[CL]**

Let `φ` be the tangent angle, `t̂ = (cos φ, sin φ)`, so `φ = atan2(y', x')` and

```
φ' = (x'y'' − y'x'') / w² = κ w ,      i.e.   κ · speed = dφ/dt .
```

Integrating `speed(offsetParam γ d ·) = (1 − dκ)·w` over `[a,b]` (on which
`1 − dκ ≥ 0`; see §6 for sign changes) and using `∫κ w dt = φ(b) − φ(a)`:

```
arcLengthOf (offsetParam γ d) a b
  = arcLengthOf γ a b − d · (φ(b) − φ(a)) .       (★)
```

**[SY]**. This is the classical formula for the length element of a parallel
curve, `ds_d = ds − d·dφ`, i.e. offset length = base length + d × total signed
turning angle **[CL]** (a reparametrization-free restatement of `κ = dφ/ds`,
which is elementary geometry; Gauss's `∫κ ds =` total curvature).

Script checks of (★), all to high precision:

| base | data | residual `num − (★)` |
|---|---|---|
| ellipse (§2.3) | a=2, b=1, d=3/10, θ∈[0,1] | `0 × 10⁻⁵⁰` |
| monomial (n=5) | C=1/10, d=1/3, x∈[½,1] | `0 × 10⁻⁶⁰` |
| monomial (n=3) | C=1/4, d=2/5, x∈[½,1] | `0 × 10⁻⁶⁰` |
| cubic pair | x=t³−t²+2t+1, y=−(t³/3+t²/2+t), d=1/2, t∈[0,1] | `0 × 10⁻⁴⁹` |

### 1.3 Why the extra term is elementary **[SY]**

The second term `d·Δφ` needs no antiderivative: it is the *difference of the
tangent angle*, and for every base curve and closure operation the tracing is
explicit, so `φ = atan2(y', x')` is an elementary function of the parameter. In
fact:

* graph `y = f(x)`: `φ = arctan(f'(x))`, so `Δφ = Δ arctan(f')`;
* circle/ellipse/first-kind curves: `atan2` of algebraic/triangular data;
* cubic pair: `atan2(quadratic, quadratic)` (a rational function).

So the offset arc length is `(base arc length) + (arctan-type elementary term)`,
and **offsetting adds nothing hypergeometric.** The one subtlety — that `arctan`
is itself a ₂F₁ — is harmless: it is the *elementary* one (H1),
`arctan z = z·₂F₁(½,1;3/2;−z²)`, already landed.

---

## 2. Case analysis

### 2.1 Line **[SY]**

κ = 0, so `speed(offset) = speed γ` and the offset is the parallel line: same
length. Δφ = 0. Elementary.

### 2.2 Circle **[SY]**

`γ = (R cos θ, R sin θ)`, `κ = 1/R`, `w = R`:

```
speed(offset) = |1 − d/R| R = |R − d| ,   length = |R − d|·Δθ .
```

Concentric circle; elementary. (★) gives `RΔθ − dΔθ = (R−d)Δθ`.

### 2.3 Ellipse **[SY]** + **[NC 60]**

`γ = (a cos θ, b sin θ)`, `w = √(a²sin²θ + b²cos²θ)`, and
`x'y'' − y'x'' = ab` (constant), so

```
κ = ab / w³ ,    κ·w = ab / w² ,    offset density = w − d·ab/w² .
```

The extra integrand is a **rational** function of θ:

```
∫ ab/(a²sin²θ + b²cos²θ) dθ = arctan((a/b) tan θ)     [SY, residual 0 in (G)],
```

because `d/dθ arctan((a/b)tanθ) = ab/w²`. Hence

```
offset length (θ₁→θ₂)
  = a·(E-form difference) − d·( arctan((a/b)tanθ₂) − arctan((a/b)tanθ₁) ) ,
```

where `∫₀^θ w dθ` is the second-kind (E) integral of the ellipse.
**No elliptic integral of the third kind occurs.** This contradicts the task's
guess ("mixture of E, K, and possibly Π"); the reason is that the natural
footpoint parametrization makes `κ·w` rational, not `1/√(quadratic)`.

Concrete check (ellipse a=2, b=1, d=3/10, θ∈[0,1]):

```
numeric offset length        = 0.94761983184313388394567257239294184333628736596398  (θ∈[0,1])
base length (quadrature)     = 1.3256631975799981116934056691552009461321191741781
E closed form a√(1−c)E(c')   = 1.3256631975799981116934056691552009461321191741781
d·(φ(1)−φ(0))                = +0.3 (π/2 − arctan(cot 1 /2))   (= 0.3·arctan(2 tan 1))
residual (num − closed)      = 0 × 10⁻⁵⁰                                     [NC 50]
```

### 2.4 Monomial graph `y = Cxⁿ` **[SY]** + **[NC 60]**

**Curvature (the task's formula is wrong).** For `f(x) = Cxⁿ`,
`f' = nCx^{n−1}`, `f'' = n(n−1)Cx^{n−2}`, so

```
κ = f''/(1+f'²)^{3/2}
  = n(n−1)·C·x^{n−2} / (1 + n²C²x^{2n−2})^{3/2}  ,
```

**not** `n(n−1)(Cx)^{n−2}/…`. The two differ by the factor `C^{3−n}` (checked
symbolically: at C=3/2, n=5, x=1 the ratio is `4/9 = C^{-2}`; script (F)).
Note `n=1` gives κ = 0 (the line), `n=2` gives `κ = 2C/(1+4C²x²)^{3/2}`.

Let `m = 2n−2`, `b = nC`, so `w = √(1 + b²x^m)`. Then

```
(1 − dκ)·w = w − d·f''/w²
           = √(1 + b²x^m) − d·d/dx[ arctan(f'(x)) ] ,
```

where `d/dx arctan(nCx^{n−1}) = n(n−1)Cx^{n−2}/(1+n²C²x^{2n−2}) = f''/w²`.
The first piece is exactly V4 / H6:

```
∫₀^X √(1 + b²x^m) dx = X · ₂F₁(−½, 1/m; 1+1/m; −b²X^m) ,       [SY, V4]
```

and the second is elementary `−d·arctan(nCx^{n−1})`. So

```
arcLengthOf (offset of y=Cxⁿ) over [x₀,X]
  = [V4(X) − V4(x₀)] − d·[ arctan(nCX^{n−1}) − arctan(nCx₀^{n−1}) ] .
```

Concrete checks (offset traced by `x`, so the arclength is parametrization-free):

| n | m | C | d | x-window | numeric offset length | residual |
|---|---|---|---|---|---|---|
| 5 | 8 | 1/10 | 1/3 | [½,1] | 0.3693012840383946753664771818133866591020679800711573590967 | `0 × 10⁻⁶⁰` |
| 3 | 4 | 1/4 | 2/5 | [½,1] | 0.3675249285965122948761042863128214674105156168560713272623 | `0 × 10⁻⁶⁰` |

The hypergeometric content is `₂F₁(−½, 1/m; 1+1/m; −b²Xᵐ)` with
`m ∈ {2,4,6,8,10}` — **exactly the H6 family**. The offset adds only arctan.

### 2.5 The other base curves **[SY]**

* `power_law a b` (`y = ax^b`, x>0): same graph computation with `f' = abx^{b−1}`;
  offset length = (its V4 integral) + `d·arctan(abx^{b−1})`. Its base integral is
  R1's family; the offset adds arctan only.
* `exp_two` (`y = 2ˣ`): `f' = ln2·2ˣ`, `f''/w² → arctan(2ˣ ln2)`. Base integral
  is its own; offset adds elementary.
* `sine` (`y = sin x`): `f' = cos x`, `f''/w² → arctan(cos x)`. Base integral is
  its own (R4c's question); offset adds elementary.

### 2.6 Cubic pairs and `ThirdKind.lean` (task item 3) **[SY]**

`Offset.lean`'s `offsetCubicPairArc_PConstructibleCurve` builds the parallel copy
of a cubic pair **for intersection** (`crossing_Pconstructible`); the file never
measures the offset's arc length. Had it done so, (★) applies with the base being
the cubic pair, whose arc length is precisely the object of `ThirdKind.lean`:

* base speed `w = √(quartic)`; the general cubic pair's arc length carries an
  incomplete third-kind term at `n = 1 + h² = sec²ψ₀ > 1` (ThirdKind.lean head);
* the offset adds only `−d·Δφ`, with `φ = atan2(quadratic, quadratic)`
  elementary and P-constructible.

So the offset arc length would be `(incomplete Π) + (elementary)`. **The offset
neither creates nor removes the third-kind term.** No complete special case
lowers it to a ₂F₁: the complete integral is
`Π(n,c) = (π/2)·F₁(½;1,½;1;n,c)` (Appell), which per PLAN §1 is **not** a ₂F₁,
and the elementary turning-angle term supplies no compensating hypergeometric
completion. Whether `n` is P-constructible is therefore beside the point — there
is no ₂F₁ to have a parameter of.

Numeric confirmation (script (E)): for `x=t³−t²+2t+1`, `y=−(t³/3+t²/2+t)`,
`d=1/2`, `t∈[0,1]`,

```
numeric offset length = 2.8869261382034282716174734859860606264840282545971
base length           = 2.7260508610051071749167711788067299669736506068183
∫κ ds = Δφ            = −0.3217505543966421934014046143586613190207
residual              = 0 × 10⁻⁴⁹
```

---

## 3. The ₂F₁ verdict, with parameter identity

**There is no new ₂F₁ family, hence no new parameter identity attributable to
the offset.** The complete ledger of what the offset arc length contains:

| contribution | hypergeometric identity | parameter set | status |
|---|---|---|---|
| base = monomial graph | V4 / H6 | `(−½, 1/m; 1+1/m)` | landed (`hyp_graphFamily_class_Pconstructible`) |
| base = ellipse, complete arc | `E = (π/2)₂F₁(−½,½;1;c)` | `(−½,½;1)` ∈ elliptic class | landed (`hyp_elliptic_class_Pconstructible`) |
| base = ellipse, open arc | `a·ellipticE c φ` (incomplete) | Appell `F₁` | **not a ₂F₁** (PLAN §1) |
| base = cubic pair | `Π` (incomplete, ThirdKind) | `F₁` / `F_D` | **not a ₂F₁** (PLAN §1) |
| extra term (all curves) | `d·Δ arctan` | `(½,1;3/2)` | landed (H1, elementary) |

Any ₂F₁ reached via an offset is either the base curve's own (already in the
landed classes) or the elementary `arctan` (H1). The offset's contribution is
`d` times a **turning angle**, a difference of angles, and neither the angle
value nor its differential carries new monodromy.

---

## 4. Coverage by the landed classes

* **`hyp_elliptic_class_Pconstructible`** `= (½+ℤ, ½+ℤ, 1+ℕ)`: covers the ellipse
  offset's complete-arc part (the E value `₂F₁(−½,½;1;c)`, since `−½ ≡ ½ mod 1`
  and `1 ∈ 1+ℕ`). The elementary part is H1.
* **`hyp_graphFamily_class_Pconstructible`** `= (−½+ℤ, 1/m+ℤ, 1+1/m+ℕ)`: covers
  the monomial-graph offset's ₂F₁ part exactly, via the same `m = 2n−2` and
  argument `−b²Xᵐ` (`m ∈ {2,4,6,8,10}` for `n ≤ 6`). The elementary part is H1.
* General (non-complete, non-V4) arcs land outside the ₂F₁ world entirely
  (Appell/Π), and the offset does not pull them into it.

**Conclusion of item 3:** the offset result is already covered; it introduces no
class outside the two landed ones.

---

## 5. Affine images (task item 4)

* **`rotate` (integer degrees) and `translate_x/translate_y`** are isometries.
  An isometry `T` commutes with offsetting, `T(offsetParam γ d t) = offsetParam (T∘γ) d t`
  (the unit normal is rotated, not changed in length), and preserves arc length
  and turning angle. So the offset of an isometric image has the same length and
  the same classification.
* **`scale_x`/`scale_y`** (anisotropic) do not commute with offsetting: the unit
  normal of `(a·x, b·y)` is not the scaled unit normal. But the identity (★) is
  *universal* — it holds for any regular `C¹` tracing — so it applies to the
  scaled curve `T∘γ` with `κ_T`, `φ_T` its own curvature and tangent angle. The
  scaled tracing is still explicit, so `φ_T = atan2(b y', a x')` is elementary,
  and the offset of the image is `(image base arc length) + (elementary)`.
  For example a rotated/scaled ellipse still has base arc length `∝ E` (a
  different parameter `c`), and a scaled monomial graph still has base arc
  length a V4-type `∫√(polynomial)`.

Hence **the classification is invariant under all five affine operations** when
they act on the *base*: at every stage the offset adds only the elementary
turning-angle term, so it can neither create a ₂F₁ family nor move the base
family into a new one.

A clarification on what is being claimed: the five operations are curve-closure
operations, and item 4 asks about their effect on *offsets of the base*. An
affine map applied **after** an offset, `T(offsetParam γ d t) = M(γt + d n) + b`,
is a *distorted* parallel curve, no longer the offset of anything unless `M` is a
similarity — its length `∫|1 − dκ|w·|M t̂| dt` is a genuinely different integral
and is not the "offset arc length" this note classifies. For a similarity
(`rotate`, `translate_*`) the two commute exactly and the length is unchanged; for
anisotropic `scale_x`/`scale_y` the composite is out of scope. What the note
claims is the invariant that matters for R4: whatever explicit base tracing the
five operations produce, **its** offset adds only an elementary term.

---

## 6. Caveats and loopholes (stated explicitly)

1. **Sign changes / cusps of the offset.** `speed(offsetParam) = |1 − dκ|·w`. If
   `|d|` exceeds the radius of curvature somewhere, the factor `1 − dκ` changes
   sign and the integral acquires an extra contribution at the explicit roots of
   `1 − dκ = 0`. Those roots solve an explicit algebraic equation and the
   correction is again a finite elementary expression, so no new ₂F₁ appears.
   (`offset`'s `hreg` forbids `speed γ = 0`, not `1 − dκ = 0`.)
2. **`atan2` bookkeeping.** (★) is stated with `φ` the continuous tangent angle;
   the `arctan` representation may need a `±π` correction, and `π` is
   P-constructible, so this is cosmetic.
3. **Coincidence [SP].** In principle `(base length) + (elementary)` could equal
   some unrelated ₂F₁ at isolated special parameters; no mechanism produces it
   and it would not be a family. Consistent with R1/PLAN §7's "do not claim
   non-P-constructibility outright", this is not ruled out, only unfound.
4. **The task's curvature formula** `n(n−1)(Cx)^{n−2}/…` for `y = Cxⁿ` is a typo;
   the correct numerator is `n(n−1)Cx^{n−2} = f''(x)` (§2.4).
5. **A real positive by-product, outside this question.** Offsetting *does*
   manufacture new P-constructible numbers — but through **intersections**
   (`Offset.lean`'s degree-10 crossing roots), not through arc length. That is
   not an R4/₂F₁ matter.

---

## 7. Label ledger

| statement | label |
|---|---|
| `speed(offsetParam γ d t) = |1 − dκ(t)|·speed γ t`, κ = (x'y''−y'x'')/w³ (§1.1) | [SY] + [NC 60] |
| `arcLengthOf (offsetParam γ d) a b = base − d·(φ(b)−φ(a))` (§1.2) | [SY]; [CL] for `ds_d = ds − d·dφ` |
| ellipse offset = E + elementary (no Π) (§2.3) | [SY] + [NC 60] |
| monomial offset = V4 ₂F₁ + arctan (§2.4) | [SY] + [NC 60] |
| curvature formula correction (§2.4) | [SY] + [NC 20] |
| cubic-pair offset = incomplete Π + elementary; no complete ₂F₁ (§2.6) | [SY] + [NC 49] |
| `∫dθ/(a²sin²θ+b²cos²θ) = (1/(ab))arctan((a/b)tanθ)` (§2.3) | [SY] (residual 0) |
| V4 / H6 arc-length identity reused | [CL] (PLAN §2 V4), [NC 60] here |
| `arctan z = z·₂F₁(½,1;3/2;−z²)` (the offset's elementary term, as ₂F₁) | [CL] (PLAN §4 H1) |
| affine invariance of the classification (§5) | [SY] |
| sign-change correction is elementary (§6) | [SY] + [SP] (existence of sign changes depends on `d`) |
| coincidence loophole (§6) | [SP] |

No `sorry`; no Lean file touched.

---

## 8. Scripts

| script | contents | backend |
|---|---|---|
| `archived files/hypergeometric-scripts/R4b-offset-checks.wl` | (A) general symbolic offset-speed identity; (B) ellipse numeric vs closed form; (C) monomial n=5 numeric; (D) monomial n=3 numeric; (E) cubic-pair numeric; (F) curvature-formula correction; (G) elementary integral identity | Wolfram Language kernel |

The script was executed on the Wolfram kernel via `wolfram_WolframLanguageEvaluator`;
all residuals reported above were produced there. (Python/mpmath was not used.)
