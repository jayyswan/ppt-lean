# Log-scale chart axes: what they would make reachable

**Status:** survey, 2026-11-18. Research only: no `.lean` edit, no `lake` command. Log axes are
**not** in `Defs.lean`; adding them is the user's decision.
**Sources read:** `Pptc/Defs.lean`; `notes/reachability/R10-decomposition-dictionary.md` (§1, §3,
Claim 3.2 "what would break it"); `R9-singularity-spectrum.md` §0; `notes/offset-inversion/R3-separation.md`
§3 (Lemmas 3.2, 3.3); `R8-missing-curve-audit.md` rows 7/10/13/16; `notes/trendline/`.
**Backend:** mpmath 1.4.1 at 40 digits, script `checks.py` in this folder (cells C1–C8).
Labels: **[Proof]**, **[Numeric]** (mpmath, not Wolfram), **[Heuristic]**, **[Open]**.

---

## 0. Verdicts

1. **The model.** A chart trendline drawn on a log axis is the image of the trendline under
   `Φ(x,y) = (log x, y)` (log x), `Ψ(x,y) = (x, log y)` (log y) or `ΦΨ` (both). The base of the
   log only rescales an axis, which `scale_x`/`scale_y` already do (`log_Pconstructible`).
   Log axes act **only on trendlines**: linear, logarithmic, polynomial (degree ≤ 6), power,
   exponential. They never act on `sine`, `ellipse`, Béziers or text.

2. **Four new graph families, and only four** (§1). Everything else in the 5 × 3 table is
   an existing catalogue entry:
   - **N1** `p(e^X)`: an exponential polynomial with rates `0, λ, …, 6λ`;
   - **N2** `log p(x)`;
   - **N3** `log p(e^X)`: softplus, `log cosh`, log-sum-exp;
   - **N4** `A·exp(k e^X)`: the Gompertz curve and the Gumbel CDF. Its swap is the iterated log
     `log(c log x + b)`.

3. **Transfer lemma [Proof].** A log-axis curve meeting a curve `D` gives nothing new if the
   pull-back `Φ⁻¹(D)` (or `Ψ⁻¹(D)`) is drawable: the readout is `log` of an old one. In
   particular, N-curve ∩ line is **never** new (§2). The new equations are N-curve ∩ (curve
   whose pull-back is not drawable), and N-curve ∩ N-curve.

4. **Biggest gain: R10's three-rate miss closes for commensurate rates [Proof].** R10 Claim 3.2
   names the breaking condition: "a construction that turns a single `z = e^{ku}` into a
   polynomial `z + z²` in the graph function". N1 is exactly that. Any
   `Σ a_j e^{jλu} − Σ b_j e^{jμu} + Bu + C`, with up to 6 multiples of each of two rates, is a
   depth-1 hit (§3.1). Rates that are not covered by two rays (e.g. `{1, √2, √3}`) remain a
   miss **[Heuristic]**.

5. **New equation shapes on Route I [Heuristic novelty].** Each family adds equations not
   reachable before:
   - Gaussian-type `e^{q(x)} = p(x)`, e.g. `e^{x²} = x + 2` (root 1.05710…);
   - Gompertz/Gumbel `exp(−e^{−x}) = q(x)`;
   - `p(e^X) = q(X)` with `deg q ≥ 2`;
   - `log p(x) = sin x` and the like.

   Lambert-reducible cases are old.

6. **Boxes add nothing [Proof sketch].** The tangent equation of any rotated N-curve is
   algebraic in `u = e^X` (N1, N3), algebraic in `x` (N2), or of Lambert type (N4). All of
   these are already reachable (§4).

7. **Arc lengths.** N1–N3 give new *instances* of abelian integrals (incomplete
   hyperelliptic, with third-kind poles), not a new class. N4 gives the first arc length whose
   integrand mixes `u` with `e^{ku}`:

   ```
   ∫ √(1 + A²k²u²e^{2ku}) du/u
   ```

   That is a genuinely new transcendental class. It is not Li₂: the square root does not
   cancel (§5). A general-argument polylog is still out of reach.

8. **Named open rows (R8): unchanged, but a lemma must be repaired [Proof sketch, needs review].**
   N3 breaks the premise of R3 Lemma 3.3 / R9 §0.1, that a tower graph function has finitely
   many finite log points: `log(1 + e^{2X})` has one at every `iπ(m + ½)`. The exclusions of the
   involute, rhumb, tractrix and Biot rows survive under a **refined invariant**, the
   *monodromy value* (§6):
   - N-curves' infinite log families have monodromy in `2πi·ℝ` (C5: `2πi`);
   - the targets' have **real** nonzero monodromy (C5: `gd` has `2π`).

   The `1/log` and `δ log δ` exclusions (`tan x = λx`, the `l = 0` well) are unaffected. The
   one new singularity type is a single `log log` point (N4 swap), which is neither of those.

9. **PowerPoint fidelity is unprobed [Open].** It is not yet measured whether PowerPoint draws
   a polynomial or exponential trendline on a log axis as the exact transformed curve, rather
   than as a polyline of transformed samples. The domains are also unmeasured: where `p ≤ 0`,
   and backward/forward forecast on log axes. Do this probe first, in the style of
   `notes/trendline/trendline-origin-A-com.md`.

---

## 1. The catalogue

Trendline types (data coordinates) against axis choice (screen coordinates). `p ∈ ℚ[x]`,
`deg p ≤ 6`. The parameters are rational up to fitting; §1.2 covers the coefficient freedom.

| trendline (data) | log x: `X = log x` | log y: `Y = log y` | log–log |
|---|---|---|---|
| linear `ax + b` | `a e^X + b` (**E1**) | `log(ax + b)` (**E5**) | `log(a e^X + b)` (**N3**, deg 1) |
| logarithmic `c log x + b` | line | `log(c log x + b)` (**N4 swap**) | `log(cX + b)` (**E5**) |
| polynomial `p(x)` | `p(e^X)` (**N1**) | `log p(x)` (**N2**) | `log p(e^X)` (**N3**) |
| power `a x^b` | `a e^{bX}` (**E1**) | `log a + b log x` (**E5**) | line |
| exponential `c e^{bx}` | `c·exp(b e^X)` (**N4**) | line | `log c + b e^X` (**E1**) |

Linear on log–log is N3 with a degree-1 polynomial. Softplus `log(1 + e^X)` is its simplest
case.

### 1.1 The new families

- **N1 `h(X) = p(e^{λX})`.**
  - Entire function.
  - Rates `jλ`, `0 ≤ j ≤ 6`, so up to six exponential atoms in one graph.
  - With the shear `(X, Y) ↦ (X, Y + αX)` it carries a linear drift too.
  - Defined on all of `ℝ` (data `x > 0`).
- **N2 `h(x) = log p(x)`**, on the components of `{p > 0}`.
  - Log points at every root of `p`, each with monodromy `2πi × multiplicity`.
  - With one distinct root it is E5. It is new only when `p` has ≥ 2 distinct roots, real or
    complex.
- **N3 `h(X) = log p(e^{λX})`.**
  - Includes softplus `log(1 + e^X)`, and `log cosh X = log((e^{2X}+1)/2) − X` (C6).
  - Log points at `X = (log r + i arg r + 2πin)/λ` for each root `r` of `p`. That is
    **infinitely many** finite log points, in vertical lattices.
- **N4 `h(X) = A exp(k e^{λX})`.**
  - Gompertz `a e^{−b e^{−cX}}`; Gumbel CDF `exp(−e^{−X})`.
  - Entire. Its swap `X = λ⁻¹ log(k⁻¹ log(Y/A))` has a log point at `Y = A` and a single
    **`log log` point** at `Y = 0`.

### 1.2 Coefficient freedom

`scale_y` by a P-constructible `K` and `translate_x` by a P-constructible `s` turn N1 into
`K Σ a_j c^j e^{jλX}`, with `a_j ∈ ℚ` and `c = e^{λs}` any positive P-constructible number. So
for two terms the coefficients are fully free. For three or more terms the ratios
`a_i a_k / a_j²` (with `i + k = 2j`) are rational invariants. If fitting to rational data yields
only rational `a_j` (as for `poly_graph`), a three-term target such as `e^{3u} + π e^{2u} + e^u`
is **not** directly one N1 graph. It can still be split across the two sides of a Route-I
difference. [Proof for the invariant; whether a fit can produce irrational coefficients is
**[Open]**, cf. power-fit exponents `log 3 / log 2` from rational data.]

---

## 2. The transfer lemma

> **Lemma 2.1 [Proof].** Let `C` be a drawable data-plane curve, let `D` be a screen curve, and
> suppose `Φ⁻¹(D) = {(x, y) : (log x, y) ∈ D}` is drawable. Then `Φ(C) ∩ D = Φ(C ∩ Φ⁻¹(D))`, and
> its readout `X = log x` is P-constructible whenever the old readout `x` is
> (`log_Pconstructible`). The same holds for `Ψ` and `ΦΨ`.

`Φ` is a bijection `(0,∞) × ℝ → ℝ²`, so it commutes with intersection, and singleton
intersections stay singletons. C1 checks one instance at 40 digits (`|X − log u| ≈ 3·10⁻⁴²`).

Pull-backs that **are** drawable, so give nothing new:

| `D` (screen) | `Φ⁻¹(D)` | `Ψ⁻¹(D)` |
|---|---|---|
| line | `a log x + b` (E5) | `e^{b} e^{ax}` (E1) |
| `Y = e^{kX}` | `x^k` (power law) | `e^{e^{kx}}`-type: N4, **not** drawable on linear axes |
| `Y = log X` | `log log x`: N4 swap, **not** drawable | line |

So the genuinely new single-intersection equations are an N-curve against a partner whose
pull-back is not drawable:
- a polynomial of degree ≥ 2: `p(e^X) = q(X)`, `log p(x) = q(x)`;
- `sine`;
- `ellipse`;
- a Bézier;
- another N-curve.

---

## 3. Route-I hits (depth 1)

### 3.1 Commensurate exponential sums: R10 Claim 3.2 withdrawn for this case

> **Proposition 3.1 [Proof].** Let
> `F(u) = Σ_{j=1}^{6} a_j e^{jλu} − Σ_{j=1}^{6} b_j e^{jμu} + Bu + C`,
> with each side's coefficients obeying §1.2. Then `F = g₁ − g₂` with
> - `g₁ = p₁(e^{λu}) + Bu + C`;
> - `g₂ = p₂(e^{μu})`.
>
> Both are N1 plus a shear. Each comes from a polynomial trendline on a log-x axis, then
> `scale_x`, a linear map, and a translation. `inter_x` against `translate_y g₂ x` gives
> `u = F⁻¹(x)` on any monotone branch.

Examples:
- **C2.** `e^u + e^{2u} + e^{3u} + u = 5` has root `u = 0.224142176785…`, from one N1 graph and a
  horizontal line. The second side is not needed.
- **C2.** `⅓ cosh³u` (R10 row 4, "four rates") is `g₁ − g₂` with
  `g₁ = (e^{3u} + 3e^u)/24` and `g₂ = −(e^{−u}·3 + e^{−3u})/24`, a reflected N1 (residual
  `2·10⁻⁴¹`). It was already **R** by another route; this is a second, uniform route.

Mixed atoms such as "two exponential rates + one trig frequency" remain misses: log axes never
touch `sine`.

### 3.2 Gaussian-type equations (N2 against a polynomial, through `Ψ`)

`log p(x) = q(x)` is equivalent to `p(x) = e^{q(x)}`. For `deg q ≥ 2` the atom `e^{q(x)}` is not in
E1–E9.

Example (C8): `e^{x²} = x + 2` has root `1.05710354999…`. Cases where both `p` and `q` are
monomials reduce to Lambert W and are old. The general case is **[Heuristic]** new: there is no
reduction found, and no proof of novelty.

### 3.3 Gompertz / Gumbel equations (N4)

`A exp(k e^X) = q(X)` with `deg q ≥ 2` is new (Transfer: `Φ⁻¹` of a parabola is not drawable).
Against a line it is old (`c e^{kx} = a log x + b` was E1 ∩ E5).

Statistics gives one immediate family. The quantiles of the Gumbel distribution are elementary,
so they are old. But "the CDF equals a polynomial" type equations, such as a Gumbel/normal-quantile
cross-over computed with polynomial approximants, are new. Nothing named was found.
**[Heuristic]**

### 3.4 N-curve against N-curve

Two log-axis charts can be overlaid as plain curves in one plane, for example
`p(e^X) = log q(X)` (N1 ∩ N2). Such equations nest an exponential inside a log of a polynomial.
They are new by atom count. **[Heuristic]**

---

## 4. Boxes add nothing new [Proof sketch]

`box_xmax`/`box_ymax` of a rotated or sheared N-curve read a point where
`h'(X) = m` for a P-constructible slope `m`:

| family | `h'(X) = m` | solved by |
|---|---|---|
| N1 | `λ u p'(u) = m`, `u = e^{λX}` | algebraic `u`, then `X = log u / λ` |
| N2 | `p'(x) = m p(x)` | algebraic `x` |
| N3 | `λ u p'(u) = m p(u)` | algebraic `u`, then `log` |
| N4 | `Akλ u e^{ku} = m` | Lambert W (`notes/lambert`) |

The extremal value `h` at that point is again N-evaluated at an old number. N1–N3 values are
elementary in old numbers. N4's value is `A exp(k·W(·)/k)`, which is elementary in the Lambert
value. So box readouts of single N-curves are all old. Boxes of **offsets** of N-curves, and of
`arc_of_length` sub-arcs, are **[Open]**. They inherit the new arc-length functions of §5.

---

## 5. Arc length

Screen arc length is `∫ √(1 + h'(X)²) dX`. With `u = e^{λX}` (C3, C7 check the substitution):

| family | integrand | class |
|---|---|---|
| N1 | `√(1 + λ²u²p'(u)²) du/(λu)` | hyperelliptic (`deg (u p')² ≤ 12`, genus ≤ 5), third-kind pole at `u = 0` |
| N2 | `√(p² + p'²) dx / |p|` | hyperelliptic, third-kind poles at the roots of `p` |
| N3 | `√(p² + λ²u²p'²) du / (λ u p)` | same type as N2 in `u` |
| N4 | `√(1 + A²k²λ²u²e^{2ku}) du/(λu)` | **mixed**: `u` and `e^{ku}` are algebraically independent |

- **N1–N3 are not a new class.** `power_law` with a rational exponent already gives
  superelliptic integrands of unbounded genus. What is new is specific moduli, with third-kind
  poles at prescribed places. It is worth checking against `Pptc/ThirdKindAll/` before claiming
  any instance as new.
- **A Pythagorean case (C4).** `p = x² − 1` gives `(x² − 1)² + (2x)² = (x² + 1)²`, so the speed
  of `log(x² − 1)` is the rational `(x² + 1)/(x² − 1)`, and the arc length is
  `x + log((x − 1)/(x + 1))`. It is elementary. More generally, `p = a x² + bx + b²/(4a) − a` is
  the only shape with a rational speed: the degree count forces `deg p = 2`.
- **N4 is the one new transcendental class.** The substitution `w = Akλ u e^{ku}` makes it
  `∫ √(1 + w²) dw / (w (1 + ku))`, with `u` a Lambert-W function of `w`. This is the class
  `arc_of_length` + `box` would invert along a Gompertz curve.
- **Polylogarithms.** `Li₂(x) = ∫ s/(eˢ − 1) ds` needs an integrand that is **rational** in
  `(s, eˢ)`. N4 has the right atoms, but under an irreducible square root. Shears and scales
  only replace `1 + h'²` by a quadratic form in `(1, h')`, which is never a perfect square for
  N4's `h'`. General-argument Li₂ stays out of reach. **[Heuristic]**

---

## 6. The singularity invariants (R3, R9) and the named rows

**What breaks.** R3 Lemma 3.3 and R9 §0.1 state that a tower graph function has only finitely
many finite log branch points. N3 violates this: `log(1 + e^{2X})` has a log point at every
`iπ(m + ½)`. Those are exactly the locations of `gd`'s log points, which drive the exclusions of
the involute, rhumb, tractrix and Biot rows (R8 §3.2, R3 (3.4.1)).

**What survives.** The *monodromy values* differ (C5, 40-digit loop integrals at `iπ/2`):

```
d/dX log(1 + e^{2X}) :  loop integral = 2πi      (imaginary)
d/du gd(u) = sech u   :  loop integral = 2π       (real)
```

> **Lemma 6.1 [Proof sketch, needs review].** Every finite log point of an N-curve graph function
> (either orientation), after real affine data and real scaling, has monodromy in `i·ℝ`. A
> curve's infinitely many log points are all of this kind, so all but finitely many log points
> of a tower-plus-log-axes graph function have imaginary monodromy.

*Sketch.* N1 and N4 are entire. Their swaps are `log` of a real-coefficient algebraic function of
`e^{λY}` (or of `log Y`), whose residues are rational, giving monodromy `2πi·ℚ·K` with `K` the real
`scale_y`. N2 and N3 are `log p` with `p` real, giving monodromy `2πi × multiplicity`. Affine maps
with real entries multiply monodromy by real factors. The finitely many log points of the old
catalogue are unaffected.

> **Corollary 6.2 [Proof sketch].** The Route-I exclusions of R8 rows 7, 10, 13, 16 (B convention)
> survive the addition of log axes, with "infinitely many finite log points" in R3 §3 replaced
> by "infinitely many finite log points with non-imaginary monodromy".

The target `F` has real nonzero monodromy (a multiple of `2πd`, R3 Lemma 3.2) at infinitely many
points. Pulling back by an algebraic `Ã` multiplies it by integers, so it stays real. A difference
`g₁ − g₂` has non-imaginary monodromy at only finitely many points. This is the same contradiction
as R3, on the real part.

**`1/log` and `δ log δ` (R9 rows: `tan x = λx`, the `l = 0` well).** None of N1–N4 has either. The
only new singularity type is the single `log log` point of N4's swap. R9's exclusions need
*infinitely many* such points, so they stand. R9 §0.1's classification list should gain
"`log log`, at most one per N4 swap" and drop "finitely many" for log points.

**Net effect on R8.** No named row changes status. The rows needing trig inside a log or an
exponential (beams' log-cosine, rhumb, involute, tractrix) are untouched, because log axes never
act on `sine`.

---

## 7. Suggested next steps

1. **PowerPoint probe** (Verdict 9): polynomial and exponential trendlines on log-x, log-y and
   log–log axes. Measure the rendered curve against `p(e^X)`, `log p(x)` and `A exp(k e^X)` to
   pixel accuracy, plus the domain behaviour where `p ≤ 0`. Everything above is conditional on
   this.
2. **Review Lemma 6.1** properly, and check R3 §3.4's argument goes through with the monodromy
   refinement. This is the one place where log axes could invalidate an existing negative.
3. **Constructor sketch, if adopted** (one constructor per axis mode, data-side trendline types
   only):
   ```lean
   | logx_poly (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 6) :
       PConstructibleCurve {q : ℝ × ℝ | q.2 = Polynomial.aeval (Real.exp q.1) p}
   | logy_poly (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 6) :
       PConstructibleCurve {q : ℝ × ℝ | 0 < Polynomial.aeval q.1 p ∧
         q.2 = Real.log (Polynomial.aeval q.1 p)}
   | logx_exp (a b : ℚ) :
       PConstructibleCurve {q : ℝ × ℝ | q.2 = a * Real.exp (b * Real.exp q.1)}
   ```
   `logxy_poly` (N3) is the remaining one. N1 with a degree-1 polynomial is E1, so nothing old is
   duplicated beyond that.
4. **First Lean target:** Proposition 3.1 for `e^u + e^{2u} + e^{3u} + u` (strictly increasing, one
   N1 curve, one `inter_x`). It is the analogue of R10's H1.
