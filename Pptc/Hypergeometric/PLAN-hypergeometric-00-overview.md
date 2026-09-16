# PLAN-hypergeometric: shared context (read this first, every task)

Goal of the programme: establish which values of the Gauss hypergeometric function
`₂F₁(a, b; c; z)` are P-constructible. The second, equally important goal is to push those
results *back out*: use each P-constructible ₂F₁ family as a bridge to new P-constructible
numbers (`Γ` quotients, definite integrals, `₃F₂` values, Legendre functions, AGM, lattice
constants). The bridge-back half (§5) is the reason to do this at all. A ₂F₁ family that
only restates `ellipticF_Pconstructible` is worth little. One that turns into a statement
about `Γ`, or about a number nobody would have tied to `PConstructible`, is worth a lot.

Mathlib has `ordinaryHypergeometric` (`₂F₁`) and very little else about it (§3). Everything
already P-constructible that this plan leans on is in `Pptc/Basic.lean` (elliptic integrals,
`log`, `rpow`, `arcsin`, `arctan`) and `Pptc/Gamma.lean` (`Γ(n/24)` for all `n : ℤ`).

**Where the files live.** This plan, the `NOTES-hypergeometric-R*.md` research notes and every
`HANDOFF-hypergeometric-*.md` log sit in `pptc/Pptc/Hypergeometric/`, beside the Lean sources
they describe (Lake ignores non-`.lean` files). Numeric scripts stay in
`archived files/hypergeometric-scripts/` at the repo root, which is outside the git root, and
the notes cite them by that path.

## Status — 2026-09-15

**Waves 0 and 1 are done.** Nine files compile, no `sorry`, no axioms beyond `propext`,
`Classical.choice`, `Quot.sound`: `Basic` (L1, including the `arcsin` case, which needed an
arcsine power series built from scratch — Mathlib has none), `Elliptic` (L2), `Contiguous`
(L3: the derivative plus five contiguous relations), `Gauss` (L4), `Graphs` (L5a, extended to
affine images of `y = xⁿ`), `Euler` (L7a), `Polya` (L8). Two are incomplete:

- **L6a `Quadratic.lean`: blocked.** Only the formal power-series identity landed. The blocker
  is the missing `PowerSeries` evaluation API (no `PowerSeries.sum`, no `IsLinearTopology ℝ ℝ`),
  which forces a Fubini argument valid only on `|z| < (√2−1)/2` plus analytic continuation.
  **Retry through the Euler integral instead** (see B7): L7a landed `hyp_eq_integral`, and the
  classical proof of the quadratic transformation is a change of variable inside that integral.
- **L9 `Signatures.lean`: conditional.** `V7` is an explicit hypothesis; the reduction to
  `hyp_half_half_one_Pconstructible` is unconditional. R2 confirms `V7` is not an instance of
  any standard transformation, so it needs a fresh coefficient or ODE argument. The theorem is
  deliberately **not** tagged `@[pconstructible_cond]`, since `hV7` is an unproved identity
  rather than a side condition and `sideTac` could never discharge it.

**Deviations worth knowing.** `hyp_one_eq_Gamma` (L4) also assumes `0 < a`, `0 < b`, `b < c`:
the non-negative dominated-convergence route at `z = 1` needs them. Now that L3 has landed,
shifting the parameters into range with the contiguous relations should lift that restriction.
`hyp_neg_half_arcLength_Pconstructible` (L5a) also needs `n ≤ 6` (inherited from `poly_graph`)
and, for the affine version, an explicit injectivity hypothesis.

**What the research changed.** See §5; in short, R1 closed B6 negatively and R2 found a better
route for H5 than the one this plan assumed.

Each row is **one agent run**, owning **one file** with **one deliverable**. All Lean files live
under `Pptc/Hypergeometric/`. The generic ₂F₁ facts are split away from their PConstructible
corollaries, so most tasks depend only on `Basic`, and the work fans out as early as possible.

| id | wave | file / deliverable | content | depends on |
|---|---|---|---|---|
| L1 | 0 | `Hypergeometric/Basic.lean` | API contract (below) + elementary cases (H1) | none |
| L8 | 0 | `Hypergeometric/Polya.lean` | closed forms of `u(3)`, `p(3)` are PConstructible (B5) | none (`Pptc.Gamma`) |
| R1 | 0 | `NOTES-hypergeometric-R1.md` | origin problem for `power_law`; hyperelliptic route to new `Γ` (B1, B6) | none |
| R2 | 0 | `NOTES-hypergeometric-R2.md` | explicit cubic/sextic signature reductions (H5) | none |
| R3 | 0 | `NOTES-hypergeometric-R3.md` | Watson/Pólya reduction; check bcc/fcc formulas (B5) | none |
| L2 | 1 | `Hypergeometric/Elliptic.lean` | `K`, `E` as ₂F₁ (H2) | L1 |
| L3 | 1 | `Hypergeometric/Contiguous.lean` | derivative + three-term relations, generic (H3) | L1 |
| L4 | 1 | `Hypergeometric/Gauss.lean` | Gauss summation + denominator-24 family (H4) | L1 (`Pptc.Gamma`) |
| L5a | 1 | `Hypergeometric/Graphs.lean` | arc lengths of `y = xⁿ` as ₂F₁ (H6, first part) | L1 |
| L6a | 1 | `Hypergeometric/Quadratic.lean` | quadratic transformation, generic (B7) | L1 |
| L7a | 1 | `Hypergeometric/Euler.lean` | Euler integral representation, generic (B2) | L1 |
| L3b | 2 | `Hypergeometric/EllipticClass.lean` | contiguous class of `(½,½;1)` is PConstructible | L2, L3 |
| L5b | 2 | `Hypergeometric/GraphsClass.lean` | contiguous classes of the H6 families | L3, L5a |
| L6b | 2 | `Hypergeometric/Clausen.lean` | `Σ C(2n,n)³(x/64)ⁿ` PConstructible (B3) | L2, L6a |
| L6c | 2 | `Hypergeometric/AGM.lean` | `agm` definition + PConstructible (B4) | L2, L6a |
| L9 | 2 | `Hypergeometric/Signatures.lean` | quartic signature V7; cubic/sextic after R2 (H5) | L2 (R2 for cubic/sextic) |
| L7b | 3 | `Hypergeometric/Moments.lean` | trigonometric moment integrals (B2) | L3b, L7a |
| L10 | 3 | `Hypergeometric/GammaBridge.lean` | Gauss's second theorem; B1 rows as consistency theorems | L4, L6a, L9 |
| L11 | 4 | `Pptc/Hypergeometric.lean` | umbrella module importing all of the above | everything |

All tasks in the same wave can run at once. A task starts once every file it depends on
compiles *and* has an `.olean`.

**Fan-out mechanics.**

- When a task finishes, run `lake build Pptc.Hypergeometric.<File>` for **that one target**, so
  the next wave can import it. Never chain several targets in one command (`CLAUDE.md`,
  Gotchas). `Pptc.Gamma` is one of the heavy targets, so L4 and L8 should not both be building
  at the same time.
- **The L1 contract.** Wave-1 agents code against L1's names, so L1 must export exactly these,
  and must not rename them afterwards. The names are suggestions until L1 lands; after that
  they are fixed.
  - `hyp (a b c z : ℝ) : ℝ`: an abbreviation for `ordinaryHypergeometric (𝕂 := ℝ) a b c z`,
    so statements stay short.
  - `hypCoeff (a b c : ℝ) (n : ℕ) : ℝ`: the `n`-th coefficient, with the lemma
    `hyp_eq_tsum_coeff`.
  - `hasSum_hyp {a b c z} (hz : |z| < 1) (hc : ∀ n : ℕ, c ≠ -n)`: `HasSum (fun n => hypCoeff a b c n * z ^ n) (hyp a b c z)`.
  - `hyp_eq_of_hasSum`: the identification lemma. If `f z = ∑ hypCoeff a b c n * z ^ n` on
    `|z| < 1`, then `f z = hyp a b c z`.
  - `hypCoeff_succ`: the ratio `hypCoeff (n+1) = hypCoeff n * (a+n)(b+n)/((c+n)(n+1))`, the
    single fact that most coefficient-level proofs reduce to.
- Wave-1 agents that need a lemma missing from L1 add it **to their own file** and note it in
  their HANDOFF. They never edit `Basic.lean`, which would invalidate everyone's `.olean`.

Lean tasks: follow `CLAUDE.md` (iterate with `lean_diagnostic_messages`; targeted imports; a
`-- Theorem:` line on every theorem; `/-! ### -/` sections explaining *why*; no `sorry` on
`main`). Tag closure results `@[pconstructible]` / `@[pconstructible_cond]`.
Research tasks: **do not edit any `.lean` file.** Every identity in the notes must be checked
numerically to ≥ 15 digits or proved symbolically, and must say which. Scripts go in
`archived files/hypergeometric-scripts/`.
Every task keeps `HANDOFF-hypergeometric-<id>.md` at the repo root; create it first and append
one line after every step.

## 1. What is and is not a ₂F₁ (verified)

The parameter `c = k²` follows the repo convention. `F₁` is Appell's two-variable function and
`F_D` is Lauricella's.

| repo object | hypergeometric form | ₂F₁? |
|---|---|---|
| `ellipticF c (π/2)` = `K` | `(π/2) ₂F₁(½, ½; 1; c)` | **yes** |
| `ellipticE c (π/2)` = `E` | `(π/2) ₂F₁(−½, ½; 1; c)` | **yes** |
| `ellipticPi c n` | `(π/2) F₁(½; 1, ½; 1; n, c)` | no |
| `ellipticF c φ` | `sin φ · F₁(½; ½, ½; 3/2; sin²φ, c sin²φ)` | no |
| `ellipticE c φ` | `sin φ · F₁(½; ½, −½; 3/2; sin²φ, c sin²φ)` | no |
| `ellipticPiInc` | `F_D` in three variables | no |

So this programme **does not simplify** the incomplete-integral theorems in `Basic.lean`,
`ThirdKind.lean` or `Jacobi.lean`. Its reach is the complete integrals, `Gamma.lean`, and the
new families below.

## 2. Verified facts you may rely on

Checked with the Wolfram kernel; the script is
`archived files/hypergeometric-scripts/00-overview-checks.wl`. Digits are the accuracy of the
difference computed there. "Classical" means taken from the literature and not re-checked.

- **(V1–V2)** `K = (π/2) ₂F₁(½,½;1;c)`, `E = (π/2) ₂F₁(−½,½;1;c)`. Exact at `c = 3/10`.
- **(V3)** The Appell forms in §1 for incomplete `F` and complete `Π`. ≥ 68 digits.
- **(V4) Power-law arc length.** For `y = x^b` with `m = 2b − 2 > 0`:
  `∫₀^X √(1 + b² x^m) dx = X · ₂F₁(−½, 1/m; 1 + 1/m; −b² X^m)`. 29 digits (`b = 5/2`).
  The proof is one line: `(1/m)ₙ / (1 + 1/m)ₙ = 1/(mn + 1)`.
- **(V5) Gauss's second theorem** at the four Ramanujan signatures:
  `₂F₁(a, 1−a; 1; ½) = √π / (Γ((1+a)/2) Γ(1 − a/2))` for `a ∈ {½, ⅓, ¼, ⅙}`. ≥ 68 digits.
- **(V6) Quadratic transformation and Clausen.** `₂F₁(½,½;1;z) = ₂F₁(¼,¼;1;4z(1−z))` (for
  `z ≤ ½`), and `₂F₁(¼,¼;1;x)² = ₃F₂(½,½,½;1,1;x)`. ≥ 68 digits.
- **(V7) Quartic signature.**
  `₂F₁(¼,¾;1;z) = (1+√z)^(−½) ₂F₁(½,½;1; 2√z/(1+√z))`. Exact at `z = 1/5`.
- **(V8) Legendre function.** `P_{−1/3}(x) = ₂F₁(⅓,⅔;1;(1−x)/2)`. 69 digits.
- **(V9) Euler integral, trigonometric form.**
  `∫₀^{π/2} sin^{2j}θ cos^{2l}θ (1 − c sin²θ)^{−a} dθ = ½ B(j+½, l+½) ₂F₁(a, j+½; j+l+1; c)`.
  30 digits (`j=2, l=1, a=−½, c=2/5`).
- **(V10) Kummer's theorem** `₂F₁(a,b;1+a−b;−1) = Γ(1+a−b)Γ(1+a/2)/(Γ(1+a)Γ(1+a/2−b))`.
  69 digits at `(⅓, ⅙)`.
- **(V11) Pólya's cubic-lattice constant.** The expected number of returns to the origin of
  simple random walk on `ℤ³` is
  `u(3) = (√6/(32π³)) Γ(1/24)Γ(5/24)Γ(7/24)Γ(11/24) = 1.5163860591519780…`
  (Glasser–Zucker 1977). It also equals `(12/π²)(18 + 12√2 − 10√3 − 7√6) K(k₆)²`, where
  `k₆ = (2−√3)(√3−√2)` is a root of `x⁴ + 12x³ + 2x² − 12x + 1`. The two closed forms agree to
  67 digits. The defining integral `∫₀^∞ (e^{−t/3} I₀(t/3))³ dt` agrees to about 5 digits
  (tail-limited). The return probability is `p(3) = 1 − 1/u(3) = 0.340537329550999…`.
- **Classical (not re-checked):** Gauss's summation theorem
  `₂F₁(a,b;c;1) = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))` for `c − a − b > 0`. Gauss's AGM formula
  `agm(1, √(1−k²)) = π / (2K(k))`. Chebyshev's criterion that `∫ xᵖ(α + βx^m)^q dx` is
  elementary iff one of `(p+1)/m`, `q`, `(p+1)/m + q` is an integer.

## 3. Mathlib inventory and constraints

Verified to exist (names confirmed by search):

- `ordinaryHypergeometric` (notation `₂F₁`) and `ordinaryHypergeometricSeries`, in
  `Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric` (present in this repo's `.lake`).
  `ordinaryHypergeometric_eq_tsum`, `ordinaryHypergeometricSeries_apply_eq`,
  `ordinaryHypergeometricSeries_radius_eq_one`,
  `ordinaryHypergeometricSeries_eq_zero_of_neg_nat`, and
  `ordinaryHypergeometric_radius_top_of_neg_nat₁/₂/₃`.
- Binomial series: `Real.one_add_rpow_hasFPowerSeriesOnBall_zero` (`Mathlib.Analysis.Analytic.Binomial`).
- Wallis-type integrals: `integral_sin_pow_even`, `integral_sin_pow`,
  `EulerSine.integral_cos_pow_eq`.
- Abel's theorem: `Real.tendsto_tsum_powerSeries_nhdsWithin_lt` (`Mathlib.Analysis.Complex.AbelLimit`).
- Euler's limit for `Γ`: `Real.GammaSeq_tendsto_Gamma`; Beta integrals in
  `Mathlib.Analysis.SpecialFunctions.Gamma.Beta`.

**Not in Mathlib:** the Euler integral representation, the hypergeometric ODE, contiguous
relations, Gauss/Kummer summation, the quadratic transformations, `₃F₂` or any `pFq`, and AGM.

**The junk-value trap.** `₂F₁` is a `tsum`. It is meaningful on `|z| < 1`, and at `z = 1` when
`c − a − b > 0` (the terms are then absolutely summable). For `|z| > 1` the series diverges
and the `tsum` returns 0. There is no analytic continuation. Every statement must carry
`|z| < 1`, or the `z = 1` hypothesis. A transformation that leaves the disc (Pfaff with `z < −1`,
say) needs its own definition, and the first time one is needed, stop and flag it in the
HANDOFF rather than defining a continuation ad hoc. Likewise `c ∈ −ℕ` makes Mathlib's
coefficients junk; exclude it.

## 4. Forward direction: which ₂F₁ values are P-constructible

**H1: elementary cases (L1).** From existing closure lemmas:
`₂F₁(a,b;b;z) = (1−z)^(−a)` (`rpow_Pconstructible`), `₂F₁(1,1;2;z) = −log(1−z)/z`,
`₂F₁(½,1;3/2;−z²) = arctan z / z`, `₂F₁(½,½;3/2;z²) = arcsin z / z`. The real deliverable is
the API: a reusable lemma "a function with this power series on the unit ball equals `₂F₁`",
so that each case is a coefficient computation, not a new analytic proof.

**H2: the elliptic bridge (L2).** Target statements (names are suggestions):

```lean
theorem ellipticF_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticF c (π / 2) = π / 2 * ordinaryHypergeometric (𝕂 := ℝ) (1/2) (1/2) 1 c
theorem ellipticE_pi_div_two_eq_hyp {c : ℝ} (hc : |c| < 1) :
    ellipticE c (π / 2) = π / 2 * ordinaryHypergeometric (𝕂 := ℝ) (-1/2) (1/2) 1 c
```

Route: expand `(1 − c sin²θ)^(∓½)` with the binomial series, and bound the tail uniformly in
`θ` by the tail at `|c|`. Swap sum and integral (`intervalIntegral.hasSum_integral_of_dominated_convergence`
or similar; confirm the name), evaluate each term with `integral_sin_pow_even`, and match
coefficients against `ordinaryHypergeometricSeries_apply_eq`. Corollary: `₂F₁(±½, ½; 1; z)` is
P-constructible for P-constructible `z ∈ (−1, 1)`.

**H3: derivative and contiguous closure (L3).** The key structural fact: over the rational
functions in `z`, the contiguous class `{₂F₁(a+i, b+j; c+k; z)}` is spanned by `F` and `F′`
(away from the degenerate parameters). So the right closure invariant is

> if `₂F₁(a,b;c;z)` and `d/dz ₂F₁(a,b;c;z)` are P-constructible, so is every contiguous
> `₂F₁(a+i, b+j; c+k; z)` with `c + k ∉ −ℕ`,

and it is the ₂F₁ analogue of `Gamma_add_intCast_Pconstructible`. Ingredients:
`d/dz ₂F₁(a,b;c) = (ab/c) ₂F₁(a+1,b+1;c+1)` (termwise from the power series), and Gauss's
three-term relations (proved on coefficients). Instance (L3b): for the elliptic class
`(½+ℤ, ½+ℤ, 1+ℕ)`, `F = 2K/π` and `F′` comes from `dK/dc = (E − (1−c)K)/(2c(1−c))`. Both are
P-constructible, so the whole class is.

**H4: Gauss summation and the denominator-24 family (L4).**

```lean
theorem hyp_one_eq_Gamma {a b c : ℝ} (h : 0 < c - a - b) (hc : ∀ n : ℕ, c ≠ -n) :
    ordinaryHypergeometric (𝕂 := ℝ) a b c 1
      = Gamma c * Gamma (c - a - b) / (Gamma (c - a) * Gamma (c - b))
-- Headline: every rational a, b, c with 24a, 24b, 24c ∈ ℤ, c − a − b > 0, c ∉ −ℕ.
theorem hyp_one_Pconstructible_of_den_24 ... : PConstructible (ordinaryHypergeometric a b c 1)
```

Recommended proof, which avoids the Euler integral: the recurrence
`F(a,b;c;1) = ((c−a)(c−b) / (c(c−a−b))) F(a,b;c+1;1)`, iterated `n` times. Then
`F(a,b;c+n;1) → 1` and `Real.GammaSeq_tendsto_Gamma` for the product (Andrews–Askey–Roy,
Thm 2.2.2). The recurrence at `z = 1` needs Abel's theorem to pass from `z < 1` to `z = 1`.
The headline is then just `Gamma_intCast_div_twentyfour_Pconstructible`. Also worth stating:
Kummer (V10) and Gauss's second theorem (V5), once H6 or the quadratic transformation (B7)
provides a route. They give the families at `z = −1` and `z = ½`.

**H5: Ramanujan's signatures — use R2's parametric forms.** R2 delivered the cubic and sextic
reductions, verified to 79 digits, and they are naturally *parametric*. For `p ∈ [0, 1)` the
sextic one reads

```
z = ξ(p) = (27/4) p²(1+p)²/(1+p+p²)³,     k² = x(p) = p(2+p)/(1+2p),
₂F₁(⅙,⅚;1;ξ(p)) = (1 − x + x²)^{1/4} · ₂F₁(½,½;1;x(p)),
```

and the cubic one likewise with `γ(p) = (1+p+p²)/√(1+2p)`. **Do not eliminate `p`.** Stated in
`p`, both the argument and the prefactor are rational (or square roots) in `p`, so a
P-constructible `p` gives a P-constructible value immediately, and R2's degree-12 caveat on the
eliminated prefactor — which exceeds the degree-9 ceiling of `Pptc/Nonic` — never arises. To
state the result for an arbitrary P-constructible `z` instead, recover `p` with
`root_Pconstructible_le_six_coeffs` (`Pptc/Basic.lean`): `p` is a root of a sextic whose
coefficients are P-constructible in `z`, and the argument maps have degree 6 exactly. Both maps
are onto `[0, 1)`, so no `z` in range is lost. This is the cheapest route to two of the
signatures and it needs none of the transformation machinery that blocked L6a. The quartic `V7`
is the odd one out: R2 checked DLMF 15.8 and found no standard transformation matching it.

**H6: arc lengths of monomial graphs, a non-elliptic source (L5a, L5b).** `poly_graph` draws
`y = xⁿ` for `n ≤ 6`, *through the origin*, and `scale_x`/`scale_y` supply any P-constructible
coefficient. By V4 its arc length from `(0,0)` is a ₂F₁ with `m = 2n − 2 ∈ {2, 4, 6, 8, 10}`:

> `₂F₁(−½, 1/m; 1 + 1/m; w)` is P-constructible for every P-constructible `w ∈ (−1, 0]` and
> `m ∈ {2,4,6,8,10}`, and so, by H3, is its whole contiguous class.

`m = 2` is elementary (`asinh`). `m = 4` is elliptic (F2 of `PLAN-jacobi-00-overview`).
`m = 6, 8, 10` are periods of `y² = 1 + x^m`, of genus 2, 3 and 4: **not elliptic**. These are
the first ₂F₁ values in the programme that the elliptic machinery does not already give.
Through H3 they yield, for instance, `∫₀^X x^p (1 + C x^m)^{q} dx` for all `p ∈ ℕ` and
`q ∈ ½ + ℤ`. Chebyshev's criterion says exactly which of these are secretly elementary; the
theorem should cover all of them, but the section comment should say which are genuinely new.

`power_law` would give every rational `m`, but its curve excludes `x = 0`. `arc_length` then
yields only differences `G(X₁) − G(X₀)` with `X₀ > 0`, where `G(X) = X ₂F₁(…; −b²X^m)`. Removing
that restriction is R1's first question.

## 5. Bridging back: what a P-constructible ₂F₁ family buys

Each item is labelled **new** (a number or family not currently known P-constructible),
**unifies** (re-derives existing results through one mechanism, which is a cross-check and a
simplification), or **speculative**.

**B1: summation theorems turn ₂F₁ values into `Γ` quotients (unifies, and maps the frontier).**
Gauss's second theorem (V5) reads `P_{−a}(0) = ₂F₁(a,1−a;1;½) = √π/(Γ((1+a)/2) Γ(1−a/2))`.
Run backwards, any route making `₂F₁(a,1−a;1;½)` P-constructible makes that `Γ` product
P-constructible:

| `a` | reached via | `Γ` product obtained | status in `Gamma.lean` |
|---|---|---|---|
| ½ | `K(1/√2)` (H2) | `Γ(3/4)²` | have (lemniscatic) |
| ¼ | V7 + H2 | `Γ(5/8)Γ(7/8)` | have (denominator 8) |
| ⅓ | cubic signature (R2) | `Γ(2/3)Γ(5/6)` | have (denominator 6) |
| ⅙ | sextic signature (R2) | `Γ(7/12)Γ(11/12)` | have (denominator 12) |
| ⅕, ⅛, … | **unknown** | e.g. `Γ(3/5)Γ(9/10)` | **not reached** |

The first four rows re-derive denominators 4, 6, 8 and 12 by a single uniform mechanism,
where `Gamma.lean` currently uses a separate substitution for each. That is a strong
consistency check. The last row is the insight: it says exactly **which ₂F₁ value a new `Γ`
denominator would need**, namely `₂F₁(a,1−a;1;½)` for `a ∉ {½,⅓,¼,⅙}`. The elliptic
machinery cannot supply it (those four are precisely the signatures reducible to `K`).

**R1 has now closed this.** The four reachable signatures are exactly the Schwarz *algebraic*
cases, and the H6 arc-length family is `₂F₁(−½, 1/m; 1+1/m; z)`, whose parameter identity
`c = a + b + 3/2` fails every standard quadratic transformation. So H6 cannot reach an
`a ∉ {½,⅓,¼,⅙}`, and a new row needs a mechanism outside the Schwarz list. The runner-up target
is recorded for the future: `₂F₁(⅕,⅘;1;½) = √π/(Γ(3/5)Γ(9/10)) = 1.1137746646208464520265…`
(50 digits), new at denominators 5 and 10.

**B2: the Euler integral turns ₂F₁ families into definite integrals (new, moderate).**
`₂F₁(a,b;c;z) = Γ(c)/(Γ(b)Γ(c−b)) ∫₀¹ t^{b−1}(1−t)^{c−b−1}(1−zt)^{−a} dt` for `c > b > 0`.
Whenever the ₂F₁ value and the Beta prefactor are both P-constructible, so is the integral.
Concrete target (L7b, after L7a proves the Euler integral), via V9 and H3:

> `∫₀^{π/2} sin^{2j}θ cos^{2l}θ (1 − c sin²θ)^{r/2} dθ` is P-constructible for all `j, l ∈ ℕ`,
> odd `r ∈ ℤ`, and P-constructible `c ∈ (−1, 1)`.

The prefactor is `π × rational`. Integration by parts would also reach this; the point is
that H3 gives it uniformly and the same template then applies to the H6 families (moments
`∫₀¹ tᵖ(1−t)^q(1 + Ct^m)^{±½}`).

**B3: Clausen turns ₂F₁² into ₃F₂ (new).** V6 gives
`₃F₂(½,½,½;1,1;x) = Σ C(2n,n)³ (x/64)ⁿ = (2K(z)/π)²` with `z = (1 − √(1−x))/2`, so

> `Σₙ C(2n,n)³ (x/64)ⁿ` is P-constructible for every P-constructible `x ∈ [0, 1)`.

The same holds for the other three Ramanujan `₃F₂`s once H5 is done. Since Mathlib has no
`₃F₂`, state it with an explicit `tsum`. This also opens Ramanujan–Sato series: they evaluate
to `1/π`, which is already P-constructible, so they add nothing directly. But their
*generating functions* at non-singular arguments are exactly these `₃F₂` values, and those
are new.

**B4: named functions that are ₂F₁ (new, cheap once H2/H5 are done).**
- Legendre functions `P_ν(x) = ₂F₁(−ν, ν+1; 1; (1−x)/2)` for `ν ∈ {−½, −⅓, −¼, −⅙} + ℤ` and
  P-constructible `x ∈ (−1, 3)` (V8). The `ν = −½` case is H2 directly.
- Incomplete Beta `B(x; p, q) = (xᵖ/p) ₂F₁(p, 1−q; p+1; x)` on the H6 classes.
- AGM: `agm(a, b)` is P-constructible for P-constructible `a, b > 0`, since
  `agm(1, √(1−k²)) = π/(2K(k))` and `agm` is homogeneous. Mathlib has no AGM, so this needs a
  definition (the limit of the iteration) plus Gauss's theorem. **This does not depend on
  B7.** The classical proof is Landen's substitution inside the integral: show
  `I(a,b) = ∫₀^{π/2} dθ/√(a²cos²θ + b²sin²θ)` is unchanged by one AGM step, then
  `I(a,a) = π/(2a)`. No quadratic transformation of ₂F₁ appears, so L6c can proceed while L6a
  is blocked. Worth doing: `agm` is a well-known constant generator (Gauss's constant, and `π`
  via Brent–Salamin).

**B5: lattice Green's functions and Pólya's constant (new as a statement; the identity is
speculative to formalize).** V11 writes Pólya's `u(3)` through `Γ(n/24)`, and independently
through `K(k₆)` with `k₆` a degree-4 algebraic number. *Either* form is already P-constructible
with no new work (`Gamma_intCast_div_twentyfour_Pconstructible`; or
`ellipticF_Pconstructible` at the P-constructible parameter `k₆²`). So, **conditional on the
Watson/Glasser–Zucker evaluation**, the return probability `p(3) = 0.3405373…` of 3-D random
walk is P-constructible, with two independent reasons that must agree. The analogous
body-centred cubic `Γ(1/4)⁴/(4π³)` and face-centred cubic `9Γ(1/3)⁶/(2^{14/3}π⁴)` Watson
integrals are classical and fall the same way; R3 checked them (the fcc return number is
`9Γ(1/3)⁶/(2^{14/3}π⁴)`, three times the older `3Γ(1/3)⁶/(2^{14/3}π⁴)`, which is Watson's
`I₂` itself, not the return number). What is realistic in Lean is to state the closed forms and prove them
P-constructible, with the section comment naming the classical identity. Formalizing the
Watson integral itself, `(1/π³)∭ dx dy dz/(3 − cos x − cos y − cos z)`, is R3's question. It
goes through Bessel/`₂F₁` products and is probably a programme of its own.

**B6: hyperelliptic periods — CLOSED NEGATIVELY by R1.** The hope was that H6's curves
`y² = 1 + x^m` would deliver their complete periods `(1/m) B(p/m, ½ − p/m)`, which at `m = 10`
involve `Γ(1/10), Γ(1/5), Γ(3/10), Γ(2/5)` — genuinely outside the denominator-24 family. R1
shows why no drawable construction closes them, and the reason is more basic than the
`x = 0` restriction this plan worried about:

> An arc length is a **second-kind** integral `∫√(1 + x^m) dx`. The Beta-value periods are
> **first-kind** integrals `∫dx/√(1 + x^m)`. They are different periods of the same curve, so
> reaching `x = 0`, or any other repair to the endpoints, cannot convert one into the other.

R1 adds: for integer `b` the origin is *already* reachable through `poly_graph`, so H6 loses
nothing there; for non-integer `b` no drawable curve shares the density `√(1 + Cx^m)` (offset
changes the density, a rectangle edge is straight, a Bézier's density is a quartic); the
second-kind integral diverges at `x = ∞`; and the genus-1 integration-by-parts trick that
`Basic.lean` uses for `ellipticF` has no genus-2 analogue. **Do not re-attempt this.**

What survives is a precise statement of the missing primitive, which is the most valuable
open question left in the programme: *a primitive laying a first-kind hyperelliptic
differential along a bounded arc* — a drawable `γ` with `speed γ(t) = 1/√(1 + x(t)^m)`, or any
closed drawable curve of genus ≥ 2. With one, `(1/10) B(1/10, 2/5) = Γ(1/10)Γ(2/5)/(10√π) =
1.19057982162037096532…` would follow, and with it a `Γ` product at denominators 5 and 10.

**B7: transformations move the argument (enabling).** Pfaff/Euler
(`z ↦ z/(z−1)`), quadratic (V6, and `z ↦ 4√z/(1+√z)²`) and the Goursat cubic/sextic maps all
have P-constructible algebraic coefficients, so they transport P-constructibility along `z`.
Respect the junk-value trap (§3): every transformed argument must stay in `(−1, 1)`.

L6a tried the power-series route (both sides satisfy the same coefficient recurrence) and
**stalled**: with no `PowerSeries` evaluation API the formal identity does not transfer to
real arguments, and the Fubini bound `4|z|(1+|z|) < 1` covers only `|z| < 0.207`, leaving an
analytic continuation to do. The retry should instead substitute inside `hyp_eq_integral`
(L7a, landed), which is the classical proof and stays with real functions throughout. Only
Clausen (L6b) still depends on the outcome; AGM no longer does (B4).

**Non-goals.** Algebraic ₂F₁ (Schwarz's list): its values are algebraic numbers of degree far
above 9, and ₂F₁ adds no construction for them. Confluent/Bessel functions: those are limits,
not values. Any impossibility result: the project has no tools for proving a number is not
P-constructible, so state positive families only.

## 6. Suggested order and milestones

Waves 0 and 1 are done (§Status). What is left, in order:

**Wave 2, as re-scoped after the research (four agents, all startable now):**

- **L3b `EllipticClass.lean` — highest value, and unblocked.** With L2 and L3 both landed,
  show by induction on the shifts that every `hyp (½+i) (½+j) (1+k)` is a rational-function
  combination of `hyp ½ ½ 1` and `hyp (−½) ½ 1`, hence P-constructible. This is what unlocks
  L5b and L7b, and it is the ₂F₁ analogue of `Gamma_add_intCast_Pconstructible`.
- **L6c `AGM.lean` — now independent of L6a.** Take the Landen-substitution route in B4, not
  the quadratic transformation.
- **L9 `Signatures.lean` (extend) — switch to R2's parametric forms** for the cubic and sextic
  signatures (H5). Leave `V7` conditional; the quartic is the hard one.
- **L5b `GraphsClass.lean`** — the contiguous classes of the H6 families, after L3b.

**Wave 2 retries, lower priority:** L6a through the Euler integral (B7), and then L6b
(Clausen), which is the only remaining consumer of the quadratic transformation.

**Wave 3** (L7b, L10). The trigonometric moments, and B1's rows as consistency theorems
against `Gamma.lean` — `a = ½, ¼` from L2 and the conditional `V7`, and `a = ⅓, ⅙` once L9's
parametric extension lands.

**Wave 4** (L11). The umbrella module, plus a final `lake build Pptc.Hypergeometric`.

**A follow-up worth scheduling:** lift the `0 < a`, `0 < b`, `b < c` hypotheses of
`hyp_one_eq_Gamma` by shifting parameters with L3's contiguous relations, which would widen
the denominator-24 family (L4) to the negative-parameter cases.

On concurrency: `CLAUDE.md` caps concurrent LSP elaborations at 2, so four simultaneous Lean
agents will queue. The layout still pays off, because agents think and search in parallel
while they wait.

## 7. What counts as success

- **Programme success:** H2 + H3 + H4 in `main`, sorry-free — **met**, pending a commit — plus
  at least two bridge-back theorems from §5 that state a number or family not previously
  P-constructible. L5a's arc-length family is one; B4-AGM is the nearest second, with B3
  behind L6a.
- **Breakthrough (restated after R1).** The `₂F₁(a, 1−a; 1; ½)` route for a new `a` is closed
  to every mechanism in this plan, so the breakthrough is now the *first-kind differential
  gap* of B6: a drawable curve, in the constructor language of `Defs.lean`, whose arc length
  realises `∫ dx/√(1 + x^m)` over a bounded arc, or any closed drawable curve of genus ≥ 2.
  That would give `Γ(1/10)Γ(2/5)` and with it denominators 5 and 10. R1 §4 has the numeric
  evidence and the exact shape of what is missing.
- **Useful negative:** a clean statement of which ₂F₁ families *cannot* come from the six base
  curves' arc lengths by the mechanisms here, with its assumptions and loopholes listed. As in
  the Jacobi programme, do not claim non-P-constructibility outright.
