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

## Status — 2026-09-16

**Waves 0 and 1 are done and wave 2 inbound is complete.** Every file compiles, no
`sorry`, no axioms beyond `propext`, `Classical.choice`, `Quot.sound`: `Basic` (L1, including the
`arcsin` case, which needed an arcsine power series built from scratch — Mathlib has none),
`Elliptic` (L2), `Contiguous` (L3: the derivative plus five contiguous relations), `Gauss` (L4,
extended), `Graphs` (L5a, extended to affine images of `y = xⁿ`), `Euler` (L7a), `Polya` (L8),
and the wave-2 files `Quadratic` (L6a), `EllipticClass` (L3b), `Signatures` (L9), `Clausen`
(L6b) and `GraphsClass` (L5b, both the level-`c₀` class and the `c`-advance).

- **V7 (the quartic Goursat transformation): DONE (new).** The formerly-assumed quartic
  transformation is proved, so the L9 quartic signature is unconditional. New files:
  `Goursat.lean`, `SqrtSeries.lean`, `Heun.lean`, `HeunMobius.lean`, `V7.lean`, `V7Eval.lean`,
  `V7MobiusEval.lean`, `V7Real.lean`. Detail in the L9 bullet below.
- **L6a `Quadratic.lean`: DONE.** `hyp_quadratic` now proves `V6`,
  `₂F₁(½,½;1;z) = ₂F₁(¼,¼;1;4z(1−z))`, unconditionally on `0 ≤ z < ½`. The blocker (no
  `PowerSeries.sum`, no `IsLinearTopology ℝ ℝ`) was routed around: the formal power-series
  identity is transferred to `HasSum` level on the small disc `4|z|(1+|z|) < 1` by a Fubini
  re-summation, then continued analytically along the Cassini interval
  `((1−√2)/2, ½)`. The Euler-integral change of variable was tried first and dropped (Landen
  weights are incompatible).
- **L6b `Clausen.lean`: DONE — flagship outbound.** `clausen_tsum_Pconstructible` is
  unconditional: `Σₙ C(2n,n)³ (x/64)ⁿ` is P-constructible for P-constructible `x ∈ [0,1)`.
  The proof reads the recurrence `8(n+1)³ g_{n+1} = (2n+1)³ g_n` off the formal third-order ODE
  satisfied by `hypSeries (1/4) (1/4) 1 ^ 2`, matches it against `dₙ = C(2n,n)³/64ⁿ`, and
  transfers to reals through the (absolutely convergent) Cauchy product of two `hasSum_hyp`
  series. As a by-product, `hyp_one_fourth_one_Pconstructible` makes the **fourth Ramanujan
  signature** `₂F₁(¼,¼;1;·)` P-constructible for `0 ≤ x < 1` — the last piece of H5 that does
  not need `V7`.
- **L9 `Signatures.lean`: quartic DONE, cubic/sextic conditional.** The quartic `V7` is now
  **proved** (see below) and `hyp_quarter_three_quarter_Pconstructible` is unconditional and
  `@[pconstructible_cond]`. R2's **cubic** `(⅓,⅔;1;·)` and **sextic** `(⅙,⅚;1;·)` reductions
  are still landed parametrically in `p` (the classical transformation is the explicit
  hypothesis; the PConstructible reduction is unconditional — those two theorems are
  deliberately not tagged), together with the `z = ½` special values `(★)`, `(★★)`, the
  domain/positivity lemmas `α,β,γ,x,ξ`, and their PConstructible closure lemmas.
- **V7 `₂F₁(¼,¾;1;z) = (1+√z)^(−½)₂F₁(½,½;1;2√z/(1+√z))`: DONE.** Proved in
  `V7Real.lean` (headline `hyp_quarter_three_quarter`), on the framework
  `Goursat.lean` (general formal hypergeometric equation `hypSeries_ode`),
  `SqrtSeries.lean` (the formal `(1+X)^(−½)`), `Heun.lean`, `HeunMobius.lean`, `V7.lean`
  (formal identity `phiSeries_eq_rSeries`), `V7Eval.lean`, `V7MobiusEval.lean` (real
  evaluations). Route: `w = √z` turns both hypergeometric equations into one Heun equation
  `X(1−X²)F''+(1−3X²)F'−(3/4)XF=0`, whose constant term fixes the solution; a Cauchy product
  plus analytic continuation on `(0,1)` transfers the coefficient identity to `ℝ`. This is
  the ₂F₁ analogue of the L6a quadratic transformation, and it also supplies the previously
  missing general hypergeometric ODE, which the cubic/sextic work can reuse.
- **L3b `EllipticClass.lean`: DONE.** The two Legendre relations for `deriv hyp(±½,½;1)` are
  proved and made `PConstructible`, the general shifts `hyp_shift_a`, `hyp_shift_b`,
  `hyp_shift_c_up`, `hyp_shift_a_down` (DLMF 15.5.14, 15.5.21 solved for `c+1`, 15.5.20a) are in,
  and `hyp_three_term_a`/`hyp_three_term_b` eliminate `₂F₁′` between the up- and down-shifts to
  give a derivative-free second-order recurrence in each numerator parameter. The class theorem
  `hyp_elliptic_class_Pconstructible` proves the whole `(½+ℤ, ½+ℤ, 1+ℕ)` class P-constructible
  for P-constructible `z ∉ {0,1}`, `|z| < 1`: level `c = 1` by strong induction on
  `|i| + |j|` with nine explicit corner seeds, then `c ↦ c+1` by `hyp_shift_c_up` with `₂F₁′`
  rewritten at the same level via 15.5.20a. It is the ₂F₁ analogue of
  `Gamma_add_intCast_Pconstructible`.
- **L4 `Gauss.lean`: DONE.** `hyp_one_eq_Gamma'` now proves Gauss's summation
  `₂F₁(a,b;c;1) = Γ(c)Γ(c−a−b)/(Γ(c−a)Γ(c−b))` with only `c − a − b > 0` and the three
  non-pole conditions `c, c−a, c−b ∉ −ℕ` — the positivity hypotheses `0<a`, `0<b`, `b<c` of the
  original integral proof are gone. The machinery: `summable_hypCoeff_one`,
  `tendsto_hyp_nhdsWithin_one`, `tendsto_nat_mul_hypCoeff_one`, `tendsto_one_sub_mul_deriv_hyp`,
  the **recurrence at `z = 1`** `hyp_one_recurrence`
  (`₂F₁(a,b;c+1;1) = c(c−a−b)/((c−a)(c−b)) · ₂F₁(a,b;c;1)`), the diagonal recurrences
  `hyp_one_diag_a`/`hyp_one_diag_b` (`₂F₁(a+1,b;c+1;1) = c/(c−b)·₂F₁(a,b;c;1)`, and `a↔b`),
  the invariance `hypD_shift_a`/`hypD_shift_b` of `D = ₂F₁(a,b;c;1)/G(c)`, and the induction
  `hypD_shift_a_nat`/`hypD_shift_b_nat` that moves `(a,b,c)` to `(a+N,b+N,c+2N)` (preserving
  `c−a−b`) into the range of the original theorem.
- **L5b `GraphsClass.lean`: DONE.** The missing second seed is by differentiating the V4
  arc-length identity at its upper limit: `deriv_graphFamily_Pconstructible`
  (`deriv_graphFamily_H6_Pconstructible` for `n ∈ {2..6}`) makes `₂F₁′(−½,1/m;1+1/m;w)`
  P-constructible whenever the base value is (via `differentiableAt_hyp`). `hyp_shift_b_down`
  (the missing `b`-down shift), `hyp_contiguous_neighbours_Pconstructible` /
  `hyp_graphFamily_neighbours_Pconstructible` give the immediate contiguous neighbours, and
  `hyp_graphFamily_level_zero_Pconstructible` proves the whole `(i,j)` class at
  `c = c₀ = 1+1/m` (`n ≥ 3`; `n = 2` degenerates). The `c`-advance
  `hyp_graphFamily_class_Pconstructible` then inducts on `k`: for `j ≠ k+1` by `hyp_shift_c_up`
  with `₂F₁′` rewritten at the same level by `hyp_shift_a_down`, and for the degenerate
  `j = k+1` (where `c₀ − b₀ = 1`, so `hyp_shift_c_up` fails) by the `b`-recurrence
  `hyp_three_term_b`, non-degenerate there (`c − b + 1 = 2`) and consuming the level-`k+1`
  values `j = k`, `k−1`. The whole class `₂F₁(−½+i, 1/m+j; 1+1/m+k; −b²Xᵐ)` is P-constructible
  for `n ∈ {3,…,6}`.

**Deviations worth knowing.** `hyp_neg_half_arcLength_Pconstructible` (L5a) still needs `n ≤ 6`
(inherited from `poly_graph`) and, for the affine version, an explicit injectivity hypothesis.
The L5b class theorem is now landed (`hyp_graphFamily_class_Pconstructible`).

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
| R4a | 2 | `NOTES-hypergeometric-R4a-bezier.md` | inbound survey: cubic Bézier arc length as ₂F₁? (R4) | none |
| R4b | 2 | `NOTES-hypergeometric-R4b-offset.md` | inbound survey: offset-curve arc length as ₂F₁? (R4) | none |
| R4c | 2 | `NOTES-hypergeometric-R4c-sine-exp.md` | inbound survey: `sine`/`exp_two`/`rectangle` arcs as ₂F₁? (R4) | none |
| L2 | 1 | `Hypergeometric/Elliptic.lean` | `K`, `E` as ₂F₁ (H2) | L1 |
| L3 | 1 | `Hypergeometric/Contiguous.lean` | derivative + three-term relations, generic (H3) | L1 |
| L4 | 1 | `Hypergeometric/Gauss.lean` | Gauss summation + denominator-24 family (H4) | L1 (`Pptc.Gamma`) |
| L5a | 1 | `Hypergeometric/Graphs.lean` | arc lengths of `y = xⁿ` as ₂F₁ (H6, first part) | L1 |
| L6a | 1 | `Hypergeometric/Quadratic.lean` | quadratic transformation, generic (B7) | L1 |
| L7a | 1 | `Hypergeometric/Euler.lean` | Euler integral representation, generic (B2) | L1 |
| L3b | 2 | `Hypergeometric/EllipticClass.lean` | contiguous class of `(½,½;1)` is PConstructible | L2, L3 |
| L5b | 2 | `Hypergeometric/GraphsClass.lean` | contiguous classes of the H6 families | L3, L5a |
| L6b | 2 | `Hypergeometric/Clausen.lean` | `Σ C(2n,n)³(x/64)ⁿ` PConstructible (B3) | L2, L6a |
| ~~L6c~~ | — | moved out: `Pptc/AGM.lean` | `agm` needs no ₂F₁ at all (B4); not this programme | — |
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

**Most of this section is outbound, and outbound is scheduled second** (§6). These are the
payoffs of the inbound map, not a parallel track: every family added inbound widens what each
mechanism below delivers, so proving them early means proving them twice. Read this section as
the specification of what the programme collects at the end, and as the argument for which
inbound families are worth the most.

**The test for membership.** An outbound item belongs to this programme only if ₂F₁ is *the*
route to it — that is, if there is no obvious path to the same result from the machinery the
repo already has. "A ₂F₁ proof exists" is not enough; `agm` (B4) and Pólya (B5) both have one
and are still not this programme's business, because `Basic.lean` and `Gamma.lean` reach them
directly. §6 moves those two out. Applying the test to the rest:

| item | is ₂F₁ the route? | verdict |
|---|---|---|
| B3 Clausen `₃F₂` | yes — Clausen's formula is irreducibly hypergeometric | **keep: flagship outbound** |
| B4 Legendre `P_ν`, `ν ∈ {−⅓,−¼,−⅙}+ℤ` | yes — needs the signature reductions | **keep** |
| B4 incomplete Beta on the H6 classes | yes — the graph families arrive as ₂F₁ | **keep** |
| B4 Legendre `P_{−½}` | no — it is `(2/π)K` directly | drop to a remark |
| B2 moment integrals | no — integration by parts reaches them from `ellipticE`/`ellipticF` | low value; state only if free |
| B1 `Γ` rows for `a ∈ {½,⅓,¼,⅙}` | no — `Gamma.lean` already has every value | cross-check only, not a result |
| B1 frontier analysis (`which a is new`) | yes — the question only exists in ₂F₁ terms | **keep as analysis** |
| B4 `agm`, B5 Pólya | no | out of the programme (§6) |

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
  `agm(1, √(1−k²)) = π/(2K(k))` and `agm` is homogeneous. **Why this is not trivial:** every
  AGM iterate is P-constructible (arithmetic and `sqrt_Pconstructible`), but `agm` is their
  *limit*, and the class has no limit constructor — nor could it, since every real is a limit
  of rationals. Gauss's formula is exactly what turns the limit into a finite expression. The
  same applies to B3's `tsum`: an infinite object enters only through a closed form or through
  `arc_length`. Mathlib has no AGM, so this needs a
  definition (the limit of the iteration) plus Gauss's theorem. **This does not depend on
  B7.** The classical proof is Landen's substitution inside the integral: show
  `I(a,b) = ∫₀^{π/2} dθ/√(a²cos²θ + b²sin²θ)` is unchanged by one AGM step, then
  `I(a,a) = π/(2a)`. No quadratic transformation of ₂F₁ appears, so L6c can proceed while L6a
  is blocked. The target identity, in this repo's convention `c = k²` (Wikipedia states `K` in
  the modulus, so the arguments differ by a square), is

  ```
  agm x y = π / 4 * (x + y) / ellipticF (((x - y) / (x + y)) ^ 2) (π / 2),
  ```

  with the equivalent forms `agm x y = (π/2)·I(x,y)⁻¹` and
  `agm x y = π (∫₀^∞ dt/√(t(t+x²)(t+y²)))⁻¹`; all three checked to 30+ digits against
  `ArithmeticGeometricMean[1, 3/10]`. For `x, y > 0` the parameter `((x−y)/(x+y))² < 1` is
  automatic, so the P-constructibility corollary is about five lines once the identity is in
  place. **No ₂F₁ occurs anywhere in this**, so it is not a result of this programme: §6 moves
  it out to `Pptc/AGM.lean`, to be judged on its own merits. Worth doing: `agm` is a well-known constant generator (Gauss's constant, and `π`
  via Brent–Salamin).

**B5: lattice Green's functions and Pólya's constant (new as a statement; the identity is
speculative to formalize; uses no ₂F₁, so not a result of this programme — see §6).** V11 writes Pólya's `u(3)` through `Γ(n/24)`, and independently
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

**Inbound before outbound.** A task is **inbound** if it puts new ₂F₁ values into
`PConstructible`, and **outbound** if it spends ₂F₁ values on something else. The programme
runs every inbound task first, and parks the outbound ones until the inbound map is as
complete as it can be made. The reason is that the outbound theorems are corollaries of
whatever the inbound map turns out to be: each new family reached inbound multiplies what the
outbound mechanisms of §5 deliver, whereas an outbound theorem proved early has to be revisited
every time the map grows. So `agm` — a well-formed result, and nearly free once its identity is
in place — waits, because it yields no ₂F₁ value.

**Wave 2, inbound only — DONE (L3b, L9, L6a and L5b all landed; the L4b follow-up too):**

- **L3b `EllipticClass.lean` — highest value, DONE.** With L2 and L3 both landed, show by induction
  on the shifts that every `hyp (½+i) (½+j) (1+k)` is a rational-function combination of
  `hyp ½ ½ 1` and `hyp (−½) ½ 1`, hence P-constructible. It is the ₂F₁ analogue of
  `Gamma_add_intCast_Pconstructible`, and it multiplies every inbound family that follows.
  *Progress:* the Legendre relations and the general shifts `hyp_shift_a`, `hyp_shift_b`,
  `hyp_shift_c_up`, `hyp_shift_a_down` are landed in `EllipticClass.lean`, as are
  `deriv_half_half_one_Pconstructible` / `deriv_neg_half_half_one_Pconstructible`; the class
  theorem `hyp_elliptic_class_Pconstructible` is landed. Route taken: for fixed `(j,k)` the sequence
  `i ↦ ₂F₁(½+i, ½+j; 1+k; z)` satisfies a second-order linear recurrence over `ℚ(z)` (from
  `hyp_shift_a` / `hyp_shift_a_down`, with `₂F₁′` eliminated via 15.5.20a), so the level
  `c = 1+k` is generated by two consecutive `i`-seeds; then advance `k` with `hyp_shift_c_up`,
  whose `₂F₁′` is itself expressible at the *same* level by 15.5.20a. `hyp_shift_b` and its
  `b`-down analogue give the `j`-direction.
- **L9 `Signatures.lean` (extend) — DONE (conditional).** R2's parametric cubic and sextic
  reductions are landed, with the `z = ½` special values; `V7` (quartic) stays conditional.
- **L6a `Quadratic.lean` retry — DONE.** `hyp_quadratic` proves `V6` unconditionally on
  `0 ≤ z < ½`; it is what reaches `₂F₁(¼,¼;1;·)`, the fourth signature.
- **L5b `GraphsClass.lean` — DONE.** The whole class `₂F₁(−½+i, 1/m+j; 1+1/m+k; −b²Xᵐ)`
  (`hyp_graphFamily_class_Pconstructible`), both the level-`c₀` class and the `c`-advance.
- **Follow-up, inbound — DONE (L4b).** `hyp_one_eq_Gamma'` lifts `0 < a`, `0 < b`, `b < c` in
  `hyp_one_eq_Gamma` using contiguous relations, widening the denominator-24 family at `z = 1`.

**Parked, outbound**, in the order the membership test of §5 ranks them:

1. **L6b (Clausen `₃F₂`)** — the flagship. `Σ C(2n,n)³(x/64)ⁿ` has no route from the repo's
   existing machinery; Clausen's formula is irreducibly hypergeometric.
2. **B4's Legendre functions at `ν ∈ {−⅓,−¼,−⅙}+ℤ`, and incomplete Beta on the H6 classes** —
   likewise only reachable once the corresponding inbound families exist.
3. **L7b (moment integrals)** — low value: integration by parts reaches the same integrals
   from `ellipticE`/`ellipticF`. State them only if L3b makes them nearly free.
4. **L10 (B1's `Γ` rows)** — not a result but a cross-check, since `Gamma.lean` already has
   every value involved. What is worth keeping from B1 is the frontier analysis, which is a
   question that only exists in ₂F₁ terms.

None is blocked; they are scheduled after the inbound map, and each grows as it grows.

**Not part of this programme at all.** `agm` (B4) and Pólya (B5) use **no ₂F₁**: `agm` needs
`agm = π/4 · (x+y)/K(...)` with `K` P-constructible since `Basic.lean`, and Pólya needs only
`Gamma.lean` plus `ellipticF_pi_div_two_Pconstructible`. They were swept in here because the
first route this plan imagined for `agm` went through the quadratic transformation; the Landen
route removed the last ₂F₁ from it. So `agm` leaves the plan — if it is wanted, it is a small
standalone task in `Pptc/AGM.lean`, judged on its own merits — and `Polya.lean`, already
landed, belongs beside `Gamma.lean` rather than in this directory. Keep the test in mind when
adding items: *if a result needs no ₂F₁ lemma, it does not belong in this plan, however
attractive it is.*

**Wave 4** (L11). The umbrella module, plus a final `lake build Pptc.Hypergeometric`.

**R4: the inbound survey — DONE, and it closes the map.** The inbound sources exploited are
the ellipse (L2), monomial graphs (L5a) and the `z = 1` Γ route (L4); R4 asked what ₂F₁ family,
if any, each *other* drawable arc length gives. Run in three parts (`NOTES-hypergeometric-R4a/
-b/-c`), every identity checked with the Wolfram kernel:

| curve family | arc length | ₂F₁? |
|---|---|---|
| general cubic Bézier (`ThirdKind.lean`) | genus-1, **incomplete** `F`/`E`/`Π` (Appell `F₁`) | no |
| `offset` of any base curve | `arcLength γ − d·Δφ` (elementary turning excess) | no |
| `sine` restricted arc | incomplete `E` `= sinφ·F₁(½;½,−½;3/2;·)` (Appell `F₁`) | no |
| `exp_two`, `rectangle`, all affine images | elementary (Chebyshev) | no |

The general Bézier reduces to incomplete `F`/`E`/`Π`, and a real Bézier has no simple real root
of `speed²` (a sum of two squares), so it never completes to a `K`/`E`/`Π` ₂F₁; its only ₂F₁
degenerations are `y=Cx³` (the `m=4` graph family) and the `h=0` ellipse limit, both already
landed. An offset's arc length is the base length plus `d` times the (elementary) turning
angle, so `offset` adds no hypergeometric family. The sine's only ₂F₁ values are its complete
sub-arcs `√2·E(½) = (π/√2)₂F₁(−½,½;1;½)`, already in the elliptic class. **The elliptic class,
the graph family and the `z=1` Γ route are the whole inbound map.**

**Follow-up (L4b) — DONE.** `hyp_one_eq_Gamma'` lifts the `0 < a`, `0 < b`, `b < c` hypotheses
of `hyp_one_eq_Gamma` using contiguous relations, widening the denominator-24 family (L4) to
the negative-parameter cases.

On concurrency: `CLAUDE.md` caps concurrent LSP elaborations at 2, so four simultaneous Lean
agents will queue. The layout still pays off, because agents think and search in parallel
while they wait.

## 7. What counts as success

- **Programme success:** H2 + H3 + H4 in `main`, sorry-free — **met** — plus at least two
  bridge-back theorems from §5 that state a number or family not previously P-constructible.
  L5a's arc-length family (now the full `hyp_graphFamily_class_Pconstructible`) is one; B3
  (Clausen, `clausen_tsum_Pconstructible`) is landed, and B4's Legendre functions are the next
  candidate (`agm` left the programme, §6).
- **Breakthrough (restated after R1).** The `₂F₁(a, 1−a; 1; ½)` route for a new `a` is closed
  to every mechanism in this plan, so the breakthrough is now the *first-kind differential
  gap* of B6: a drawable curve, in the constructor language of `Defs.lean`, whose arc length
  realises `∫ dx/√(1 + x^m)` over a bounded arc, or any closed drawable curve of genus ≥ 2.
  That would give `Γ(1/10)Γ(2/5)` and with it denominators 5 and 10. R1 §4 has the numeric
  evidence and the exact shape of what is missing.
- **Useful negative:** a clean statement of which ₂F₁ families *cannot* come from the six base
  curves' arc lengths by the mechanisms here, with its assumptions and loopholes listed. As in
  the Jacobi programme, do not claim non-P-constructibility outright. **R4 (§6) delivers this
  for the whole curve language:** every base curve except the ellipse and the monomial graphs
  has an arc length that is either elementary or an *incomplete* Appell integral, and `offset`
  reduces to the base length plus an elementary turning angle. The only caveat is that a
  coincidence at a special algebraic endpoint is not excluded by these arguments.
