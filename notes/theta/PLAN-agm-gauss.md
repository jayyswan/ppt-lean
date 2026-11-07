# Plan: Gauss's AGM theorem, and `agm` is P-constructible

Written 2026-11-07. **Not started.** First step of the theta programme (see "Afterwards").
Earlier sketch: `notes/archive/PLAN-hypergeometric-00-overview.md`, item B4. That sketch moved the
AGM out of the hypergeometric programme as "`Pptc/AGM.lean`", but the file was never written.

## Targets

New file **`Pptc/AGM.lean`**. It imports `Pptc.Basic` and
`Mathlib.Analysis.SpecialFunctions.ArithmeticGeometricMean`, plus the specific
change-of-variables modules (`Mathlib.MeasureTheory.Function.JacobianOneDim`).

```lean
-- Gauss's theorem, in this repo's parameter convention `c = k²`.
theorem ellipticF_pi_div_two_eq_pi_div_agm {c : ℝ} (hc : c < 1) :
    ellipticF c (Real.pi / 2) =
      Real.pi / (2 * (NNReal.agm 1 ⟨Real.sqrt (1 - c), Real.sqrt_nonneg _⟩ : ℝ))

-- The named operation.
@[pconstructible_cond]  -- or @[pconstructible] if stated with junk values; see §5
theorem agm_Pconstructible {x y : NNReal} (hx : PConstructible (x : ℝ))
    (hy : PConstructible (y : ℝ)) : PConstructible (NNReal.agm x y : ℝ)

-- Named constant: Gauss's constant G = 1/agm(1, √2) = 0.8346268…
theorem gaussConstant_Pconstructible :
    PConstructible ((NNReal.agm 1 (NNReal.sqrt 2) : ℝ)⁻¹)
```

**Why it is not trivial.** Every AGM iterate is P-constructible, but `agm` is their limit, and
the class has no limit constructor. Gauss's theorem turns the limit into one complete integral,
and `ellipticF_pi_div_two_Pconstructible` (`Basic.lean`) already proves that integral
P-constructible.

**Prior art.**
- Not in Mathlib (#34397, "integral representation of the AGM", was closed unmerged
  2026-11-06), and not in Tau Ceti. The roadmap draft
  `C:\dev\TauCeti\roadmap-draft\EllipticIntegrals\Suggested.lean` M4.2/M4.4 states it with `sorry`.
- B. Braams' `lean-codes` proves it, as `Carlson.TwoVariable.carlsonRK_sq_eq_inv_agm`
  (`R_K(x², y²) = 1/agm x y`) together with `Real.compEllIntKk_eq` (`K(k) = π/2·R_K(1−k², 1)`).
  It is on Lean 4.36 and rests on Carlson's R-function, so we cannot import or cheaply port it.
  Use it only as a reference for statement shapes.

## 1. Mathematics (Newman's proof)

For `a, b > 0` put

    I(a, b) = ∫₀^{π/2} dθ / √(a² cos²θ + b² sin²θ),
    J(a, b) = ∫₀^∞  dt / √((t² + a²)(t² + b²)).

1. **Bridge to `F`.** `1·cos²θ + (1 − c) sin²θ = 1 − c sin²θ`, so
   `ellipticF c (π/2) = I(1, √(1 − c))` for `c < 1`. This is pointwise equality of integrands,
   with no substitution.
2. **`I = J`.** Substitute `t = b tan θ`, which maps `(0, π/2)` onto `(0, ∞)` increasingly:
   `dt = b sec²θ dθ`, `t² + b² = b² sec²θ`, `t² + a² = (a² cos²θ + b² sin²θ)/cos²θ`. The
   integrands match.
3. **Newman's invariance.** With `m = (a + b)/2` and `g = √(ab)`, the map
   `x ↦ t = (x − ab/x)/2` is a strictly increasing bijection `(0, ∞) → ℝ`, and

       t² + g² = (x + ab/x)²/4,
       t² + m² = (x² + a²)(x² + b²)/(4x²),
       dt = (x + ab/x)/(2x) dx,

   so `dt/√((t² + m²)(t² + g²)) = 2 dx/√((x² + a²)(x² + b²))`. Hence
   `∫_ℝ (m, g) = 2 J(a, b)`. The integrand in `t` is even, so `∫_ℝ = 2 J(m, g)`, and
   **`J(m, g) = J(a, b)`**. Through step 2 this is `I(√(ab), (a + b)/2) = I(a, b)`, with
   `I` symmetric (`θ ↦ π/2 − θ`) or `J` symmetric by inspection.
4. **Iterate.** Mathlib's `NNReal.agmSequences x y n` is the pair `(gₙ₊₁, aₙ₊₁)` (index 0 is
   already one step: `(√(xy), (x + y)/2)`). Induction gives
   `I(x, y) = I(gₙ, aₙ)` for all `n`.
5. **Squeeze, so no continuity of `I` is needed.** For `0 < p ≤ q`, the integrand of
   `I(p, q)` lies between `1/q` and `1/p`, so `π/(2q) ≤ I(p, q) ≤ π/(2p)`. With `gₙ ≤ aₙ`
   (`agmSequences_fst_le_snd`) and both tending to `agm x y` (`tendsto_agmSequences_fst_agm`,
   `tendsto_agmSequences_snd_agm`), and `agm x y > 0` (`agm_pos`), the constant sequence
   `I(x, y)` is squeezed to `π/(2 agm x y)`.
6. **Gauss.** `ellipticF c (π/2) = I(1, √(1 − c)) = π/(2 agm 1 √(1 − c))`.
7. **P-constructibility.**
   - Use `agm_mul_distrib` and `agm_comm` to reduce to `agm 1 r`, with
     `r = min/max ratio ≤ 1`: `agm x y = x · agm 1 (y/x)` for `x > 0`.
   - Then `agm 1 r = π/(2 ellipticF (1 − r²) (π/2))`, with `1 − r² < 1` for `r > 0`.
   - `x = 0` or `y = 0` gives `agm = 0` (`agm_zero_left`/`agm_zero_right`).
   - `π`, `sqrt` and division are all in the tactic's lemma set.

Numerics: the archived B4 note checked the equivalent form
`agm x y = π/4·(x + y)/ellipticF(((x − y)/(x + y))², π/2)` to 30+ digits against
`ArithmeticGeometricMean[1, 3/10]`. The exact statement of §6,
`EllipticK[c] == Pi/(2 ArithmeticGeometricMean[1, Sqrt[1-c]])`, was checked in Wolfram on
2026-11-07 at `c = 3/10` and `c = −2` (zero to about 89 digits); `G = 0.83462684167407318628…`.

## 2. Declarations, in order (one file, about 300–450 lines)

| # | Declaration | Notes |
|---|---|---|
| 1 | `agmI a b`, `agmJ a b` | definitions; `agmJ` as `∫ t in Set.Ioi 0, …` |
| 2 | `ellipticF_pi_div_two_eq_agmI` | step 1, `intervalIntegral.integral_congr` + `ring_nf` under `sqrt` |
| 3 | `agmI_bounds` | step 5 bounds, `intervalIntegral.integral_mono_on`, constants integrate to `π/2·const` |
| 4 | `agmI_eq_agmJ` | step 2; the main analytic risk (below) |
| 5 | `agmJ_newman` | step 3; the second risk |
| 6 | `agmI_agmSequences` | step 4, induction on `n` using `agmSequences_succ`/`_zero` |
| 7 | `agmI_eq_pi_div_two_agm` | step 5, `tendsto_nhds_unique` with `tendsto_of_tendsto_of_tendsto_of_le_of_le` |
| 8 | `ellipticF_pi_div_two_eq_pi_div_agm` | step 6 |
| 9 | `agm_Pconstructible`, `gaussConstant_Pconstructible` | step 7 |
| 10 | `example`s | `agm x x = x` consistency; the Wolfram value of `G` to a few digits is not checkable in Lean, so skip it |

## 3. The two change-of-variables steps (where the time goes)

Use **`MeasureTheory.integral_image_eq_integral_abs_deriv_smul`**
(`Mathlib/MeasureTheory/Function/JacobianOneDim.lean:66`). It needs a measurable set `s`, a
`HasDerivWithinAt f (f' x) s x` for `x ∈ s`, and `InjOn f s`. It equates `∫ y in f '' s, g y`
with `∫ x in s, |f' x| • g (f x)`, **with no integrability hypothesis**, which is what makes
the improper integrals painless.

- Step 2: `s = Ioo 0 (π/2)`, `f θ = b tan θ`, image `Ioi 0` (prove `f '' s = Ioi 0`; surjectivity
  from `arctan`). Convert `∫ θ in (0)..(π/2)` to `∫ θ in Ioo 0 (π/2)`
  (`intervalIntegral.integral_of_le`, `integral_Ioc_eq_integral_Ioo`).
- Step 3: `s = Ioi 0`, `f x = (x − ab/x)/2`, image `univ` (surjectivity: solve the quadratic
  `x² − 2tx − ab = 0`, positive root `t + √(t² + ab)`). Derivative `(1 + ab/x²)/2 > 0`, which
  gives injectivity via `StrictMonoOn`.
- Evenness: `∫ t, h t = 2 ∫ t in Ioi 0, h t` for even `h`. Look for
  `integral_comp_neg_Ioi` / `integral_Iic_eq…`, or split `univ = Iic 0 ∪ Ioi 0` and use
  `integral_comp_neg`. **Integrability is needed here** (for `integral_union`). The integrand
  is bounded by `1/(t² + min²)`, which is integrable (`integrable_inv_one_add_sq` scaled).
  So prove `Integrable` for `J`'s integrand once and reuse it.

Fallback if step 3 resists: Gauss's own substitution in trigonometric form,
`sin θ = 2a sin φ/((a + b) + (a − b) sin²φ)` on `[0, π/2]`. That is a finite interval
(`intervalIntegral.integral_comp_mul_deriv`), but its derivative algebra is heavier. Try
Newman first.

**Not a route:** `Pptc/Hypergeometric/Quadratic.lean`'s `hyp_quadratic` is the Goursat
transformation `z ↦ 4z(1 − z)`, not Landen's `k ↦ (1 − k′)/(1 + k′)`, so it does not give the
AGM step.

## 4. Workflow

- Develop with `lean_diagnostic_messages`, `lean_goal` and `lean_multi_attempt` on
  `Pptc/AGM.lean`. Confirm the Mathlib names above with `lean_local_search`/`lean_hover_info`
  before use (AGM lemma names verified 2026-11-07 against the vendored Mathlib).
- Final: `lake env lean Pptc/AGM.lean`; `lean_verify` on `ellipticF_pi_div_two_eq_pi_div_agm`
  and `agm_Pconstructible` (only `propext`, `Classical.choice`, `Quot.sound`); add the module to
  `Pptc.lean` if the umbrella file lists modules. No whole-project `lake build`.
- Split across agents along the table: steps 4 and 5 are independent and are the hard part.
  Each could be one `@lean-prover` call in its own scratch file, then merged. Logs go in
  `notes/theta/HANDOFF-agm-<step>.md`.

## 5. Small decisions to make when implementing

- **Tagging.** `agm_Pconstructible` needs no side condition (`agm` of nonnegative reals is
  total), so tag it `@[pconstructible]`. Check `Pptc/Tactic.lean` for whether `NNReal`-coerced
  goals are matched.
- **Tau Ceti shape.** Optionally also state `legendreK`-style
  `K(k) = π/(2·agm 1 √(1 − k²))` in the modulus `k`. This is only a restatement, useful if the
  file is later offered to the Tau Ceti EllipticIntegrals roadmap (M4.4).

## Afterwards (separate plans, not this one)

1. Theta constants: `θ₃(q)² = 2K/π`, `θ₄(q)² = 2k′K/π`, `θ₂(q)² = 2kK/π` at the nome
   `q = exp(−πK′/K)`, via the duplication identities `θ₃(q)² + θ₄(q)² = 2θ₃(q²)²`,
   `θ₃(q)θ₄(q) = θ₄(q²)²` (so `agm(θ₃², θ₄²) = 1`), this theorem, and Mathlib's
   `jacobiTheta_S_smul`. Identities verified in Wolfram 2026-11-07 (about 79 digits).
2. Theta functions at `z = πF(φ)/(2K)` via Jacobi's third-kind formula: much larger, deferred.
