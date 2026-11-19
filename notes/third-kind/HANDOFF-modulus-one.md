# HANDOFF — modulus one (`Pptc/ThirdKindAll/ModulusOne.lean`)

## Target (proved)

```lean
theorem Pconstructible.ellipticPiInc_one_modulus_Pconstructible {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hmod : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - 1 * Real.sin θ ^ 2 ≠ 0)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 1 n Φ)
```

`lake build Pptc.ThirdKindAll.ModulusOne` succeeds; `lean_verify` on the headline
declaration reports axioms `propext, Classical.choice, Quot.sound` (no `sorryAx`), and the
file contains no `sorry`/`admit`/`axiom`/`native_decide`.

## Proof outline

Everything lives in `namespace Pconstructible`, file imports `Pptc.ThirdKindAll.Standard`.

### 1. Principal-branch facts

| name | statement |
| --- | --- |
| `abs_lt_pi_div_two_of_mem_uIcc` | `|Φ| < π/2 → θ ∈ uIcc 0 Φ → |θ| < π/2` |
| `abs_lt_pi_div_two_of_one_sub_sin_sq` | `hmod` (with `1 - 1 * sin²`) forces `|Φ| < π/2` (the points `±π/2` would be poles) |
| `abs_sin_lt_one` | `|θ| < π/2 → |sin θ| < 1` (from `cos > 0` and `sin² + cos² = 1`) |
| `ellipticEIntegrand_one` | `ellipticEIntegrand 1 θ = cos θ` on `|θ| < π/2` |
| `ellipticPiIntegrand_one` | `ellipticPiIntegrand 1 n θ = 1/((1 - n sin²θ) cos θ)` |
| `mul_sin_sq_lt_one_of_ne` | pole-free segment ⇒ `n sin²θ < 1` for **every** `θ ∈ uIcc 0 Φ` (IVT on `[0,θ]` and `[θ,0]`; needed because the `n > 1` antiderivative requires the bound at every interior point, not only at `Φ`) |
| `abs_sqrt_mul_lt_one` | `0 < n → n s² < 1 → |√n s| < 1` |

### 2. Antiderivatives in `s = sin θ`

`1/((1 - n s²)(1 - s²))` is split by partial fractions
`1/((1-n s²)(1-s²)) = 1/(1-n) · (1/(1-s²) - n/(1-n s²))`.

| def | formula | regime |
| --- | --- | --- |
| `modulusOneAntiOne` | `s/(2(1-s²)) + artanh s/2` | `n = 1` (`1/(1-s²)²`) |
| `modulusOneAntiPos` | `(artanh s - √n artanh(√n s))/(1-n)` | `0 < n`, `n ≠ 1` |
| `modulusOneAntiNeg` | `(artanh s + √(-n) arctan(√(-n) s))/(1-n)` | `n ≤ 0` (also uniform at `n = 0`) |

Derivative lemmas `hasDerivAt_modulusOneAntiOne/Pos/Neg` each give
`HasDerivAt (anti) (1/((1 - n s²)(1 - s²))) s` from `|s| < 1` plus (for `Pos`) `n s² < 1`.
They are built from `hasDerivAt_artanh` (in `Pseudo.lean`, since Mathlib lacks it) and
`Real.hasDerivAt_arctan`, plus `field_simp`/`ring`.

### 3. The substitution

`ellipticPiInc_one_modulus_eq` : for any `F` with
`HasDerivAt F (1/((1 - n s²)(1 - s²))) (sin θ)` on the segment and `F 0 = 0`,

```lean
ellipticPiInc 1 n Φ = F (Real.sin Φ)
```

Proof: chain rule `(F ∘ sin)' θ = 1/((1 - n sin²θ)(1 - sin²θ)) · cos θ`, and
`1 - sin²θ = cos²θ` turns this into `ellipticPiIntegrand 1 n θ`; then
`intervalIntegral.integral_eq_sub_of_hasDerivAt` with continuity of the integrand supplied
by `hne` and `ellipticEIntegrand 1 θ = cos θ ≠ 0`.

### 4. Assembly

Case split `n < 1` (`by_cases n ≤ 0` → `Neg` branch, else `Pos` with `n < 1`), `n = 1`
(`One`), `1 < n` (`Pos`, bound from `mul_sin_sq_lt_one_of_ne`). Each branch rewrites with
`ellipticPiInc_one_modulus_eq` and closes with `pconstructible`, feeding it
`artanh_Pconstructible`, `arctan_Pconstructible` and the hypotheses
`PConstructible (sin Φ)` / `PConstructible (√n · sin Φ)`.

Helper `modulusOneAntiPos_Pconstructible` packages the `Pos` case (used twice).

## Notes / remaining issues

* `modulusOneAntiPos_Pconstructible` keeps a `n ≠ 1` argument (named `_hn1`) that is not
  needed for constructibility; it is there to mirror `hasDerivAt_modulusOneAntiPos`. Same
  for the `_hn : 0 < n` of `mul_sin_sq_lt_one_of_ne`, whose IVT argument does not use it.
* The `n > 1` branch genuinely needs the *pointwise* bound `n sin²θ < 1` on the whole
  segment (not just at `Φ`), because the `artanh(√n s)` antiderivative is only
  differentiable on `(-1/√n, 1/√n)`. `mul_sin_sq_lt_one_of_ne` supplies it.
* `field_simp` needs the *ring-normalised* nonzero hypothesis `1 - s^2 * n ≠ 0` (in
  addition to `1 - n * s^2 ≠ 0`) to clear the denominators in the two `artanh` identities;
  both derivative lemmas pass it explicitly.
* No changes were made to any other file.

## Working log

- Read `Standard.lean` (models `gtOne_sin_sq_lt_one`, `ellipticPiInc_Pconstructible_one_all`)
  and `ModulusRecip.lean` (model for substitution + FTC).
- Found `hasDerivAt_artanh` / `artanh_Pconstructible` in `Pseudo.lean`;
  `Real.hasDerivAt_arctan`, `abs_lt_of_sq_lt_sq` in Mathlib. `Real.sin_lt_one` does **not**
  exist in this Mathlib, hence `abs_sin_lt_one` is proved from `cos > 0`.
- Chose the "derivative in θ" route (no `integral_deriv_smul_comp'`, no monotonicity of
  `sin` on the segment) — needs only the pointwise pole bound above.
- All lemmas clean via `lean_diagnostic_messages`; `lake build Pptc.ThirdKindAll.ModulusOne`
  succeeded (29 s); `lean_verify` shows no `sorryAx`.
