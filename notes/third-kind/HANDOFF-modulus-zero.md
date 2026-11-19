# Handoff — `Pptc.ThirdKindAll.ModulusZero`

Status: **complete and compiling**. `lake build Pptc.ThirdKindAll.ModulusZero` succeeds;
`lean_diagnostic_messages` is empty (no errors, no linter warnings); the axiom check on the
headline theorem reports only `propext`, `Classical.choice`, `Quot.sound` (no `sorryAx`).

## Target (proved exactly as specified)

```lean
theorem ellipticPiInc_zero_modulus_Pconstructible {n Φ : ℝ}
    (hnP : PConstructible n) (hΦP : PConstructible Φ)
    (hne : ∀ θ ∈ Set.uIcc (0 : ℝ) Φ, 1 - n * Real.sin θ ^ 2 ≠ 0) :
    PConstructible (ellipticPiInc 0 n Φ)
```

File: `Pptc/ThirdKindAll/ModulusZero.lean` (new; imports `Pptc.ThirdKindAll.Standard`).

## Proof outline

At `c = 0`, `ellipticEIntegrand 0 θ = 1`, so the integrand is `1 / (1 - n sin²θ)`, and
`1 - n sin²θ = cos²θ (1 + (1 - n) tan²θ)`. Rather than substitute `t = tan θ` (whose
`g u = 1/(1 + (1-n)u²)` is *not* globally continuous when `n > 1`, so
`integral_comp_tan` does not apply), the proof uses `tan`-based antiderivatives directly in
`θ` through `intervalIntegral.integral_eq_sub_of_hasDerivAt`.

Declarations, in file order:

1. `integral_one_div_one_add_mul_sq` — `∫₀^U du/(1 + b u²) = arctan (√b U)/√b` (`b > 0`).
2. `integral_one_div_add_sq` — `∫₀^U du/(b + u²) = arctan (U/√b)/√b` (`b > 0`).
3. `integral_one_div_one_sub_mul_sq` — `∫₀^U du/(1 - b u²) = artanh (√b U)/√b`
   (`b > 0`, `|√b U| < 1`); the bound is propagated to `uIcc 0 U` via `|u| ≤ |U|`.
4. `ellipticPiIntegrand_zero_eq_tan` — the pointwise identity
   `ellipticPiIntegrand 0 n θ = (1/cos²θ) · 1/(1 + (1-n) tan²θ)` (needs `cos θ ≠ 0` and
   `1 - n sin²θ ≠ 0`).
5. `ellipticPiInc_zero_eq_arctan` — `n < 1`, `|Φ| < π/2`:
   `Π(0,n,Φ) = arctan (√(1-n) tan Φ)/√(1-n)`.
6. `ellipticPiInc_zero_one_eq` — `n = 1`, `|Φ| < π/2`: `Π(0,1,Φ) = tan Φ`.
7. `ellipticPiInc_zero_eq_artanh` — `n > 1`, `0 ≤ Φ < π/2`, no pole on `[0, Φ]`:
   `Π(0,n,Φ) = artanh (√(n-1) tan Φ)/√(n-1)`.
   Positivity of `1 - (n-1) tan²θ` on the interval comes from `gtOne_sin_sq_lt_one`
   plus monotonicity of `sin` on `[0, Φ]`.
8. `integral_one_div_one_sub_mul_cos_sq` — `n < 1`, `|Φ| < π/2`:
   `∫₀^Φ dθ/(1 - n cos²θ) = arctan (tan Φ/√(1-n))/√(1-n)` (the `cot`-side antiderivative).
9. `ellipticPi_zero_modulus_eq` — the complete integral
   `Π(n) = arctan(√(1-n))/√(1-n) + arctan(1/√(1-n))/√(1-n)` for `n < 1`.
   **Note:** the suggested "half-interval symmetry `f(π/2 - θ) = f(θ)`" is *false* for
   `sin²` (`f(π/2-θ) = 1/(1 - n cos²θ)`). Instead the interval `[0, π/2]` is split at `π/4`:
   the first half uses (5) at `π/4`, the second is reflected (`integral_comp_sub_left`) to
   `∫₀^{π/4} dθ/(1 - n cos²θ)` and evaluated with (8).
10. `ellipticPi_zero_modulus_Pconstructible` — `n < 1` gives the `hK` needed below.
11. `ellipticPiInc_zero_Pconstructible_of_le_half_pi` — the `1 ≤ n`, `0 ≤ Φ` case
    (cases `n = 1` / `1 < n`, using (6), resp. (7) + the `artanh` bound
    `(n-1) tan²Φ < 1` derived from `n sin²Φ < 1`).
12. `ellipticPiInc_zero_modulus_Pconstructible` — main theorem:
    * `n < 1`: `ellipticPiInc_Pconstructible_of_base'` with `c = 0`, `hK` from (10) and
      the base case from (5) — the base case at `0 ≤ θ < π/2` is immediate once (5) has
      turned it into `arctan` of a P-constructible number;
    * `1 ≤ n`: `abs_lt_pi_div_two_of_one_le` forces `|Φ| < π/2`; (11) handles `Φ ≥ 0`,
      and `Φ < 0` is reduced by oddness (`ellipticPiInc_neg`) to `-Φ > 0`.

## Notes / gotchas for follow-up work

* `Real.sqrt` algebra in `field_simp` needs `Real.sq_sqrt`/`Real.mul_self_sqrt` supplied
  explicitly; `field_simp` does not use them by default.
* `field_simp` will not identify `1 + t²(1-n)` with `1 - (n-1)t²` on its own — passing the
  *nonzero* fact in the matching syntactic form plus a trailing `ring` is the cheap fix.
* `linarith` does not look through `θ ∈ Set.Icc 0 Φ`; destruct the membership into
  `⟨hθ0, hθΦ⟩` first (this bit the first draft of `hpos`).
* `abs_lt_of_sq_lt_sq'` already returns the conjunction `-1 < x ∧ x < 1`; do not wrap it in
  `abs_lt.mp`.
* No `sorry`, `admit`, `axiom`, `native_decide`, or `set_option maxHeartbeats` anywhere in
  the file; no other file was modified.
