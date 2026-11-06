# PLAN: `Γ(q)` is P-constructible for every rational `q` (conditional)

Source: `gamma-power-laws.pdf` ("Γ at every rational from power-law arc lengths").
Target: `Pptc/GammaRational.lean` (umbrella + final theorem) over a directory
`Pptc/GammaRational/`, split so that most of the work runs in parallel.

```lean
theorem Gamma_rat_Pconstructible (hPL : PowerLawWithOrigin) (q : ℚ) :
    PConstructible (Real.Gamma q)
```

## Status update (2026-09-25): the origin extension was reverted

The `Defs.lean` change this plan depended on has been **reverted**. `power_law` again draws
only the half-line `x > 0`, so the origin-inclusive `power_law` is not constructible and the
final theorem is not unconditional. The whole development is retained but made conditional on
the named hypothesis

```lean
def PowerLawWithOrigin : Prop :=
  ∀ a b : ℚ, 0 < b →
    PConstructibleCurve
      {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < b)) ∧ pt.2 = (a : ℝ) * pt.1 ^ (b : ℝ)}
```

declared in `Pptc/GammaRational/ArcLength.lean`. Its *only* use is the image side condition
`powerLawParam_image_subset`; every other lemma in the development is unconditional. If
`power_law` is ever widened, `PowerLawWithOrigin` becomes one application of the constructor
and `Gamma_rat_Pconstructible` follows with no further work. The `PowerLawWithOrigin` guard
`0 < b` matters because Mathlib's `Real.rpow` sets `0 ^ b = 0` for negative `b` too, which
would place a spurious origin on the hyperbola `y = a / x`.

## 0. State of the tree (original, checked 2026-09-22; superseded above)

* `Defs.lean` already carries the one axiom change the paper asks for (uncommitted):
  `power_law` now reads `(0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < b)) ∧ pt.2 = a * pt.1 ^ b`.
* That change breaks **exactly three proofs in `Basic.lean`** (5 errors, LSP-verified):
  line 232 (`sqrt_Pconstructible`), lines 551/557 (`powerLaw_root_pos_Pconstructible`),
  lines 964/971 (`powerLaw_cubic_root_pos_Pconstructible`). No other file uses the
  constructor. Every downstream `.olean` is now stale.
* Everything else the proof needs exists: `pi_Pconstructible`, `sqrt_Pconstructible`,
  `cos_Pconstructible`, `rpow_Pconstructible` (positive base, any P exponent: gives all
  real `n`-th roots), `rat_Pconstructible`/`ratval_Pconstructible`, and in `Gamma.lean`
  the functional-equation transfer lemmas (`Gamma_add_intCast_Pconstructible`,
  `Gamma_mul_Gamma_one_sub_Pconstructible`, `dupFactor`, `dupFactor_Pconstructible`,
  `Gamma_mul_Gamma_add_half'`, `Gamma_intCast_div_two_Pconstructible`, ...).
* `Gamma.lean` imports `Level24`, `GaussMultiplicationK3`, `EllipticFSecondSingular`, so
  importing it drags in the heavy chain, all of which must be rebuilt after the `Defs`
  change. **Do not import `Pptc.Gamma` from the new files**; see W0.2.

## 1. The mathematics, as formalized (deviates from the paper on purpose)

The paper goes ℓ(σ) → A(σ) → J(s) = ∫₀^∞ → B(ρ, ½-ρ) → B(y, ½) → cycle formula. Two
simplifications make the Lean much lighter, and both were checked numerically to ~39
digits (Wolfram, s = 5, 3, 7/2, 10/3, 13/4, 7):

**(a) No improper integrals.** Instead of ∫₀^∞ and the Beta integral of the second kind,
split Mathlib's first-kind Beta integral at `t = 1/2`. Put

    halfBeta α β := ∫_{(0,1/2)} t^(α-1) (1-t)^(β-1) dt.

Then `B(α, β) = halfBeta α β + halfBeta β α` (reflect `t ↦ 1 - t` on `[1/2, 1)`), and the
single substitution `t = x^σ / (1 + x^σ)`, which carries `(0,1)` onto `(0,1/2)`, gives

    halfBeta (1/σ) (1/2 - 1/σ) = σ · A(σ),   A(σ) := ∫₀¹ dx / √(1 + x^σ)      (σ > 0).

(Integrand collapse: `t^(ρ-1) = x^(1-σ) (1+x^σ)^(1-ρ)`, `(1-t)^(-1/2-ρ) = (1+x^σ)^(1/2+ρ)`,
`dt = σ x^(σ-1) (1+x^σ)^(-2) dx`, product `σ (1+x^σ)^(-1/2)`.) With `ρ ∈ (0, 1/2)`,
`s = 1/ρ`, `s' = 1/(1/2 - ρ)` this is the paper's fold, symmetrically:

    Γ(ρ) Γ(1/2 - ρ) = √π · B(ρ, 1/2 - ρ) = √π · (s·A(s) + s'·A(s')).              (Π)

**(b) No cycle-formula product.** Work multiplicatively modulo P. Given (Π) for rational
`ρ ∈ (0,1/2)`:

1. *Half-shift ratio* `H(x) := Γ(x)/Γ(x + 1/2) ∈ P` for every rational `x > 0`:
   * base `ρ ∈ (0,1/2)`: `H(ρ) = Γ(ρ)Γ(1/2-ρ) / (Γ(1/2-ρ)Γ(1/2+ρ))`, and the denominator
     is a reflection product `Γ(y)Γ(1-y)` at `y = 1/2 - ρ` (P, nonzero);
   * base `x ∈ ½ℤ`: both values are P already (`Gamma_intCast_div_two_Pconstructible`);
   * step: `H(x) · H(x + 1/2) = Γ(x)/Γ(x+1) = 1/x`, so `H(x + 1/2) = 1 / (x · H(x))`.
     Induct on `k` in `x = ρ + k/2`.
2. *Doubling ratio* `D(x) := Γ(x)² / Γ(2x) = dupFactor x · H(x) ∈ P` (Legendre).
3. `Γ(x)^(2^k) / Γ(2^k x) ∈ P` by induction on `k` (`D` at `2^k x`, squared chain).
4. *Odd denominator* `x = p/N`, `N` odd: pick `ℓ = φ(N) ≥ 1`, so `N ∣ 2^ℓ - 1` and
   `2^ℓ x = x + m` with `m ∈ ℕ`. `Γ(x+m)/Γ(x) = ∏_{i<m} (x+i) ∈ P`, hence
   `Γ(x)^(2^ℓ - 1) ∈ P`, positive, and `rpow_Pconstructible` with exponent
   `1/(2^ℓ - 1)` recovers `Γ(x)`. (No `gcd(p, N) = 1` needed.)
5. *General `q > 0`*: `q = p / (2^j N)`, `N` odd. Induct on `j`:
   `Γ(q)² = D(q) · Γ(2q)` and `2q` has exponent `j - 1`; take the square root.
6. *`q ≤ 0`*: shift by an integer with `Gamma_add_intCast_Pconstructible`.

Arc-length side (paper §1, Lemma 2), unchanged:

* `γ(t) = (t, b⁻¹ t^b)`, `b = 1 + σ/2`, on `[0,1]` lies on `power_law (b⁻¹) b` (the origin
  is on it now since `b > 0`), is injective, differentiable on all of `[0,1]` (`b > 1`,
  `Real.hasDerivAt_rpow_const` with `Or.inr`), and has `speed = √(1 + t^σ)` for `t ≥ 0`.
  Endpoints `(0,0)`, `(1, b⁻¹)` are rational. So `ℓ(σ) = ∫₀¹ √(1+x^σ) ∈ P` by `arc_length`.
* `d/dx (x √(1+x^σ)) = (1 + σ/2)√Q - (σ/2)/√Q` on `(0,1)`, so
  `A(σ) = (1 + 2/σ) ℓ(σ) - 2√2/σ`. (FTC on `(0,1)` only: `x^σ` need not be
  differentiable at `0` when `σ < 1`.)

## 2. File layout and exact statements

All files `namespace Pconstructible`, targeted imports, `-- Theorem:` lines, `/-! ### -/`
blocks, 100-column limit. The orchestrator writes every file below **as a skeleton with
these statements and `sorry` bodies first** (step W0.3), so the pieces are guaranteed to
snap together; workers fill proofs and must not change a statement without flagging it.

### `Pptc/GammaRational/HalfBeta.lean` — definition only (Mathlib only)

```lean
/-- The Beta integrand integrated over the left half `(0, 1/2)` of `[0, 1]`. -/
noncomputable def halfBeta (α β : ℝ) : ℝ :=
  ∫ t in Set.Ioo (0 : ℝ) (1 / 2), t ^ (α - 1) * (1 - t) ^ (β - 1)
```

### F1 `Pptc/GammaRational/ArcLength.lean` (imports `Pptc.Defs` + Mathlib; not `Basic`)

```lean
def PowerLawWithOrigin : Prop :=
  ∀ a b : ℚ, 0 < b →
    PConstructibleCurve
      {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < b)) ∧ pt.2 = (a : ℝ) * pt.1 ^ (b : ℝ)}

noncomputable def powerLawParam (σ : ℝ) (t : ℝ) : ℝ × ℝ :=
  (t, (1 + σ / 2)⁻¹ * t ^ (1 + σ / 2))

theorem speed_powerLawParam {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t) :
    speed (powerLawParam σ) t = Real.sqrt (1 + t ^ σ)
theorem arcLengthOf_powerLawParam {σ : ℝ} (hσ : 0 < σ) :
    arcLengthOf (powerLawParam σ) 0 1 = ∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ)
-- the four side conditions of `PConstructible.arc_length`, for rational σ:
theorem powerLawParam_image_subset (hPL : PowerLawWithOrigin) {σ : ℚ} (hσ : 0 < σ) :
    powerLawParam σ '' Set.Icc 0 1 ⊆
      {pt : ℝ × ℝ | (0 < pt.1 ∨ (pt.1 = 0 ∧ 0 < (1 + σ / 2 : ℚ))) ∧
        pt.2 = (((1 + σ / 2)⁻¹ : ℚ) : ℝ) * pt.1 ^ (((1 + σ / 2 : ℚ)) : ℝ)}
theorem powerLawParam_injOn (σ : ℝ) : Set.InjOn (powerLawParam σ) (Set.Icc 0 1)
theorem powerLawParam_differentiableAt {σ : ℝ} (hσ : 0 < σ) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    DifferentiableAt ℝ (fun s => (powerLawParam σ s).1) t ∧
      DifferentiableAt ℝ (fun s => (powerLawParam σ s).2) t
theorem powerLawParam_intervalIntegrable {σ : ℝ} (hσ : 0 < σ) :
    IntervalIntegrable (speed (powerLawParam σ)) MeasureTheory.volume 0 1
```

Only `powerLawParam_image_subset` mentions the origin-inclusive shape; its proof is
unconditional, because any image point of `powerLawParam` satisfies the predicate. The
hypothesis `hPL` is used one level up, in `powerLawArc_Pconstructible`, to supply the
`PConstructibleCurve` argument to `arc_length`. All the analytic lemmas are unconditional.
(This file was written when `power_law` still included the origin; the hypothesis records
that the *curve* is the missing primitive, not the membership.)

Hints: `deriv` of the second coordinate is `t ^ (σ/2)` (use `HasDerivAt.deriv`, the
`b⁻¹ · b = 1` cancellation, `Real.hasDerivAt_rpow_const (Or.inr _)`); `(t^(σ/2))^2 = t^σ`
via `Real.rpow_natCast`/`Real.rpow_mul` for `t ≥ 0`. For the integral use
`intervalIntegral.integral_congr` on `uIcc 0 1`. Integrability: `speed` agrees with the
continuous `√(1+t^σ)` on `[0,1]` (`IntervalIntegrable.congr` or `ContinuousOn`). Template:
`arcLengthOf_parabolaParam` / `parabolaArc_Pconstructible` in `Basic.lean` (~line 1830).
The `image_subset` statement must match the origin-inclusive set **syntactically after
`push_cast`**; under the reverted `Defs` the matching constructor no longer exists, so
`hPL` stands in for it.

### F2 `Pptc/GammaRational/Conversion.lean` (Mathlib only)

```lean
theorem integral_inv_sqrt_one_add_rpow {σ : ℝ} (hσ : 0 < σ) :
    ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹
      = (1 + 2 / σ) * (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ σ)) - 2 * Real.sqrt 2 / σ
```

Hints: `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le` with
`F x = x * √(1 + x^σ)`, `ContinuousOn` on `Icc`, `HasDerivAt` on `Ioo 0 1`
(`Real.hasDerivAt_rpow_const (Or.inl hx.ne')`, `Real.hasDerivAt_sqrt`), derivative
integrable because it equals a continuous function on `[0,1]` (split it as the
combination `(1+σ/2)√Q - (σ/2)/√Q` *before* integrating, and use
`intervalIntegral.integral_sub`/`integral_const_mul`). `F 1 = √2`, `F 0 = 0`.

### F3 `Pptc/GammaRational/Substitution.lean` (imports `HalfBeta` + Mathlib)

```lean
theorem halfBeta_inv_eq {σ : ℝ} (hσ : 0 < σ) :
    halfBeta σ⁻¹ (1 / 2 - σ⁻¹) = σ * ∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ σ))⁻¹
```

Hints: this is the hardest analytic step. Use **`integral_image_eq_integral_abs_deriv_smul`
on `Ioo`** exactly as `beta_one_third_one_half_integral` / `beta_one_quarter_one_half_integral`
do in `Gamma.lean` — it needs *no* integrability hypothesis, which matters because
`t^(ρ-1)` is unbounded at `0`. Do **not** try `integral_comp_mul_deriv` (needs a continuous
integrand on the closed image). Map `φ x = x^σ / (1 + x^σ)`; show `φ '' Ioo 0 1 = Ioo 0 (1/2)`
with the explicit inverse `t ↦ (t / (1 - t))^(1/σ)`; `InjOn` from strict monotonicity;
`φ' x = σ x^(σ-1) / (1 + x^σ)^2`; pointwise collapse on `x ∈ Ioo 0 1` to
`σ * (√(1 + x^σ))⁻¹` (all bases positive, so `Real.rpow_add`/`rpow_neg`/`div_rpow` apply).
Finish with `integral_const_mul`, `intervalIntegral.integral_of_le`,
`integral_Ioc_eq_integral_Ioo`.

### F4 `Pptc/GammaRational/BetaSplit.lean` (imports `HalfBeta` + Mathlib)

```lean
theorem betaIntegral_ofReal_eq_halfBeta {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Complex.betaIntegral α β = ((halfBeta α β + halfBeta β α : ℝ) : ℂ)
theorem Gamma_mul_Gamma_half_sub {ρ : ℝ} (h0 : 0 < ρ) (h1 : ρ < 1 / 2) :
    Real.Gamma ρ * Real.Gamma (1 / 2 - ρ)
      = Real.sqrt Real.pi * (halfBeta ρ (1 / 2 - ρ) + halfBeta (1 / 2 - ρ) ρ)
```

Hints: (i) real ↔ complex, generalizing `betaIntegral_one_third_one_half` in `Gamma.lean`
(`Complex.ofReal_cpow` for nonnegative bases). (ii) Integrability of the real integrand on
`Ioo 0 1`: either transfer `Complex.betaIntegral_convergent` (norm of the complex
integrand = the real one) or prove it on each half directly
(`intervalIntegral.intervalIntegrable_rpow'` times a continuous bounded factor). (iii) Split
`Ioo 0 1 = Ioo 0 (1/2) ∪ Ico (1/2) 1` (`setIntegral_union`, or interval integrals with
`integral_add_adjacent_intervals`), and reflect the right half with
`intervalIntegral.integral_comp_sub_left` (`t ↦ 1 - t`). (iv) The Γ identity:
`Complex.Gamma_mul_Gamma_eq_betaIntegral`, `Complex.Gamma_ofReal`, `ρ + (1/2 - ρ) = 1/2`,
`Real.Gamma_one_half_eq`. If a statement is easier in interval-integral form, add a
`halfBeta_eq_intervalIntegral` bridge lemma here rather than changing `halfBeta`.

### W0.2 `Pptc/GammaFunctional.lean` (extracted from `Gamma.lean`)

Move `Gamma.lean`'s sections from "Elementary numbers used below" through "The
half-integers" (lines ~111–336: `half_Pconstructible`, `sqrt_pi_Pconstructible`, `Γ` at
integers and `1/2`, recurrence, reflection, duplication incl. `dupFactor`,
`Gamma_intCast_div_Pconstructible`, `Gamma_intCast_div_two_Pconstructible`) verbatim into
this new module, importing only `Pptc.Basic` + the Mathlib Gamma modules it needs.
`Gamma.lean` then imports `Pptc.GammaFunctional` and loses those lines. Names unchanged, so
nothing downstream moves. (Moving, not copying, per the "generalize, don't copy"
convention.)

### F5a `Pptc/GammaRational/HalfShift.lean` (imports `Pptc.GammaFunctional`)

```lean
/-- The hypothesis the analytic half delivers: products `Γ(ρ) Γ(1/2 - ρ)`. -/
def HalfProducts : Prop :=
  ∀ ρ : ℚ, 0 < ρ → ρ < 1 / 2 →
    PConstructible (Real.Gamma (ρ : ℝ) * Real.Gamma (1 / 2 - (ρ : ℝ)))

theorem Gamma_div_Gamma_add_half_Pconstructible (hΠ : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) / Real.Gamma ((x : ℝ) + 1 / 2))
theorem Gamma_sq_div_Gamma_two_mul_Pconstructible (hΠ : HalfProducts) (x : ℚ) (hx : 0 < x) :
    PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ)))
```

Steps 1–2 of §1(b). Useful: `Real.Gamma_pos_of_pos`, `Real.Gamma_add_one`, `Real.Gamma_mul_Gamma_one_sub`,
`Gamma_mul_Gamma_one_sub_Pconstructible`, `Gamma_mul_Gamma_add_half'`. `PConstructible.div`
has no side condition, so every `a/c = (a/b)(b/c)` rewrite needs only `b ≠ 0`, which
positivity of `Γ` on `(0, ∞)` supplies. Decompose `x = ρ + k/2` with
`ρ = Int.fract (2x) / 2`.

### F5b `Pptc/GammaRational/Doubling.lean` (imports `Pptc.GammaFunctional`)

```lean
theorem Gamma_rat_Pconstructible_of_dup
    (hdup : ∀ x : ℚ, 0 < x → PConstructible (Real.Gamma (x : ℝ) ^ 2 / Real.Gamma (2 * (x : ℝ))))
    (q : ℚ) : PConstructible (Real.Gamma (q : ℝ))
```

Steps 3–6 of §1(b); fully independent of F5a (it takes the doubling ratio as a
hypothesis). Useful: `Nat.ModEq.pow_totient` (with `Nat.Coprime 2 N` from `N` odd),
`Nat.totient_pos`, `Nat.exists_eq_two_pow_mul_odd` (for `q.den`), `Real.Gamma_add_one`
for the Pochhammer ratio (induction on `m`), `rpow_Pconstructible` + `Real.rpow_natCast`/
`Real.rpow_mul` for the root (template: end of `Gamma_one_third_Pconstructible`),
`Gamma_add_intCast_Pconstructible` for `q ≤ 0`. Suggested internal lemmas:
`Gamma_pow_two_pow_div_Pconstructible (k : ℕ)`, `Gamma_add_nat_div_Pconstructible`,
`Gamma_odd_den_Pconstructible`, then induction on `j` in `q = p / (2^j * N)`.

### A1 `Pptc/GammaRational.lean` — assembly (imports all of the above)

```lean
theorem powerLawArc_Pconstructible (hPL : PowerLawWithOrigin) (σ : ℚ) (hσ : 0 < σ) :
    PConstructible (∫ x in (0 : ℝ)..1, Real.sqrt (1 + x ^ (σ : ℝ)))
theorem inv_sqrt_integral_Pconstructible (hPL : PowerLawWithOrigin) (σ : ℚ) (hσ : 0 < σ) :
    PConstructible (∫ x in (0 : ℝ)..1, (Real.sqrt (1 + x ^ (σ : ℝ)))⁻¹)
theorem halfProducts (hPL : PowerLawWithOrigin) : HalfProducts
theorem Gamma_rat_Pconstructible (hPL : PowerLawWithOrigin) (q : ℚ) :
    PConstructible (Real.Gamma q)
```

* `powerLawArc`: `PConstructible.arc_length (hPL _ _ _) (powerLawParam σ) zero_le_one` +
  F1's six lemmas, endpoints by `pconstructible`/`ratval_Pconstructible`, then rewrite with
  `arcLengthOf_powerLawParam`.
* `inv_sqrt`: F2 + `pconstructible`.
* `halfProducts`: F4 at `ρ`, F3 at `σ = ρ⁻¹` and `σ = (1/2 - ρ)⁻¹` (rewrite
  `(ρ⁻¹)⁻¹ = ρ`, `1/2 - ρ = ((1/2 - ρ)⁻¹)⁻¹`, i.e. the second `halfBeta` is F3 at `s'`),
  then `inv_sqrt` at both.
* final: `Gamma_rat_Pconstructible_of_dup (Gamma_sq_div_Gamma_two_mul_Pconstructible (halfProducts hPL))`.
* Optional showcase: `Gamma_one_fifth_Pconstructible hPL` as a one-liner, with the paper's
  Example 9 in a comment (curves with exponents `7/2, 8/3, 9/4, 6`).
* Do **not** tag `Gamma_rat_Pconstructible` `@[pconstructible]`: it takes a hypothesis, and no
  instance of `PowerLawWithOrigin` exists in this tree. (It was tagged when the `Defs` change
  was live; the tag would now be dead and would break `pconstructible` usage only if someone
  tried to discharge the hypothesis.)

## 3. Schedule and dependencies

```
W0.1 fix Basic ──► lake build Pptc.Basic ──► W0.2 GammaFunctional ──► F5a ─┐
                                                                  └─► F5b ─┤
W0.3 skeletons (Mathlib-only files) ──► F1  F2  F3  F4 (parallel) ─────────┼─► A1 ─► W3
                                                                           │
```

| Task | Deliverable | Depends on | Start |
|------|-------------|------------|-------|
| W0.1 | `Basic.lean` compiles under new `power_law`; `lake build Pptc.Basic` | — | now |
| W0.2 | `GammaFunctional.lean` extracted; `lake build Pptc.GammaFunctional` | W0.1 | wave 0 |
| W0.3 | all skeletons with `sorry`, statements elaborate | — (F5a/F5b/A1 skeletons need W0.2) | now |
| F1 | ArcLength | `Pptc.Defs` olean only | wave 1 |
| F2 | Conversion | Mathlib only | wave 1 |
| F3 | Substitution | HalfBeta | wave 1 |
| F4 | BetaSplit | HalfBeta | wave 1 |
| F5a | HalfShift | W0.2 | wave 1b |
| F5b | Doubling | W0.2 | wave 1b |
| A1 | assembly + final theorem | all | wave 2 |
| W3 | docs, axiom check, final builds | A1 | wave 3 |

**W0.1 details.** The three broken sites all need the same fix: `power_law`'s first
conjunct is now a disjunction.
* line ~232: build it with `Or.inl h`.
* lines ~551 and ~964: `hpow` currently assumes `0 < u`; drop that hypothesis
  (`Real.rpow_natCast` holds for every `u`), and destructure the disjunction instead of
  `hupos`. At `u = 0` the uniqueness argument still goes through because `huniq` covers
  every root in the window.
* lines ~557 and ~971: `hmem`'s stated set literal must be updated to the new shape
  (`Or.inl hβ`).
Also fix the now-false *comments*: `Basic.lean` ~264–267, ~488, ~519, ~559 ("`power_law`
draws only `x > 0`"); `Defs.lean` ~195 (the `{(x, √x) : 0 < x ≤ 1}` example no longer
illustrates a missing endpoint; replace it with, e.g., the hyperbola branch `b < 0`, which
still omits its limit point); `Box.lean` ~218–225 (a `power_law` with `b > 0` cropped to
`[0, c]` is now compact). Hyperbola comments (~1951, ~2074, ~2136) stay true (`b = -1`).
Commit `Defs` + `Basic` together locally.

**Parallelism.** Wave 1 has six independent single-file workers (F1–F4 can start at once,
alongside W0.1/W0.2; F5a/F5b as soon as W0.2's olean exists). The guard caps LSP
elaborations at 2 concurrent, so more than ~4 simultaneous workers mostly queue; run F3
and F4 (the long ones) first, with F1/F2 beside them, then F5a/F5b.

**Expected difficulty.** F3 > F4 > F5b > F1 > F5a > F2 ≈ A1. F2, F5a and A1 are each well
under 100 lines.

## 4. Worker instructions (paste into each `@lean-prover` task)

* One file, one deliverable. Log each step to `lean/HANDOFF-gamma-rational-<task>.md`.
* Iterate with `lean_goal` / `lean_multi_attempt` / `lean_diagnostic_messages`; paths as
  `pptc/Pptc/GammaRational/Foo.lean`. **No `lake build`** except the single final check of
  your own target (`lake build Pptc.GammaRational.Foo`), and never a whole-project build.
* Do not change the skeleton statement. If it is false or unprovable as written, stop
  and report the counterexample/obstruction instead.
* Confirm lemma names with `lean_local_search`/`lean_loogle` before use; Lean 4.33
  (`le_total`, not `le_or_lt`).
* Done = no `sorry`, no errors/warnings, `lean_verify` shows only `propext`,
  `Classical.choice`, `Quot.sound`.

## 5. W3: close-out

1. `lean_verify Pconstructible.Gamma_rat_Pconstructible`.
2. `lake build Pptc.GammaRational` (alone).
3. Separately, and only then, `lake build Pptc.Gamma -j1` to confirm the extraction left
   `Gamma.lean` intact (heavy: pulls the `Level24` chain; nothing else running). The other
   heavy targets (`DegreeSeven`, `ThirdKind`, `Offset`, `Jacobi`, ...) also need a rebuild
   after the `Defs` change but are unaffected by this plan; build them one at a time later.
4. Docs: `Gamma.lean`'s module docstring says denominators beyond 24 need a new input each
   time; add a paragraph pointing to `Pptc.GammaRational`, which settles *every* rational
   given the origin-inclusive `power_law`. Update `CLAUDE.md`'s `power_law` bullet (it
   still says "for `x > 0`"). Add `Pptc.GammaRational` to `Pptc.lean` if that umbrella
   lists modules.
5. Commit locally; ask before pushing.

## 6. Risks

* **F1 statement shape.** The `power_law` set involves `((1 + σ/2 : ℚ) : ℝ)` casts; the
  image-subset lemma must line up with the constructor. Verify the fit first (see F1).
* **F3 surjectivity/injectivity** on `Ioo` with `rpow` is fiddly but routine; the explicit
  inverse avoids IVT.
* **F4 integrability near both endpoints.** If transferring `betaIntegral_convergent` is
  awkward, prove `IntegrableOn` on each half directly; only one singular endpoint per half.
* **Rational ↔ real casts** in F5a/F5b (`((2 * x : ℚ) : ℝ)` vs `2 * (x : ℝ)`): normalize
  with `push_cast` at the start of every proof; statements use the real-side form.
