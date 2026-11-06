# Plan: closed-form ₂F₁ values at rational parameters are P-constructible

`Gamma_rat_Pconstructible` (`Pptc/GammaRational.lean:128`) is unconditional: Γ(q) is
P-constructible for every rational q. Every classical closed-form evaluation of ₂F₁ is a
ratio of Γ values, so at rational parameters each one becomes a P-constructibility theorem.
This plan covers the four that enlarge the set of ₂F₁ values we can reach:

| Phase | Theorem | Evaluation point | New file |
|---|---|---|---|
| 1 | Gauss | z = 1 | `GaussRational.lean` |
| 2 | general Goursat quadratic transformation | (infrastructure) | `GoursatGeneral.lean` |
| 3 | Gauss's second theorem | z = 1/2 | `GaussSecond.lean` |
| 4 | Pfaff transformation and boundary continuity at −1 | (infrastructure) | `Pfaff.lean` |
| 5 | Kummer and Bailey | z = −1 and z = 1/2 | `KummerBailey.lean` |

All files go in `Pptc/Hypergeometric/`.

**Ordering.**
- Phases 1, 2 and 4 are independent and can run in parallel.
- Phase 3 needs phases 1 and 2.
- Phase 5 needs phases 3 and 4.

**One phase per agent.** Each phase is one deliverable. Give each agent exactly one phase and
its own progress log, `C:\dev\Powerpoint\lean\HANDOFF-hyp-<phase>.md`; the agent appends a line
after each step.

**Out of scope:** the ₃F₂ sums (Dixon, Watson, Whipple), Beta values, and removing the pole
hypotheses from Gauss's theorem. None of them adds a new ₂F₁ value.

## Identities (all checked in Wolfram; each difference simplified to exactly 0)

For a = 3/7, b = 2/9, c = 5/11 and, for the transformations, z = 3/10:

- **Kummer** (DLMF 15.4.26):
  ₂F₁(a, b; 1+a−b; −1) = Γ(1+a−b) Γ(1+a/2) / (Γ(1+a) Γ(1+a/2−b))
- **Gauss's second theorem** (DLMF 15.4.28):
  ₂F₁(a, b; (a+b+1)/2; 1/2) = √π Γ((a+b+1)/2) / (Γ((a+1)/2) Γ((b+1)/2))
- **Bailey** (DLMF 15.4.30):
  ₂F₁(a, 1−a; c; 1/2) = Γ(c/2) Γ((c+1)/2) / (Γ((a+c)/2) Γ((1−a+c)/2))
- **Goursat quadratic transformation:**
  ₂F₁(2a, 2b; a+b+½; z) = ₂F₁(a, b; a+b+½; 4z(1−z)), for 0 ≤ z < 1/2
- **Pfaff transformation:**
  ₂F₁(a, b; c; z) = (1−z)^(−a) ₂F₁(a, c−b; c; z/(z−1)), for z < 1/2 and |z| < 1

How the pieces connect:
1. **Gauss's second theorem** is Goursat at z → 1/2⁻ plus Gauss at 1.
   - At z = 1/2 the inner argument 4z(1−z) reaches 1.
   - The right-hand series has c − a − b = 1/2 > 0, so it converges there for every a, b.
2. **Pfaff at z = 1/2** sends the argument to −1:
   ₂F₁(a, b; c; ½) = 2^a ₂F₁(a, c−b; c; −1).
   This links each value at ½ to a value at −1.
3. **Kummer(A, B)** is Pfaff applied to Gauss-second with parameters
   (a, b, c) = (A, 1+A−2B, 1+A−B).
4. **Bailey(a, c)** is Pfaff in the *second* parameter (using `hyp a b = hyp b a`):
   ₂F₁(a, 1−a; c; ½) = 2^(1−a) ₂F₁(c−a, 1−a; c; −1).
   That is Kummer with A = c−a, B = 1−a.

## Ground rules for every phase

- Use the lean-lsp loop: `lean_diagnostic_messages`, `lean_goal`, `lean_multi_attempt`.
- **No whole-project `lake build`.**
  - If an import's `.olean` is missing, build that one module only, e.g.
    `lake build Pptc.Hypergeometric.Gauss`.
  - Never chain several build targets in one command.
- Final check for each file:
  - `lake env lean Pptc/Hypergeometric/<File>.lean` from `pptc/`;
  - `lean_verify` on each main theorem. Only `propext`, `Classical.choice` and `Quot.sound`
    may appear.
- **Imports:** targeted only, never `import Mathlib`.
- **Style:**
  - Use the Apache header copied from `Gauss.lean`.
  - Wrap the file in `namespace Pconstructible` and `noncomputable section`.
  - Give each theorem a `-- Theorem:` line.
  - Write a module docstring saying why the argument works.
  - Keep lines to 100 characters.
  - No `sorry`.
- **Before using a lemma:** confirm it exists and check its signature with
  `lean_local_search` / `lean_hover_info`. Names cited below are believed correct; their
  signatures are not guaranteed.
- **Leave existing files alone:** do not edit `Gauss.lean`, `Quadratic.lean`, `Goursat.lean`
  or `SubstODE.lean`. New results go in new files.
- **Git:** commit locally on `main` in `pptc/` when the phase is done. **Do not push.**

---

## Phase 1: Gauss at every rational (`GaussRational.lean`)

Extend `hyp_one_Pconstructible_of_den_24` (`Gauss.lean:573`) to all rational parameters. It
was limited to 24ths only because of the Γ values available when it was written.

**Ingredients:**
- `hyp_one_eq_Gamma'` (`Gauss.lean:865`): the lifted Gauss theorem, with no positivity
  hypotheses on a, b.
  ```lean
  theorem hyp_one_eq_Gamma' {a b c : ℝ} (h : 0 < c - a - b)
      (hca : ∀ n : ℕ, c - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, c - b ≠ -(n : ℝ))
      (hc : ∀ n : ℕ, c ≠ -(n : ℝ)) :
      hyp a b c 1 = Real.Gamma c * Real.Gamma (c - a - b) /
        (Real.Gamma (c - a) * Real.Gamma (c - b))
  ```
- `Gamma_rat_Pconstructible (q : ℚ)`. It is not tagged `@[pconstructible]`; call it
  directly.
- `PConstructible.mul` and `PConstructible.div`. `div` has no side condition.

**Target:**
```lean
-- Theorem: `₂F₁(a, b; c; 1)` is P-constructible for all rational `a, b, c` with
-- `c − a − b > 0` and none of `c`, `c − a`, `c − b` a nonpositive integer.
theorem hyp_one_rat_Pconstructible {a b c : ℚ} (h : (0 : ℝ) < c - a - b)
    (hca : ∀ n : ℕ, (c : ℝ) - a ≠ -(n : ℝ)) (hcb : ∀ n : ℕ, (c : ℝ) - b ≠ -(n : ℝ))
    (hc : ∀ n : ℕ, (c : ℝ) ≠ -(n : ℝ)) :
    PConstructible (hyp (a : ℝ) b c 1)
```

**Proof (about 10 lines):**
1. `rw [hyp_one_eq_Gamma' h hca hcb hc]`.
2. Rewrite `(c : ℝ) - a - b`, `(c : ℝ) - a` and `(c : ℝ) - b` as casts of rationals with
   `show ... = ((c - a - b : ℚ) : ℝ) by push_cast; ring`. Do the longest one first, since
   `c - a` is a subterm of `c - a - b`. Mirror `Gauss.lean:582`.
3. Finish with `PConstructible.div (PConstructible.mul ..) (PConstructible.mul ..)` and four
   calls to `Gamma_rat_Pconstructible`.

**Imports:** `Pptc.Hypergeometric.Gauss`, `Pptc.GammaRational`.

---

## Phase 2: the general Goursat quadratic transformation (`GoursatGeneral.lean`)

This is the big phase.

**Target:** for `c = a + b + 1/2` not a nonpositive integer and `0 ≤ z < 1/2`,
```lean
hyp (2 * a) (2 * b) (a + b + 1 / 2) z = hyp a b (a + b + 1 / 2) (4 * z * (1 - z))
```

**Template.** `Quadratic.lean` proves exactly this for a = b = 1/4 (its theorem
`hyp_quadratic`, line 925). Follow the same two-part structure, with general parameters:

1. **Formal identity.** Show that
   `(hypSeries a b c).subst (4X(1−X)) = hypSeries (2a) (2b) c` in `ℝ⟦X⟧`.
   - The general tools exist:
     - `hypSeries_ode` (`Goursat.lean:64`): the hypergeometric equation for any (a, b, c);
     - `hypSeries_subst_ode` (`SubstODE.lean:57`): its pullback along any substitution,
       multiplied through by `(Dφ)³`.
   - With φ = 4X(1−X), the factor Dφ = 4(1−2X) is a unit in `ℝ⟦X⟧` (constant term 4), so
     it can be cancelled.
   - Then show the result is the hypergeometric equation for (2a, 2b; c).
   - The coefficient recurrence `(n+1)(n+c) uₙ₊₁ = (n+2a)(n+2b) uₙ`, with u₀ = 1, pins the
     series down, because c is not a nonpositive integer.
   - **Before formalizing**, confirm the pulled-back equation symbolically in Wolfram, with
     the multiplier written out. That is the step most likely to hide a sign or factor slip.
2. **Analytic transfer.** Generalize the following from `Quadratic.lean`:
   - the double series `quadFamily`;
   - its summability bound (`summable_quadFamily`, line 760), using a general coefficient
     bound for `|hypCoeff a b c m|`, which needs radius of convergence ≥ 1;
   - `hyp_quadratic_small` (line 906), which gives the identity on 4|z|(1+|z|) < 1;
   - the identity-theorem extension to [0, 1/2), as in `hyp_quadratic` (lines 949–973, via
     `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`).

   Several of the coefficient lemmas about `quadSubst` (`coeff_quadSubst_pow_eq` and its
   neighbours) do not depend on the parameters, so they can be imported and reused rather
   than copied.

**Imports:** `Pptc.Hypergeometric.Quadratic` and `Pptc.Hypergeometric.SubstODE`; add
`Pptc.Hypergeometric.Goursat` too if `SubstODE` does not already import it.

**Optional follow-up**, not part of this phase: re-derive `hyp_quadratic` as the
a = b = 1/4 corollary.

---

## Phase 3: Gauss's second theorem (`GaussSecond.lean`)

**Needs** phases 1 and 2.

**Target, the identity:** for A, B with (A+B+1)/2, (A+1)/2 and (B+1)/2 not nonpositive
integers,
```lean
hyp A B ((A + B + 1) / 2) (1 / 2) =
  Real.sqrt Real.pi * Real.Gamma ((A + B + 1) / 2) /
    (Real.Gamma ((A + 1) / 2) * Real.Gamma ((B + 1) / 2))
```

**Proof.**
1. Set a = A/2, b = B/2 and c = a + b + 1/2 = (A+B+1)/2.
2. Use phase 2 for z ∈ [0, 1/2) and let z → 1/2⁻.
   - **Left side:** `hyp A B c` is continuous at 1/2, which is inside the unit disc. Get this
     from its `AnalyticOnNhd` (see `Quadratic.lean:949` for how that is obtained).
   - **Right side:** 4z(1−z) → 1⁻. Use `tendsto_hyp_nhdsWithin_one` (`Gauss.lean:464`), which
     needs c − a − b = 1/2 > 0, true for every a, b.
3. Uniqueness of limits gives `hyp A B c (1/2) = hyp a b c 1`.
4. Apply `hyp_one_eq_Gamma'`. It gives Γ(c) Γ(1/2) / (Γ(b+1/2) Γ(a+1/2)); rewrite
   `Real.Gamma (1/2) = √π` with `Real.Gamma_one_half_eq`.

**Target, constructibility:** `hyp_second_rat_Pconstructible` for rational A, B under the same
pole conditions. Every Γ argument is rational; `√π` is P-constructible (`pconstructible` should
close it, or use `Gamma_one_half_Pconstructible` in `GammaFunctional.lean`).

---

## Phase 4: Pfaff and continuity at −1 (`Pfaff.lean`)

**Independent** of phases 1–3.

**Target, Pfaff:** for c not a nonpositive integer and z ∈ (−1, 1/2),
```lean
hyp a b c z = (1 - z) ^ (-a) * hyp a (c - b) c (z / (z - 1))
```
Use `Real.rpow`; 1 − z > 0 on this interval. Suggested proofs, in order of preference:

- **Coefficient route.** Expand (1−z)^(−a−k) binomially and compare coefficients of zⁿ. The
  identity reduces to Chu–Vandermonde:
  `∑ₖ C(n,k) (−1)ᵏ (c−b)ₖ/(c)ₖ = (b)ₙ/(c)ₙ`.
  - Search Mathlib for an `ascPochhammer` Vandermonde before proving it; otherwise prove it by
    induction on n.
  - The rearrangement is the same kind of double series as `quadFamily`. It is absolutely
    summable for |z| small, so prove it there first.
  - Then extend to (−1, 1/2) with the identity theorem: both sides are analytic, because
    |z| < 1 and |z/(z−1)| < 1 on that interval.
- **ODE route.** Show both sides satisfy the (a, b; c) hypergeometric equation and agree at 0.
  This is more work, because the prefactor means it is not a pure substitution.
- **Euler-integral route** (`hyp_eq_integral`, `Euler.lean:246`, with t ↦ 1−t). This only
  works for c > b > 0, so it would still need an extension argument. Not recommended.

**Target, continuity at −1:** if 0 < C − A − B and C is not a nonpositive integer, then
```lean
Filter.Tendsto (fun w => hyp A B C w) (𝓝[>] (-1)) (𝓝 (hyp A B C (-1)))
```
- `summable_hypCoeff_one` (`Gauss.lean:376`) gives `Summable (hypCoeff A B C ·)`. Over ℝ that
  means absolute summability, so the Weierstrass M-test makes the series continuous on [−1, 1].
  Mathlib's `continuous_tsum` / `continuousOn_tsum` should apply directly.
- Also record `hyp A B C (-1) = ∑' n, hypCoeff A B C n * (-1) ^ n` as a `HasSum`; it is needed
  in phase 5.

---

## Phase 5: Kummer and Bailey (`KummerBailey.lean`)

**Needs** phases 3 and 4.

**Step 1: Pfaff at 1/2.** Let z → 1/2⁻ in phase 4's Pfaff identity.
- The left side is continuous at 1/2 (inside the disc).
- (1−z)^(−a) → 2^a.
- z/(z−1) → −1 from the right. Use phase 4's continuity at −1; this needs
  c − a − (c−b) = b − a > 0 for the parameters on the right.

Result: `hyp a b c (1/2) = 2 ^ a * hyp a (c - b) c (-1)`, under b − a > 0 and the pole
conditions.

**Kummer (z = −1).** Target, for 1 − 2B > 0 (absolute convergence at −1) and the pole
conditions:
```lean
hyp A B (1 + A - B) (-1) =
  Real.Gamma (1 + A - B) * Real.Gamma (1 + A / 2) /
    (Real.Gamma (1 + A) * Real.Gamma (1 + A / 2 - B))
```
- Apply Pfaff at 1/2 with (a, b, c) = (A, 1+A−2B, 1+A−B). Then c − b = B, and the
  convergence condition b − a = 1 − 2B > 0 is exactly the hypothesis.
- Substitute Gauss's second theorem for the left side and solve for the value at −1.
- Simplify the Γ quotient with the duplication formula (`Real.Gamma_mul_Gamma_add_half`).
- **Check numerically in Wolfram** that the Gauss-second Γ quotient divided by 2^A equals the
  Kummer quotient, before fighting the algebra in Lean.

**Bailey (z = 1/2).** Target:
```lean
hyp a (1 - a) c (1 / 2) =
  Real.Gamma (c / 2) * Real.Gamma ((c + 1) / 2) /
    (Real.Gamma ((a + c) / 2) * Real.Gamma ((1 - a + c) / 2))
```
- Swap the parameters (`hyp a b c = hyp b a c`, from symmetry of `hypCoeff`; find or prove
  it), then apply Pfaff at 1/2 in the other parameter:
  `hyp a (1-a) c (1/2) = 2^(1-a) * hyp (c-a) (1-a) c (-1)`.
- This is Kummer with A = c − a, B = 1 − a. Its condition 1 − 2B > 0 is a > 1/2.
- The left side is symmetric under a ↦ 1 − a, so the theorem covers **every a ≠ 1/2**.
- **Known gap:** a = 1/2 (that is, ₂F₁(½, ½; c; ½)) is left out. Closing it needs Bailey's own
  quadratic transformation, ₂F₁(a, 1−a; c; z) = (1−z)^(c−1) ₂F₁((c−a)/2, (c+a−1)/2; c; 4z(1−z))
  (checked in Wolfram), which is a separate phase-2-sized job. State the theorem with
  `a ≠ 1/2` and say so in the docstring.

**Constructibility:** `hyp_kummer_rat_Pconstructible` and `hyp_bailey_rat_Pconstructible`
for rational parameters under the same hypotheses. Every Γ argument is rational. The
prefactors 2^a with a rational are P-constructible; check which `rpow` lemma the
`pconstructible` tactic knows.

---

## Done when

- Each phase's file compiles with no errors and its axioms are clean.
- Each phase is committed locally on `main` in `pptc/`.
- Nothing is pushed: pushing needs the user's explicit go-ahead.
