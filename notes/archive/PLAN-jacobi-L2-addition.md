# PLAN-jacobi-L2: the addition theorem for `cn`, and closure under addition (Lean, phase 2)

**Requires L1 finished** (`hasDerivAt_jacobiAm/Sn/Cn/Dn` in `Pptc/JacobiAddition.lean`).
Read `PLAN-jacobi-00-overview.md` §2 (F4). Use `@lean-prover`. Log: `HANDOFF-jacobi-L2.md`.
Verify by LSP (`lake build` of new modules is broken here, see L1). Do not push.

## Targets

```lean
-- Theorem: the addition theorem for `cn`.
theorem jacobiCn_add {c : ℝ} (hc : c < 1) (u v : ℝ) :
    jacobiCn c (u + v) =
      (jacobiCn c u * jacobiCn c v - jacobiSn c u * jacobiSn c v * jacobiDn c u * jacobiDn c v)
        / (1 - c * jacobiSn c u ^ 2 * jacobiSn c v ^ 2)

-- Theorem: the amplitudes at which `am` is P-constructible are closed under addition.
theorem jacobiAm_Pconstructible_add {c u v : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) (hv : PConstructible (jacobiAm c v)) :
    PConstructible (jacobiAm c (u + v))
```

## Proof plan for `jacobiCn_add` (Euler's argument, no `arccos`, no branches)

Fix `w := u + v` and consider, as a function of `x`,
`N(x) := cn x · cn (w−x) − sn x · sn (w−x) · dn x · dn (w−x)`,
`D(x) := 1 − c · sn²x · sn²(w−x)`.

1. `D x > 0`: `sn² ≤ 1` (from `jacobiSn_sq_add_jacobiCn_sq`), so `c·sn²·sn² < 1` when
   `0 ≤ c < 1`, and it is `≤ 0` when `c ≤ 0`. Split with `le_total`.
2. Show `HasDerivAt (fun x => N x / D x) 0 x` for every `x`. Get the derivative from L1 plus
   the chain rule for `x ↦ w − x`, then prove it equals `0`. Clearing `D²` leaves a polynomial
   identity in `s₁ c₁ d₁ s₂ c₂ d₂ c` that holds **modulo** `s₁²+c₁²=1`, `s₂²+c₂²=1`,
   `d₁² = 1 − c s₁²`, `d₂² = 1 − c s₂²` (`jacobiSn_sq_add_jacobiCn_sq`, `jacobiDn_sq`). Use
   `linear_combination (e₁) * h₁ + … ` and find the coefficients with a CAS: sympy
   `reduced(numerator, [relations])` via the Python at
   `C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`, or the Wolfram MCP.
   Numerically sanity-check the identity first.
3. So the function is constant (`is_const_of_deriv_eq_zero`, or `IsLocallyConstant` via
   `HasDerivAt`; check the names). Its value at `x = 0` is
   `cn 0 · cn w − 0 = cn w` over `D 0 = 1`, using `jacobiSn_zero`, `jacobiCn_zero`,
   `jacobiDn_zero`. Evaluate at `x = u` to get the theorem.

If step 2's algebra fights you, first prove a pure-algebra lemma on variables
`s₁ c₁ d₁ s₂ c₂ d₂ c : ℝ` with the four relations as hypotheses, then instantiate it.

## `jacobiAm_Pconstructible_add`

`sn`, `cn`, `dn` at `u` and `v` are P-constructible (`jacobiSn_Pconstructible_of_am`,
`jacobiCn_Pconstructible_of_am`, `jacobiDn_Pconstructible_of_am hcP`). So the right-hand side of
`jacobiCn_add` is P-constructible (the `pconstructible` tactic should do it after `rw`). Finish
with `jacobiAm_Pconstructible_of_cn`.

Every theorem needs a `-- Theorem:` line. Add a short `/-! ### ... -/` block explaining why the
invariant is constant: along `x ↦ (am x, am (w−x))` the sum of first-kind integrals is fixed, and
the addition formula is the algebraic first integral of that flow. Axiom check as in L1. Commit
locally.
