# PLAN-jacobi-L3: local-to-global reduction (Lean, phase 3)

**Requires L2 finished** (`jacobiAm_Pconstructible_add`). Use `@lean-prover`.
Log: `HANDOFF-jacobi-L3.md`. Verify by LSP. Do not push.

## Why

This turns the open problem into a local one: it is enough to construct the amplitude for
arbitrarily small arguments. Any future positive result, for example from a construction that only
works near `0`, then extends to the whole line for free.

## Targets

```lean
-- Theorem: `am` at `n u` is P-constructible whenever it is at `u`.
theorem jacobiAm_Pconstructible_nsmul {c u : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) (n : ℕ) :
    PConstructible (jacobiAm c (n * u))

-- Theorem: if the amplitude is P-constructible at every P-constructible argument near `0`,
-- it is P-constructible at every P-constructible argument.
theorem jacobiAm_Pconstructible_of_near_zero {c ε : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hε : 0 < ε)
    (hloc : ∀ u, PConstructible u → |u| < ε → PConstructible (jacobiAm c u))
    {u : ℝ} (huP : PConstructible u) : PConstructible (jacobiAm c u)
```

## Hints

* `nsmul`: induction on `n`. The base case is `jacobiAm_zero hc` (`am 0 = 0`) with
  `zero_Pconstructible`. The step is `(n+1) u = n u + u` and `jacobiAm_Pconstructible_add`.
* `near_zero`: pick `n : ℕ` with `|u| / ε < n` (`exists_nat_gt`), so `n ≥ 1` and
  `|u / n| < ε`. `u / n` is P-constructible (the `pconstructible` tactic, or
  `PConstructible.div` with `nat`/`int_Pconstructible`). Then `u = n * (u / n)`
  (`mul_div_cancel₀`, `n ≠ 0`).

Also update the module doc of `Pptc/JacobiAddition.lean` to summarise all three phases. Then
add a single sentence to the "Where this leaves `sn`, `cn`, `dn`" block in `Jacobi.lean`
pointing to the local-to-global reduction. Keep the edit minimal, and do not rewrite the
"Why the first kind resists" paragraph: the research tasks will propose replacement text for
it. Axiom check, then commit locally.
