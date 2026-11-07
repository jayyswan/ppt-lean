# Plan: the lower branch `W₋₁` of the Lambert W function is P-constructible

Written 2026-11-07. Target: a named operation the library does not yet have.
Tracked in GitHub issue #9.
`Pptc/Basic.lean` (section `LambertW`, line ~1962) proves the principal branch
(`lambertW_Pconstructible`) and says "The lower branch `W₋₁` is not reachable this way and is
not defined here". It *is* reachable, with the same two curves; only the cropping window changes.

## 1. Mathematics

`W₋₁(x)` is the unique `w ≤ -1` with `w·eʷ = x`, defined for `-1/e ≤ x < 0`.

- **Monotonicity.** `mulExp u = u·eᵘ` has derivative `(1 + u)eᵘ < 0` on `(-∞, -1)`, so
  `mulExp` is strictly decreasing on `(-∞, -1]`. It falls from `0⁻` (as `u → -∞`) to
  `mulExp (-1) = -1/e`.
- **Existence.** For `-1/e ≤ x < 0`, take `t = max 1 (2/(-x))`. From
  `eᵗ ≥ 1 + t + t²/2 > t²/2` (`Real.quadratic_le_exp_of_nonneg`) we get
  `t·e⁻ᵗ < 2/t ≤ -x`, i.e. `mulExp (-t) > x`. With `mulExp (-1) = -1/e ≤ x`, the decreasing
  form of the intermediate value theorem on `[-t, -1]` gives a root `w ∈ [-t, -1]`.
- **Uniqueness** among `w ≤ -1`: strict antitonicity.
- **No solution elsewhere.** For `x ≥ 0`, `mulExp w < 0` whenever `w ≤ -1`. For `x < -1/e`,
  `mulExp w ≥ -1/e` on `(-∞, -1]` by antitonicity. Junk value `0` in both cases, matching
  `lambertW`.

**The construction.** As for the principal branch, `w` is the abscissa where `y = eᵘ` meets the
left branch of the hyperbola `y = x/u` (`u < 0`): on that branch the crossing condition is exactly
`u·eᵘ = x`. For `x < 0` the two curves meet twice, at `W₀(x) ∈ [-1, 0)` and at
`W₋₁(x) ≤ -1`, which coincide at `x = -1/e`. The principal proof crops the exponential to
`[-1, 0] × [0, 1]`; here crop it to

    [-n, -1] × [0, 1],    n : ℕ with -w ≤ n   (exists_nat_ge),

so only the lower root survives. The bound `n` exists by the Archimedean property. It does not
need to be computed from `x`: `PConstructible` is a `Prop`, and `(n : ℝ)` is P-constructible
by `nat_Pconstructible`. (The `y`-window `[0, 1]` is harmless. `y ≤ e⁻¹` would also force
`u ≤ -1`, but a finite `x`-window is needed anyway, because `restrict` takes four bounds.)

At `x = -1/e` both windows contain the single root `-1`. That is fine: the crossing is still a
singleton, and `W₋₁(-1/e) = W₀(-1/e) = -1`.

## 2. Where it goes

New file **`Pptc/LambertWm1.lean`**, `import Pptc.Basic`, in `namespace Pconstructible`. This
avoids touching the ~280 KB `Basic.lean` (a rebuild of it is ~60 s and invalidates every
downstream `.olean`). It reuses, unchanged, from `Basic.lean`:

- `mulExp`, `hasDerivAt_mulExp`
- `exp_PConstructibleCurve` (`y = eᵘ`)
- `hyperbola_neg_PConstructibleCurve` (`{p | p.1 < 0 ∧ p.2 = c / p.1}`)
- `nat_Pconstructible`, `neg_Pconstructible`, `zero_Pconstructible`
- `PConstructible.inter_x`, `PConstructibleCurve.restrict`

Optionally, a one-line edit to the `Basic.lean` docstring later ("not reachable this way" →
"see `Pptc.LambertWm1`"). That edit forces a `Basic` rebuild, so leave it for a batch with other
`Basic` edits, or skip it.

## 3. Declarations, in order

Each with a `-- Theorem:` line; the module docstring explains the window choice (§1).

1. `strictAntiOn_mulExp : StrictAntiOn mulExp (Set.Iic (-1))`.
   `strictAntiOn_of_deriv_neg (convex_Iic _)`, continuity as in `strictMonoOn_mulExp`;
   `interior_Iic`, then `(1 + u) < 0` and `Real.exp_pos`, `mul_neg_of_neg_of_pos`.
2. `mulExp_neg_lt {t : ℝ} (ht : 1 ≤ t) : -(2 / t) < mulExp (-t)`, or directly
   `x < mulExp (-t)` under `2/(-x) ≤ t`. Use `Real.quadratic_le_exp_of_nonneg`,
   `Real.exp_neg`, `field_simp` and `nlinarith`. This is the only lemma with real arithmetic in it.
3. `exists_mulExp_eq_le {x} (hlo : -Real.exp (-1) ≤ x) (hneg : x < 0) :
   ∃ w, w ≤ -1 ∧ mulExp w = x`. Use `intermediate_value_Icc'` on `[-t, -1]`.
4. `lambertWm1 (x : ℝ) : ℝ := if h : ∃ w, w ≤ -1 ∧ mulExp w = x then h.choose else 0`
   (`open Classical in`, docstring as for `lambertW`).
5. `lambertWm1_eq {x w} (hw : w ≤ -1) (hwx : mulExp w = x) : lambertWm1 x = w` (copy of
   `lambertW_eq` with `strictAntiOn_mulExp.injOn`).
6. `lambertWm1_mul_exp (hlo) (hneg) : lambertWm1 x * exp (lambertWm1 x) = x` and
   `lambertWm1_le (…) : lambertWm1 x ≤ -1`.
7. `lambertWm1_of_not_mem` (junk value): if `x < -1/e` or `0 ≤ x`, then `lambertWm1 x = 0`.
   Both cases: no `w ≤ -1` solves it (antitonicity / sign).
8. **`@[pconstructible] lambertWm1_Pconstructible {x} (hx : PConstructible x) :
   PConstructible (lambertWm1 x)`.**
   - Junk branch: `zero_Pconstructible`.
   - Main branch: obtain `w`, rewrite with `lambertWm1_eq`, get `n` with `-w ≤ n`, then

         hE := PConstructibleCurve.restrict exp_PConstructibleCurve (-(n : ℝ)) (-1) 0 1 …
         PConstructible.inter_x (y := Real.exp w) hE (hyperbola_neg_PConstructibleCurve hx) ?_

     The singleton proof follows the `hneg` case of `lambertW_Pconstructible` almost line
     for line. Swap `strictMonoOn_mulExp`/`Set.mem_Ici` for `strictAntiOn_mulExp`/`Set.mem_Iic`,
     and use the bounds `-n ≤ w` (from `hn`), `w ≤ -1`, `0 ≤ eʷ`, `eʷ ≤ 1`
     (`Real.exp_le_one_iff`), with `w < 0` from `w ≤ -1`.
9. Sanity checks (`example`s), as for `lambertW`:
   - `lambertWm1 (-Real.exp (-1)) = -1` (the branch point, shared with `W₀`);
   - `lambertWm1 (-2 * Real.exp (-2)) = -2`;
   - optional, to show the branches really differ: `lambertWm1 (-Real.log 2 / 2) = -2 * Real.log 2`
     while `lambertW (-Real.log 2 / 2) = -Real.log 2` (`e^{-2 log 2} = 1/4`, `e^{-log 2} = 1/2`).

## 4. Risks

- **`intermediate_value_Icc'`.** Confirm its exact form (`Icc (f b) (f a) ⊆ f '' Icc a b`) with
  `lean_hover_info` before use.
- **Lemma 2's inequality.** The algebra is the only non-template step; try it in
  `lean_multi_attempt` first.
- **Restrict-window order.** The window set is `xmin ≤ p.1 ∧ p.1 ≤ xmax ∧ ymin ≤ p.2 ∧ p.2 ≤ ymax`,
  so the `rintro` pattern is `⟨hEc, hb1, hb2, -, -⟩` as in the principal proof.
- **Imports.** `Pptc.Basic` already imports what is needed (`intermediate_value_Icc` and the
  monotonicity-from-derivative lemmas are used there). `strictAntiOn_of_deriv_neg` lives in the
  same Mathlib file as `strictMonoOn_of_deriv_pos`.

## 5. Workflow

- Iterate with `lean_diagnostic_messages` and `lean_multi_attempt` on `Pptc/LambertWm1.lean`.
  Do not run whole-project `lake build`.
- Final check: `lake env lean Pptc/LambertWm1.lean`, then `lean_verify` on
  `Pconstructible.lambertWm1_Pconstructible`. Only `propext`, `Classical.choice` and `Quot.sound`
  are allowed.
- Add the module to the umbrella import file (if `Pptc.lean` lists modules), and build that one
  narrow target only if something must import it.
- One deliverable; size estimate about 120 lines, one sitting, no subagent needed. If one is used:
  `@lean-prover`, log in `notes/lambert/HANDOFF-Wm1.md`.
