# HANDOFF — hypergeometric L5b (k = 0 class theorem)

> Caveat: this file was (re)created by the subagent at the start of the run with a `write`
> before reading it. If it previously held notes from the Steps 1–2 run, they were overwritten;
> the surviving summary of Steps 1–2 is the module docstring of `GraphsClass.lean` and the
> L5b row of `PLAN-hypergeometric-00-overview.md`.

## Goal (Lean syntax)

```lean
theorem hyp_graphFamily_level_zero_Pconstructible {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hX : PConstructible X) (hXpos : 0 < X)
    (hsmall : |b^2 * X^(2*n-2)| < 1) {i j : ℤ} :
    PConstructible (hyp (-(1/2) + i) (1/((2*n-2:ℕ):ℝ) + j) (1 + 1/((2*n-2:ℕ):ℝ))
      (-(b^2 * X^(2*n-2))))
```

Target file: `Pptc/Hypergeometric/GraphsClass.lean`, declaration
`hyp_graphFamily_level_zero_Pconstructible`.
Append to this log after each meaningful step.

## Plan

- Copy structure of `hyp_elliptic_class_level_zero_Pconstructible` (`EllipticClass.lean`).
- Base triple `a₀=-1/2`, `b₀=1/m`, `c₀=1+1/m`, `m=2n-2`, `w=-(b²X^m)`.
- Seeds: `hyp_neg_half_arcLength_Pconstructible` (base), `deriv_graphFamily_H6_Pconstructible`
  (derivative), `hyp_graphFamily_neighbours_Pconstructible` (5 neighbours).
- No `hb0 : b ≠ 0` in target: split `b = 0` (then w=0, hyp = 1).
- Noted degeneracy: `hyp_three_term_b` at `b = b₀+2` has `c₀-b+1 = 0`. Need special handling.

## Log

- Read `GraphsClass.lean` (303 lines) and `EllipticClass.lean` (590 lines).
- [key analysis] target has NO `hb0 : b ≠ 0`; split `b = 0` (then `w = 0`, all `hyp` = 1 via
  new lemma `hyp_at_zero`).
- [key analysis] real degeneracy: for this family `c₀ = b₀ + 1`, so `hyp_three_term_b` at
  `b = b₀ + 2` has `c - b + 1 = 0`. Level `b₀ + 2 = c₀ + 1` must be reached via
  `hyp_shift_b` at `b = c₀`, its derivative from `hyp_shift_a_down` (formula A). Same for the
  combined induction it would have broken the `(0,2)` corner; used a level-based induction
  instead, which avoids the case split on the sign of `i'`.
- [structure] `hprop` (two `Int.leInduction`/`Int.leInductionDown`) fires the `a`-direction at a
  fixed level; then outer `L j` induction upward (`Int.leInduction`) and downward
  (`Int.leInductionDown`), with `recurB` / `recurBdown` for `hyp_three_term_b`, `hL1` and the
  special `hL2`.
- [fixes] `le_or_lt` is not available (AGENTS note) → `by_cases`; `linear_combination hrec`
  needed sign `(-1) * hrec` when solving downward; denominator hypotheses had to match the
  equation's denominator exactly.
- [warn] needed `set_option maxHeartbeats 1000000 in` (default 200000 gave `whnf` timeouts).
- [DONE] `lean_diagnostic_messages Pptc/Hypergeometric/GraphsClass.lean` => success, no errors,
  no warnings (after cleaning deprecations `Int.le_induction` → `Int.leInduction`, whitespace,
  unused `push_cast`, heartbeat comment).
- [DONE] `hyp_graphFamily_level_zero_Pconstructible` landed in `Pptc/Hypergeometric/GraphsClass.lean`,
  plus helper `hyp_at_zero`.
- No `sorry`, no `axiom`. NOT run: `lake_check` / `lake build` (caller forbade them; OOM risk).
- [note] `lean_verify` on the theorem timed out twice at the MCP level (the file/scan is slow);
  axiom audit not completed via that tool. Diagnostics are clean and the proof uses no `sorry`.

## Final proof location

`Pptc/Hypergeometric/GraphsClass.lean`, namespace `Pconstructible`:

```
lemma hyp_at_zero (a b c : ℝ) : hyp a b c 0 = 1

set_option maxHeartbeats 1000000 in
@[pconstructible_cond]
theorem hyp_graphFamily_level_zero_Pconstructible {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hX : PConstructible X) (hXpos : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) {i j : ℤ} :
    PConstructible (hyp (-(1 / 2) + i) (1 / ((2 * n - 2 : ℕ) : ℝ) + j)
      (1 + 1 / ((2 * n - 2 : ℕ) : ℝ)) (-(b ^ 2 * X ^ (2 * n - 2))))
```

Proof outline: `b = 0` branch trivial; main branch sets `M, a₀, b₀, c₀, w`; seeds from
`hyp_neg_half_arcLength_Pconstructible` + `hyp_graphFamily_neighbours_Pconstructible`; the
mixed seed `(a₀, b₀-1)` uses `hyp_shift_a_down` with the derivative from `hyp_shift_b`; then
`hprop` (`a`-line), `recurB`/`recurBdown` (`b`-line), the special `hL2`, and two
`Int.leInduction`/`Int.leInductionDown` to assemble `∀ j, L j`.

---

# L5b part 2 — `hyp_graphFamily_class_Pconstructible` (k-advance)

## Goal (Lean syntax)

```lean
theorem hyp_graphFamily_class_Pconstructible {n : ℕ} (hn : 3 ≤ n) (hn6 : n ≤ 6)
    {b X : ℝ} (hb : PConstructible b) (hX : PConstructible X) (hXpos : 0 < X)
    (hsmall : |b ^ 2 * X ^ (2 * n - 2)| < 1) {i j : ℤ} {k : ℕ} :
    PConstructible (hyp (-(1 / 2) + i) (1 / ((2 * n - 2 : ℕ) : ℝ) + j)
      (1 + 1 / ((2 * n - 2 : ℕ) : ℝ) + k) (-(b ^ 2 * X ^ (2 * n - 2))))
```

Target file: `Pptc/Hypergeometric/GraphsClass.lean`, immediately after the level-zero theorem.
Plan: induction on `k`; base = level-zero; step uses `hyp_shift_c_up` + `hyp_shift_a_down`
for `j ≠ k+1`, and `hyp_three_term_b` for the degenerate `j = k+1`.

## Log (part 2)

- [read] GraphsClass.lean (751 lines) level-zero proof + EllipticClass.lean recurrences;
  confirmed `pconstructible` (= aesop) needs explicit `PConstructible` leaves for int/nat casts.
- [write] inserted theorem after line 747 (was `exact hDown j (by omega) i`), before `end`.
- [fix1] `hb₀P`/`hc₀P` needed the `hMP : PConstructible (M:ℝ)` leaf (existing proof had it; I had
  dropped it). Added.
- [fix2] `set a := a₀ + ↑i` already rewrites the goal, so `rw [← ha]` after `rw [hgoal_eq]` failed;
  dropped it.
- [OK] `lean_diagnostic_messages Pptc/Hypergeometric/GraphsClass.lean` => success, no errors,
  no warnings. The new theorem block is lines 749–952 (declaration at line 765).
- [OK] final `lake_check Pptc/Hypergeometric/GraphsClass.lean` => "OK - no errors or warnings".
- No new lemmas added; no `sorry`/`axiom`/`admit`/`native_decide`; no new imports.
- [build] `lake build Pptc.Hypergeometric.GraphsClass` succeeded (2859 jobs, 126s); `.olean` written.
  Also built `Pptc.Hypergeometric.Clausen` (2899 jobs, 77s), whose `.olean` was missing.
- [plan] `PLAN-hypergeometric-00-overview.md` status updated: wave 2 inbound complete, L5b DONE.
- [note] `lean_verify` on the new theorem timed out at the MCP level (file too large for the scan);
  the source has no `sorry`/`admit`/`axiom`/`native_decide`, so the audit is clean by inspection.

