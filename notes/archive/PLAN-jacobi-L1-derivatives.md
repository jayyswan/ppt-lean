# PLAN-jacobi-L1: derivatives of `am`, `sn`, `cn`, `dn` (Lean, phase 1 of 3)

Read `PLAN-jacobi-00-overview.md` §2 (F4) first. Use `@lean-prover`, following `AGENTS.md`.
Log: `HANDOFF-jacobi-L1.md`.

## Why

Phase 2 proves the addition theorem by showing that an expression has derivative zero. That
needs the four derivatives below. They are also worth having in their own right.

## Setup

Create `pptc/Pptc/JacobiAddition.lean`, with the usual header comment block (copy it from
`Jacobi.lean`), `import Pptc.Jacobi`, a `/-! # Pptc.JacobiAddition ... -/` module doc, and
`namespace Pconstructible`. Add targeted Mathlib imports only if a lemma is missing, never
`import Mathlib`.

**Verify through the LSP** (`lean_diagnostic_messages` on `Pptc/JacobiAddition.lean`).
`lake build` of new modules is currently broken on this machine (it fails reading a random
`.olean.private`), so a red build is not evidence of a bug. Do not run a whole-project build.

## Targets (in this order)

```lean
-- Theorem: the amplitude is differentiable, with derivative `dn`.
theorem hasDerivAt_jacobiAm {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiAm c) (jacobiDn c u) u

theorem hasDerivAt_jacobiSn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiSn c) (jacobiCn c u * jacobiDn c u) u

theorem hasDerivAt_jacobiCn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiCn c) (-(jacobiSn c u * jacobiDn c u)) u

theorem hasDerivAt_jacobiDn {c : ℝ} (hc : c < 1) (u : ℝ) :
    HasDerivAt (jacobiDn c) (-(c * jacobiSn c u * jacobiCn c u)) u
```

## Proof hints (verify every name with `lean_hover_info`/`lean_loogle` before use)

* `hasDerivAt_jacobiAm` is the inverse function theorem in one variable. Candidates:
  `HasDerivAt.of_local_left_inverse`, which needs (i) `ContinuousAt (jacobiAm c) u`,
  (ii) `HasDerivAt (ellipticF c) f' (jacobiAm c u)` with `f' ≠ 0`, and (iii)
  `∀ᶠ y in 𝓝 u, ellipticF c (jacobiAm c y) = y`. You have:
  * (ii) `hasDerivAt_ellipticF hc (jacobiAm c u)` (in `Basic.lean`), with derivative
    `ellipticFIntegrand c (jacobiAm c u) = (ellipticEIntegrand c (jacobiAm c u))⁻¹`, which is
    positive by `ellipticFIntegrand_pos`. The inverse of that is `jacobiDn c u` by definition
    (`inv_inv`).
  * (iii) holds everywhere by `ellipticF_jacobiAm hc`.
  * (i) is the only real work. `ellipticF c` is a continuous strictly monotone surjection
    (`strictMono_ellipticF`, `surjective_ellipticF`, and continuity from `hasDerivAt_ellipticF`).
    Build `StrictMono.orderIsoOfSurjective` and use `OrderIso.continuous` on its symm, then
    show that the symm agrees with `jacobiAm c` (both are left inverses:
    `jacobiAm_eq_of_ellipticF_eq`). Alternatively, look for a Mathlib lemma giving continuity
    of the inverse of a strictly monotone continuous surjection directly.
* `sn`, `cn`: chain rule, `(Real.hasDerivAt_sin _).comp u (hasDerivAt_jacobiAm hc u)`, then
  `ring`/`mul_comm`.
* `dn`: `hasDerivAt_ellipticEIntegrand c θ h` (in `Basic.lean`) composed with `am`. The side
  condition is `1 - c * sin² ≠ 0`, from `one_sub_mul_sin_sq_pos hc` (check the name). The
  derivative `-(2 c sin cos)/(2 Δ) · Δ` simplifies to `-c sin cos` using
  `ellipticEIntegrand_pos` (`field_simp`).

Every theorem needs a `-- Theorem: ...` line. Keep lines ≤ 100 chars. Before finishing, append
temporary `#print axioms hasDerivAt_jacobiDn` and check that only `propext`,
`Classical.choice` and `Quot.sound` appear, then delete the line.

## Done when

All four compile with zero errors and no `sorry` in `Pptc/JacobiAddition.lean`. Record the
final state in the log. Commit locally (the git root is `pptc/`) with a message saying that
verification was by LSP. **Do not push.**
