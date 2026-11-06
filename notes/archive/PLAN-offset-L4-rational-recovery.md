# PLAN-offset-L4: rational-curve recovery and the parabola window bijection (Lean)

Read `PLAN-offset-00-overview.md` (O6, O7), `NOTES-offset-B4.md` §3–5, `NOTES-offset-A4.md`.
Use `@lean-prover`. Log: `HANDOFF-offset-L4.md`.

## Why

A4 (Z-confirmed) uses rational (PH/parabola) offsets, whose crossings are exact polynomial systems
with **degree-1** parameter recovery — much cheaper than the cubic-pair quintic. B4 proved
`offsetParam_parabola` in scratch and identified the missing link to make rational-offset recovery
usable: the window bijection for the rational reparametrization, plus the two rational recovery
identities. This plan banks those.

## Setup

Create `pptc/Pptc/RationalRecovery.lean`, `import Pptc.Offset`, standard header + module doc,
`namespace Pconstructible`. Targeted imports only; `offsetParam_parabola` may be copied from
`Scratch/OffsetB4.lean` (do not import scratch files).

**Verify through the LSP**, not `lake build`.

## Targets (single deliverable: the file with all three proved)

```lean
-- Theorem: the offset of the parabola is a rational curve, with s = 2t + √(1+4t²) > 0.
-- (Proved in Scratch/OffsetB4.lean; copy it here as the foundation.)
theorem offsetParam_parabola (d t : ℝ) :
    offsetParam parabola d t = parabolaOffsetRat d (2 * t + Real.sqrt (1 + 4 * t ^ 2))

-- Theorem: the reparametrization s ↦ 2t + √(1+4t²) is strictly increasing with s ≥ 1, hence a
-- bijection ℝ → (0, ∞); consequently the offset arc is the rational curve on a window.
theorem strictMonoOn_parabolaS : StrictMonoOn (fun t : ℝ => 2 * t + Real.sqrt (1 + 4 * t ^ 2))
    Set.univ

theorem offsetParam_parabola_image (d a b : ℝ) (hab : a ≤ b) :
    offsetParam parabola d '' Set.Icc a b
      = parabolaOffsetRat d '' Set.Icc (2 * a + Real.sqrt (1 + 4 * a ^ 2))
          (2 * b + Real.sqrt (1 + 4 * b ^ 2))

-- Theorem: cleared-degree-≤n recovery for a proper rational parametrization.
theorem normalEq_rat_eq_zero {P Q D : Polynomial ℝ} {X Y t : ℝ} (hD : D.eval t ≠ 0) ...
```

## Proof hints

* `strictMonoOn_parabolaS`: derivative `2 + 4t/√(1+4t²) > 0` (`parabola_sqrt_pos`,
  `Real.lt_sqrt`), then `strictMonoOn_of_deriv_pos`/`strictMono_of_deriv_pos` (verify the name).
  Bound: `√(1+4t²) > |2t|`, so `s ≥ 1` (already `parabola_sqrt_pos` for `s > 0`).
* `offsetParam_parabola_image`: `Set.image_congr` with `offsetParam_parabola` and monotonicity of
  `Icc` under a strictly monotone map (`Set.Icc_image` style; check the exact name).
* `normalEq_rat_eq_zero`: clear denominators with `deriv (P/D) = (P'D − PD')/D²`
  (`deriv_div`/`HasDerivAt`); the scratch file has the statement, proof is `field_simp; ring`.

## Done when

All targets compile with no `sorry`; `#print axioms` clean. Record in the log. Commit locally,
**do not push**.
