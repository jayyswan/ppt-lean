# PLAN-offset-L1: the polynomial-graph offset arc is a constructible curve (Lean)

Read `PLAN-offset-00-overview.md` §1–2 first. Use `@lean-prover`, following `AGENTS.md`.
Log: `HANDOFF-offset-L1.md`.

## Why

A1 (Z-confirmed) showed that offsetting a degree-`n` polynomial graph and crossing a line gives
a point coordinate of degree `4n−2` (14, 18, 22 for `n=4,5,6`), directly through
`crossing_Pconstructible`. The only non-library ingredient is that the parallel copy of a
regular graph arc is itself a `PConstructibleCurve`; the wave-1 statement
`offsetPolyGraphArc_PConstructibleCurve` in `pptc/Pptc/Scratch/OffsetA1.lean` is `sorry`. Banking
it makes the degree-14 number a library theorem.

## Setup

Create `pptc/Pptc/OffsetPolyGraph.lean` with the standard header, `import Pptc.Offset`, a
`/-! # Pptc.OffsetPolyGraph ... -/` module doc, and `namespace Pconstructible`. Targeted Mathlib
imports only, never `import Mathlib`.

**Verify through the LSP** (`lean_diagnostic_messages` on `Pptc/OffsetPolyGraph.lean`), not
`lake build`. If the `lean_*` tools are missing, use the single-file `lake_check` fallback.

## Target (single deliverable)

```lean
-- Theorem: the parallel copy, at any P-constructible signed distance, of a regular arc of a
-- polynomial graph with rational coefficients (degree ≤ 6) is a constructible curve.
theorem offsetPolyGraphArc_PConstructibleCurve
    (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 6)
    {d u v : ℝ} (hd : PConstructible d) (hu : PConstructible u) (hv : PConstructible v)
    (huv : u < v) :
    PConstructibleCurve
      (offsetParam (fun t : ℝ => (t, Polynomial.aeval t p)) d '' Set.Icc u v)
```

## Proof hints (verify every name with `lean_hover_info`/`lean_loogle` first)

* The proof generalises `offsetCubicPairArc_PConstructibleCurve` (`Pptc/Offset.lean`) verbatim.
  The tracing `γ := fun t => (t, p.aeval t)` is smooth (`ContDiff` of polynomials), its first
  coordinate is the identity (so `InjOn γ (Icc u v)` is immediate), and
  `speed γ t = √(1 + (p′ t)²) ≥ 1 ≠ 0`, so `hreg` is free.
* `hsub : γ '' Icc u v ⊆ Γ_p` is definitional once `Γ_p` is the `poly_graph` set; check
  `Defs.lean`'s `poly_graph` unfolding and the `PConstructibleCurve.poly_graph` constructor.
* `hC1` follows from continuity of `p.derivative`.
* Substitute `hdeg` (and `Polynomial.natDegree` bookkeeping) only where the constructor needs the
  degree-≤6 bound.

## Follow-on (optional, only if the above is clean)

State the explicit degree-14 instance as a `PConstructible` statement for the real root of the
Z-recorded degree-14 minimal polynomial `65536 X¹⁴ − 262144 X¹² + … − 150847`; keep it in the same
file. Do **not** attempt to formalise irreducibility/Galois — that is not the deliverable.

## Done when

`offsetPolyGraphArc_PConstructibleCurve` compiles with zero errors and no `sorry`, and
`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`. Record the final state in
the log. Commit locally (`pptc/`), message saying verification was by LSP. **Do not push.**
