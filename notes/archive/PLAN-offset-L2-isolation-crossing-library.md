# PLAN-offset-L2: the isolation-only crossing lemma (Lean, library migration)

Read `PLAN-offset-00-overview.md` §2, §5, and `NOTES-offset-B4.md` §2.2. Use `@lean-prover`.
Log: `HANDOFF-offset-L2.md`.

## Why

B4 proved, in scratch, that two constructible curves meeting in an *isolated* point have
P-constructible coordinates, with no parametrization and no finiteness hypothesis
(`crossing_PConstructible_of_isolated`). This is strictly cheaper than `crossing_Pconstructible`
and is the canonical interface for A3-style offset×offset crossings. It is still only in
`pptc/Pptc/Scratch/OffsetB4.lean` (imported by nothing), so it is not yet usable by the library.
This plan moves it — with the rationalization companions — into the library.

## Setup

Create `pptc/Pptc/CrossingIsolation.lean`, `import Pptc.Basic` (and `Pptc.Offset` only if needed),
standard header + module doc, `namespace Pconstructible`. Targeted Mathlib imports only.

**Verify through the LSP**, not `lake build`.

## Targets (single deliverable: the file with all five proved)

```lean
-- Theorem: if w² = S and E + w·O = 0, then E² − S·O² = 0 (clears a square root).
theorem rationalize {E O w S : ℝ} (hS : w ^ 2 = S) (h : E + w * O = 0) :
    E ^ 2 - S * O ^ 2 = 0

-- Theorem: the sign pattern g·w + d·h = 0 rationalizes to g²S − d²h² = 0.
theorem rationalize_mul {g h d w S : ℝ} (hS : w ^ 2 = S) (hcross : g * w + d * h = 0) :
    g ^ 2 * S - d ^ 2 * h ^ 2 = 0

-- Theorem: two constructible curves meeting in an isolated point have P-constructible coords.
theorem crossing_PConstructible_of_isolated {S T : Set (ℝ × ℝ)}
    (hS : PConstructibleCurve S) (hT : PConstructibleCurve T) {x₀ y₀ : ℝ}
    (hS₀ : (x₀, y₀) ∈ S) (hT₀ : (x₀, y₀) ∈ T)
    (hiso : ∃ ε : ℝ, 0 < ε ∧ ∀ q ∈ S, q ∈ T → dist q (x₀, y₀) < ε → q = (x₀, y₀)) :
    PConstructible x₀ ∧ PConstructible y₀

-- Theorem: the exact recovery equations for a rational parametrization.
theorem rational_param_recovery {P Q D : Polynomial ℝ} {X Y t : ℝ} (hD : D.eval t ≠ 0)
    (hX : X = P.eval t / D.eval t) (hY : Y = Q.eval t / D.eval t) :
    (Polynomial.C X * D - P).eval t = 0 ∧ (Polynomial.C Y * D - Q).eval t = 0

-- Theorem: recovery through an affine-transformed offset is the base normal equation.
theorem chain_recovery {γ : ℝ → ℝ × ℝ} {d t : ℝ} {W : ℝ × ℝ} (hW : W = offsetParam γ d t) :
    (W.1 - (γ t).1) * deriv (fun s => (γ s).1) t
      + (W.2 - (γ t).2) * deriv (fun s => (γ s).2) t = 0
```

## Proof hints

* All five proofs are already written in `Scratch/OffsetB4.lean`; copy them, re-checking names
  against the library (`exists_rat_btwn`, `rat_Pconstructible`, `PConstructibleCurve.restrict`,
  `PConstructible.inter_x/inter_y`, `offsetParam_normal_eq_zero`). Do not re-derive.
* Watch the scratch file's namespace and the `Scratch` import hygiene: the new file must not
  import any scratch file.

## Done when

The file compiles with zero errors and no `sorry`; `#print axioms` on each shows only `propext`,
`Classical.choice`, `Quot.sound`. Record in the log. Commit locally, **do not push**.
