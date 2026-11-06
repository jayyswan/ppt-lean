# PLAN-offset-L3: the offset×conic crossing engine (Lean)

Read `PLAN-offset-00-overview.md` §2, A2 (`NOTES-offset-A2.md`), and `NOTES-offset-B4.md` §6 (H1).
Use `@lean-prover`. Log: `HANDOFF-offset-L3.md`.

## Why

A2 (Z-confirmed) reaches degree-20 constructible numbers by crossing a cubic-pair offset with an
ellipse, and degree-30 with a nodal cubic. The Lean statement H1 drafted in `Scratch/OffsetB4.lean`
is the "offset × conic" engine that would bank the degree-20 result: it isolates the conic
rationalization plus the finiteness interface from the existing `Offset.lean` machinery.

## Setup

Create `pptc/Pptc/OffsetConic.lean`, `import Pptc.Offset`, standard header + module doc,
`namespace Pconstructible`. Targeted imports only, never `import Mathlib`.

**Verify through the LSP**, not `lake build`.

## Target (single deliverable)

```lean
-- Theorem: a real crossing parameter of a cubic-pair offset with a conic is P-constructible.
-- `hnotid` excludes the degenerate case where the conic contains a whole offset arc (which is what
-- makes F ∘ Γ have finitely many zeros).
theorem offsetConic_cross_root_PConstructible {T : Set (ℝ × ℝ)}
    (hT : PConstructibleCurve T) {F : ℝ → ℝ → ℝ}
    {c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃ d β : ℝ}
    (hc₀ : PConstructible c₀) (hc₁ : PConstructible c₁) (hc₂ : PConstructible c₂)
    (hc₃ : PConstructible c₃) (he₀ : PConstructible e₀) (he₁ : PConstructible e₁)
    (he₂ : PConstructible e₂) (he₃ : PConstructible e₃) (hd : PConstructible d)
    {a b c e f g : ℝ}
    (hF : ∀ X Y, F X Y = a * X ^ 2 + b * X * Y + c * Y ^ 2 + e * X + f * Y + g)
    (hTzero : ∀ q ∈ T, F q.1 q.2 = 0)
    (hnotid : ∃ s : ℝ, F (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).1
        (offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d s).2 ≠ 0)
    (hreg : cubicDer c₁ c₂ c₃ β ≠ 0 ∨ cubicDer e₁ e₂ e₃ β ≠ 0)
    (hβT : offsetParam (cubicPairParam c₀ c₁ c₂ c₃ e₀ e₁ e₂ e₃) d β ∈ T) :
    PConstructible β
```

## Proof hints (verify names before use)

* `F (offsetParam γ d t) = 0`; write `w = speed γ t`, `w² = x'² + y'²`, and rationalize the conic
  with `CrossingIsolation.rationalize_mul` (PLAN-offset-L2) after clearing denominators.
* Finiteness of `{t | F (offsetParam γ d t) = 0}` is the pattern of `offsetCross_finite_roots`
  (`Offset.lean`): `Polynomial.finite_setOfPred_isRoot` on the rationalized polynomial; `hnotid`
  supplies non-identical-zero.
* Finish with `offsetCubicPair_cross_root_PConstructible` (`Offset.lean:595`), exactly as the
  scratch H1 draft indicates.

## Follow-on (optional)

State the explicit F2 instance (cubic pair `(t³+t+1, 2t³−t²+3)`, `d=2`, ellipse `4X²+9Y²=36`) as a
`PConstructible` root of the Z-recorded degree-20 polynomial. Keep it in the same file; no
irreducibility/Galois formalisation.

## Done when

`offsetConic_cross_root_PConstructible` (and the optional instance) compiles with no `sorry`, and
`#print axioms` is clean. Record in the log. Commit locally, **do not push**.
