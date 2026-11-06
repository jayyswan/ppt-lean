# Handoff — degree-9 crossing engine

## Deliverable

New file `pptc/Pptc/ScratchNine.lean` (imports only `Pptc.Basic`, no `import Mathlib`).
It compiles cleanly: `lake_check Pptc/ScratchNine.lean` reports
`OK - no errors or warnings`.

Declaration proved:

```
Pconstructible.cubicGraph_cubic_cross_root_Pconstructible
```

Exact signature (as written in the file, `namespace Pconstructible`):

```lean
theorem cubicGraph_cubic_cross_root_Pconstructible
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ β : ℝ}
    (ha : ∀ k, PConstructible (match k with
      | 0 => a₀ | 1 => a₁ | 2 => a₂ | _ => a₃))
    (hb : ∀ k, PConstructible (match k with
      | 0 => b₀ | 1 => b₁ | 2 => b₂ | _ => b₃))
    (hc : ∀ k, PConstructible (match k with
      | 0 => c₀ | 1 => c₁ | 2 => c₂ | _ => c₃))
    (hb₃ : b₃ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hroot : cubicVal a₀ a₁ a₂ a₃ β =
      cubicVal c₀ c₁ c₂ c₃ (cubicVal b₀ b₁ b₂ b₃ β)) :
    PConstructible β
```

A helper lemma is also proved: `Pconstructible.cubicVal_identity (x : ℝ) :
cubicVal 0 1 0 0 x = x`.

## Deviation from the requested signature: `hc₃ : c₃ ≠ 0` is required

The literal statement requested (only `hb₃ : b₃ ≠ 0`, no condition on `c₃`) is **false**.
The crossing polynomial is `p t = cubicVal a t - cubicVal c (cubicVal b t)`. If `p` is
identically zero then `hroot` holds for *every* real `β`, so `β` cannot possibly be
concluded P-constructible.

Explicit counterexample to the literal statement:

* `a₀ = 0, a₁ = 0, a₂ = 0, a₃ = 1`  (so `a = t³`),
* `b₀ = 0, b₁ = 0, b₂ = 0, b₃ = 1`  (so `b = t³`, `b₃ ≠ 0`),
* `c₀ = 0, c₁ = 1, c₂ = 0, c₃ = 0`  (so `c = s`).

All coefficients are P-constructible and `b₃ = 1 ≠ 0`, while
`cubicVal a β = β³ = cubicVal c (cubicVal b β)` holds for every `β ∈ ℝ`.
Taking any non-P-constructible real `β` (they exist, since the P-constructible reals are
countable) gives a genuine counterexample.

Adding `hc₃ : c₃ ≠ 0` makes `p` have leading coefficient `-c₃ b₃³ ≠ 0`, hence `natDegree p = 9`
— precisely the degree-9 regime the engine is meant to cover, and the symmetric hypothesis to
`hb₃`. (One could weaken `hc₃` to "`p` is not the zero polynomial"; `c` genuinely cubic is the
natural coefficient-level form and is what the review's "replace the parabola by a cubic"
means.)

## Proof outline (mirrors `weierstrassCross_root_Pconstructible`, degree 6→9)

In `pptc/Pptc/ScratchNine.lean`:

* `Γ : ℝ → ℝ × ℝ := cubicPairParam a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃`, tracing `t ↦ (a t, b t)`.
* `Δ : ℝ → ℝ × ℝ := cubicPairParam c₀ c₁ c₂ c₃ 0 1 0 0`, tracing `s ↦ (c s, s)`
  (`cubicVal_identity` supplies the identity ordinate). Both are `PConstructibleCurve`s by
  `cubicPairArc_PConstructibleCurve`.
* `F (A, B) := A - cubicVal c₀ c₁ c₂ c₃ B`; `F (Γ t) = p t` where
  `p t := cubicVal a t - cubicVal c (cubicVal b t)`.
* `hΓβ : Γ β = Δ y₀` with `y₀ := cubicVal b β`, using `hroot`.
* Finiteness: `Ap := C a₃*X^3 + C a₂*X^2 + C a₁*X + C a₀`,
  `Bp := C b₃*X^3 + C b₂*X^2 + C b₁*X + C b₀`,
  `Cp := C c₃*X^3 + C c₂*X^2 + C c₁*X + C c₀`,
  `P := Ap - Cp.comp Bp`, with `P.eval = p`. `P ≠ 0` because
  `(Cp.comp Bp).natDegree = Cp.natDegree * Bp.natDegree = 3*3 = 9` (via
  `Polynomial.natDegree_comp`, `compute_degree!` using `hc₃`/`hb₃`) whereas
  `Ap.natDegree ≤ 3`; if `P = 0` then `Ap = Cp.comp Bp` forces `9 ≤ 3`.
* Rational windows `u < β < v` and `w < y₀ < z` from `exists_rat_btwn`
  (`rat_Pconstructible` for `PConstructibleCurve.restrict` bounds inside
  `crossing_Pconstructible`).
* `crossing_Pconstructible` then returns `PConstructible (Γ β).2`, i.e. `y₀`.
* Finish with `cubicVal_root_Pconstructible` on the cubic `b t - y₀` (root `β`), whose
  constant coefficient `b₀ - y₀` is P-constructible.

## Commands run and outcomes

* `lake_check Pptc/ScratchNine.lean` (which runs `lake env lean Pptc/ScratchNine.lean`) —
  final result: `exit 0`, `OK - no errors or warnings`.
* `lean_verify Pconstructible.cubicGraph_cubic_cross_root_Pconstructible` — axioms:
  `[propext, Classical.choice, Quot.sound]`, no warnings. Same for `cubicVal_identity`.
* No `sorry`/`admit`/`axiom`; no existing files were edited; no whole-project build was run.

## Caveats / next steps

* The theorem is correct and axiom-clean, but it is the corrected statement: it carries the
  extra `hc₃ : c₃ ≠ 0`. Do not delete it — see the counterexample above.
* `ScratchNine.lean` is a scratch file and is currently not imported by anything; if the
  engine is to be used it should be folded into `Pptc/Basic.lean` (with the large section
  comment) and, if a `pconstructible`-style closure lemma is wanted, tagged appropriately.
  Until then it does not affect library build targets.
* The stronger variant taking `hpne : ¬ (∀ t, cubicVal a t = cubicVal c (cubicVal b t))`
  instead of `hc₃` would cover the degenerate-`c` cases too; it was not needed for the
  degree-9 engine.
