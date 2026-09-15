import Pptc.Basic

/-! # Scratch: real roots of rational nonics with a nonreal root

This file is imported by nothing. It records the final Lean statement of
`PLAN-nonic-meyer.md` and the shape of the proof, with the single mathematical gap
(Meyer's theorem / Hasse--Minkowski for rational quadratic forms) left as `sorry`.

The argument, matching `NOTES-nonic-meyer.md`:

1. If `q` is reducible, a factor has degree `≤ 8` and `root_Pconstructible_le_eight`
   finishes. So `q` is irreducible; it has a nonreal root by hypothesis.
2. Form the trace form `Q(f) = Tr (f ^ 2)` on `A = ℚ[X] / (q)`. It is indefinite because of
   the nonreal root (Hermite's signature `(r₁ + r₂, r₂)`).
3. Produce `ψ, φ ∈ ℚ[X]`, `deg ≤ 6`, with `Tr (φ (ψ x)) = Tr (φ (ψ x)) ^ 2 = 0`:
   * `r₂ ≥ 3`: take `ψ = X`; dimension count plus Meyer (or a rational radical vector);
   * `r₂ ∈ {1, 2}`: real collisions make `Q | V_ψ` indefinite on an open set, which then
     contains a rational `ψ`; Meyer gives the rational isotropic vector.
4. `R = charpoly (mult by φ (ψ x))` is `Y ^ 9 - p` with `p ∈ ℚ[Y]`, `deg p ≤ 6`
   (Newton: `e₁ = e₂ = 0`).
5. `y = φ (ψ β)` satisfies `y ^ 9 = p y`, so `y` is P-constructible by
   `powerLaw_root_Pconstructible` (`n = 9 > 6`).
6. `z = ψ β` is a root of `φ X - y` (degree `≤ 6` over the constructible reals), so `z` is
   P-constructible by `root_Pconstructible_le_six_coeffs`.
7. `β` is a root of `ψ X - z` (degree `≤ 6`), so `β` is P-constructible.

Infrastructure to reuse from `DegreeSeven.lean`: `companion7`, `companion7'_trace_pow`,
`companion7_trace_aeval`, `companion7_charpoly_aeval_isRoot`, the coefficient-killing lemma
`e₁ = e₂ = e₃ = 0`, and `isotropic_plane_trivial`. These generalise from `Fin 7` to `Fin 9`.
-/

open Polynomial Pconstructible

namespace Pptc.NonicMeyer

/-- Conjecture N, stated. The proof is in `NOTES-nonic-meyer.md`; the only missing Mathlib
ingredient is Meyer's theorem (an indefinite rational quadratic form in at least five variables
has a nonzero rational zero), which is not available at Lean 4.33. -/
theorem root_Pconstructible_of_rat_nonic_nonreal
    {q : Polynomial ℚ} (hq : q ≠ 0) (hdeg : q.natDegree = 9)
    (hrel : ∃ z : ℂ, aeval z (q.map (algebraMap ℚ ℂ)) = 0 ∧ z.im ≠ 0)
    {β : ℝ} (hroot : aeval β q = 0) : PConstructible β := by
  sorry

end Pptc.NonicMeyer
