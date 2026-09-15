import Pptc.Defs

/-! # OffsetA1 — scratch headline for the offset-atlas task (imported by nothing)

The atlas `NOTES-offset-A1.md` shows that crossing the offset of a polynomial graph
`y = p(x)` with a line yields a point coordinate of degree `4n − 2` over `ℚ`
(`n = 4,5,6` give degrees 14, 18, 22).  The extraction is `crossing_Pconstructible`
(`Pptc.Basic`), so the only genuinely new Lean ingredient is that the parallel copy of a
regular arc of a polynomial graph is itself a `PConstructibleCurve`.  That is the theorem
below; its proof is the same as `offsetCubicPairArc_PConstructibleCurve` once one notes
that `fun t => (t, p.aeval t)` is injective (its first coordinate is the identity) and has
speed `√(1 + p'^2) ≥ 1`.

This file is UNPROVED (`sorry`) and must be reported as such. -/

namespace Pconstructible

/-- The parallel copy, at any P-constructible signed distance, of a regular arc of a
polynomial graph with rational coefficients (degree ≤ 6) is a constructible curve. -/
theorem offsetPolyGraphArc_PConstructibleCurve
    (p : Polynomial ℚ) (hdeg : p.natDegree ≤ 6)
    {d u v : ℝ} (hd : PConstructible d) (hu : PConstructible u) (hv : PConstructible v)
    (huv : u < v) :
    PConstructibleCurve
      (offsetParam (fun t : ℝ => (t, Polynomial.aeval t p)) d '' Set.Icc u v) := by
  sorry

end Pconstructible
