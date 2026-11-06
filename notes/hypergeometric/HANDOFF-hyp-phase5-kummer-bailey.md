# Phase 5 — Kummer & Bailey (`Pptc/Hypergeometric/KummerBailey.lean`)

Goal (Lean):
- `hyp_pfaff_half {a b c} (hc : ∀ n, c ≠ -(n:ℝ)) (hba : 0 < b - a) :
    hyp a b c (1/2) = 2^a * hyp a (c-b) c (-1)`
- `hyp_kummer {A B} (h : 0 < 1 - 2*B) (h1..h4) :
    hyp A B (1+A-B) (-1) = Γ(1+A-B)*Γ(1+A/2)/(Γ(1+A)*Γ(1+A/2-B))`
- `hyp_bailey {a c} (ha : a ≠ 1/2) (hc) (h1..h6) :
    hyp a (1-a) c (1/2) = Γ(c/2)*Γ((c+1)/2)/(Γ((a+c)/2)*Γ((1-a+c)/2))`
- `hyp_kummer_rat_Pconstructible`, `hyp_bailey_rat_Pconstructible`

Plan: read GaussSecond + GammaFunctional + GammaRational; write file; iterate with lean-lsp.

## Log
- read PLAN Phase 5 + Pfaff.lean (full API confirmed).
- verified Kummer/Pfaff-half/Bailey numerically with mpmath (both a<1/2 and a>1/2). OK.
- wrote Pptc/Hypergeometric/KummerBailey.lean with all 6 decls.
- iterated: fixed `lt_div_iff_of_neg` (needed `change`), `Real.inv_rpow` orientation
  (x⁻¹^y = (x^y)⁻¹, then rpow_neg + inv_inv), `mul_comm` direction in hdiv,
  `field_simp at hd` normalising (2+A)/2.
- removed unused `h6` from `hyp_bailey_of_one_half_lt` (it is not implied by the outer
  hypotheses for a↦1-a; it is genuinely unused in that branch).
- `hGd` derived from `h5` (Γ(1+(c-a)/2)=0 ⟹ 1+c-a = -(2m+1) is a pole), not from h2.
- Bailey final algebra: `mul_div_assoc` goes the wrong way; used explicit `hstep` by `ring`.
- `lean_diagnostic_messages`: success=true, zero diagnostics (no errors, no sorry).
- removed dead `have`s hGc/hpowne; kept hGc2/hGch (they reference h1/h2, avoiding the
  `unusedVariables` linter warnings) with a comment.
- FINAL: `lake env lean Pptc/Hypergeometric/KummerBailey.lean` -> EXIT=0.
- FINAL: lean_verify on all six declarations -> axioms = {propext, Classical.choice,
  Quot.sound}, trust=standard, no sorryAx.
- Only new file touched: Pptc/Hypergeometric/KummerBailey.lean (418 lines, <=100 cols).
- Gap: `hyp_bailey` assumes `a ≠ 1/2` (documented in the module docstring); a = 1/2 needs
  Bailey's quadratic transformation, out of scope. h5/h6 are genuinely needed (docstring
  explains the a=3/4, c=-1/4 counterexample).
