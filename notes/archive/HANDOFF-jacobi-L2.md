# HANDOFF-jacobi-L2

## Goal

Extend `pptc/Pptc/JacobiAddition.lean` with:
```lean
theorem jacobiCn_add {c : ℝ} (hc : c < 1) (u v : ℝ) :
    jacobiCn c (u + v) =
      (jacobiCn c u * jacobiCn c v - jacobiSn c u * jacobiSn c v * jacobiDn c u * jacobiDn c v)
        / (1 - c * jacobiSn c u ^ 2 * jacobiSn c v ^ 2)

theorem jacobiAm_Pconstructible_add {c u v : ℝ} (hcP : PConstructible c) (hc : c < 1)
    (hu : PConstructible (jacobiAm c u)) (hv : PConstructible (jacobiAm c v)) :
    PConstructible (jacobiAm c (u + v))
```

## Plan

1. Orient in `Pptc/Jacobi.lean`: names for sn/cn/dn definitions, sq relations, zeros,
   `jacobiAm_Pconstructible_of_cn`, `jacobiSn/Cn/Dn_Pconstructible_of_am`.
2. Numerically sanity-check the cn addition identity.
3. Find `linear_combination` coefficients for the polynomial identity via sympy.
4. Prove `jacobiCn_add` via Euler argument (N/D constant).
5. Prove `jacobiAm_Pconstructible_add`.
6. Axiom check on `jacobiCn_add`; remove temp line; commit.

## Log

- [start] read PLAN overview + L2 brief. Created this log.
- [algebra] Verified (sympy) the cleared identity `N'·D − N·D' = 0` mod `h1..h4`.
  Found clean certificates:
  * `N' − 2c·s1·s2·P = (-c1·s2·d2)·h3 + (s1·c2·d1)·h4`, where `P = s1c1d2 − s2c2d1`.
  * `N·Q − P·D = (-c2·s2·d1)·h1 + (s1·c1·d2)·h2 + (s1·s2²·c1·d2)·h3 − (s1²·s2·c2·d1)·h4`,
    where `Q = s1c2d2 − c1s2d1`, and `D' = 2c·s1·s2·Q` by `ring`.
  Both verified = 0 by sympy.
- [names] `is_const_of_deriv_eq_zero (hf : Differentiable 𝕜 f) (hf' : ∀ x, deriv f x = 0) (x y) : f x = f y`.
  `HasDerivAt.div hc hd hx : ... ((c' * d x - c x * d') / d x ^ 2) x`.
  `HasDerivAt.comp (x) (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : HasDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x`.
- [algebra lemma] `add_deriv_zero` compiles in ScratchL2 (certificates confirmed).
- [impl] wrote full section in `Pptc/JacobiAddition.lean`.
- [fixes] `HasDerivAt.const_sub` for `fun y => w - y`; `Function.comp_def` for the chain rule;
  `Pi.mul_apply` + `ring` for the 4-factor derivative; `Pi.pow_apply` + `funext` to convert
  function-power to lambda for `sq` derivatives; positivity via a `calc` with
  `mul_le_mul_of_nonneg_left/right`.
- [VERIFY] `lake env lean Pptc/JacobiAddition.lean` -> "OK - no errors or warnings."
- [axioms] `#print axioms Pconstructible.jacobiCn_add` -> `[propext, Classical.choice, Quot.sound]`.
- [cleanup] scratch files `ScratchL2.lean`, `ScratchAxiom.lean` deleted; temp `#print axioms` removed.
- Auxiliary lemmas added: `add_deriv_zero`, `jacobiQuot_denom_pos`, `hasDerivAt_jacobiQuot` (all private).
- Main targets: `jacobiCn_add`, `jacobiAm_Pconstructible_add`.
- [commit] `86af844` "JacobiAddition: addition theorem for cn and P-constructibility under addition (L2)".
- DONE. Not pushed.
