# HANDOFF — Box B11: `arc_of_length` composability (plan §3.N7)

Deliverable: research note `pptc/Pptc/NOTES-box-composability.md`. **No Lean edits, no lake.**
All reads via `read`/`rg`; all numerics via `wolfram_WolframLanguageEvaluator` (backend noted per
number in the note).

## Log
- [start] Read `PLAN-bounding-box.md` (§3.N7 at lines 283–294), `Pptc/BoxGraph.lean`,
  `Pptc/Box.lean`, `Defs.lean` (arc_of_length 375-387, arc_length 151-164, box 207-212).
- [recon] `rg` for `arcLengthOf`: no additivity lemma exists; `intervalIntegral.integral_add_adjacent_intervals`
  is used at `Basic.lean:3475,4089,4179`, `Jacobi.lean:349,405`, `EllipticFSecondSingular.lean:448`,
  `Hypergeometric/Elliptic.lean:159`. Mathlib signature at
  `IntervalIntegral/Basic.lean:1095`.
- [key] Structural conclusion: W4/B8 are theorems, not constructors; they accept arbitrary
  P-constructible start/curve data, so a two-stroke value is one W4/B8 application with a derived
  start — N7 adds no elements to `PConstructible`. Genuine new reach = the single inverse step (N1).
- [numerics] Wolfram (`WorkingPrecision -> 80`):
  - b* = A⁻¹(1/2) = 0.44633388551759072893813142528262481720135752704286437386727212215 [NC 50]; A(b*)-1/2 = 0 to 40 digits.
  - b(5/6) = 0.66853980531481528583030370971811105499750151685395 [NC 50]; two-step vs one-step differ by 0 to 59 digits.
  - tangent composition x = 0.8193378068802944789000789643424797534864 [NC 40].
  - translated-cubic composition x = 0.9250026249606502457723282611183514230256 [NC 40] = b* + A₃⁻¹(1/2),
    with A₃⁻¹(1/2) = 0.4786687394430595168341968358357266058243 [NC 40] and A₃⁻¹(1) = 0.790706893627604843078476035616379666889633851 [NC 45] matching N4.
- [verdict] Negative: composability is real but yields no new number; same-curve = single stroke at
  the sum; cross-curve candidates reduce to arithmetic or to sums of independent single-stroke values.
- [done] Note written. Proposed lemmas (not done): `arcLengthOf_add`, composition-collapse corollaries.

## Status
Note complete. No Lean changed; nothing to build.
