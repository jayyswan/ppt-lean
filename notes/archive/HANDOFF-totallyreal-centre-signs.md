# HANDOFF: TotallyReal centre7_chain_signs / centre8_chain_signs

## Goal (Lean syntax)
Two sorry-free theorems in `Pptc/TotallyReal/Certificate.lean`:

```lean
theorem centre7_chain_signs :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ δ, 0 < δ → δ < ε → chainStep1' centre7 (centre7roots.1 - δ) *
          chainStep1' centre7 (centre7roots.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε → chainStep2' centre7 centre7roots.1 (centre7roots.2.1 - δ) *
          chainStep2' centre7 centre7roots.1 (centre7roots.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε → chainStep3' centre7 centre7roots.1 centre7roots.2.1 (centre7roots.2.2.1 - δ) *
          chainStep3' centre7 centre7roots.1 centre7roots.2.1 (centre7roots.2.2.1 + δ) < 0) ∧
      (∀ δ, 0 < δ → δ < ε → chainStep4' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
            (centre7roots.2.2.2 - δ) *
          chainStep4' centre7 centre7roots.1 centre7roots.2.1 centre7roots.2.2.1
            (centre7roots.2.2.2 + δ) < 0)
```
and identical `centre8_chain_signs` with centre8/centre8roots.

## Plan
1. Read `exists_chain_roots_local` (~line 879) and `SignChange.lean` lemmas.
2. Add private helper `signChange_forall_small_of_factorization` in Certificate.lean.
3. Exhibit exact factorizations for step1 (quadratic), step2 (linear), step4 (quartic),
   step3 (rational with denominator cube).
4. Combine at a common ε.

## Log
- [start] created log; about to orient.
- Located `exists_chain_roots_local` (~879), `SignChange.lean` lemmas,
  centre7/8 defs and roots (1312-1743).
- Added to Certificate.lean: `exists_forall_signChange_of_factorization` (uniform `∃ε ∀δ`
  version), `psumY_add_smul_five`, private `yConicY_add_smul_right'` (because the public one
  is defined *later* than the insertion point), and centre7 step1/step2/step4 sign lemmas.
- Diagnostics region 1746-2010: clean (no errors, no warnings).
- Added step-3 machinery for centre7: `centre7Step3Den`, `centre7Step3H` (explicit quintic
  cofactor of `chainStep3Cleared`, computed with Wolfram; H7(8064/617) =
  -108084339737784597018125/8236327287823872, matching the plan's step-3 derivative),
  `centre7_step3_cleared`, `centre7_step3_sign`. Added `centre7_chain_signs`.
  Key gotcha: `norm_num` must be given the *whole* unfold list in one call (incl.
  `ymoment2Y`); a preceding `simp only` leaves `![...] 2` vector indices unreduced and
  `ring` then times out.
- Diagnostics region 1746-2135: clean.
- Added centre8 analogues (step1/2/4 + `centre8Step3Den`/`centre8Step3H` from Wolfram,
  H8(-5322/2915) = -98878323721972460544/179928739375) and `centre8_chain_signs`.
- Diagnostics region 2135-2390: clean. Both headline theorems elaborated.
- Final signatures:
  `theorem centre7_chain_signs : ∃ ε : ℝ, 0 < ε ∧ (∀δ,0<δ→δ<ε→ ...) ∧ ...` (4 clauses)
  `theorem centre8_chain_signs : ...` (same shape, centre8).
- No changes to SignChange.lean (private helper `exists_forall_signChange_of_factorization`
  lives in Certificate.lean).
- FINAL `lake_check Pptc/TotallyReal/Certificate.lean`: exit 0. The only `sorry` warnings
  are the 4 pre-existing ones (lines 1264, 3257, 3286, 5292). All other warnings (lines
  345, 2801, 3024, 3047, 3420, 3428, 3513, 3521, 3736, 4206, 4207, 4763) are pre-existing
  and lie outside the inserted region 1746-2390; none are introduced by this work.
- FINAL `axiom_check`:
    Pconstructible.centre7_chain_signs: [propext, Classical.choice, Quot.sound]
    Pconstructible.centre8_chain_signs: [propext, Classical.choice, Quot.sound]
  (no `sorryAx`).
- DONE.
