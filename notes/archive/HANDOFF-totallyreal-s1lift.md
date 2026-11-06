# HANDOFF: exists_PC_inputs_s1

Target file: `pptc/Pptc/TotallyReal/Certificate.lean` (namespace `Pconstructible`)
Deliverable: `exists_PC_inputs_s1 {m} {αs : Fin m → ℝ} {U} ... : ∃ I : ChainBInputs m, (all six slots coordwise PConstructible) ∧ chainBtoY αs I ∈ U ∧ all six psumY (yvec αs ·) 1 = 0`.

Plan (PLAN-addendum §2.3 / §3 item E):
1. Generic `exists_PC_tuple_mem` (refactor of `exists_Pconstructible_lift` with `G` continuous).
2. Apply to `G := Φ αs hm = chainBtoY αs ∘ correctAll`.
3. Output corrected `I'`.

## Log
- 2026-09-26: created log. Starting reads.
- Added after `continuous_yvec`: `continuous_chainBtoY`, `exists_PC_tuple_mem` (fresh six-step proof, not refactoring `exists_Pconstructible_lift`), `correctSlot`/`correctAll`/`correctPhi`, `continuous_correctSlot`, `continuous_correctAll`, `continuous_correctPhi`, `psumY_yvec_correctSlot`, `correctSlot_eq_self`, `correctSlot_Pconstructible`, and `exists_PC_inputs_s1`. Now checking diagnostics.
- Fixed 3 elaboration issues: `chainBtoY (n := m)` (binder is `n`, not `m`); removed redundant `rfl` in `hfix` (rw already closed); added missing `?_` (13 conjuncts).
- `lean_diagnostic_messages`: no errors in the whole file, no warnings in the new block (3696-3932). Only the pre-existing `linter.style.emptyLine` warnings in `exists_Pconstructible_lift` remain.
- FINAL: `lake_check Pptc/TotallyReal/Certificate.lean` → exit 0, no errors; warnings only: 4 pre-existing `sorry` (lines 778, 2134, 2163, 4169) and pre-existing style/deprecation warnings elsewhere.
- FINAL: `axiom_check Pptc/TotallyReal/Certificate.lean Pconstructible.exists_PC_inputs_s1` → `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
- Declarations added (all in file, namespace `Pconstructible`): `continuous_chainBtoY` (private), `exists_PC_tuple_mem` (private), defs `correctSlot`, `correctAll`, `correctPhi`, private `continuous_correctSlot`, `continuous_correctAll`, `continuous_correctPhi`, `psumY_yvec_correctSlot`, `correctSlot_eq_self`, `correctSlot_Pconstructible`, and public `exists_PC_inputs_s1`. `exists_Pconstructible_lift` left untouched; `exists_PC_tuple_mem` duplicates its six-step argument for an arbitrary continuous `G` (permitted fallback).
- DONE.
