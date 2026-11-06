# HANDOFF: totallyreal assembly (remove last sorry)

Goal: remove last `sorry` on `Pconstructible.exists_oddTschirnhaus` in
`pptc/Pptc/TotallyReal/Certificate.lean` (~line 5406), by reworking
`exists_b_good_of_PC_roots` (~line 5318) to use `exists_open_good7/8`.

Target statement (to prove):
```
theorem exists_oddTschirnhaus ... : ∃ b : Fin n → ℝ, ...
```

Plan: 1) rework exists_b_good_of_PC_roots; 2) prove exists_oddTschirnhaus by
`rcases hn with h7 | h8`, subst, dispatch to exists_open_good7/8.

## Log
- [start] Created log.
- Read target region 5100-5419, exists_open_good7/8 (3378/3395), centre7/8 (1292/1531),
  ChainGood (490), signatures of exists_PC_inputs_s1, stepRoots_Pconstructible,
  chainBLift_Pconstructible_of_roots, chainBLift_yvec, chainBLift_Pconstructible.
  All match the caller's sketch. Now editing.
- Edited exists_b_good_of_PC_roots (docstring + signature + body) to the new route:
  exists_PC_inputs_s1 -> stepRoots_Pconstructible -> chainBLift_Pconstructible_of_roots.
- Edited exists_oddTschirnhaus: rcases hn; subst h7/h8; dispatch exists_open_good7/8.
- First attempt used `subst n` which picked hnat (wrong direction); changed to `subst h7`/`subst h8`.
- Diagnostics errors region 5305-5420: NONE (success). Only linter.style.emptyLine warnings
  (pre-existing double-spacing style). No sorry keyword remains.
- `lake_check Pptc/TotallyReal/Certificate.lean` -> exit 0, no `declaration uses sorry`
  warning (only unrelated pre-existing warnings).
- `axiom_check Pconstructible.exists_oddTschirnhaus` -> [propext, Classical.choice,
  Quot.sound] (no sorryAx). DONE.

## Final statement (pptc/Pptc/TotallyReal/Certificate.lean:5398)
```
theorem exists_oddTschirnhaus (hn : n = 7 ∨ n = 8) {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = n) (hsep : q.Separable)
    (hcoeff : ∀ k, PConstructible (q.coeff k)) {αs : Fin n → ℝ}
    (hαs : ∀ i : Fin n, q.eval (αs i) = 0) (hnd : Function.Injective αs) :
    ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧
      Function.Injective (yvec αs b) ∧ psumY (yvec αs b) 1 = 0 ∧
      psumY (yvec αs b) 3 = 0 ∧ psumY (yvec αs b) 5 = 0
```
