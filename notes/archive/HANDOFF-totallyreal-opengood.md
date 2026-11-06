# Handoff: remove sorries in exists_open_good7/8 (Certificate.lean)

Goal:
- Delete old `exists_chain_roots` (line ~1265) + WARNING docstring.
- Replace `exists_open_good7` / `exists_open_good8` sorry-proofs with the corrected statements:
  `∃ U : Set (ChainYInputs 7), IsOpen U ∧ centre7 ∈ U ∧ ∀ I ∈ U, ∃ lam x mu kappa,
   ChainGood I lam x mu kappa ∧ (∃t, chainStep1' I t ≠ 0) ∧ (∃t, chainStep2' I lam t ≠ 0)
   ∧ (∃t, chainStep3Cleared ... ≠ 0) ∧ (∃t, chainStep4' I lam x mu t ≠ 0)`
- File: pptc/Pptc/TotallyReal/Certificate.lean. Namespace `Pconstructible`.

Plan: use `exists_chain_roots_local` + small radius for injectivity; hne witnesses at c_k - ε/2.

## Log
- [start] created log. Orienting.
- Added private continuity lemmas `continuousAt_chainStep3Cleared_fixed`,
  `continuousAt_chainY_fixed` (~line 843). Compile clean.
- Rewrote exists_open_good7/8 statements+proofs to use a new generic private theorem
  `exists_open_good_of_centre` (vandermonde trick for injectivity; fixed witness offset
  `c_k - δ`; `exists_chain_roots_local` at radius ε' = min ε₀ (ρ/2)).
- Iteration 1 diags: fixed vandermonde def notation, continuous_finsetProd, hden2δ
  membership, h3₀/hV3, 𝓝→nhds.
- Iteration 2 diags: fixed implicit-arg `h heq`; hV3 simpa membership. Re-running.
- Region 3233-3505: NO errors. Full-file error diagnostics: NO errors.
- WARNING docstrings on good7/good8 replaced with short ones; `exists_chain_roots` +
  its WARNING docstring deleted. `rg sorry` now only hits exists_oddTschirnhaus (line ~5413)
  and one comment. Running `lake_check`.
- `lake_check Pptc/TotallyReal/Certificate.lean`: exit 0; the only "declaration uses `sorry`"
  warning is line 5406 (`exists_oddTschirnhaus`). All other warnings pre-existing style.
- `axiom_check`: exists_open_good7 / exists_open_good8 depend only on
  [propext, Classical.choice, Quot.sound] — no `sorryAx`.

## RESULT (done)
Final signatures (identical shape for 7 and 8):
```
theorem exists_open_good7 :
    ∃ U : Set (ChainYInputs 7), IsOpen U ∧ centre7 ∈ U ∧
      ∀ I ∈ U, ∃ lam x mu kappa : ℝ, ChainGood I lam x mu kappa ∧
        (∃ t : ℝ, chainStep1' I t ≠ 0) ∧
        (∃ t : ℝ, chainStep2' I lam t ≠ 0) ∧
        (∃ t : ℝ, chainStep3Cleared (chainP I lam) (chainQ0 I lam x)
            (t • chainW1 I lam + chainW3 I lam) ≠ 0) ∧
        (∃ t : ℝ, chainStep4' I lam x mu t ≠ 0)
```
Proved via new private `exists_open_good_of_centre` (generic in `n`), which uses
`exists_chain_roots_local` at radius `ε' = min ε₀ (ρ/2)`, a Vandermonde product for
injectivity, and a ball in the combined space `ChainYInputs n × ℝ⁴` for the nonvanishing
conjuncts. `exists_chain_roots` deleted (was sorry, no code callers).
