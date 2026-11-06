# HANDOFF — nonic WP4 (Pptc/NonicTschirnhaus.lean)

Goal:
- `spread_rat_cast`: for rational ψ, v,
  `spread q (fun j => (ψ j : ℝ)) (fun k => (v k : ℝ))
     = ((∑ i, ∑ j, v i * gramOf (aeval (companion9' q) (polyOfVec9 ψ)) i j * v j : ℚ) : ℝ)`
- `tschirnhausDatum_of_signs_rat` (hypothesis form)
- `exists_tschirnhaus9_of_real_signs` (hypothesis form)
- `tschirnhausDatum_of_nonreal` (only if `exists_real_signs` present)

Plan: g(ρ) = p_v(ψ(ρ)) with p_v = ∑ v_k X^{k+1}, ψ = polyOfVec9.
`gram_eq_trace_shift`, `aeval_comp`, `companion9_trace_pow_aeval` k=1,2,
convert roots Finset→Multiset sum, then `.re` of a rational cast.

## Log
- [start] read PLAN WP4, NonicMeyer (gramOf/polyOfVec9/gram_eq_trace_shift/
  companion9_trace_pow_aeval/tschirnhausDatum_of_signs/exists_tschirnhaus9_of_datum),
  NonicWitness (spread/spreadCore/exists_rat_signs). `exists_real_signs` NOT yet present.
- [scratch] NonicWitness was mid-edit -> prototyped in Pptc/ScratchWP4.lean against
  NonicMeyer with local copies of spread/spreadCore/roots_nodup. GETS: `map_sub`,
  `map_div₀`, `map_pow` DO rewrite `algebraMap ℚ ℂ`; `norm_num` kills `algebraMap 9`;
  `Complex.ofReal_ratCast` + `Complex.ofReal_re` cast `.re`; `Finset.sum_eq_multiset_sum`
  + `Multiset.toFinset_val` + `Multiset.dedup_eq_self.mpr` bridge roots Finset/Multiset.
  Scratch FULLY COMPILED (spread_rat_cast + both wrappers), then deleted.
- [write] Pptc/NonicTschirnhaus.lean: polyOfVec9_map_eval, polyOfVec9_natDegree_le,
  spreadCore_eq_of_algebraMap, spread_rat_cast, tschirnhausDatum_of_signs_rat,
  exists_tschirnhaus9_of_real_signs. (Names `v₋/v₊` do not parse in Lean; used `vm/vp`.)
- [build] `lake build Pptc.NonicWitness` OK (needed its .olean for the import).
- [lsp] lean_diagnostic_messages Pptc/NonicTschirnhaus.lean -> success (no errors/warnings).
- [note] `exists_real_signs` STILL ABSENT from NonicWitness (worker not done), so
  `tschirnhausDatum_of_nonreal` omitted, per instructions. `exists_tschirnhaus9_of_real_signs`
  uses `exists_rat_signs hs` (the current signature `(h : ∃ real signs)`); if the worker
  changes `exists_rat_signs` to `(hmon h9 hsep hrel)` this call must be adapted.
- [update] worker then landed `exists_real_signs {q} (hmon h9 hsep) (hrel) : ∃ real signs`
  (NonicWitness:733); `exists_rat_signs` kept the old `(h : ∃ real signs)` signature.
- [add] `tschirnhausDatum_of_nonreal := tschirnhausDatum_of_signs_rat hmon h9 hsep
  (exists_rat_signs (exists_real_signs hmon h9 hsep hrel))`  [note: user's literal body
  `exists_rat_signs hmon h9 hsep hrel` does not typecheck with this `exists_rat_signs`;
  the composed form matches their "exists_real_signs -> exists_rat_signs" description.]
- [build] `lake build Pptc.NonicWitness` OK (2nd try, after worker finished).
- [final] `lake_check Pptc/NonicTschirnhaus.lean` -> "OK - no errors or warnings".
  Declarations: polyOfVec9_map_eval, polyOfVec9_natDegree_le, spreadCore_eq_of_algebraMap,
  spread_rat_cast, tschirnhausDatum_of_signs_rat, exists_tschirnhaus9_of_real_signs,
  tschirnhausDatum_of_nonreal. No sorry/axiom. Scratch deleted. DONE.
