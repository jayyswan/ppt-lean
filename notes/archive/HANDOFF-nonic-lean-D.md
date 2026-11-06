# HANDOFF: nonic main theorem (Pptc/Nonic.lean)

Goal: NEW file `pptc/Pptc/Nonic.lean`, exactly one `sorry` (Meyer gap).
Deliverables:
- `exists_tschirnhaus9 {q} (hmon) (h9) (hsep) (hrel) : ∃ ψ φ, ...` with `sorry`.
- `root_Pconstructible_of_rat_nonic_nonreal_sep ... : PConstructible β` proved.

Plan: lean_check after write; verify `Polynomial.aeval_comp` arg order.

## Log
- [start] created handoff; read NonicRecovery.lean and NonicPowerLaw.lean.
- [dep] NonicRecovery.olean was missing; built `lake build Pptc.NonicRecovery` (46s).
- [write] created Pptc/Nonic.lean with both declarations; `aeval_comp` needs implicit x,
  so final arg is `(by rw [Polynomial.aeval_comp])` not explicit application.
- [done] `lake_check Pptc/Nonic.lean` -> exit 0; sole warning: sorry at line 31
  (exists_tschirnhaus9). No blockers.

## Round 2: general (non-monic, reducible) nonic theorem
- [start] target `root_Pconstructible_of_rat_nonic_nonreal`; plan: normalise to monic q₀, use
  minpoly m; if deg m ≤ 8 use root_Pconstructible_le_eight, else m = q₀ and apply `_sep`.
- [note] no lean-lsp MCP tools this session; falling back to lake_check + mathlib_search.
- [lemmas] #checked: minpoly.monic/ne_zero/aeval/irreducible/dvd,
  IsIntegral = RingHom.IsIntegralElem (exists monic+eval₂=0), Irreducible.separable,
  Monic.natDegree_eq_zero, leadingCoeff_mul, eq_C_of_natDegree_eq_zero.
- [write] appended `root_Pconstructible_of_rat_nonic_nonreal` before section `end`.
  Fix: in `hsum` use `hh` (not `← hh`) to replace q₀ by m*h.
- [done] `lake_check Pptc/Nonic.lean` -> exit 0; sole warning is the sorry at line 38
  (inside `exists_tschirnhaus9`). Scratch CheckNonic.lean deleted. No blockers.
