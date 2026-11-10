# HANDOFF-offinv-R7 — the d = 0 case

Progress log for stream R7 (issue 18, open item 1). Deliverable: `notes/offset-inversion/R7-dzero.md`.
Research only: no `.lean` edits, no `lake`.

- Read R3 §3.9(4)/§5.2(5), R2 Q3, R1 row 1, Defs (`exp_two`, `linearMap_PConstructibleCurve`,
  `inter_x`, `translate_y`), Basic.lean `linearMap_PConstructibleCurve` (no determinant condition).
- First framing (graph reachability): tried a branch-point/asymptotic invariant for the graph of `F₀`.
  Verified the exp-end invariant (coordinates linear in `t` as `z=e^{λt}→0`; `G` grows exponentially),
  so the graph is not a tower curve. But realised this is only a *sufficient* condition.
- Key observation: `¼sinh 2u = (e^{2u} − e^{−2u})/8` splits into a `+2` and a `−2` exponential, so
  `F₀` may be a *difference* of two `exp_two` graph functions. Verified: `g₁ − g₂ − F₀ = 0`.
- Wolfram: confirmed the affine images `M₁, M₂` of `exp_two`; `F₀' = cosh²u`; the `inter_x` root equals
  the arc-length root at `x = 1/4, 1, 2, 10, 100` to 50 digits.
- Wrote `R7-dzero.md`: §2 the exact decomposition and depth-1 construction, §3 why graph reachability
  was the wrong question, §4 the `gd` atom, §5 status.
- Updated `R3-separation.md` §3.9(4) and §5.2(5), `SUMMARY.md` §3 and §7, and added an R7 postscript to
  the plan.
