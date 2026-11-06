# PLAN-offset-C1: the totally real septic via the offset decic engine

Read `PLAN-offset-00-overview.md`, `NOTES-offset-B1.md` (all), `NOTES-offset-B2.md` §5. Log:
`HANDOFF-offset-C1.md`; deliverable: `NOTES-offset-C1.md`.

## The question

B1 reduced the degree-7 frontier to a **square** covering system. With `u = t³+a t²+b t+c` monic,
`v' = p t²+q t+r`, `Δ = d²(A²+B²)`, the offset→line decic is
`W = u²(u'²+v'²) − Δ v'²`; a monic septic `q` is covered iff `W ≡ 0 mod q`, i.e.
`u(rᵢ)²(u'(rᵢ)²+v'(rᵢ)²) = Δ v'(rᵢ)²` at the seven roots `rᵢ`. That is **7 equations of degree ≤4
in the 7 unknowns** `a,b,c,p,q,r,Δ`. A point of this system with `Δ>0` and all data in `K` proves:
*every real root of every totally real septic over `K` lies in `K`.*

B1's evidence: over ℝ every tested totally real rational septic has a real solution with `Δ>0`,
and PSLQ at 200 digits gives `deg(Δ)≤5`, `deg(a)≤6` for all tested `q`. **This is evidence, not a
proof, and the exact elimination was never computed.**

## Questions

1. **P0 — the elimination ideal.** Compute `Elim_{a,b,c,p,q,r}(Δ)` over the field of the
   coefficients of `q`. Is its degree (in `Δ`) bounded by 6 uniformly? If yes, the septic theorem
   follows via `root_Pconstructible_le_six_coeffs`. Quantify the growth of the coefficients.
2. **P1 — the real branch.** Prove (or find a counterexample to) the existence of a real solution
   with `Δ>0` for every totally real `q`. Decide whether `Δ>0` is forced or merely observed.
3. **P2 — avoid elimination.** Find a triangular parametrization of the solution variety: from `q`
   and finitely many rational choices, a `K`-point of `(∗)` with the last condition a degree-≤6
   univariate with a certified sign change. The slack for this lives in the **conic-crossing**
   family (B1 §2: 7 equations in 14 raw parameters, solution dim ≳6), not in the square decic.
4. **P4 — negative control.** Decide whether the observed low degree is a small-Galois artefact by
   testing `q` with large Galois group, and whether the real intersection is ever empty.

## Methods (bounded, in this order)

* Re-run `B1-10-counts.py` and `B1-12-movetree.py` first to reproduce rank 7 and the 60-digit
  move tree.
* Dedicated CAS: try **Singular** or **Macaulay2** (sympy `lex` and `grevlex`, and Wolfram
  `Eliminate`/`GroebnerBasis`, all timed out in wave 1). Compute the elimination ideal in a
  prime field first, `sat`-urate the `v'=0` locus, then lift with rational reconstruction.
* Alternatively, homotopy continuation: a monodromy/total-degree solver on the square system to
  count complex solutions and track the real ones.
* Use Wolfram `CylindricalDecomposition` on the conic family's covering system for real
  feasibility by root pattern.

## Deliverable

`NOTES-offset-C1.md`: the exact elimination degree or a documented wall; the real-branch verdict;
either a proof of the totally real septic theorem or a precise statement of the remaining gap.
Tag every claim `[Lean]`/`[symbolic]`/`[numeric, N digits]`. **Never** report the septic as solved
on evidence alone.
