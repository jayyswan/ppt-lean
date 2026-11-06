# HANDOFF-offset-B2 (append-only progress log)

- 2026-09-13 start: read PLAN-offset-00-overview.md and PLAN-offset-B2-theory.md.
- read septicpaper_revised.tex (full), Basic.lean Hermite paragraph (l.455-489), Offset.lean l.650-829 (closing sections). Created NOTES skeleton.
- literature search: Farb-Wolfson 1803.04063, Wolfson 2001.06515, Sutherland 2107.08139 & 2312.04430 (all over C); Heberle-Sutherland NYJM 2023; Gomez-Gonzales 2510.10272; casus irreducibilis (Isaacs 1985, Cox Thm 8.6.5/8.6.12, Loewy 1922). Key: no standard 'real resolvent degree'; classical RD all over C.
- B2-01 script: found totally real irreducible S7 septic f=x^7-14x^5+49x^3-36x+1 (7 real roots, cycle types force S7).
- B2-02c script: exact Hermite trace-form signatures: totally real (7,0)/(6,0); one pair (6,1)/(5,1); two pairs (5,2)/(4,2).
- proved reduction Theorem: minimal counterexample to odd-degree root splitting has primitive Galois group (block/inductive argument); K real closed iff primitive odd-degree irreducibles split.
- Lean scratch pptc/Pptc/Scratch/OffsetB2.lean created, compiles clean, axioms propext/Classical.choice/Quot.sound only.
- B2-03 script: decic dImage rank 7; PGL2-saturation rank 9 (codim 1), so Edec misses an invariant and does NOT cover general degree 10.
- NOTES-offset-B2.md written in full (reduction thm, literature table, engine formalism + 2 lemmas, no-side, offsets, ranked list, side discoveries, leads).
- status: completed.
