# HANDOFF: Hasse invariant well-definedness (Aux.lean)

Goal: prove `hasseMinkowskiInv.eq_of_equivalent` (Equivalent Q1 Q2 → hasseMinkowskiInv Q1 = hasseMinkowskiInv Q2) in new file `Pptc/HasseMinkowski/HasseInvariant/Aux.lean`, namespace `Pptc.HasseMinkowski`. Record any p=2 bilinearity gaps as explicit named hypotheses; no other sorries. Produce stitch plan for `hilbertSym_padic_two_adic_eq` / `hilbertSym_padic_two_mul_left`.

Plan: read HasseInvariant.lean + RankCriteria.lean + HilbertSymbol defs; build Aux.eq_of_equivalent by induction on the Aux constructors; top-level by induction on Equivalent.
