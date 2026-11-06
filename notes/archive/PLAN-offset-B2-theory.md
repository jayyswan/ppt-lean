# PLAN-offset-B2: theory — resolvent degree over ℝ, real closedness, what an engine must do

Read `PLAN-offset-00-overview.md`, `septicpaper_revised.tex`, the Hermite trace-form paragraph in
`pptc/Pptc/Basic.lean` (~l.455-490), and the closing sections of `pptc/Pptc/Offset.lean`.
Log: `HANDOFF-offset-B2.md`. Deliverable: `NOTES-offset-B2.md`. Scripts: prefix `B2-`.

## Why

The other tasks compute families. This task supplies the framework that says which families
would **suffice**, and which cannot. The questions have a long history: Hilbert's 13th problem,
Tschirnhaus reductions, resolvent degree, and essential dimension. The twist here is that
everything must be **real** and **inside a specific countable field `K`**.

## Questions

1. **The reduction for real closedness.** Take the ordered field `K ⊂ ℝ`, which has square roots
   of positives and all real roots of degree-≤6 polynomials over `K`.
   * State and prove (or cite precisely) the minimal set of target statements that would make `K`
     real closed. Start from Artin's criterion: every odd-degree polynomial has a root.
   * Use the known closure properties to cut the list down. Suppose the result holds for all odd
     degrees below `n`. Show it suffices to handle polynomials whose root field is a **primitive**
     extension (no intermediate fields). Are there further reductions via Galois theory (2-Sylow
     arguments, or reducing to a particular transitive group) that shrink the target to specific
     group-theoretic situations, e.g. only primitive groups of odd degree? Do the known septic
     results (the non-real-root case) remove some groups for degree 7 outright?
   * Deliver a clean statement: "`K` is real closed iff, for every `n`, every … of type … has a
     root in `K`", with the smallest type you can justify.
2. **Resolvent degree and Hilbert's 13th problem.** Survey, with URLs, the literature giving upper
   bounds `RD(n)`: Hamilton, Sylvester, Hilbert, Wiman, Chebotarev, Brauer; and recent work by
   Wolfson (*Tschirnhaus transformations after Hilbert*), Farb–Wolfson, Sutherland,
   Heberle–Sutherland, and Gómez-Gonzáles. Explain the "accessory irrationalities" these
   reductions use, and then:
   * **Which of those reductions are real**? That is, which work with real accessory
     irrationalities and real Tschirnhaus maps, for every real-root pattern? The totally real case
     is where the complex reductions (Bring–Jerrard, Hamilton) fail over ℝ. Is there literature
     on "real resolvent degree", Tschirnhaus maps over real closed fields, or the signature
     obstruction? Search thoroughly and report what exists.
   * Translate into the project's terms. `K` already contains degree-≤6 roots, which act like
     accessory irrationalities of degree ≤ 6. What does the theory say about the smallest
     dimension an engine family needs in order to cover general degree `n`, under the constraint
     that the accessory irrationalities are **real, of degree ≤ 6, or themselves produced by
     engines**?
3. **A formal model of "engine families".** Define an engine as a real algebraic family of
   polynomials together with real semialgebraic side conditions. The families known so far are:
   degree-6 with free coefficients; power law + graph; the nonic hypersurface; the septic
   Tschirnhaus + power law; the codim-3 decic. Prove the closure rules: cofactor, Möbius,
   Tschirnhaus, composition of engines, and parameters from earlier engines. Then:
   * Show that the set of polynomials covered is determined by (engine dimension, degree, real
     structure, solvability of the covering system).
   * State and prove an **obstruction lemma** of the Hermite type, for a general engine: when
     does a totally real target stay out of reach because some trace form is definite? Is the
     decic offset family subject to such an obstruction? (It contains polynomials with non-real
     roots, and its real structure differs from the power-law engine's.)
   * State and prove a **sufficiency lemma**. For example: "if an engine of degree `N` has
     effective dimension `N − 3` modulo Möbius, and its real locus meets every real-root-pattern
     component, then together with a rational-segment sign-change argument it covers degree `N`."
     Make it as strong as honesty allows, and locate the exact point where solvability of the
     covering system enters.
4. **Can the "no" side be settled?** Is there any conceivable argument that a specific real
   algebraic number is **not** in `K`? Consider: countability, which is useless for algebraic
   numbers; Galois / monodromy invariants of all finite construction trees, which is hard
   because offsets already give `A₁₀`; o-minimality, which is useless since everything is
   definable; and *uniform* (parametric) constructions, where monodromy of the root function over
   a region of coefficient space is an invariant. What do uniform constructions built from the
   moves compute? Do they give algebraic functions with monodromy constraints, or can they reach
   the root function of the generic septic over a totally real region? Say what can and cannot
   be proved.
5. **Where offsets fit.** Using only the facts in the overview (or your own quick computations),
   say which of the offset mechanisms (line / conic / Bézier crossings, offset×offset, chains,
   rational offsets) could in principle meet the sufficiency lemma for degree 7 and for all
   degrees, and which are ruled out by the obstruction lemma.

## Deliverable

1. The summary.
2. The real-closedness reduction theorem with its proof.
3. A literature table: result, real or complex, what it needs, URL.
4. The engine formalism with the obstruction and sufficiency lemmas, each with a full proof or a
   precisely stated gap.
5. The uniform-construction discussion.
6. A ranked list of "what an offset construction would have to achieve", which will be handed to
   the synthesis.
7. The Side discoveries and Leads sections.
