# PLAN-algebraic: every real algebraic number is P-constructible

**Target (Lean):**

```lean
theorem algebraic_Pconstructible {α : ℝ} (h : IsAlgebraic ℚ α) : PConstructible α
```

**Status:** plan, written 2026-11-04 after a quick analysis (§1–§2). Nothing launched.

**Ground rule for this plan: do not conclude negatives.** Obstructions are recorded *scoped to
the route they block* ("this route cannot…"), never as "the target is false". A route
obstruction is labelled [Proof] only with a written proof. Otherwise it is [Heuristic].

Read first, every task:
- `pptc/Pptc/NonicReal/NOTES-general.md` and `THREE-PAIRS.md` (the earlier nonic search);
- `pptc/Pptc/TotallyReal/` module docstrings (the working odd-route machinery for n = 7, 8);
- `pptc/Pptc/Octic/PLAN.md`;
- `pptc/Pptc/Nonic/Nonic.lean` docstring.

## 1. Where we stand (inventory, 2026-11-04)

| Degree | Coefficients | Status | Where |
|---|---|---|---|
| ≤ 6 | P | done | `Basic` (`root_Pconstructible_le_six_coeffs`) |
| 7 | P | done (all cases) | `DegreeSeven`, `TotallyReal/Main` (`root_Pconstructible_deg7_coeffs`) |
| 8 | P | done (all cases) | `Octic/Main` (`root_Pconstructible_deg8_coeffs`) |
| 9 | ℚ, with a nonreal root | done | `Nonic/Nonic` (`root_Pconstructible_of_rat_nonic_nonreal`), via Meyer / Hasse–Minkowski |
| 9 | P, ≥ 3 conjugate pairs | constructed on paper, all aux degrees ≤ 6; needs realness certificates | `NonicReal/THREE-PAIRS.md` |
| 9 | P with s ∈ {1, 2}; any totally real (ℚ or P) | **open** | `NOTES-general.md` |
| ≥ 10 | — | not started | — |

**The algebraic part of P.** Write `F = P ∩ ℝ_alg`. It is a real field closed under real roots of
polynomials of degree ≤ 8 over itself. The question is whether `F = ℝ_alg`.

## 2. Quick analysis: what shapes any route

1. **ℚ coefficients suffice for the headline.** Every real algebraic number is a root of a
   rational polynomial.
   - The degree-n step only has to handle q ∈ ℚ[X]. Recovery steps may still use P coefficients
     of lower degree, which is already covered.
   - With ℚ coefficients, arithmetic tools apply: Hasse–Minkowski is already formalized,
     rational points can be used, and so can the structure of number fields. The rational nonic
     case with a nonreal root fell this way.
   - Prefer ℚ-specific arguments wherever they are easier than P-generic ones.

2. **The Aₙ filter** (NOTES-general).
   - A tower of degree-≤ 8 steps never produces A₉, or any Aₙ with n ≥ 9, as a composition
     factor. So every route to degree n needs **one drawable crossing ("engine") whose equation
     carries Aₙ**, plus a tower of cheap steps to find a Tschirnhaus element τ that puts the
     resolvent into the engine's shape.
   - Unbounded n therefore needs engines of unbounded degree. `power_law y = xⁿ` supplies those.
   - *Proof status:* argued in NOTES. Formalizing it is not needed for the positive target.

3. **Engine shape determines both the cost and the realness obstruction.**
   - *Sparse shapes* like `yⁿ = quartic(y)` need `p₁ … p_{n−5} = 0`. That includes
     `p₂ = Σyᵢ² = 0`, which is impossible for totally real fields. By Descartes, any sparse
     shape has at most about 10 real roots, so it cannot serve totally real fields for large n.
   - *The odd shape* `t·Q(t²) − c` (the engine of `TotallyReal`) has no realness obstruction. It
     needs a drawable graph of `Q` of degree (n−1)/2, or more odd power sums killed instead.
   - *Dense shapes* (crossings of two Béziers) have only one condition, but of degree ≥ 100.
     The two-cubic-Bézier map has Jacobian rank 8 on monic nonics (measured 2026-11-04). That
     means 6 invariants against 7 needed, which matches the census entry "1 condition"; it is
     not a new finding.

4. **Drawable graphs with P coefficients are the bottleneck parameter.**
   - Graphs of arbitrary P-coefficient polynomials are drawable only up to degree 4 (Lemma Q:
     depress, scale, shear).
   - Degrees 5 and 6 are drawable only up to rational invariants (an affine image of a rational
     `poly_graph` has 5 P parameters).
   - If arbitrary P-coefficient graphs of every degree were drawable, the theorem would be
     immediate: cross the graph with y = 0.
   - So the question "which algebraic curves, with how many free P parameters, are drawable?" is
     central. The one source of *unbounded* parameter counts is the **offset/affine tower**:
     non-conformal affine maps alternating with whole-curve offsets, each adding parameters
     (R2/R4 of offset inversion). Whether such towers give useful engines is unexplored.

5. **The cost of Tschirnhaus grows** [Heuristic, to be checked in stream G1].
   - Killing k power sums with auxiliary equations of bounded degree needs n ≥ G(k), where G
     grows very fast (Hamilton–Sylvester–Hilbert–Brauer, resolvent-degree literature).
   - A sparse engine needs k ≈ n − 5, and the odd engine with a quartic graph needs k ≈ n/2.
   - So for general n, purely generic algebra cannot carry those routes. Unbounded n needs
     extra structure: arithmetic (ℚ), real geometry, or engines with growing parameter counts.
   - Degree 9 is *not* blocked by this. Its routes are concrete.

## 3. Two tiers

- **Tier 1: degree 9, everything.** First for ℚ coefficients, which is enough for "every real
  algebraic number of degree ≤ 9", then for P coefficients. This is a concrete frontier with prior
  work, and a strong result on its own.
- **Tier 2: all n.** A research programme. It needs a route whose cost does not explode:
  - arithmetic over ℚ;
  - engines with growing parameter counts;
  - or a transcendental route.

  Tier 2 runs in parallel at the level of theory, so that Tier 1's methods are chosen with
  generalization in mind.

## 4. Streams

**Rules for all streams.**
- Use Wolfram for every number and identity, one self-contained call per computation. Python
  only as a fallback, and label it.
- Label every claim [Proof], [Wolfram], [Heuristic] or [Open].
- No `Defs.lean` changes.
- Research streams write `notes/algebraic/<id>.md`, with a findings summary first and "Other
  things noticed" last. They keep a log in `HANDOFF-alg-<id>.md` at `C:\dev\Powerpoint\lean`.
- Lean streams use `@lean-prover` discipline: lean-lsp loop, no whole-project build, one
  narrow target, no `sorry`. They commit locally and never push.
- Read §1–§2 and the prior notes before starting, and do not repeat their measured results.

### Tier 1 (degree 9)

| id | kind | question | depends on |
|---|---|---|---|
| N1 | Lean + certificate | **Formalize s ≥ 3 real nonics** (`THREE-PAIRS.md`): the rational realness certificates for s = 3 and 4, modelled on `TotallyReal/Certificate.lean`, then the Lean chain (engine `power_law 9` × quartic graph, recovery via the octic theorem). | — |
| N2 | math (ℚ focus) | **Rational nonics with s ∈ {0, 1, 2}, using arithmetic.** For q ∈ ℚ[X] the Tschirnhaus varieties are defined over ℚ. (a) Odd route: find ℚ-points or low-degree points on `{S₁ = S₃ = S₅ = S₇ = 0}` ⊂ ℙ⁸ using number-field structure: subfields, automorphisms, norm forms, the trace form's Hasse invariants. Try families like `τ = f(α)` with f of low degree. (b) For s = 1, 2: does Meyer (rank ≥ 5 indefinite) or Hasse–Minkowski give `p₂ = 0` plus further conditions in the rational case where P-generic methods failed? (c) Record every partial class reached, e.g. "totally real nonics with a rational point on V". | — |
| N3 | math (P coefficients) | **s ∈ {1, 2} real nonics.** Pursue the conic route of NOTES result 3 (y⁹ engine, s = 2: real conics exist, 2 of 12). Reduce the conic construction's 24-solution system using special choices, as the octic certificate did. For s = 1, characterize the degenerate real lines. | — |
| N4 | math (engine census, extended) | **New engines from this session's curve knowledge.** Measure, as in the NOTES census (conditions, their degrees, realness, Galois group of the cost equation): (a) whole-curve **offsets** (offset parabola / power law / Bézier × line, × power law); (b) **rational-exponent power laws**, which give shapes like `Q(t^b) − c·t^a`: enumerate sparse patterns with no `p₂` condition; (c) **box/extremum engines**: critical-point equations of affine images of drawable algebraic curves and their offsets (derivative shapes); (d) **affine–offset towers** of depth 2–3: parameter counts, crossing degrees, and Jacobian rank of the crossing-polynomial map on monic nonics after Tschirnhaus normalization. Rank them by cost for s = 0. | — |
| N5 | math | **Totally real nonics via the odd route, beyond lines.** NOTES showed lines are no shortcut. Look for points of the (3,5,7) complete intersection `{S₁ = S₃ = S₅ = S₇ = 0}` off the pairing ℙ³'s using conics, rational surfaces, or ℚ-structure (with N2). Any new engine from N4 that admits s = 0 cheaply supersedes this. | N4 partially |

### Tier 2 (all n)

| id | kind | question | depends on |
|---|---|---|---|
| G1 | literature | **Tschirnhaus and resolvent-degree literature, with exact citations**: Hamilton, Sylvester, Hilbert (degree 9 → 4 parameters), Brauer, Chebotarev, Wolfson ("Tschirnhaus transformations after Hilbert"), Heberle–Sutherland bounds; real and arithmetic variants; essential dimension; "fewnomial" and sparse-resolvent results; Umemura/Thomae (theta constants) and Mellin/Sturmfels (A-hypergeometric) solutions of general equations. For each: what it gives for P (which degrees, at what auxiliary degree) and what it needs. | — |
| G2 | math | **Drawable algebraic curves and their parameter counts.** Characterize, with proofs where possible, the algebraic curves `PConstructibleCurve` can reach from the constructors: affine images, Béziers, power laws, offsets, towers. How many free P parameters at each degree? Which P-coefficient polynomial graphs are drawable? This is the bottleneck quantity from §2.4. | — |
| G3 | math | **General-n engine search.** Using G2, look for an engine family whose number of conditions stays bounded, or grows slower than the Tschirnhaus capacity, as n grows. Candidates: offset towers, crossings of two rotated power laws, power law × Bézier, iterated box/extremum constructions. Test versality numerically for n = 9…13 (Jacobian rank of the crossing-polynomial map modulo Tschirnhaus), and count real crossings for totally real targets. | G2 |
| G4 | math | **Route constraints, scoped.** Make the Aₙ filter, the Descartes realness bounds and the parameter-count bounds precise as statements about *classes of routes*. The aim is to know exactly what an all-n route must look like. These are not conclusions about the target. | G1, G2 |
| G5 | math (low priority) | **Transcendental routes to algebraic numbers.** Can P evaluate the special functions in G1's general-equation formulas: hypergeometric pFq at algebraic arguments for trinomials (Mellin), or theta constants (Umemura)? Gamma at rationals and closed-form ₂F₁ are already available. NOTES argued that `arc_of_length` inverts one integral at a time; test that argument. | G1 |

## 5. Order

- **Wave 1** (all independent): N1 (Lean), N2, N4, G1, G2.
- **Wave 2:** N3 and N5 (taking N2/N4 results), then G3 (taking G2).
- **Wave 3:** G4, G5 if warranted. Then the orchestrator writes `notes/algebraic/SUMMARY.md`:
  - degree-9 status by case;
  - the best general-n route candidate;
  - a Lean roadmap.
- **Lean:** each degree-9 case that closes on paper gets its own Lean stream after N1 sets the
  pattern.
