# PLAN-algebraic: every real algebraic number is P-constructible

**Target (Lean):**

```lean
theorem algebraic_Pconstructible {α : ℝ} (h : IsAlgebraic ℚ α) : PConstructible α
```

**Status:** wave 1 done (2026-11-04): N1a, N2, N4, G1, G2; notes in `notes/algebraic/`. Results in §6.
Wave 2 not launched.

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
| 9 | ℚ with s ∈ {1, 2} | done: covered by the nonreal-root theorem above (N2) | `Nonic/Nonic` |
| 9 | P with s ∈ {1, 2}; any totally real (ℚ or P) | **open**; for ℚ the only open case is totally real | `NOTES-general.md`, N2 |
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

## 6. Wave 1 results (2026-11-04)

- **N1a** (`N1a.md`): rational certificate for s = 3, 4 **not found yet**.
  - The chain was rewritten as 8 steps, all of degree ≤ 6; the ruling plane is replaced by two
    quadratic steps.
  - The pencil quintic is `E'(λ)/λ³`, so a rational λ* comes from a pair with v = 0.
  - The (2,2) signature needs no formalization.
  - Blocker: the rank-4 discriminant is never a rational square (~80 centres), so step R5 onward
    lives in ℚ(√d). Scoped to rational-root centres.
  - Next: centres over ℚ(√d), or isolating-interval certificates.
  - Lean breakdown: 9 files; Engine9, Resolvent9 and ChainOpen can start now. Lemma C needs a
    k-step generalization.
- **N2** (`N2.md`):
  - Rational s ∈ {1, 2} is already done.
  - The odd route at n = 9 needs `e₁ = e₃ = e₅ = e₇ = 0` (degree 105).
  - **Overshoot engines:** the crossing polynomial may have degree > 9 if `χ_τ` divides it. With a
    rational sextic graph the odd route drops to **2 conditions**: 1, τ, τ³, …, τ¹³ are
    ℚ-dependent. This locus has degree 1428 and real points in every totally real K. No ℚ-point
    has been found yet.
  - Solvable Galois groups are handled (sketch). PSL(2,8), PΓL(2,8), A₉ and S₉ remain; the list
    is from memory.
  - Rational degree-8 graphs would close the rational case; that is a `Defs` decision for the
    user.
- **N4** (`N4.md`):
  - **Gap theorem [Proof]:** a totally real sparse shape needs every gap ≤ 2, which leaves three
    6-term classes: A (odd), B (A inverted) and C {9,7,5,4,2,0} (new, no drawable crossing yet).
  - New s = 0 engines: Bézier × Neile and parabola-offset × conic through 3 known points. Each has
    2 conditions, of degree ≥ 18 and ≥ 15.
  - Ranking for s = 0: odd route > N4-2 > N4-1.
  - Scoped to the routes tried, no family keeps its condition count bounded as n grows.
- **G1** (`G1.md`):
  - No real or arithmetic resolvent-degree literature was found.
  - Wolfson, Sutherland and Heberle–Sutherland bounds are cited.
  - Realness constraints [Proof]: a t-term shape needs n ≤ 2(t−1) for totally real f, and
    Hilbert's 3-plane step needs s ≥ 4.
  - New heuristic, the **square lift** `f(y² + c)`: c controls s, at the cost of doubling the
    degree.
  - Some classical citations are unverified.
- **G2** (`G2.md`):
  - Algebraic P-curves are `Aff ∘ (offset ∘ Aff)^j (base)`; each offset layer adds 3 parameters
    while the degree roughly doubles.
  - Line crossings are versal only for D ≤ 4. The parabola offset × line has codimension 1 in the
    monic sextics.
  - Lead: offset × circle (through the circular points).

### User decisions (2026-11-04)

- `poly_graph` stays capped at degree 6. Routes that need rational degree-8 graphs are out.
- **All resources go to degree > 9 and to general strategies for extending the tower.** The
  degree-9 streams (N1b, N1-Lean, N3, N5) are parked.

### Wave 2 (launched 2026-11-04): general n

Framing for every stream:
- Write `F_{<n}` for the closure of ℚ under real roots of degree < n. By induction on n,
  auxiliary equations of any degree < n are allowed.
- The obstacles are therefore:
  - realness;
  - the degree of the variety of good Tschirnhaus elements, i.e. finding points on it with
    coordinates in `F_{<n}`;
  - the Aₙ filter, which requires one engine step that carries Aₙ.
- By a dimension count, divisibility `χ_τ | (crossing polynomial)` almost always has solutions; it
  is the *cost* of finding them that matters.

| id | question |
|---|---|
| H1 | **Incidence cost for engine families, general n.** For a crossing polynomial of degree D ≥ n (power law `x^m` with m free, against a line, conic, quartic graph, Bézier, offset or circle), study the incidence variety `{(τ, params) : χ_τ ∣ crossing}`. Give its dimension and degree, and look for low-degree or rational components (lines, linear spaces, rational curves). Tabulate cost against n for n = 9…13. Include N2's overshoot and G2's offset × circle. |
| H2 | **Real Tschirnhaus over `F_{<n}`.** Which conditions (killing p₁…p_k, divisibility patterns) can be met with real points over `F_{<n}`, as a function of n and s? Cover points on subvarieties of degree < n, polar cones, and linear spaces (Hilbert/Sylvester/Brauer, made real). Include G1's square lift as a way to manufacture nonreal pairs. |
| H3 | **Arithmetic route for rational q of any degree n.** Combine Meyer, Birch, Heath-Brown and Browning–Heath-Brown (forms in many variables) with the affine freedom of rational sextic graphs and power laws, and with overshoot. For which n does a rational (or `F_{<n}`) τ give a drawable engine when q has a nonreal root? Then the square lift for totally real q. |
| H4 | **Transcendental Galois sources.** P has elliptic integrals and their inverses (arc length, `arc_of_length`, box). Can it evaluate division values of elliptic or abelian functions, or modular or theta functions, à la Hermite–Klein–Umemura? Which non-solvable Galois groups does this reach, e.g. PSL(2,p), PSL(2,8), and any Aₙ? |
| H5 | **Crack degree 10 (and 11) concretely, by any route.** Rational with a nonreal root first, then the rest. This is the test case for H1–H3. |

**Wave 2 done (2026-11-04).** See `notes/algebraic/SUMMARY.md`.
- Headline: a route for rational decics with a nonreal root (H5), using `power_law 10` against a
  rational sextic graph. It needs a rational point on a smooth (2,3) complete intersection
  V'_K ⊂ ℙ⁸ (MI-1). The point was found for an explicit S₁₀ decic.
- General n: the bookkeeping law; real Brauer (k! < n); the elliptic ceiling at PSL(2,p).

### Wave 3 (launched 2026-11-04; user: focus on leads 3 and 4; MI-1 and the S₁₀ decic in Lean stay open)

| id | question |
|---|---|
| W1 | **Offset towers as engines.** Overshoot with towers of depth j: what does it cost to find τ, and does the number of free parameters keep pace with n? |
| W2 | **Two-graph and big-F engines.** H1's τ = R(P(τ)) (a rational sextic graph against a rotated copy of itself), and H3's F = 9 and F = 13 families, at n = 10–12: measured rank, degree, realness and search. |
| W3 | **Transcendental monodromy.** Inverse periods via offset towers; the scope of Ritt and Lattès (which polynomials are conjugate to linear maps by exp, cos or ℘); and the monodromy of transcendental crossings (sine or `exp_two` against algebraic curves). Could any of them carry Aₙ into an algebraic output? |

### Wave 2 (original proposal, superseded)

- **N1b:** find a certificate centre over ℚ(√d), or an isolating-interval certificate, for s = 3 and
  s = 4.
- **N1-Lean:** Engine9, Resolvent9 and ChainOpen, which are not blocked by the certificate. One
  worker per file.
- **N5:** totally real nonics. Use points over P-towers, not just ℚ, on N2's overshoot locus and on
  the odd variety `{e₁ = e₃ = e₅ = e₇ = 0}`.
- **N3:** P-coefficient s ∈ {1, 2}, restricted to the odd and even engines (N2's Descartes table).
- **G3:** general-n engines. Cover overshoot for general n, two-curve crossings with a power law,
  the square lift, and offset × circle.

**Wave 3 done (2026-11-05).** See `notes/algebraic/SUMMARY.md` §5.
- Offset towers and the two-graph family meet the parameter count; the cost lies in genus ≥ 1 and
  high-degree loci.
- Transcendental routes are closed, scoped.
- New positive: solvable-Galois real algebraic numbers are P-constructible (sketch).

### X1: Galois-class induction (launched 2026-11-05, Opus; user's idea)

- **Change of measure.** Induct on Galois complexity, not degree. The hypothesis is
  `A(𝒞_{<n}) ⊆ P`: every real algebraic number whose Galois group has all its composition
  factors in sections of S_m (m < n) is P-constructible.
- **Tower lemma.** Prove the hypothesis propagates, including the realness issue: real elements of
  extensions generated by complex roots.
- **Base case.** Settle it from the repo.
- **Inductive step.** Redo it with the enlarged parameter field. The test cases are W1's square
  conditions and MI-1.
- **Output.** Reduce the target to precise open statements, if possible.
- Note: `notes/algebraic/X1.md`.

**X1 done (2026-11-05).** Theorem X: the full target follows from (SR), points of the twisted
trinomial variety over ℚ^solv ∩ ℝ. (SR) is implied by a positive answer to Taylor's question, which
is open. Solvable real algebraic numbers ⊆ P [Proof]. The Galois-class base case needs (BR_n). See
SUMMARY §6.

### X2 (planned, not run; user is conserving usage)

Recast (SR) so that a Wooley/Brauer-type theorem applies (Wooley, arXiv:1501.01789: dim ≥ 2^{2^deg}
⇒ solvable points; Cor 4.6: odd degree over totally real K ⇒ K-points). Four directions:
1. a sign-tracking real Brauer/Wooley;
2. trading degree for dimension: Weil restriction, parameter-rich engines, auxiliary variables,
   overshoot;
3. odd-degree-only engine conditions, starting from the odd shape;
4. dim/deg verdict per route.

Full brief: the X2 prompt in the 2026-11-05 session.

**X2 done (2026-11-05).** See SUMMARY §7.
- Real Wooley (RW) is proved, but no existing engine lies in its range.
- (BD), a family with bounded-degree, unbounded-parameter crossings, would close all n.
- Theorem O: degrees 9–13 including totally real, conditional on a rational point of O_m.

### Y1: offset engine via support functions (proposed 2026-11-05, not launched)

**Reformulation [Proof sketch, orchestrator].**
- Offset by d is the Minkowski sum with d·disk, and linear maps commute with Minkowski sums. So
  `Aff ∘ (offset ∘ Aff)^J (base)` = affine base ⊕ Σ_j d_j·E_j, where the E_j are ellipses.
- Its point with unit normal u is x(u) = ∇H(u), with H(u) = h₀(P₀ᵀu) + Σ_j d_j·√(Q_j(u)) and
  Q_j = |P_jᵀu|². The parabola's support function h₀ is rational.
- So the offset distances d_j enter **linearly**, which is exactly the (BD) shape. All degree growth
  comes from the shape square roots √Q_j.
- Crossing with a line at normal slopes s = τ_k gives one linear equation over K ⊗ L in
  (d_1..d_J, c). With J ≈ n−1 layers, Cramer's rule plus Galois descent gives d_j ∈ L for free,
  **provided** each Q_j(τ) is a square in K ⊗ L. That is W1's condition.
- Distinct positive-definite Q_j share no branch points, so each layer adds a new double cover
  (W1/G2 genus growth).

**Questions for Y1.**
- Find τ and many shapes with Q_j(τ) a square in K ⊗ L, through rational points of the conics
  ρ² = Q(τ), the fibre product of double covers, or Mordell–Weil growth over K.
- Get bases other than the parabola: rational sextic graphs, Béziers, power laws with rational
  support functions.
- Use the circle partner: rank +2.
- Can any non-ellipse Minkowski summand be drawn? That is, a non-circular "pen" or stroke in
  PowerPoint. It would give (BD) outright.

**Y1c done (2026-11-05).** See `notes/algebraic/Y1c.md`. Scoped to the operations tested: no curved
non-elliptical Minkowski summand.
- Strokes are exact disk-pen offsets: 0.03 pt at w = 30.
- Compound lines are several offsets at once.
- The only non-disk summands are polygons (miter/square joins, highlighter ink), and they are inert
  [Proof sketch]: they act as translations.
- Bevels, contour, extrusion and soft edges are raster.
- By-products:
  - a vector stroke-outline route: opaque shadow → EMF → ungroup ×2;
  - dash ends sit at exact arclength multiples of w.
- Caveat: some stroke weights, shadow values and other settings were set via COM or typed in the
  pane. Fine for measurement, not for a construction.
- Next per plan: Y1a, the simultaneous-squares problem (Opus), if wanted.

**Y1a done (2026-11-05).** See `notes/algebraic/Y1a.md`.
- **Theorem R [Proof].** Given τ ∈ K_L and n−1 non-homothetic positive-definite forms Q_j over L
  with every Q_j(τ) a square in K_L, plus two nondegeneracy conditions, β ∈ P. The offset distances
  come from linear algebra, and totally real q is fine.
- Tower formula verified to 10⁻⁵⁰.
- End-to-end test on a totally real S₅ quintic: the parabola tower crossing works.
- **Open:** the simultaneous squares for n ≥ 7, i.e. L-points off the degenerate line on V_τ. V_τ is
  a smooth complete intersection of n−3 diagonal quadrics: K3 at n = 6, general type for n ≥ 7. τ
  may vary.
- Searches at n = 9 and 10 found nothing.
- Leads:
  - n = 6 (K3: elliptic fibrations);
  - genus-0 or genus-1 curves on V_τ;
  - the family over τ.

### Next streams (2026-11-05)

| id | status | question |
|---|---|---|
| Z1 (C) | **launched** (Sonnet) | **Additive or sweeping PowerPoint operations for (BD).** Look for any UI operation that adds geometry or sweeps a shape, giving many linear parameters at bounded degree. Candidates: Morph, 3-D models, stretchy equation glyphs, crop-to-shape, radar/surface/contour charts, untested ink pens (brush, pencil, galaxy), and anything else. Y1c already covered strokes and effects. |
| Z2 (B1) | planned | **Engine shape C = {9,7,5,4,2,0}** (N4 gap theorem; serves totally real nonics). Is there a drawable crossing that realises it, and what are the cost and realness of its conditions? |
| Z3 (B2) | planned | **Cusp/extremum engine.** Offsets of a cubic Bézier have a cusp polynomial of degree 12 that seems to carry A₁₂ (N4). Measure the rank and cost of using it as an engine (box readout of the cusp), and whether a cubic factor can be forced. |

Also noted, not scheduled:
- N1b (ℚ(√d) certificate);
- bounded-height degree-10 witnesses;
- the S₁₀ decic and radicals in Lean;
- partner curves absorbing a square root (W1);
- PSL(2,8)/PΓL(2,8) nonics;
- N3 and N5.

**Z1 done (2026-11-05).** See `notes/algebraic/Z1.md`. No (BD) family was found among the operations
tested.
- Chart smoothing is a uniform Catmull-Rom spline. It is local: each segment depends on 4 points.
- Polynomial trendlines are capped at order 6, and chart data carry only fill-handle values.
- Radar and area charts are polylines; surface and contour charts are raster.
- No vector intermediate frame of a Morph could be read.
- Curved connectors are local presets.
- Merging shapes only takes unions.
- Not measured: 3-D models (no COM insert), the equation editor (COM dropped), picture tools, the
  remaining ink pens.
