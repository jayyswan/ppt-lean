# PLAN-algebraic: every real algebraic number is P-constructible

**Target (Lean):**

```lean
theorem algebraic_Pconstructible {α : ℝ} (h : IsAlgebraic ℚ α) : PConstructible α
```

**Status:** wave 1 done (2026-11-04): N1a, N2, N4, G1, G2; notes in `notes/algebraic/`. Results in §6.
Wave 2 not launched.
**2026-11-17:** the separate "Real Algebraics" project (sessions 1–24) is imported in `RA.md`;
its effect on the degree-9 push is in `PLAN-degree9.md` §9 and `SUMMARY.md` §12.

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
| Y1b | math (arithmetic/descent) | **Square descent and variable-affine offset towers (added 2026-11-10; done 2026-11-10: scoped negative).** The general-method attack on Y1a's simultaneous-squares condition: can the rank-one square be deformed to nondegenerate positive-definite forms over L? Answer: the deformation is the whole PD cone, so Y1b.1 = the first step of SS; there is no H¹(L,μ₂) class; the pencil curve is the K-twist of (ℤ/2)ⁿ with t = 0 the S_n-resolvent scheme. See `Y1b.md`. | Y1a, G3 |
| W4 | math + Lean | **Text-warp engines (added 2026-11-10).** The new `PConstructibleCurve.text` constructor gives new algebraic curve families (egg, piriform, offset egg) with P parameters. Measure them as engine components: crossing degrees, condition varieties, F-points, and whether they close or relax an open n = 9–12 case. See `WARP.md`. | N4, G2, H3 |
| X1L | Lean | **Formalize Taylor ⇒ R_alg ⊆ P (X1 Theorem X).** Prove the conditional theorem from a trinomial lift, using the already-proved `root_Pconstructible_of_solvable_gal` and a polynomial-gcd recovery; collect weaker point-existence hypotheses (degree ≤ 8, real quadratic, 0-cycle, P-tower). See `PLAN-taylor-lean.md`. | X1, `Pptc/Solvable/Main.lean` |

## 5. Order

- **Wave 1** (all independent): N1 (Lean), N2, N4, G1, G2.
- **Wave 2:** N3 and N5 (taking N2/N4 results), then G3 (taking G2). **Y1b.1 is done** (2026-11-10):
  scoped negative, see `Y1b.md`. Y1b.4 is not launched; Y1b.2 is vacuous and Y1b.3 is answered.
- **Wave 3:** G4, G5 if warranted (Y1b.4/Y1b.5 no longer apply in the planned form). Then the orchestrator
  writes `notes/algebraic/SUMMARY.md`:
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
SUMMARY §6. **Lean plan:** `PLAN-taylor-lean.md` formalizes the conditional theorem
Taylor/trinomial point ⇒ `R_alg ⊆ P`; `Pptc/Solvable/Main.lean` already proves the solvable-real
input. The P half (T0–T2) does not wait on the open geometry.

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
  may vary. **Y1b** (added 2026-11-10) attacked this by deforming the rank-one square; done
  2026-11-10 with a scoped negative (`Y1b.md`, §Y1b below).
- Searches at n = 9 and 10 found nothing.
- Leads:
  - n = 6 (K3: elliptic fibrations);
  - genus-0 or genus-1 curves on V_τ;
  - the family over τ.

### Y1b: square descent and variable-affine towers (2026-11-10, done: Y1b.1 negative)

**Y1b.1 done (2026-11-10).** See `notes/algebraic/Y1b.md`. Verdict: the rank-one deformation is
not a descent condition and does not weaken SS.
- The conic \(r^2 - Q_{B_1}(\tau)t = \ell(\tau)^2\) is smooth and has the \(K_L\)-point \((0,\ell)\)
  with \(t = 0 \in L\) already; the \(H^1(L,\mu_2)\) class is zero. The \(t \in L\) condition is the
  pencil curve \(X_C \subset V_\tau\), a \((\mathbb{Z}/2)^n\)-cover of the \(t\)-line of genus
  \(1 + (n-3)2^{n-2}\) (129, 321, 769 at \(n = 7, 8, 9\)).
- **Equivalence:** every positive-definite form is \(B_0 + tB_1\) with \(B_0 = \ell\ell^T \succeq 0\)
  and \(t > 0\). So Y1b.1 \(\Leftrightarrow\) \(V_\tau(L)\) meets the positive-definite chamber, the
  first step of SS. Varying \(B_1\) sweeps \(V_\tau\).
- **Arithmetic:** the cover is the \(K\)-twist of the split \((\mathbb{Z}/2)^n\)-cover; the fibre at
  \(t = 0\) is the \(S_n\)-resolvent scheme of \(q\) (components of degrees \(\binom{n}{k}\); the
  \(k = 1\) component is \(K\) itself [Wolfram \(n = 5\)]). So the arithmetic Galois closure has
  \(S_n\) as a quotient and is not solvable for \(n \ge 5\); A1's Theorem G (solvable step) does
  not apply, and no Kummer vanishing produces a point.
- **Scoped negative:** for \(L = P\) there is no pencil component beyond the trivial one reachable by
  the free constructions. Y1b.4 not launched; Y1b.2 vacuous (shapes were already free); Y1b.3
  answered (the obstruction is the \(S_n\)-torsor \(K/\mathbb{Q}\), not a \(\mu_2\)-class).
- By-products: the exact conic and parametrization; the pencil curve and its genus; the
  identification with Z5's \(\pi: V_\tau \to \mathbb{P}^2\) picture; the resolvent table; a
  correction to the applicability clause of A1 Theorem G (check the arithmetic closure, not the
  geometric monodromy).


This is the general-method attack. Y1a's Theorem R reduces all n to two ingredients:

1. τ ∈ K_L;
2. J ≥ n−1 pairwise non-homothetic positive-definite forms Q_j over L with every Q_j(τ) a square
   in K_L.

The geometry of \(V_\tau\) is already understood: a smooth complete intersection of \(n-3\)
diagonal quadrics, K3 at \(n=6\), general type for \(n\ge 7\). The open problem is **arithmetic**,
not geometric. Fixed engines (egg, piriform, offset egg, text warp) add a constant number of
parameters and cannot change the asymptotics; Y1b is the stream that tries to make the square
hypothesis constructive.

**Core question.** Can the degenerate (rank-one) square be deformed to nondegenerate
positive-definite forms over \(L\)?

- Take \(B_0=\ell\ell^T\) with \(\ell(\tau)\neq0\); then \(Q_{B_0}(\tau)=\ell(\tau)^2\) is a
  square.
- For \(B_t=B_0+tB_1\), with \(B_1\) positive definite and \(t>0\), \(B_t\) is positive definite.
  The square condition \(Q_{B_t}(\tau)=r^2\) is a conic over \(K_L\) with the \(K_L\)-point
  \((t,r)=(0,\ell(\tau))\).
- Ask whether it has a point with \(t\in L\), \(r\in K_L\), and \(B_t\) positive definite. This is
  a **Kummer/descent** condition, not a real-geometry condition. The first job is to compute the
  obstruction for \(n=7,8,9\).

**Why it could work.** The conic has a \(K_L\)-point; the rank-one boundary is a square. If the
\(t\)-coordinate can be chosen in \(L\), we get one nondegenerate square form. Varying \(B_1\)
gives non-homothetic forms, and \(J\ge n-1\) of them feed Theorem R. The rank-one line is the
only obvious source of \(K_L\)-points, so the whole general method may hinge on this deformation.

**Why it could fail.** The conic's \(L\)-points may be obstructed by a nontrivial Kummer class;
the \(t\)-coordinate may lie in \(K_L\setminus L\) for every \(B_1\). Then the distance-only tower
has a scoped obstruction, and the fallback is variable affine layers, overshoot, or a new pen.
The parabolic base remains the right base: the square condition is about the affine ellipses, not
about the base curve, so the warp egg is not a shortcut here.

**Tasks.**

| id | model | question / deliverable |
|---|---|---|
| Y1b.1 | math/computation (Wolfram or Magma) | **DONE 2026-11-10: scoped negative.** See `Y1b.md`. The conic is smooth with the \(L\)-point \((0,\ell)\) already; \(t\in L\) defines the pencil curve \(X_C\subset V_\tau\) of genus \(1+(n-3)2^{n-2}\); the deformation family is all positive-definite forms, so Y1b.1 = the first step of SS. The obstruction class is the \(S_n\)-torsor \(K/\mathbb{Q}\): the \(t=0\) fibre is the \(S_n\)-resolvent scheme. |
| Y1b.2 | math (parameter count) | **DONE 2026-11-10: vacuous.** The shapes were already free (Theorem R quantifies over all \(B_j\)); the square conditions are not equations on \(B_j\). The only constraint is \(J+2\ge n\); kernel dimension \(J+2-n\). Nothing to absorb. |
| Y1b.3 | math (arithmetic) | **DONE 2026-11-10: negative.** No \(H^1(L,\mu_2)\) class exists (the conic is split at \(t=0\)). The correct statement is \(X_C(L)\); the arithmetic closure has \(S_n\) as a quotient, so no Kummer vanishing applies. Includes a correction to A1 Theorem G's solvability clause. |
| Y1b.4 | math (end-to-end) | **Not launched** (no input from Y1b.1/Y1b.3). |
| Y1b.5 | fallback | Overshoot and variable-shape layers are untouched by this negative; a different base or circle partner remains the fallback. No mechanism found from the rank-one pencil. |

**Order.** Y1b.1 first: it is one computation and decides whether the deformation is real.
Y1b.2 and Y1b.3 can run in parallel; Y1b.4 only after a positive Y1b.1/Y1b.3.

**Kill criteria (scoped).** If every tested \(B_1\) gives no positive-definite \(L\)-point and the
obstruction is nonzero, record a scoped obstruction to the distance-only offset tower; do not
conclude anything about the target. If the deformation works, proceed to Y1b.4; no negative about
`algebraic_Pconstructible` follows from Y1b.

**Cost.** Y1b.1: one focused Wolfram/Magma computation for \(n=7,8,9\). Y1b.2: one parameter-count
stream. Y1b.3: one arithmetic/descent stream. Y1b.4: one end-to-end and Lean stream.

### Next streams (2026-11-05)

| id | status | question |
|---|---|---|
| Z1 (C) | **launched** (Sonnet) | **Additive or sweeping PowerPoint operations for (BD).** Look for any UI operation that adds geometry or sweeps a shape, giving many linear parameters at bounded degree. Candidates: Morph, 3-D models, stretchy equation glyphs, crop-to-shape, radar/surface/contour charts, untested ink pens (brush, pencil, galaxy), and anything else. Y1c already covered strokes and effects. |
| Z2 (B1) | **launched** (Sonnet) | **Engine shape C = {9,7,5,4,2,0}** (N4 gap theorem; serves totally real nonics). Is there a drawable crossing that realises it, and what are the cost and realness of its conditions? |
| Z3 (B2) | **launched** (Sonnet) | **Cusp/extremum engine.** Offsets of a cubic Bézier have a cusp polynomial of degree 12 that seems to carry A₁₂ (N4). Measure the rank and cost of using it as an engine (box readout of the cusp), and whether a cubic factor can be forced. |

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

**Z2 done (2026-11-05).** See `notes/algebraic/Z2.md`.
- C's own variety has degree 144, dearer than the odd route's 105. Its full realisation would need
  a nodal cubic with its node at infinity, which is not in G2's catalogue.
- Exact realisation: `power_law 5/2` × a shifted `power_law b=−2`. It has 5 conditions, degree 4032,
  and ≤ 7 real roots.
- The sheared variant C∪{6} has 4 conditions, degree 1344, and no totally real point found.
- New non-C engine: Bézier × y = a·x⁻² has 2 conditions of degree ≥ 28, and 9 real roots occur.
- n = 10–13: no gap-≤2 class beats Theorem O.
- Correction to N4: with signed exponents, power law × shifted power law does reach gap-≤2 supports.

**Z3 done (2026-11-05).** See `notes/algebraic/Z3.md`.
- The cusp of an offset cubic Bézier is legally readable: `restrict` + `box`. The cusp is a local
  x-extremum [Proof + Wolfram].
- The cusp polynomial has degree 12 with Galois group S₁₂ [Wolfram].
- As an engine it is dominated: rank 5, so n−5 conditions (4 at n = 9); at most 8 real cusps
  [Proof sketch], 6 observed; so no totally real nonics.
- Factor forcing equals overshoot and does not lower the count.
- By-product (new readout tool): **box readouts of offset cusps return the centre of curvature at a
  parameter where the curvature takes a prescribed value**.

### Z4: an addition without square roots (2026-11-05, launched, Sonnet)

Motivation. Every route so far reduces to a rational-points problem. Taylor himself (Question 5.5,
Ann. Toulouse 2004) "does not know if it is reasonable to expect" a positive answer to the
question behind (SR). The structural reason (Y1a): the only "addition" PowerPoint has is offsetting,
i.e. Minkowski sum with a circle; affine maps turn earlier circles into ellipses, whose support
functions are square roots √Q_j, so each new parameter doubles the degree.

Question. Is there a UI-only composition that adds many P-weighted terms **without square roots**?
- (a) a pointwise graph sum y = f(x) + c·g(x) of drawable graphs;
- (b) a Minkowski summand other than the circle/ellipse, with a square-root-free support function
  (parabola-like);
- (c) any drawable family whose crossing equation is linear in many P-parameters at bounded degree.
A hit makes general n linear algebra plus gcd recovery; a clean negative sharpens the dependence
on open problems ("PowerPoint only adds through circles").

**Z4 done (2026-11-05): no hit.** See `notes/algebraic/Z4.md`.
- (a) No pointwise sums [Proof sketch]: every curve constructor is unary with numeric parameters,
  so a curve depends on another only through P-numbers. The affine ops between offsets compose to
  one 6-parameter map; `offset` has constant d. The only built-in P-weighted sum is the cubic
  Bézier (4 weights). Without offset, about 28 parameters at most, independent of n.
- (b) No summand other than ellipses [Proof]. Scale by 0 is legal (rank-1 form, constant summand)
  but collapses the base and all earlier layers to a segment; the parallel curve of a segment is a
  translated segment; back-and-forth tracings are illegal for offset [Wolfram check a=3, b=2, d=5/7].
- (c) Best linear families: rotated ellipse × x^k (F=5, degree 2k); Bézier graph × a·x^n (F=4,
  degree n). They fail (BD) and help gcd recovery only for n ≤ 5.
- Conclusion: offsets are the only way to add parameters (J+2 for J layers), each costing a
  square root. The offset route's one obstacle is Y1a's simultaneous squares.
- Open: interleaved restrict/seam-sign case of the rank-1 tower; Z1's unmeasured features
  (3-D models, equation glyphs, picture tools).

### Z5: rational curves on V_τ (2026-11-05, launched, Sonnet)

Theorem R needs n − 1 L-points on V_τ (general type for n ≥ 7); isolated-point searches failed
(Y1a §0.7). Y1a §4.4 leaves [Open] whether V_τ contains an L-rational curve of genus 0 (conic,
twisted cubic) or genus 1 with positive rank, other than ℓ_τ — that would give infinitely many
points and solve SS_{n−1} outright, unconditionally. Lines are excluded. τ is free.
Target n = 9, totally real S₉ (the first open case): dimension count for (τ, conic ⊂ V_τ), then an
explicit search on Y1a's nonic; then twisted cubics and genus-1 curves.

### Z6: the unmeasured UI features (2026-11-05, launched, Sonnet)

Finish Z1's unmeasured list, aimed at Z4's diagnosis: look for a two-curve (pointwise-sum or
Minkowski) operation, a non-constant offset, or a (BD) family. Items: 3-D models, the equation
editor, picture tools (crop to shape), the remaining ink pens (Brush, Pencil, Galaxy, Rainbow),
what Morph interpolates (and node-count mismatch), and whether text warps' (1−y)·T(x) + y·B(x)
ever combines two user-controlled guides with P weights.

**Z6 done (2026-11-05): nothing found; mostly reasoned, one measurement.** See `notes/algebraic/Z6.md`.
- Morph has the right shape, (1−w)A + wB of two user curves, but w is a clock value (typed
  Duration) that can't be frozen, and no vector frame is readable (Z1). Its linearity is
  unconfirmed [Heuristic]; node mismatch [Open].
- Text warps: the guides are preset curves with 1–2 handles; on y = g(x) a warp gives T + g·(B−T),
  g times a fixed function, not a user-curve sum [Heuristic].
- 3-D models: COM insert fails again [Measured]; UI insert not driven [Open].
- Picture tools: preset clip paths, raster effects [Heuristic]. Equation glyphs: discrete size
  variants plus integer extender repeats [Proof sketch, OpenType MATH]. Ink pens: freehand
  centrelines [Heuristic].

**Z5 done (2026-11-05): no hit, structurally.** See `notes/algebraic/Z5.md`.
- Theorem Z5 [Proof sketch]: for Gal(K_L/L) ⊇ A_n (primitive), n ≥ 9, an L-curve C ⊂ V_τ other
  than ℓ_τ, of genus g and degree e, satisfies (n−8)e ≤ 4g−4. So there are no genus-0 or genus-1
  curves, for any τ, and real-quadratic fields of definition don't help. Proof: Galois-irreducibility
  of the 8-dim heart module forces C birational onto a plane curve; a Plücker bound on its dual
  meeting Δ* gives the inequality.
- Dimension counts: degree-d rational curves −3d−1 on V_τ; with τ free (6 effective dims, PGL₂)
  the incidence is 5−3d. V_τ: K² = 576, c₂ = 768, χ = 112.
- Wolfram conic search: N = 5 control finds 6 conics; N = 6–8 none; N = 9 only the lines ℓ_ε.
- Consequence: Theorem R needs isolated points (SS_{n−1}), which stays open.
- Open: a formal write-up; A₉-irreducibility of the heart in characteristic 2; imprimitive groups;
  curves with a ℤ/2 stabiliser.

### Assumption-breaking streams (2026-11-05)

Every route so far shares built-in assumptions. These streams drop them.

| id | status | question |
|---|---|---|
| Z7 (#1) | **launched** (Opus) | **Multi-crossing readout / field embedding.** Every engine reached α as a root of ONE crossing equation E (χ_τ a factor of E_p). But `restrict` isolates every real crossing, and P is closed under arithmetic, so α need only be a rational function of several crossings: K ⊂ F(real roots of E_p). This is a parametric-polynomial condition: Gal(E_p) must specialize to a group H with an S_n/A_n quotient acting on the N crossings (on k-subsets, imprimitively, …), and the Diophantine problem is the K-twist of the cover Y_H → parameter space, not the factor locus. Classify the H available to our engines (overshoot, trinomial, offset towers), compute the geometry of the twisted covers, and look for one that is rational/unirational or has a guaranteed F-point. Check totally real cases. |
| Z8 (#2) | planned | **F-points, not ℚ-points.** Audit each route (MI-1, Theorem O, Theorem X, Theorem R, overshoot) for where rationality of parameters is genuinely forced (e.g. `poly_graph` ℚ-coefficients) versus where any P-point suffices. Then (i) linear sections of degree ≤ 8 give F-points for free (Lemma A); (ii) genus-1 curves over F need no rank, since elliptic functions at P-arguments are drawable (H4/W3): test whether the condition varieties of Theorem O / MI-1 contain F-defined elliptic curves with real points. |
| Z9 (#4) | planned (audit) | **Hyperelliptic / theta route.** Umemura: roots of any polynomial via Siegel theta constants of a hyperelliptic curve. Audit what genus ≥ 2 abelian-function machinery is in P (single-variable arc-length inversions; combinations of several arcs; whether Abel–Jacobi inversion or Siegel modular values are reachable). External input: other groups' results on hyperelliptic functions in P (user to supply). |

**Z7 done (2026-11-05): multi-crossing readout is never strictly cheaper.** See `notes/algebraic/Z7.md`.
- [Proof] Any multi-crossing scheme needs an irreducible factor of E_p whose root orbit (size m ≥ n)
  carries A_n. m = n (n ≠ 6) is the factor case. For n ≥ 9 the next sizes are m = 2n, then
  m ≥ C(n,2) (Dixon–Mortimer 5.2B, from memory). So every current n = 9 engine of degree < 18
  allows only the factor case.
- [Proof sketch] The condition variety keeps dimension k and maps onto the factor-case one, so its
  Kodaira dimension is ≥. Trinomial engine n = 5, D = 10 genera [Wolfram]: factor 2689, square lift
  13225, twin 16801, pairs 524161.
- [Proof] Totally real with fewer than n real crossings forces m ≥ 2n; the cheapest is the square
  lift (Theorem X). Readout itself is always legitimate.
- Ties only at n = 5 (PGL(2,5) sextic) and n = 6 (twin field), both already closed.
- Open: Dixon–Mortimer and n ≤ 8 exceptions in GAP; arithmetic of the n = 5 twists; non-linear
  engines (W2).

**Z8 done (2026-11-05): five over-constraints found, no route closed.** See `notes/algebraic/Z8.md`.
- Over-constraints:
  1. Theorem O (n ≥ 10) needs no rational τ: the P-valued freedom of a rational poly_graph of
     degree d leaves d − 4 rationality conditions [Wolfram rank] (1 at n = 10, 11; 2 at n = 12, 13);
     the rest is an F-point on O_m. X2's negative height exponents concern ℚ-points only. Totally
     real still possible (T₅(t²−2)/16 − t/1000 has 10 real roots).
  2. Z5's "genus ≥ 2 ⇒ Faltings" is wrong for L = F: F-curves with a degree ≤ 8 map to ℙ¹
     (with real points) have dense F-points. At n = 9 genus 2 and all degree ≤ 7 curves on V_τ are
     excluded (Castelnuovo; every L-quadric in the system is smooth of rank 9). Open: degree 8,
     genus 3; genus 4–5 in degrees 9–16.
  3. "No field enlargement helps poly_graph rationality" is too strong (MI-1 fibre degree
     ~5400 → ~2016, still > 8).
  4. Theorem X needs points over F, not ℚ^solv ∩ ℝ: Taylor's question is sufficient, not necessary.
  5. N1a's rational certificate centre is a Lean convenience only.
- New reductions [Proof]: totally real nonics follow from one F-line in {p₁ = p₃ = p₅ = 0} ⊂ ℙ⁷
  off the pairing ℙ³'s; MI-2 decics from one F-line in {p₂ = p₃ = p₄ = 0}. Both line families are
  surfaces; no low-degree structure found.
- Genus 1 over F with a real point already has dense F-points; elliptic functions add nothing.
  Z5's argument extends to every subfield of P.
- Open: the Fano surface of lines in X₃ ∩ X₅ (degree, Kodaira dimension, fibrations).

## Follow-up sequence after Z8 (2026-11-05, planned, nothing launched)

### Guiding principle: Criterion G (to be verified in A1)

P is closed under real roots of degree ≤ 8 polynomials with P-coefficients. So the question for
every route is no longer "does this variety have rational points?" but:

> **(G)** Does the needed variety V (over F) contain a curve C, defined over F, with a real point
> and an F-rational map C → ℙ¹ of degree ≤ 8 whose fibre over some F-point contains a real point
> that satisfies the route's nondegeneracy conditions?

If yes, V has (dense) F-points on C. Genus is not the obstruction; F-rational gonality ≤ 8 is.
Brill–Noether gives geometric gonality ≤ ⌊(g+3)/2⌋, which is ≤ 8 for g ≤ 13, but an F-rational
pencil is not automatic. Z5's inequality (n−8)e ≤ 4g−4 does not exclude genus 6–13 at n = 9.

### Phase A: gatekeeping checks (parallel, cheap)

| id | model | question |
|---|---|---|
| A1 | Opus | **Verify Criterion G.** (a) When does a curve C over F with a real point carry an F-rational g¹_d, d ≤ 8, with a real point in some F-fibre? Cases: W¹_d positive-dimensional (needs F-points on W¹_d — recursive, degree?), finite W¹_d (Galois may permute the pencils), canonical / Castelnuovo models, projection from F-points of C. (b) Give the exact genus/degree window on V_τ (n = 9, primitive group) left open by Z5's inequality and Z8's Castelnuovo results. (c) GAP check of Z7's Dixon–Mortimer step (orbit sizes n, 2n, ≥ C(n,2) for n ≥ 9) and the n ≤ 8 exceptions. |
| A2 | Sonnet | **Adversarial check of Z8's positives.** (a) The rank count: a rational poly_graph of degree d under its P-valued freedom leaves exactly d − 4 rationality conditions (Theorem O, n = 10–13). (b) The two new reductions: totally real nonics ⇐ one F-line in {p₁ = p₃ = p₅ = 0} ⊂ ℙ⁷ off the pairing ℙ³'s; MI-2 decics ⇐ one F-line in {p₂ = p₃ = p₄ = 0}. (c) The 10-real-root example T₅(t²−2)/16 − t/1000 is actually usable by the route. |

### Phase B: main unconditional pushes (after A; B1 and B3 use A1's window)

| id | model | depends on | question |
|---|---|---|---|
| B1 (Z10) | Opus | A1 | **Low-gonality curves on V_τ, n = 9 totally real S₉.** Within A1's window, hunt for F-curves on V_τ (τ free): residual curves of quadric/hyperplane sections containing ℓ_τ or the ℓ_ε; curves with a ℤ/2 deck stabiliser (Z5 open); images of curves on the Fermat-type cover; degree-8 genus-3 and genus 4–13 candidates. Dimension counts with τ free (6 effective parameters). A hit closes totally real nonics unconditionally via Theorem R. |
| B2 (Z11) | Opus | A2 | **Theorem O at n = 10, 11: an F-point on O_m plus one rationality condition.** Describe the combined variety (does the condition fibre O_m over a curve/line? what are the fibres?). Apply Criterion G. Explicit Wolfram search on a totally real S₁₀ decic. |
| B3 (Z12) | Sonnet | A1, A2 | **The two line surfaces.** Fano surface of lines in X₃ ∩ X₅ (nonics) and in {p₂ = p₃ = p₄ = 0} (decics): degree, Kodaira dimension, fibrations, low-gonality F-curves (Criterion G), numerical search for F-lines on an explicit totally real nonic. |

### Phase C: hyperelliptic audit

Z9 as planned, once the user supplies the external results on hyperelliptic functions in P.

### Phase D: consolidation

Whatever B returns, update `notes/algebraic/SUMMARY.md`: status by degree, the conditional
(SR)/Taylor result (sufficient, not necessary), Criterion G, and the map of obstructions (Z4–Z8).

### Order and cost

A1 ∥ A2 → B1 ∥ B2 → B3 → D. Z9 slots in whenever its input arrives. Five agents in total
(three Opus). Each launches only on the user's go-ahead.

**A2 done (2026-11-05): Z8's positives mostly confirmed.** See `notes/algebraic/A2.md`.
- (a) Rank count CONFIRMED [Proof + Wolfram]: Jacobian rank 5 for d = 4..7, so d − 4 invariants
  (1 condition at n = 10, 11; 2 at n = 12, 13). All group parameters are rational in the data;
  offsets are not needed. Rests on rotate + scale giving every P-angle.
- (b) Both line reductions CONFIRMED as algebra [Proof]. The nonic's last step is sound (the
  septic has a real zero; β read off by gcd). **Gap:** both use Lemma N over F, which assumes
  Gal(Ω/F∩Ω) ⊇ A_n; X2 proves it only for solvable L∩Ω. Nonic: real good lines exist in the
  totally real model (smooth points of a 2-dim Fano scheme). **MI-2: no real line found for s = 2, 3**
  [Wolfram, Heuristic; min residuals 0.135, 0.042]; real lines only at s = 4. If so, the MI-2
  reduction is vacuous for s = 2, 3.
- (c) T₅(t²−2)/16 − t/1000: 10 real roots, Galois group S₁₀, a smooth real point of O₄ ∩ {b₂ = 0}.
  A realness witness only, not an F-point for a given K.

**A1 done (2026-11-05): Criterion G proved in a corrected form; the window for B1 is mapped.**
See `notes/algebraic/A1.md`.
- **Theorem G [Proof].** A curve C over a subfield of P with a real point has P-points dense in
  its real points, if a chain C → D₁ → … → ℙ¹ (or a conic) is defined over a subfield of P with every
  step of degree ≤ 8 or solvable. The real-fibre condition is automatic.
- Unconditional cases [Proof]: genus 0, genus 2–5, hyperelliptic, trigonal, degree ≤ 8 curves,
  general genus 6 (5 tetragonal pencils, odd, so one is real; also whenever 5 ∤ index). Genus 7 if
  the index divides 8. Any genus ≤ 8 with one P-point (project from the osculating (g−3)-plane).
- **Correction:** "genus ≤ 13 suffices" is false. Brill–Noether pencils are only geometric.
  Open: genus ≥ 8 without a P-point; genus 7 with 3 | index; bielliptic genus 6 with 10 | index.
- **Window on V_τ (n = 9)** [Proof sketch]: no curve spans a ℙ⁴; in ℙ⁵ Castelnuovo excludes
  degree ≥ 11; (6, 10) excluded.
  - Class A, 28 (g, e) pairs that would give P-points: g = 3: e = 8; g = 4: 9–12; g = 5: 10–16;
    g = 6: 12–19; g = 7: e ∈ {13, 14, 16, 17, 19, 20, 22, 23}.
  - Class B, needing extra structure: (6, 20) bielliptic; g = 7 with 3 | e; g = 8–13.
- (c) Z7's conclusion stands [Wolfram + maximal-subgroup classification; GAP not installed]: for
  n ≥ 9 the transitive degrees below C(n,2) are 1, 2, n, 2n. Exceptions for 5 ≤ n ≤ 8: A₅/S₅ on 6;
  A₆/S₆ on 6 and 10; A₇ on 15; A₈ on 15. Z7 erred at n = 7 (missed A₇ on 15); small-n only.

**Phase B launched (2026-11-05):** B1 (Opus; also closes A2's Lemma N gap, aims for a uniform
construction, PSL(2,8)/PΓL(2,8) side task) and B2 (Opus), with recoverable notes
(`notes/algebraic/B1.md`, `B2.md`; logs `HANDOFF-alg-B1.md`, `HANDOFF-alg-B2.md`). B3 drops the
decic (MI-2) surface per A2.

**B2 done (2026-11-05): n = 10 reduced to one F-line; not closed.** See `notes/algebraic/B2.md`.
- Set-up confirmed: the condition is I = b₂²/b₃³ ∈ ℙ¹(ℚ); need an F-point on some fibre
  W_r = O₄ ∩ {B₂² = r·B₃³}, defined over ℚ, general type, degree 1260 (630 at r = 0). r = ∞ has no
  good totally real points (b₃ ≤ 0).
- **Engine C [Proof + Wolfram]:** affine image H of a rational quintic graph × an axis-aligned
  P-conic y² = −q(x); crossings are the roots of H² + q. Theorem O at n = 10 is its case σ = τ².
  One condition fewer (dimension 5), all equations of degree ≤ 7. Special orbit r = 0:
  W^C₀ = {p₁ = p₃ = 0, p₆ = (3/8)p₂p₄ − p₂³/32, p₇ = (7/20)p₂p₅}, degree 126. (Check: the conic must
  be drawable — ellipse, or hyperbola as an affine image of power_law x⁻¹.)
- **Reduction [Proof; existence Open]:** one F-line in Y₀ = {p₁ = p₃ = 0, S₆ = 0} closes totally
  real S₁₀/A₁₀ decics (last step a binary septic, so a real root in F). Smooth non-degenerate real
  lines exist in Y₀'s 3-dimensional Fano scheme [Wolfram, numerical]; unlike MI-2, not vacuous.
- No structure for Lemma A / Theorem G: W_r, W^C_r and the Fano schemes are general type
  [Heuristic]; the 945 degenerate pairing ℙ⁴'s have no F-points.
- End-to-end engine test on χ = T₅(x)²/256 − (x² + x/7 + 1/3)/10⁴ (S₁₀, 10 real roots) [Wolfram];
  it tests the engine only, not the F-point problem.
- Lemma N over F [Proof]: holds when β's orbit over F is primitive; imprimitive or size ≤ 8 puts β
  in P by a tower. One leftover case (orbit size 9).
- n = 11 [Proof sketch]: no single-F-line reduction; leftover forms have degree 9 or 12 > 8.

**B1 done (2026-11-05): no curve on V_τ; Lemma N gap closed.** See `notes/algebraic/B1.md`.
- (0) [Proof + Wolfram] For totally real nonics, H = Gal(Ω/F∩Ω) has no subgroup of index ≤ 8 and
  is perfect: H = 1 (β ∈ P), A₉, or PSL(2,8) on 9 points (sharply 3-transitive, so Lemma N, (ND2)
  and "ℓ_τ is the only line" still hold). The mod-2 heart is irreducible for PSL(2,8) (Steinberg)
  and for A₉, closing Z5's open item.
- (1) Expected dimension of {(τ, C)} is g + 5 − 3e ≤ −16 for all 28 Class A pairs; the genus-3
  octic is Z5's equality case.
- (2) [Proof] Curves with a deck stabiliser, and special τ, can't be F-rational; F-hyperplane
  residuals at best (124, 63). Over F̄, special V_τ do carry (5, 8) curves, so the obstruction is
  F-rationality, not geometry. The line lattice (rank 220, invariant rank 4) has no window class
  [Wolfram; Heuristic]. Uniform family A(x,y)² − m(x)m(y)B needs about 102 extra nodes. Fermat
  images have genus ≥ 321.
- (3) LM search for genus-3 octics: no hit (residual 0.006–0.016, about 11 starts, no positive
  control) [Heuristic].
- (4) A uniform low-gonality curve on V_τ is very unlikely for this route [Heuristic].
- (5) PSL(2,8)/PΓL(2,8): same structure as A₉ over F; no shortcut.
- Not done: the general genus-3 model (3K − D₄), genus 4–7 searches, line-lattice saturation.

**B3 launched (2026-11-06, Opus), widened:** both line families. (N) the Fano surface of good lines
for totally real nonics (Z8/A2); (D) the Fano 3-fold of lines in Y₀ for totally real decics (B2).
Find P-points via Theorem G / Lemma A (curves cut by Schubert conditions, fibrations), or explain
why none works. Recoverable notes: `notes/algebraic/B3.md`, log `HANDOFF-alg-B3.md`.

**B3 done (2026-11-06): no P-point on either line family; Lemma A and Theorem G don't apply.**
See `notes/algebraic/B3.md`.
- [Proof] S (nonics) and T (decics) are defined over ℚ (twists of the split Fano schemes by K's
  S_n cocycle); an F-point is a line spanned by u, v ∈ K_F. K_S = O(13), K_T = O(18): both general
  type. The 945 pairing ℙ³'s give G(2,4) components meeting S̄, so the clean excess formula fails.
- [Proof] Component-orbit lemma: an F-curve is geometrically irreducible and S_n-intrinsic, or
  built from F-linear data; reducible invariant curves don't help.
- [Wolfram] Virtual Schubert numbers: S: σ₁² = 344925, σ₂ = 208800, σ₁₁ = 136125;
  T: σ₁³ = 9303984, σ₃ = 2663280. Real LM lower bounds on S: ≥ 12 good lines meet a rational ℙ⁴,
  ≥ 13 lie in X ∩ H; so deg S ≥ 25 and Lemma A fails. Real counts on T timed out.
- [Proof sketch + Heuristic] The natural F-pencils on Plücker sections of S have degree ≥ 12, ≥ 13,
  independent of K. Any other degree ≤ 8 pencil would need a fibration by curves of Plücker
  degree ≤ 8 (Serrano); none is visible (heuristic: deg S > 81 not proven).
- Intrinsic curves: Γ_Q (lines tangent to p₂ = 0) has no real points [Proof]; the F-gonality of
  Γ₇, Γ_{2,4}, Γ_pl is [Open].
- Uniform in K, both ways: failures and any success would hold for all S₉/A₉ nonics and
  S₁₀/A₁₀ decics.
- Open: irregularity and fibrations of S_split; the intrinsic curves; the real counts on T.

**Phase D done (2026-11-06).** `notes/algebraic/SUMMARY.md` updated: one-paragraph status, status
table, corrections to §§6–7 (Z8), new §8 (what PowerPoint can add), §9 (F-points: Theorem G, Lemma N,
the two one-line reductions, Engine C), §10 (the frontier: the (PRC₈) question and ranked open
targets). Remaining: Z9 (awaiting external input), B3's leftover items.

**Z9 rescoped (2026-11-06): rebuild the hyperelliptic machinery ourselves**, starting from arc
lengths of quartic graphs (user's pointer to what the external group did).
- Arc length of y = c·p(λx + μ) (p ∈ ℚ[x] quartic, P-valued affine data) is ∫ √(1 + c²λ²p′²) dx on
  w² = 1 + c²λ²p′(x)², degree 6, genus 2 (genus ≤ 4 for sextic graphs). Decompose the differential into
  first/second-kind and exact parts; when does the Jacobian split (e.g. even p, extra involutions)
  and the integral reduce to elliptic ones?
- Inversion: arc_of_length + box gives x(s) for ONE genus-2 integral. Abel–Jacobi needs two. Can
  two arcs plus an intersection/box impose two integral conditions at once? Which special values
  are algebraic?
- Galois groups reachable: division points of genus-2 Jacobians give GSp(4, ℓ) (composition
  factors PSp(4, ℓ)); 2-torsion gives split(1 + p′²). Does anything reach A_n, n ≥ 9 (W3/H4 said
  no for genus 1)? Relevance to Umemura's theta formula.

**Z9 done (2026-11-06): no hyperelliptic/theta route to A_n (n ≥ 9).** See `notes/algebraic/Z9.md`.
- [Proof] Drawable genus-2 family: arc-length curves of quartic graphs are exactly w² = D + q(u)²
  (q a real cubic over P, D > 0): 2 P-moduli; ∞₊ − ∞₋ is 3-torsion; branch points = nonreal roots of
  q = ±i√D. Sextic graphs: q quintic, genus 4. Béziers stay genus ≤ 1; offsets add only elliptic pieces.
- [Wolfram] Explicit decomposition of w du (no third-kind part). b = 0 splits (elliptic); b ≠ 0
  looks geometrically simple, End = ℤ [Heuristic]: new transcendentals, no new Galois groups.
- [Proof sketch] Only chained single inversions exist (all constructors unary); no coupled
  Abel–Jacobi inversion. Abel relations force only endpoints quadratic over P. Genus-2 periods are
  not P-numbers (no real arc closes into a cycle). Whether chains can match Jacobi inversion values
  is [Open].
- [Proof mod citations] Torsion of a genus-g Jacobian has composition factors in projective
  dimension ≤ 2g: genus 2 caps at A₇/PSp(4,ℓ); genus 4 gives A₉/A₁₀ only via 2-torsion with 10 free
  branch points, which no drawable curve has.
- [Proof] Umemura blocked first by (U1): arc-length branch points have degree ≤ 5 and real zeros
  only double, so a target's roots are never branch points.
- [Proof] New: sextic graphs from p = x⁶/6 + x²/2 have branch points exactly the roots of
  z⁵ + z + c, any c ∈ P(i) with Im c ≠ 0 — X1's (BR₅). Genus-4 theta constants of these curves would
  give (BR₅) via Thomae; P can't compute them, so this is a target, not a route.
- Open: real Abel sums making a genus-2 period a P-number; a differential-algebraic proof that
  chained single inversions never give Jacobi inversion values.

**L1 done (2026-11-06): (PRC₈) appears open and unstudied.** See `notes/algebraic/L1.md`. No work on
PAC/PRC properties of bounded-degree-root fields (or origami/neusis fields). ℚ^solv PAC is open.
Northcott gives no obstruction (Fehm 1708.06599: PAC + Northcott coexist; our field has all roots of
unity anyway). Bombieri–Zannier's Northcott is for abelian degree-≤ d composita; ℚ^(d) is open for
d > 2. Nearest: Pál 2006 (genus 0, 2–4 curves have solvable points), Çiperiani–Wiles, Rawson.

### P1: (PRC₈) for Fano complete intersections (2026-11-06, launched, Opus)

First concrete step on the frontier question (SUMMARY §10). E = real field generated by iterated
real roots of degree ≤ 8 polynomials plus all solvable real numbers (E ⊆ F = P ∩ ℝ_alg).
- Trivial part: any variety of degree ≤ 8 with a smooth real point has E-points (Lemma A: slice
  by a ℚ-linear space near the real point). So MI-1's (2,3) complete intersection (degree 6) is
  NOT a real test; the first nontrivial Fano complete intersections have degree ≥ 9.
- Question: for smooth Fano complete intersections X ⊂ ℙ^N over ℚ (degree ≥ 9) with a smooth
  real point, when does X have E-points? Tools: lines/conics/rational curves through points
  (the variety of lines through a point of a degree-(d₁..d_k) CI is a CI of degrees 1..d_i, of degree
  ∏ d_i!), Brauer/Hilbert/Wolfson resolvent-degree bounds, real Wooley (X2 Theorem RW), conic and
  del Pezzo fibrations, Kollár's real rationally connected varieties. Deliverable: the best explicit
  threshold N(d) for hypersurfaces and CIs, the first uncovered Fano types, and whether
  rational connectedness alone suffices.

**P1 done (2026-11-06).** See `notes/algebraic/P1.md` ("Theorem P1").
- Hilbert/Wolfson/Sutherland recursions don't transfer (they bound resolvent degree and start with
  a degree-d solve; Brauer's radical step breaks on realness).
- **Lemma LS [Proof sketch, Grunwald–Wang]:** any finitely many local extensions are realised by
  completions of a totally real field inside ℚ^solv. So local solubility is free over E.
- **Theorem H [Proof sketch + Cited]:** X smooth over a number field in E, with a real point,
  satisfying HP + WA over number fields ⇒ E-points dense in X(ℝ). Hypersurfaces: N ≥ (d−1)2^d
  (Birch–Skinner; 4096 at d = 9). Any smooth X: dim ≥ (D−1)2^D − 1 (Browning–Heath-Brown,
  Frei–Madritsch). Replaces X2's RW bound (4095 vs 10^4294 at D = 9); X2's regime table needs redoing.
- **Theorem W [Proof sketch]:** E is Euclidean; slicing by an E-isotropic subspace of a quadric in
  the ideal leaves degree ≤ 8. Covers (2,2,3), (2,2,4) (nondegenerate quadric), (2,2,2,2) for N ≥ 10
  (N ≥ 8 generically), (2,e), e = 5–8 unless sphere signature. **Lemma C3:** cubics with a real point
  whose second fundamental form has index ≥ 2 contain E-lines: (3,3), (3,5), (3,7) under that condition.
- Rational connectedness alone gives nothing unconditional (Picard rank 1, no fibrations);
  Colliot-Thélène's conjecture would cover all smooth Fano CIs with a real point.
- First open: (3,3) ⊂ ℙ⁶ without the index condition; (2,5) ⊂ ℙ⁷ sphere-type; (3,4) ⊂ ℙ⁷; degree-9
  hypersurfaces in ℙ⁹…ℙ⁴⁰⁹⁵.
- None of this reaches general type (V_τ, S, T); Witt slicing on V_τ has expected dimension 44 − 6n < 0.

### After P1 (2026-11-06)

| id | model | status | question |
|---|---|---|---|
| Q1 | Opus | **launched** | Verify Lemma LS + Theorem H rigorously (Grunwald–Wang incl. Wang's special case; all places; circle-method HP + WA over arbitrary number fields and exact hypotheses). Literature: is (H*) — high-dimensional smooth varieties with a real point have dense ℚ^{tr,solv}-points — already known? What it gives for Taylor's question. |
| Q2 | Sonnet | **launched** | Rebuild X2's regime table with Theorem H (and W, C3): does any route's condition variety come into range, for which n, needing ℚ- or E-points? How Theorem H changes the (BD) criterion. |
| Q3 | Opus | planned (after Q1, Q2) | **Redesign the target.** Tools work on Fano / high-dimensional / quadric-containing varieties, fail on general type. Can engines, the square lift and multi-step towers be combined so the condition variety is Fano, high-dimensional, or contains a quadric (Theorem W)? |

**Q2 done (2026-11-06): no route comes into Theorem H's range for any n.** See `notes/algebraic/Q2.md`.
- [Proof of the arithmetic] Nearest misses: MI-1 9 variables vs 36; Engine C (n = 10) 9 vs 10⁶;
  Theorem O's W_r 9 vs 10^9.5; A/C excess 14 vs ~10¹⁶; Theorem X's surface dim 2; V_τ dim 2 for all n.
  Holds even if Theorem H fails (threshold failures).
- Point kinds: H gives E/F-points, never ℚ-points (MI-1, A/C, the n = 9 quadric need ℚ). Routes
  containing p₂ = 0 have no real point (p₂ positive definite), so H and W can't apply.
- No fixed-degree CI in growing dimension: conditions n + 1 − F with F ≤ 36, degrees growing.
  H beats Lemma A only for many equal low-degree forms (c quadrics need n ≳ 2c²).
- (BD) under H [Heuristic]: fibre = n conjugate equations of degree δ; criterion
  M ≥ n + n(n+1)(δ−1)2^(δ−1) (polynomial in n, vs RW's triple exponential). Needs δ ≲ log₂M;
  offset towers (δ ≥ 2^j, M = 3j+4) miss doubly exponentially.
- Open: a block-linear Birch-type theorem [not searched]; smoothness at infinity of fibres.

**Q1 done (2026-11-06): (H*) correct for k = ℚ (and k ⊂ ℚ^{tr,solv} with real points at every
real embedding); false for arbitrary real k.** See `notes/algebraic/Q1.md`.
- Lemma LS [Proof]: prime-degree cyclic steps via Grunwald–Wang (NSW 9.2.8; Artin–Tate X.5); the
  special case needs 8 | degree, never at prime degree; real places stay split; all places covered
  (Lang–Weil + Hensel at good places, LS at the finitely many bad ones).
- HP + WA over any number field [Cited, read]: Frei–Madritsch (Mathematika 63, 2017) Thm 1.4,
  smooth geometrically integral X with dim X ≥ (deg X − 1)2^{deg X} − 1; positivity of the singular
  integral needs real points at every real place, which the construction supplies.
- Counterexample to the general-k version: k = ℚ(α), α the real root of x⁵ − x − 1, X a point.
- Literature: closest is Wooley, Monatsh. Math. 180 (2016), arXiv:1501.01789 (solvable, not real,
  points for dim ≥ 2^{2^D}). LS is likely standard in potential-automorphy work (from memory). No
  source combines LS with the circle method: (H*) is an easy corollary not in print. A modest
  partial answer to Taylor's question (circle-method range only).
- Project: nothing beyond Theorem H; no route variety qualifies.

**Q3 done (2026-11-06): no redesign brings a condition variety into range.** See `notes/algebraic/Q3.md`.
- [Proof] Thresholds depend on dim vs the number R of equations, not on unknowns (Birch dim ≳ 2R²;
  Myerson dim ≥ 8R, quadrics over ℚ). An unknown with its own equation adds nothing. Each
  K-condition is n equations, so ~c·n P-parameters per K-condition are needed: sharpened (BD).
- Best construction [Proof]: Theorem R with a Bézier base, ~n² unknowns but dim ≈ 3n vs R ≈ n²; it
  splits into J uncoupled copies of V_τ. Each ellipse summand adds ≤ 4 parameters but costs n
  equations. Sharing targets, gcd across engines, square / multi-quadratic lifts: ratio no better.
  Witt slicing of V_τ at n = 7 blocked (index ≤ 3 < 4).
- Literature [Cited]: Myerson (Invent. 2018) R quadrics in ≥ 9R variables; Myerson 1709.08917;
  Hochfilzer (Acta Arith. 2024) bidegree (2,1), (1,1); Schindler 2014; Browning–Hu 2019. All over ℚ;
  no number-field version found.
- Small wins: a cubic Bézier base with quadratic x(t) lets Theorem R use n − 2 forms [Proof +
  Wolfram]. Lemma Q: r quadrics in ~r²/2 variables with a smooth real point have dense E-points
  [Proof sketch].
- What would close it: ≥ ~9n P-parameters per K-condition at bounded degree, i.e. a Minkowski-sum or
  two-curve constructor (no UI route known).

### W4: text-warp engines (2026-11-10, proposed)

The new `PConstructibleCurve.text` constructor (`Pptc/Defs.lean`) makes every warped glyph outline
drawable, including the algebraic egg quartic, the piriform and the Gerono lobe. `WARP.md` assesses
them against the algebraic goals. This stream turns that assessment into a decision procedure: can
a warped curve, alone or as an engine component, close or relax an open case?

**What is already settled (see `WARP.md`).**
- A single warped curve adds no new numbers: line/conic intersections are degree ≤ 4/≤ 8 over F, and
  `root_Pconstructible_deg8_coeffs` already covers them. No stream is needed for that.
- The useful objects are **engines**: egg × quintic graph (degree 10, rank F = 9; one more parameter
  than the MI-1 sextic engine) and egg × sextic graph (degree 12, F = 10; still below H5's F ≥ 11
  for totally real decics).
- Nonsquare boxes add **no new algebraic modulus** for the egg family: straight/polyline presets are
  affine or reparameterize the same universal egg; curved guides are transcendental. Closed, no stream.
- A free yellow handle is already a `PConstructible` parameter in `text`; the Lean theorem should
  quantify P handles, not the old rational stops. This is part of W4d, not a separate investigation.
- The one follow-up that could reach H5's threshold was **offset egg × general conic**: F = 11,
  viable whenever the offset degree D ≤ 10 (crossing degree 2D, cofactor 2D − 10 < 11 at n = 10).
  **W4a closes it:** the egg offset has geometric degree 16 (N4's abscissa convention; the
  elimination polynomial has total degree 28), stable across four parameter choices including the
  task's `d₀=1,d₁=2` and irreducible over ℚ, so the conic crossing degree is at least 32, the
  cofactor degree is at least 22 at n = 10, and F = 11 has no room. See
  `W4-offset.md`. Scoped kill.

**Tasks.**

| id | model | question / deliverable |
|---|---|---|
| W4a | math/computation (Opus or Wolfram-heavy) | **Done (2026-11-10):** the geometric offset degree is **16** (N4 convention; elimination polynomial total degree 28, Y-degree 12), stable for `(d₀,d₁,r) = (1,2,1), (2,3,1), (1,4,1), (2,5,1/2)` and irreducible over ℚ; a two-sided Groebner elimination factors as `(degree-4 extraneous)² · (degree-28 elimination polynomial)`. Offset egg × general conic has crossing degree at least 32 and cofactor at least 22 at n = 10, far above F = 11; **close offsets of the egg as an engine route**, scoped to this construction. See `W4-offset.md`. |
| W4b | math (H3 protocol) | **Egg engines at n = 9–12.** For egg × quintic/sextic graph, compute the condition variety `χ_τ ∣ N_m`: dimension, defining equations, degree, singularities, real points, and the Jacobian rank on monic nonics/decics. The decisive question is whether its degree is < 9 (then H2 Lemma A applies over F) and whether it has a smooth real point. Compare against the F = 8 sextic engine and H3's F = 13 two-graph engine. Deliverable: `W4-engines.md`. |
| W4c | arithmetic | **Explicit targets.** Test the explicit totally real S₉ nonic `q = ∏_{i=-4}^{4}(x − i) + 1` against egg × sextic, and a totally real S₁₀ decic against egg × quintic. Seek F-points, not just real solutions; a numerical real solution is not enough. Reuse B1/B2's search machinery. Deliverable: a scoped positive or an [Open] with the search box recorded. |
| W4d | Lean | **Finish the `text` → egg/piriform bridge.** In a real file (`Pptc/Warp/Text.lean`), prove the two-`●` row's left disc normalizes to `glyphCircle a`, isolate it by `restrict`, and derive unconditional `PConstructibleCurve (eggCurve a d₀ d₁)` and the piriform. State the handle over P, not ℚ. Then import from `Pptc.lean`. Deliverable: the Lean file plus the replacement of `TriangleCircleRule` by a theorem for the catalogued row. |

**Order.** W4a is done (offset route closed). W4b is now the first open task; W4c after W4b (it needs
the engine shapes); W4d is independent of both.

**Kill criteria (scoped).** The offset kill criterion was met: the geometric offset degree is 16
(the elimination polynomial has total degree 28, also ≥ 11), so the offset-of-warps route is
closed and recorded. If the egg engines' condition varieties have degree
≥ 9 or no F-point in the tested boxes, record a scoped [Open]/[Heuristic] and do not conclude
anything about the target. No negative about `algebraic_Pconstructible` follows from W4.

**Cost.** W4a: one focused Wolfram/elimination computation (hours). W4b: one Opus stream. W4c: one
Sonnet/Opus search stream. W4d: one `lean-prover` task (the scratch lemmas in
`Pptc/Scratch/WarpText.lean` and `WarpTwo.lean` already cover the normalization and bounding box).

### C1: sine × sine (2026-11-11)

Brief: look at the whole programme afresh; weaken (SR) or find a new route.

**C1 done (2026-11-11): one new engine, target not closed.** See `notes/algebraic/C1.md`, log
`HANDOFF-alg-C1.md`, scripts in `notes/algebraic/scripts/`.
- Engine S (`sine` × `sine`, commensurable frequencies): Chebyshev trinomials T_p + a·T_q + c and the
  five-term family with phases. All roots real for small a, c; Galois group S_n [Proof for q = 1;
  Python n = 5…30].
- Theorem C1: totally real S_n numbers in P for every n.
- Theorem X′: the conditional theorem without the square lift, n − 4 conditions on K itself.
- Uniform-in-K routes with bounded engines would bound resolvent degree (C1 §5).
- Closed, scoped: more than two frequencies, RM period ratios, cubics through the conjugates,
  product-square for Theorem R, harmonic curves for BR₅.
- Not done: Lean for Engine S; geometry of the five-term variety; q ≥ 2 Galois groups as a theorem.

## Phase E: two big attempts (planned 2026-11-12, nothing launched)

**Status: R1, R2 done and reviewed (2026-11-12): both came back against the route (no group-law handle; `J_min = n − 2`). R3 is the deciding test. R3 done (see below). P1′ done 2026-11-12 (see below). P2′ done 2026-11-12 (see below). R4, R5 and P3′–P6′ not launched. Launch each stream on
the user's go-ahead.**

### E.0 Why these two, and what success would mean

After C1 the position is this.
- Every engine in `Defs` is either a bounded-parameter family, or an offset tower, whose parameters
  grow with depth but cost one square root each (Z4, Y1a).
- For a bounded family, reaching a given K is an F-point on a K-twisted Galois cover of a rational
  base. Every F-curve on such a cover is itself a full twist (B3's component-orbit lemma, C1 §2.3),
  so Theorem G never applies through the cover map. A construction uniform in K would bound
  resolvent degree (C1 §5).
- So inside the current `Defs` exactly two kinds of argument can still close all n:
  - **E-R**, an engine whose parameter count grows: Theorem R, i.e. the simultaneous squares;
  - **E-P**, arithmetic that is not uniform in K: a local–global or pseudo-real-closed statement
    for F, for the specific covers we need.

Honest odds: both are research problems with no known method. The plan is built so that each stream
ends in a written statement worth keeping, whichever way it goes, and so that dead routes are killed
early. The ground rule of this plan still holds: obstructions are scoped to their route.

**What counts as success, in decreasing order.**
1. The target, unconditionally.
2. The target conditional on a conjecture that experts do hold a view on (replacing Taylor's
   question, on which Taylor himself had none).
3. One new unconditional degree (9 totally real, or 10).
4. A proved obstruction for a whole class of routes, so that effort stops going there.

### E-R: the simultaneous squares (Theorem R)

**Where it stands.** Theorem R (Y1a): n − 1 non-homothetic positive-definite binary forms Q_j over
L with Q_j(τ) a square in K_L, plus (ND1, ND2), give β ∈ P, totally real included. Then the offset
distances come from linear algebra. Searches at n = 9, 10 found no points. Z5: no genus 0 or 1
curves on V_τ. B1: expected dimension of low-gonality curves is ≤ −16.

**Why another look is justified.** Three things were not tried.
- The problem has a group law that the surface V_τ hides (R1 below).
- The count n − 1 was never minimised against the other linear parameters available (R2).
- No search had a positive control, so "nothing found" carries little weight (R3).

| id | kind | question | depends on |
|---|---|---|---|
| R1 | math, Opus-level | **DONE 2026-11-12 (see below).** **The Jacobian formulation.** Write Q_j = (x − ω_j)(x − ω̄_j), ω_j ∈ L(i). Then Q_j(τ) is a square in K_L iff τ − ω_j ∈ K_L^× · (K_L(i)^×)². For H: y² = ∏_{j ≤ J} Q_j (genus J − 1, no real branch points) this says the K_L-point (τ, y) has trivial image under the "x − T" 2-descent map at every factor, i.e. it lies in 2·Jac(H)(K_L) up to the usual normalisation at infinity. Prove this precisely (which class group, which point at infinity, the kernel of x − T when deg is even). Then the problem becomes: **find a curve H over L in this family and R ∈ Jac(H)(K_L) with 2R on H.** Deliverables: the exact statement; a check against Y1a's totally real quintic (J = 4 there); the count of conditions "2R ∈ H" as a function of J (it is (J − 2)·n over L, against J·n − … unknowns plus 2J − 3 moduli). | — |
| R2 | math | **DONE 2026-11-12 (see below).** **The true minimum number of squares.** Theorem R uses the line as partner and the parabola as base. Tabulate the linear K-parameters available from every source at once: Bézier base (Q3: n − 2 forms), circle partner (W1: rank +2), conic or quartic-graph partner, the five-term sine family as partner (new), overshoot. State J_min(n) with proof. Each parameter that is not an offset distance removes one square. If J_min(n) ≤ 3 for some n ≥ 9 the problem is a K_L-point on a curve of genus ≤ 5 with free moduli, a different and much better problem. Expected answer [Heuristic]: J_min ≈ n − 6. | — |
| R3 | computation | **DONE 2026-11-12; revised 2026-11-12 (see below).** **Degree 7 as the control.** Plain search over ℚ (and ℚ(√d) at H = 1 only), not over the infinite field L. n = 5 positive control; n = 6 K3 and n = 7 are line-only over ℚ in the searched boxes. n = 7 is general type, so the null is the expected Bombieri–Lang outcome, not a test of the route. The n = 6 rank-4 net fibrations are defined over non-solvable degree-15 fields and do not descend to the real solvable L. Record a positive control at n = 5 (Y1a's example) run through the same code. | R1 |
| R4 | math | **Structured τ.** Look for τ for which W_τ = ⟨1, τ, τ²⟩ contains squares for a structural reason: τ a rational function of an element with a known square root in K_L; τ a value of a Chebyshev or Lattès map; τ in the image of a degree-2 map from a curve with many K_L-points. C1 §6.4 shows only indefinite or rank-1 forms arise from the obvious choices (τ = μ² + μ⁻²), so the question is whether any choice gives **two** definite forms. Two is the first nontrivial case (genus 1). | R1 |
| R5 | math | **Use elliptic curves through the conjugates.** For n ≤ 9 every K_L-point of the plane lies on an L-rational cubic (C1 §6.3), so genus-1 curves over L with new K_L-points exist rationally. Theorem R's genus-1 curves (two layers) form a 4-dimensional linear system each, too small. Question: is there a tower shape (three layers with one relation, or a non-parabola base) whose genus-1 quotient ranges over a linear system of dimension ≥ n? This is a search over tower shapes, not over points. | R2 |

**R1 done (2026-11-12), reviewed and corrected: the exact condition is lifting to `C_B`; no new handle.**
See `R1.md` (read its "Review corrections" section first), log `HANDOFF-alg-R1.md`.
- **Theorem R1 [Proof, repaired in review].** For `H: y² = ∏_{j≤J}Q_j` (`g = J−1`, `∞^±` L-rational)
  and `H̃ = C₁ ×_{ℙ¹} ⋯ ×_{ℙ¹} C_J`, the cover `π: H̃ → H` is unramified Galois with group
  `(ℤ/2)^{J−1}`, `g(H̃) = 1 + 2^{J−1}(J−2)`, and `Q_j(τ)` square for all `j` ⟺ `P ∈ π(H̃(K_L))`.
  `π` is the pull-back of an isogeny `φ: A → Jac(H)` of degree `2^{J−1}`; `π_*: Jac(H̃) → Jac(H)`
  itself is **not** an isogeny (its kernel has positive dimension for `J ≥ 3`). The obstruction is
  the tuple `[Q_j(τ)]` in `H¹(K_L, ker φ) = (K_L^×/K_L^{×2})^{J−1}`.
- **Correction to the plan.** `2·Jac(H)(K_L) ⊂ φ(A(K_L))`, so "lies in `2Jac`" is sufficient but
  strictly stronger than `SS_J`. No index on rational points is claimed. In even degree the
  2-descent map lands in `A^×/(K_L^× A^{×2})`: writing `τ − ω_j = c_j w_j²`, 2-divisibility asks
  the classes `[c_j]` to be **equal** (mod `±` squares, up to a kernel of order ≤ 2), not to vanish.
- **Strong condition** `2R = [P−∞⁺]`: for fixed `H` the solutions lie on the étale `4^g`-preimage
  curve of `H`, of genus `1 + 4^{J−1}(J−2)` (`1, 17, 129, …` at `J = 2, 3, 4`).
- **Y1a check** (`n = 5`, `J = 4`): the four identities `ρ_j² = Q_j(β)` hold exactly (re-verified
  in review); `g(H) = 3`, `g(H̃) = 17`, `deg π = 8`. `Jac(H)[2](L)` has rank `J` for `J` even and
  `J − 1` for `J` odd (so 4 here); `ker φ` has rank `J − 1` always.
- **Not usable as stated in R1.md:** the Faltings remark (our `L` is an infinite extension, so
  finiteness of `H̃(K_L)` does not follow); the "two different quintics" remark (Y1a's and Y1b's
  quintics are the same field under `x ↦ 3 − x`).
- **Assessment.** `H̃` is Y1a's `C_B`: the exact condition is the same curve as before. `J = 2` is
  trivial (`Jac = H`) and reproduces Y1a §4.6. For `J ≥ 3` the group law gives no new handle, so
  the kill criterion "R1 fails to give a usable group-theoretic handle" **is met**: R3 falls back
  to plain search (drop "via R1's doubling construction" from R3's brief).

**R2 done (2026-11-12), reviewed and corrected: the only count that gives a theorem is `n − 2`.**
See `R2.md` (read its "Review corrections" section first), log `HANDOFF-alg-R2.md`.
- **Two counts [Proof].** *Type I* parameters are jointly linear with the offsets; a nonzero
  `L`-solution is guaranteed by `U ≥ n + 1`. *Type II* parameters are only separately linear; they
  give a determinantal condition of codimension `n − P` on the tower, not free parameters. The
  plan's "each parameter that is not an offset distance removes one square" was wrong: it holds
  for Type I only.
- **Strict minimum [Proof modulo G2's catalogue].** `J ≥ n − 2`: the base contributes `B ≤ 2`
  (parabola, power law, cubic Bézier with quadratic `x(t)`), and the only uniformly available
  Type I partner parameter is the intercept of a fixed-slope line. Attained by the cubic Bézier
  base + line (Q3). For `n ≥ 9`, `J ≥ 7`, `g(C_B) ≥ 321`.
- **Dimension count for a conic or quartic-graph partner: `J = n − 6`.** The rank condition has
  codimension `n − 5` and the solution set in the `J + 2` tower parameters is a cone, so
  `J + 1 ≥ n − 5`. (R2.md's "sharp `n − 7`" forgot the scaling and is wrong; `n = 9`, `J = 2` is
  generically only the zero tower.) At `n = 9`: `J = 3`, genus 5. At `n = 10`: `J = 4`, genus 17.
- **The Type II condition is the old frontier problem.** It needs an `L`-point on a variety cut
  out by `n − 5` conditions, the same shape as the bounded-engine conditions; W1 §2 already
  identified the conic partner with H1's linear-support family. At `n = 9` the conic route is
  `SS_3` **plus** a 4-condition `L`-point problem: two open problems, not a trade.
- **No conic linearisation [Proof].** A nonzero binary quadratic form cannot vanish on a
  direction space of dimension ≥ 2. Same for circles and graphs of degree ≥ 2.
- **Sine/exp no-go [Proof].** With algebraic parameters, Lindemann–Weierstrass reduces a sine
  partner to a horizontal line. Engine S (C1) is a separate route, not a Theorem R partner.
- **Overshoot [Proof].** No linear parameter; it is a degree/realness device.
- **Kill criterion.** First half **met**: `J_min(n) = n − 2` in the only sense that gives a
  theorem. The conic variant is not a way round it. R3 (plain search at `n = 7` with the `n = 5`
  control; the cubic Bézier base with `J = 3` on Y1a's quintic is a good positive control) is the
  deciding test. R4 and R5 wait on R3.

**R3 done (2026-11-12; revised 2026-11-12 after review).** **Field actually searched: ℚ**
(boxes `|ρ| ≤ H`, plus the coefficient box for τ), with `ℚ(√d)` only at `H = 1`; no cubic
`L` was reached. This is not the infinite field `L` of Theorem R. See `R3.md` (field-scope
caveat and findings summary first), log `HANDOFF-alg-R3.md`. Plain search; the R1 doubling
construction was dropped per R1's review. **Outcome: n = 5 control passes; n = 6 and n = 7
are line-only over ℚ in the searched boxes; kill criterion not established.**
- **Fields [Wolfram].** `q5 = x⁵ − 5x³ + 4x − 1` (disc 38569), `q6 = ∏_{i=1}^6(x−i)+1`
  (disc `7⁵·23·53²`), `q7 = ∏_{i=1}^7(x−i)+1` (disc `17·3457·15601·669577`), all irreducible,
  totally real, with Galois group `S₅/S₆/S₇` certified by cycle types.
- **n = 5 control [Computed, exact; identities Wolfram].** With `τ = β`, `H = 6..11` gives
  `1,2,4,6,7,9` positive-definite classes. `H = 11` recovers all four Y1a forms up to scale
  plus five new ones; all nine identities `ρ² = Q(β)` and discriminants (`176, 3344, 16, 23,
  2159, 4199, 12704, 30448, 13648`) verified. The code does find positive-definite forms when
  they are present in the box, so the n = 6 and n = 7 null results are not a code artifact;
  this does not show that ℚ-points are a proxy for `L`-points.
- **n = 6 K3 [Computed, exact].** `τ = β`, `H ≤ 9`: every ℚ-point is `deg` (the line `ℓ_τ`) or
  `lin`; totals `8,16,24,40,48,72,88,112`, `pd = 0`. 324 τ-classes at `H = 2,3` and 48 at
  `H = 4,5` give zero nondegenerate ℚ-points. The expected elliptic-fibration F-points did
  not appear.
- **n = 6 fibrations [Proof; discriminant/norm Wolfram].** The 15 rank-4 net members give quadrics `q_{ij}`
  over degree-15 fields `F_{ij}` (stabilizer `S₂ × S₄`). The ruling discriminant
  `δ_{ij} = ∏_{k≠i,j} w_k` is a square in `F_{ij}` (the canonical square root is
  `H_{ij}`-invariant), so both rulings, and hence the two dual genus-1 fibrations, are
  defined over `F_{ij}`. A single fibration has stabilizer `S₂ × S₄` (index 15), not
  `S₂ × A₄`; the norm of `δ` is `(7^15·23^3·53^6)²`, a consistency check. `F_{ij}` is
  non-solvable, so none of these 30 fibrations is defined over the real solvable `L`.
  Scoped to these 30; not a classification of all elliptic fibrations and not a negative
  about `algebraic_Pconstructible`.
- **n = 7 [Computed, exact].** `τ = β`, `H ≤ 6`: totals `8,16,24,40,48`, all `deg`/`lin`; 324
  τ-classes at `H = 2` and 48 at `H = 3` give zero nondegenerate ℚ-points. So neither
  `J = n − 2 = 5` nor `J = n − 1 = 6` is met by a ℚ-point there. For `n ≥ 7`, `V_τ` is of
  general type; Bombieri–Lang makes the null expected, so this is not a test of the route.
  `[Heuristic]`
- **Theorem R read-out [Wolfram].** Parabola `J = 4`: kernel dim 1, and `a`, `c′` are exactly
  Y1a's values; the minpoly of `X` has Y1a's roots. Cubic Bézier `J = 3`: for all four triples
  of Y1a's forms the kernel is 1-dimensional, ND1 holds, `X ∉ ℚ`, `[K(X):ℚ] = 5` with an
  irreducible totally real minpoly. R2's `J = 3` control is confirmed.
- **Real quadratic `L` [Computed, exact].** `L = ℚ(√d)`, `H = 1`: `d = 5` with three τ shapes
  and `d = 2,3` with `τ = β + √d β²` give 18–81 solutions each, all on `ℓ_τ`, none genuine.
  The height-1 box is close to vacuous (coordinates in `{−1,0,1}`) and has no positive control:
  it also finds nothing at n = 5, where forms are known. The brute-force frontier is quadratic
  `H = 2` (`5¹⁴ ≈ 6.1 × 10⁹` per τ) and cubic `H = 1` (`3²¹ ≈ 1.0 × 10¹⁰` per τ); beyond it is
  `[Open]`.
- **Kill criterion [Heuristic]. Not established by R3.** R2's half holds (`J_min = n − 2`), but
  R3's half is a bounded-height ℚ-point statement on a general-type surface; it says nothing
  about `V_τ(L)`. The route is **parked, not closed**: it needs `n − 2` simultaneous `L`-points,
  with no group-law handle (R1), no way to lower the count (R2), and no computation that can
  see `L`-points (R3). R4/R5 stay unlaunched under the plan's order. Not closed: R2's Type II
  conic/determinantal n = 7, `J = 0/1` search and the cubic-Bézier real crossing count, both
  `[Open]`.

**Order.** R1 ∥ R2 first (paper only, one session each). R3 after R1. R4, R5 only if R2 does not kill
the route.

**Kill criteria.**
- R2 shows J_min(n) ≥ n − c for a fixed c, **and** R3 finds no structured point at n = 7 with the
  n = 5 control passing. Then write the route up as closed for constructions of this shape.
  (R3 has run and did **not** establish the second half; see the R3 completion block above.)
- R1 fails to give a usable group-theoretic handle (the doubling locus is as bad as V_τ). Then R3
  falls back to plain search and the route's odds drop sharply.

**Insight to carry in.**
- Only the *product* ∏Q_j(τ) can be made a square for free (interpolate y² at τ when 2J ≥ n − 1).
  The whole difficulty is splitting that one square into J separate ones. That is exactly the
  gap between a point of H and a point of the multiquadratic cover of H, which is the pull-back of
  H under multiplication by 2. So the natural objects are Jac(H) and its 2-isogenies, not V_τ.
- No rational curve parametrises two definite forms at once (a pencil of binary forms with four
  square members violates Riemann–Hurwitz). So any success is through genus ≥ 1.
- The moduli of H are free and defined over L, while the point is over K_L. Families of abelian
  varieties over a rational base can have unirational total space when the family is "small"
  (the Weierstrass family through two points is 𝔸⁴; Kuga–Sato varieties of level 1 have p_g = 0 up
  to the 9-fold product). Whether the analogous total space here is unirational for small J is
  the one place where a genuinely positive surprise is possible. R1 should compute this for J = 2, 3.

### E-P: arithmetic for F (a targeted pseudo-real-closed statement)

**Where it stands.** (PRC₈) is open and unstudied (L1). Theorem H (P1, Q1) gives E-points only in
the circle-method range, which no route reaches (Q2, Q3). Taylor's question implies (SR) and (SR′).

**Why another look is justified.**
- We do not need (PRC₈). For each K we need **one** point on **one** of countably many explicit
  twisted covers: I_{K′,D}, 𝒞_{K,p,q}, 𝒮_{K,p,q}, and the power × power family (C1 §3–4).
- Local solubility is already free over ℚ^{tr,solv} (Lemma LS). Only the passage from local to
  global is missing. For curves there is a standard conjecture about exactly that.
- Nobody has tried to *refute* the statement for F. A week spent on that is cheap either way.

| id | kind | question | depends on |
|---|---|---|---|
| P1′ | math | **DONE 2026-11-12 (see below).** **State the minimal conjecture.** "(T_K): for every number field K with a real place there are a totally real solvable L (or L ⊂ F) and (p, q) such that the twisted cover has an L-point of the required real type." Give it in the three equivalent forms: twisted cover; specialisation ("K_L is the root field of a member of the family over L", the Beckmann–Black / parametric-extension language of Dèbes, König–Legrand); multiplicative ("u and 1 − u dependent modulo L^×", C1 §4). Record exactly which real points are needed. | — |
| P2′ | math, Opus-level | **DONE 2026-11-12 (see below).** **Brauer–Manin under solvable base change.** For a curve X over a number field, the conjecture of Poonen and Stoll says X(𝔸)^{Br} = ∅ whenever X has no rational point; for curves the Brauer set equals the finite abelian descent set. Question: for X one of our twisted curves and (x_v) an adelic point, is there a totally real solvable L′ over which the base change of (x_v) survives *every* finite abelian descent? For one covering it is plausible (the obstruction is a class in a Selmer-type set attached to a finite Galois module, and Lemma LS lets us choose L′ with prescribed local behaviour). The difficulty is uniformity: there are infinitely many coverings and L′ must be one number field. Sub-questions: (a) how do Selmer sets of the n-coverings of Jac(X) behave in solvable towers (they can grow; does the obstruction to a *given* adelic point die?); (b) is it enough to control the 2-part or one prime, using that our X have explicit maps to a conic with group A_n; (c) does the answer change if X is allowed to vary over the countable family, so that only one member needs an unobstructed point. Deliverable: either "Stoll's conjecture ⇒ the target" [Proof], or the precise place where base change cannot help. | P1′ |
| P3′ | math + computation | **Try to refute.** Look for an invariant that could prove some curve over ℚ with real points has no F-point. Already excluded: point degrees (solvable steps give every degree, so no index obstruction); composition factors (engines carry every A_n); Northcott (L1). Still to try: (a) a height or measure argument (the set of fields reachable by bounded-parameter engines of bounded complexity is thin; is there a counting statement that survives towers?); (b) a model-theoretic invariant of the closure (is the theory of F decidable or tame in a way PRC fields are not, or vice versa); (c) a p-adic analogue: for the closure of ℚ_p-points under the same operations, does the analogous statement fail, and if so does the failure globalise. | — |
| P4′ | computation | **Small models.** Replace 8 by d ∈ {2, 3, 4} and the engines by the trinomials of degree ≤ some bound, so that the closure E_d is computable to a few levels. Ask whether explicit curves of genus above the gonality range (first cases: genus 3 non-hyperelliptic for d = 2; genus 5 or 6 for d = 3, 4) have E_d-points, by exhaustive search over small towers. Evidence of points appearing at low level supports the conjecture; systematic absence at genus just above the gonality range is a warning. | — |
| P5′ | literature, then math | **DONE 2026-11-13 (see below).** **Rumely–Moret-Bailly with a shape constraint.** The proof that ℚ^{tr} is PRC builds a function on the curve whose fibres over an interval are totally real (capacity theory). Read the proof for curves with one question: can the construction be steered so that the fibre polynomial has a prescribed sparse shape (trinomial, Chebyshev trinomial, odd)? The Fekete–Szegő side works with Chebyshev polynomials of the real set, which is suggestive given Engine S, but the Galois type of the output is uncontrolled in every version we know. Deliverable: a yes with a sketch, or the precise step where shape control is lost. | — |
| P6′ | math | **(BD) through the circle method, one more time, with Engine S.** Q3 sharpened (BD) to "about 9n P-parameters per K-condition at bounded degree". Engine S gives real-rooted shapes of unbounded degree with 3 essential parameters, so it does not meet this. Record that explicitly and check the one remaining idea: Weil restriction along a *varying* extension (degree-D points on the condition curve, D large), which raises dimension to about D; C1's working showed the total space is a quotient of a product of two Galois-closure covers, not a complete intersection of low degree. Confirm and close, or find the gap. | — |

**P1′ done (2026-11-12): the minimal conjecture, stated; three forms proved equivalent.** See
`P1prime.md`, log `HANDOFF-alg-P1prime.md`, check script `scripts/P1prime_checks.py` (Python;
Wolfram unavailable).
- **"(or L ⊂ F)" is vacuous [Proof].** It is equivalent to β ∈ F (take L = ℚ(β)). The base class
  must be fixed: TR-solv ⊂ R-solv ⊂ E ⊂ F_{<n}. The headline is (T; R-solv), implied by Taylor's
  question and weaker in that only the one real place L ⊂ ℝ is constrained.
- **Lemma D [Proof].** For Gal ⊇ A_n, n ≥ 9, no L ⊂ F_{<n} splits K: L ∩ Ω ⊆ ℚ(√disc). An
  induction on n only enlarges the base field.
- **(T_β; 𝓛) [Proof of sufficiency].** There are L ∈ 𝓛, a real M ⊇ L(β) finite over L, and an
  engine member over L with a real root x₀, M = L(x₀). The engines are tri, power × power (pp),
  Chebyshev, five-term. Theorem X uses M ⊋ L(β), via the square lift.
- **Three forms ⟺ [Proof].** (I) the M-twist of the ordered-roots (Galois-closure) variety has an
  L-point; (II) M is a factor of a specialisation algebra; (III) dependence: 1, τ, τ^D L-dependent;
  τ, 1 − τ multiplicatively dependent mod L^×; Lissajous collinearity; five-term L-dependence.
- **Canonical curve [Proof].** pp(p, q) gives the M-twist of the Galois closure Ĉ_{p,q} of the
  three-point map x^p(1 − x)^q, with monodromy S_d for coprime p, q > 0. The genus formula
  reproduces H1's 47881 at D = 9. This is the object P2′ should take.
- **Real points [Proof].** For tri, pp and five any L-point gives a drawable crossing; the real
  condition is existence only. The capacities are tri 2/3, coprime pp **3** (Python check for
  |p|, |q| ≤ 7), sine engines all patterns. The lift is needed only when r ≥ 4 at σ₀. Taylor ⇒ (T)
  needs no density step except for the Chebyshev cosine form.
- **Lemma U [Proof].** After a totally real solvable base change, K_L/L is unramified at every
  finite prime.
- **Induction measures.** Discriminant: trivial by Lemma U. Height: not well-founded on F.
  Gonality: geometric gonality is constant in β, and F-gonality is circular. All three fail;
  insight (i) is untested beyond them.

**P2′ done (2026-11-12): Stoll's conjecture restates the target; base change acts only on the
cohomological layer.** See `P2prime.md`, log `HANDOFF-alg-P2prime.md`. Paper only, no computation.
- **Stoll restates, does not imply [Proof].** Under X(𝔸_L)^{f-ab}_• = X(L), (T_β; 𝓛) ⟺ some
  twisted Belyi curve X_L^{M,p,q} has a non-empty f-ab set off the branch fibres. No unconditional
  way to show f-ab non-emptiness without a point is known in genus ≥ 2.
- **Local solubility everywhere [Proof sketch].** Free after totally real solvable base change
  (Weil bound + Lemma LS/U). **Correction to P1′ §5:** an L-point needs r ≤ 3 at *every* real
  place of L, not only σ₀; take the lift constant c ∈ ℚ to make this uniform.
- **Proposition B [Proof].** Base change of a fixed adelic point x is f-ab-unobstructed over L only
  if [L:k]·c(x) = 0 in ∏J(k_v)_•/\hat{Sel}(J/k) (norm on Selmer groups). Non-torsion obstructions
  survive every finite extension. This answers the plan's literal question negatively.
- **Levels [Proof, given a degree-1 class].** f-ab ≠ ∅ iff every level is non-empty over the same L
  (compactness). Each odd level clears after totally real solvable base change, but the
  construction needs local degree ≈ 4g·log_p n, unbounded in n: no single number field.
- **Two layers.** Layer 1, the Pic¹ class in Sha(J/L): cohomological; Ciperiani–Wiles is the
  genus-1 precedent; [Open]. Layer 2, ι(x) ∈ \overline{J(L)}: the Mordell–Weil sieve. It is
  non-cohomological, Lemma LS does not reach it, and by Siksek's dimension count plus rank
  heuristics in solvable towers it gets more rigid up the tower [Heuristic]. **This is the place
  where solvable base change cannot help.**
- **Sub-questions.** (a) Selmer growth is irrelevant for fixed points. (b) The conic is ℙ¹ over L and
  contributes nothing [Proof]; one prime ℓ keeps the full ℓ-adic Chabauty problem. (c) Jac(X) ~
  ∏_ρ B_ρ ⊗ ρ_c with B_ρ over ℚ fixed (trivial, sign and standard pieces vanish); the family gives
  structure for P3′, not leverage.
- **Kill criterion, first half:** met in the scoped sense above (not a claim that no L works).

**P5′ done (2026-11-13): no; shape control is lost at the global step.** See `P5prime.md`, log
`HANDOFF-alg-P5prime.md`, check script `scripts/P5prime_checks.py` (Python; Wolfram not attached).
- **Method, for F [Proof sketch].** With no integrality, RMB is local functions (S1), weak
  approximation in a Riemann–Roch space (S2), optional Hilbert irreducibility (S3). Capacity
  theory and Fekete–Szegő patching serve only integrality, so they are not the lever.
- **Steering is the problem [Proof].** Some f has a fibre over an e-field ⟺ X has a point over an
  e-field. For the canonical curve that is (T_β; one-step engine fields): the target one level up.
- **Not local once N ≥ 5 [Proof; Python].** "M is a tri(N)-field" is a point on the M-twist of a
  complete intersection of genus 0, 4, 49, …, 47881 (N = 4, 5, 6, …, 9), equal to H1's Γ and the
  Ĉ genus. For pp the curve has genus ≥ 4. At N ≤ 4 it is a conic (Hasse–Minkowski), so it is
  local, but those degrees are solvable. RMB imposes only S-adic open conditions.
- **Generic shape [Proof].** Every fibre is engine-shaped iff X is a component of a pull-back
  W_λ. For pp the codimension in the Hurwitz space is 2m(N − 2) − 1. Under Bombieri–Lang,
  infinitely many good fibres need an isomorphism correspondence between f and the engine (F2's
  object).
- **Signature [Proof].** Totally real fields of degree ≥ 4 are never tri- or pp-fields
  (capacity ≤ 3), so the PRC form is the wrong statement for those engines.
- **Chebyshev [Proof].** On ℙ¹ the output T_N = t₀ is a cheb member (drawable). For genus ≥ 1,
  f = h ∘ φ controls only the bottom layer (Lüroth), so the hint does not lift.
- **Open.** Is the twisted canonical curve *engine-resolvable* (a tower of engine pull-backs) over
  a real solvable L? The untwisted Ĉ is, by its Galois-closure tower, but that tower does not
  descend to the twist. Is Sh_cheb(M) (a surface) unirational? Is some degree-5 field with given
  local data provably not a tri(5)-field (a genus-4 Chabauty problem)?

**Order.** P1′ first (short). Then P2′ ∥ P3′. P4′ can run at any time on Sonnet. P5′ after P2′ if P2′
does not close. P6′ is a half-session check.

**Kill criteria.**
- P2′ shows the obstruction cannot be removed by solvable base change for these curves, **and** P3′
  finds no refutation mechanism. Then E-P ends with: the target is equivalent in difficulty to
  Taylor's question for an explicit countable family of curves, stated cleanly, and we stop.
- P3′ finds a refutation mechanism. Then everything redirects to making it a proof. That would be
  the first negative result of the programme and needs the user's decision before it is pursued,
  given the ground rule.

**Insight to carry in.**
- The object is a twisted Galois cover with group S_n (or S_{2p}) over a rational surface, and the
  only F-rational intermediate cover is the discriminant conic. So nothing abelian is visible on
  the cover itself; the abelian descent in P2′ lives on its Jacobian, which is large and whose
  torsion fields are **not** solvable. A tempting shortcut is false: Jac(X)(ℚ^{solv}) is not
  divisible, because ℚ(Jac[m]) has group inside GSp_{2g}(ℤ/m). Do not build on it.
- The freedom that Taylor's question does not use: (i) F ⊋ ℚ^{solv} ∩ ℝ, and F is closed under the
  engines themselves, so the statement is self-referential and could be proved by an induction on
  some complexity of K that we have not found; (ii) infinitely many varieties, one point needed;
  (iii) real, not totally real: only one real place of L is constrained.
- (i) is the most promising and the least explored. X1 tried induction on Galois class and found
  the base case blocked by three conjugation configurations. An induction that works would need a
  measure for which the engine step is *decreasing*. Candidates to test in P1′: the conductor or
  discriminant of K_L/L after the optimal solvable base change; the minimal height of a point on
  the twisted cover; the gonality of the cover over F.

### E.1 Resources and order across both

| step | streams | model | sessions |
|---|---|---|---|
| 1 | R1 ∥ R2 ∥ P1′ | Opus-level for R1; others Sonnet-capable with review | 1 each |
| 2 | P2′ ∥ P3′ ∥ R3 | Opus-level for P2′ | 1–2 each |
| 3 | P4′ (background), P6′ | Sonnet | 1 |
| 4 | R4, R5, P5′ as warranted | — | — |
| 5 | consolidation into SUMMARY §12 | orchestrator | 1 |

Rules as in §4: every claim labelled; Wolfram for computations where available, Python labelled as
the fallback; one note and one handoff log per stream in `notes/algebraic/`; no `Defs` changes; a
positive control for every search.

### E.2 Not in this phase

- A `Defs` change (a two-curve or multi-frequency operation). It remains the most realistic way to a
  complete solution and remains the user's decision (SUMMARY §10 item 3; C1 §6.1).
- Degree 9 totally real through the one-line reduction, the explicit S₁₀ decic, and Lean for the
  solvable case and Engine S. These are the achievable targets and can run independently.

## Phase F: forward search (planned 2026-11-13; stages A and B complete, see `F1.md`)

See `PLAN-forward-search.md`. It replaces P4′. Idea: enumerate the engine parameter `λ` over
small solvable fields and keep the cases where the fibre field descends to a field `K` over ℚ, so
that `K` is an output, not an input. Solutions with `[ℚ(λ):ℚ] = m` are rational points of a fixed
`m`-dimensional variety `W_m`; a family of solutions is a special subvariety of `W_m`, i.e. an
identity between engine maps, and that is what the search looks for. Degree 5 (Bring–Jerrard) is
the positive control and the calibration.

Stage A (`F1.md`): exact FLINT pipeline (no PARI) with 50 passing checks; `W_m = Ĉ^m/(S_d × S_m)`
(no twist); `tri(D) = pp(D − 1, 1)` up to Möbius, so the engines of degree `d` are the coprime
`pp(p, q)`, `p > q`; `W₂` is of general type for all 8 engines with `7 ≤ d ≤ 9`, not shown for
`d = 5, 6` (at `d = 5` rational or general type, open); `Ĉ` for `tri(5)` is Bring's curve.

Stage B: Bring–Jerrard gives proved `tri(5)` solutions for all 20 test quintics (exact Trager check;
filter never rejects). Sizes: `m = 6` (32–118-digit `h`) or `m = 12` (186–351 digits, including all
totally real fields, which admit no real `λ`). So stage C can only find unexpectedly small
solutions; C4 should enumerate by tower or be dropped.

Families (`F2.md`, 2026-11-13): at `d ∈ {8, 9}` every family of `m = 2` solutions (for `K` with
group `⊇ A_d`) lies over a curve `Γ ⊂ ℙ¹ × ℙ¹` along which the two fibre covers are isomorphic
(Goursat plus a computed Riemann–Hurwitz bound). Hecke-type (étale) ones are excluded for `d ≥ 7`,
because the triangle groups `Δ(2, pq, d)` are non-arithmetic and maximal (Takeuchi, Margulis,
Singerman). Bidegrees `(1, k)` and `(2, 2)` are excluded by proof, and `(2,3)`, `(3,3)` by an
exhaustive search over `F_ℓ`. What remains is ramified isomorphism correspondences of higher
bidegree, with no known construction. At `d = 5` the explicit commensurator correspondence
is not a family, and could only reach F20 quintics anyway.

## Phase D9: degree 9 and 10 (planned 2026-11-13; D0 done, see `PLAN-degree9.md`, `D0.md`)

The all-n target is set aside; `PLAN-degree9.md` aims at T9Q (every real algebraic number of degree 9).
D0's census at n = 9:

- No drawable pair has 10 jointly linear dials. The maximum, F = 9, needs a rational sextic.
- New row **E**: a cubic Bézier `(t², Y(t))` against `y = g(x)` with `g ∈ ℚ[x]` of degree ≤ 6.
  It works iff `s_{(4,3,2,1)}(τ₁, …, τ₉) = 0` for some `τ ∈ K`.
  - The condition has degree 10, is linear in `e₇`, and contains `{p₁ = p₃ = p₅ = 0}`.
  - It solves an explicit totally real S₉ nonic (positive control).
  - A height-1 search on the non-degenerate field `q₃` found nothing.
- The test field `∏(x − i) + 1` used so far is an odd-engine field. It is degenerate for these
  searches; use `q₃`.

E (2026-11-13, `D1E.md`), open:
- The condition is `25 Tr τ³ · Tr τ⁷ = 21 (Tr τ⁵)²` for centred τ.
- E polynomials are exactly `σ(t)E(t²) + r(t)`, so T9Q-via-E is versality of that 8-parameter
  family.
- Height-2 search null with a working control; no local obstruction on `q₃`.

D1 (2026-11-13, `D1.md`):
- Over ℚ it is dominated by E (degree 30).
- Over F with `g` fixed rational it has one condition on the generator and real capacity 18: a
  new single-condition F-row, degree unmeasured.

H (2026-11-13, `H-deg9.md`), dominated:
- over ℚ the fibre over a generator is a 3-fold of degree 266 in `ℙ⁵`;
- over F, `c_τ = 3`.

D9 stage 1 (E, D1, H) is done without closing T9Q; open threads are listed in `PLAN-degree9.md`.

D3 (2026-11-13, `D3.md`), open:
- the layer-2 genus-1 square condition is handled by R5 (j-matching the layer to the cubic through
  the conjugates of a K-point);
- 4 conic-support conditions at the partner remain.

D4 (2026-11-13, `D4.md`): the one condition has degree ≥ 36, so it is killed for Lemma A (scoped).
