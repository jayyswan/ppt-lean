# PLAN-degree9: raising the degree bound past 8

Planned 2026-11-13. **Nothing launched.** Launch on the user's go-ahead.

The all-n target is set aside (user decision, 2026-11-13). This plan aims at specific degrees:
9 first, then 10, for rational coefficients and for P coefficients.

**Ground rules.**
- Research only until a route closes on paper; then one Lean stream per closed case.
- **No `Defs.lean` changes, and no suggestions of any.** Every curve used must be one of the
  existing constructors. A route that needs a new curve is out of scope.
- Every claim labelled ([Proof], [Proof sketch], [Computed, exact], [Heuristic], [Open]).
- Every negative is scoped to the route it blocks.
- Every search has a positive control run through the same code.
- One note `D<k>.md` and one log `HANDOFF-alg-D<k>.md` per stream, in `notes/algebraic/`.

Read first: `SUMMARY.md` §1, §9, §10; `N2.md` (overshoot, the Descartes table); `W1.md` §0;
`R2.md` review corrections; `B3.md` findings.

## 0. Targets

| id | statement | what is missing today |
|---|---|---|
| **T9Q** | Every real algebraic number of degree 9 over ℚ is P-constructible. | Totally real nonics with group A₉, S₉, PSL(2,8) or PΓL(2,8). Everything else is proved (nonreal root: Lean; solvable: Lean; imprimitive: degree-8 theorem over P). |
| **T9P** | Every real root of a degree-9 polynomial with P coefficients is P-constructible. | At least 3 nonreal pairs: on paper (THREE-PAIRS), certificate not found (N1a), not in Lean. At most 2 pairs: open. |
| **T10Q** | The same for degree 10 over ℚ. | A₁₀/S₁₀ with a nonreal root: one rational point on a Fano variety (MI-1). A₁₀/S₁₀ totally real: one P-line on a threefold. Other groups: towers (H5), group list from memory. |
| **T10P** | The same for degree 10 over P. | Open; no route recorded. |

**Success** is T9Q. It raises the headline number from 8 to 9. T9P, T10Q and T10P are stretch
targets, in that order.

**Why degree 9 is not the all-n problem.**
- Resolvent degree does not obstruct a construction uniform in the field (Hilbert covers 9).
- One case is missing, and the obstruction in it is realness: for a totally real field the
  second power sum is positive, so the existing nonic proof (kill `p₂` by Meyer) cannot start.
- The degree-9 streams were parked on 2026-11-04. Tools found later (P-points instead of
  ℚ-points, Theorem G, Engine S, overshoot, the tower rank counts) were never applied to it.

## 1. The working principle

The root β is unknown; the curve parameters ("dials") must be numbers already constructed.
"The curves cross at β" is one equation over ℚ(β), hence 9 equations over the base field.

- If at least 10 dials enter **linearly**, a solution exists by linear algebra and is
  automatically constructible. This is the only mechanism that has ever closed a degree.
- Otherwise the dials satisfy a polynomial system, and we need a P-point on its solution
  variety. That works when the variety has degree below 9 with a smooth real point (H2 Lemma A),
  or carries a curve of low gonality over a subfield of P (A1 Theorem G), or can be solved one
  step at a time with steps of degree ≤ 8.

So each stream below is judged by three numbers at degree 9: how many dials are jointly linear,
the dimension of the solution variety, and its degree.

## 2. Stage 0: the degree-9 census (one session)

**D0. Linear-dial census at n = 9, totally real.** R2 counted jointly linear dials for offset
towers only. Do it for every pair of drawable families.

- Families: rational `poly_graph` (degree ≤ 6) and its P-affine images; P-quartic graphs (Lemma
  Q); conics; `power_law` with rational exponent; cubic Bézier; text-warp quartics (egg,
  piriform); offsets of each; rotations of each.
- For each pair record: crossing degree; real capacity (must reach 9); jointly linear dials
  (Type I in R2's sense); remaining conditions; dimension of the solution variety with a
  rational, and with a P-valued, change of generator.
- Output: one table, sorted by remaining conditions, with the realness filter applied. Rows
  with real capacity below 9 are dropped for T9Q but kept for T9P.
- Known rows to reproduce as a check: odd engine (4 conditions); N2 overshoot with a rational
  sextic (2 conditions, degree 1428); Bézier × Bézier (1 condition); depth-2 tower × circle
  (rank 10).

D0 decides the order of D1–D5. The order below is the default if D0 finds nothing new.

## 3. Stage 1: routes for T9Q

### D1. Cubic Bézier against a rational sextic graph

- **Set-up.** Find a generator τ of K, rational cubics X, Y and a rational sextic S with
  `Y(τ) = S(X(τ))`, not of the trivial kind `S` linear, `Y = S∘X`. Then the Bézier arc
  `t ↦ (X(t), Y(t))` meets `poly_graph S` at parameter τ, `inter_x` gives `X(τ)`, and τ is a
  real root of a cubic over P.
- **Count [Computed, exact, 2026-11-13].** For fixed τ and X, the condition is linear in
  (Y, S): `span(1, τ, τ², τ³) ∩ span(1, ξ, …, ξ⁶)` with `ξ = X(τ)`. It always contains
  `⟨1, ξ⟩` (the trivial solutions). A third dimension is one condition on X. For
  `q = ∏_{i=−4}^{4}(x − i) + 1`, `τ = β`, `X = t³ + a t² + b t`, it is a plane curve of degree 19
  in (a, b).
- **Work.**
  1. Let τ vary over K as well. The condition becomes one hypersurface in about 9 rational
     variables. Compute its degree and singular locus.
  2. It is determinantal. Look for linear spaces, rational subvarieties, or a parametrisation.
  3. Exact box search for rational points (one equation, so cheap), with the nonreal-root
     nonic as positive control.
  4. Variant with X quadratic (crossing degree 12).
- **Kill.** Degree far above the number of variables, no structure found, and a null search to a
  height where the positive control succeeds.

### D2. N5 revived: the overshoot locus with P-points

- N2's overshoot engine leaves 2 conditions for totally real nonics; the locus W has degree 1428
  and real points in every totally real K. It was searched over ℚ only.
- **Work.** Describe W as a variety over ℚ twisted by K: components, dimension, singularities,
  low-degree subvarieties. Apply Lemma A and Theorem G. State exactly which coordinates must be
  rational (the sextic's) and which may be in P.
- **Kill.** W is irreducible of general type with no curve of gonality ≤ 8 visible, as B3 found
  for the line surface.

### D3. Offset towers with a spare parameter

- At n = 9 a depth-2 tower against a circle has rank 10 (W1), one more than needed, and no
  realness obstruction. The solution family for a fixed field is positive-dimensional. At
  n = 10, where it was searched, it has dimension zero.
- **Work.**
  1. For one explicit totally real S₉ nonic, compute the real solution family: dimension,
     degree, components. Confirm the count against W1's rank.
  2. Look inside it for a step-by-step solution, a rational curve, or a curve Theorem G handles.
  3. State the square conditions in this formulation (ELI5: each offset's unit normal is a
     square root at β). Check whether the spare parameter can be spent to make one of them hold
     identically.
- Related, unlaunched: **R5** (for n ≤ 9 the nine conjugate points lie on a cubic over the base
  field; is there a tower shape whose genus-1 quotient uses it?) and **R4** (generators chosen so
  two square conditions hold structurally). Fold both into D3.
- **Kill.** The family has no component of degree < 9 and no low-gonality curve, and R5's linear
  system stays too small.

### D4. Two P-quartic graphs, one rotated

- Curves `y = Q(x)` and `x = R(y)` with Q, R quartics over P (Lemma Q plus `rotate`). The
  crossing polynomial is `R(Q(x)) − x`, of degree 16. No rationality conditions, real capacity
  16.
- **Count [Heuristic, 2026-11-13].** For a fixed generator there are 9 conditions on 8 effective
  parameters, so no solution is expected. With the generator free the solution family has
  expected dimension 6.
- **Work.** Verify the count numerically on one nonic. Compute the degree. Look for a
  step-by-step solution. The cubic∘cubic case (degree 9, no overshoot) is the positive control
  for the code.
- **Kill.** As D2.

### D5. B3's leftovers on the line surface

- The intrinsic curves Γ₇, Γ_{2,4}, Γ_pl on the surface S of good lines have unknown gonality
  over F. The irregularity and fibrations of S are unknown.
- **Work.** Compute genus and gonality bounds for the three curves. Compute `q(S)`.
- **Kill.** All three have gonality above 8 and S has no fibration over a curve of genus ≤ 1.

## 4. Stage 2: T9P (P coefficients)

- **E1. Finish THREE-PAIRS (at least 3 nonreal pairs).** N1a's blocker was a rational
  certificate centre. Z8 showed the centre need not be rational. Rewrite the chain with a
  P-valued centre, then formalise (Engine9, Resolvent9, ChainOpen are not blocked).
- **E2. At most 2 nonreal pairs.** By N2's Descartes table the shape must be odd or even
  (4 conditions each). Only the routes with all dials in P carry over: D3 and D4. Run E2 after
  D3 and D4 report, on whichever survives.
- A success in D3 or D4 that never uses rationality closes T9Q and T9P together.

## 5. Stage 3: degree 10

Run only after Stage 1 reports.

- **G1. MI-1.** A rational point on the (2,3) complete intersection `V'_K ⊂ ℙ⁸` for every decic
  field with a nonreal embedding. It worked on examples for s = 1, 3, 5 and failed to height 4
  at s = 4. Work: the s = 4 case; bad-prime local solubility; a fibration into conics or
  quadrics.
- **G2. Totally real decics.** One P-line on Y₀ (Engine C). Same kind of problem as D5.
- **G3. Transfer.** Whatever closed degree 9: redo its count at n = 10 and n = 11.
- **G4. The explicit S₁₀ decic in Lean** (H5's worked example). Independent of everything else.

## 6. Order and resources

| step | streams | model | sessions |
|---|---|---|---|
| 1 | D0 | Opus-level | 1 |
| 2 | D1, D3 in parallel | Opus-level; computation on Sonnet | 2–3 each |
| 3 | D2, D4, D5 as D0 ranks them | Opus-level | 1–2 each |
| 4 | E1 (independent; can start at step 1) | Lean worker | several |
| 5 | E2, G1–G4 | as warranted | — |

Review each stream's note before the next step, as in Phases E and F.

## 7. Deliverables

- `D0.md`: the census table.
- `D1.md` … `D5.md`: one per route, each ending with "closed on paper", "killed (scoped)", or
  "open, with the exact remaining problem".
- If a route closes: a statement of the theorem, the full chain of constructions with every
  curve named by its constructor, and a Lean plan.
- `SUMMARY.md` §1 updated at the end.

## 8. Cautions

- Every route here ends, at worst, at the same kind of problem as before: a P-point on a
  variety. The bet is that at degree 9 one of these varieties is small enough (degree below 9,
  low gonality, or a step-by-step solution). Nothing guarantees that.
- The counts in D1 and D4 were made on 2026-11-13 in conversation. D1's degree-19 figure is
  computed for one nonic; D4's count is a parameter count only. Both need checking in D0.
- A rational box search that finds nothing is weak evidence unless its positive control is of
  comparable size (lesson of R3 and F1 stage B).
