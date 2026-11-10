# PLAN-offset-inversion: everything about `arc_of_length` along offset curves

Read this first, every task. The starting point is `notes/offset-inversion-tangent-angle.md`.

## 0. What is known going in

Every item below is from that note: checked in Wolfram to about 40 digits, or proved on paper.
None of it is in Lean.

1. **Mechanism.**
   - Take a drawable curve with Whewell function `s = R(ψ)` (arc length as a function of
     tangent angle). Offset it by `d`. On a cusp-free stretch, the offset's arc length is
     `ΔR − dΔψ`.
   - Lay an arc of P-constructible length `x` along the offset with `arc_of_length`, then read
     the endpoint with `box_xmax`/`box_ymax`.
   - Together these solve **`R(ψ) − dψ = x`**.
2. **Coordinate.** Put `slope = sinh u`. Then `ψ = gd u`, and the equation becomes
   `A(u) − d·gd(u) = x` with `A = ∫ S du`, where `S = ds/du`.
3. **Parabola.** `sinh(2u)/4 + u/2 − d·gd u = x` has P-constructible roots for P-constructible
   `d < 1` and `x`.
4. **Power laws.** `y = x^{1+1/n} + m x` gives `S ∝ cosh²u (sinh u − m)^{n−1}`.
   - Neile's semicubical parabola collapses to `sec³ψ = αψ + β`, a single-trig equation that
     was already reachable.
5. **Dictionary of hard equations** (each needs one curve that has not been drawn):

   | Equation | Missing curve |
   |---|---|
   | `tan x = λx`, and `tan α − α = c` (the gear involute function) | catenary |
   | cantilever beam `cos x cosh x = −1`, equivalently `x + gd x = π`, equivalently `sin x = tanh x` | `y = ln sec x` |
   | goat-grazing problem | a transcendental curve |

6. **[Heuristic], not proved.** Single intersections cannot solve equations that need `u` and
   `gd u` together.

**Goal of this programme:** a complete map of the offset-inversion family.

- Which equations it solves, for every curve in the drawable tower.
- Why intersections cannot reach them, as a theorem.
- What it combines with.
- Which named problems fall into it.
- A Lean headline theorem.

**Survey, not hunt.** The named equations in §0 are entries in a catalogue, not the
measure of success. A family that solves nothing named is still a result: report it in full.
Never drop a path because it misses a particular target.

**Not in scope:** adding curves to `Defs.lean`. Curves outside the current constructors (catenary,
spirals, …) are investigated only in `PLAN-ppt-tan-curves.md`.

## 1. Ground rules (all tasks)

- **One agent, one deliverable, one file.** Keep a progress log at the repo root,
  `HANDOFF-offinv-<id>.md`. Create it first, then append a line after every step.
- **Research tasks** write `notes/offset-inversion/<id>.md` and never edit `.lean` files.
  - Use Wolfram (`WolframLanguageEvaluator`) for every identity: at least 30 digits, or a
    symbolic proof. Python (mpmath) is a fallback only, and the note must say which backend
    produced each number.
  - Do the whole computation in **one** Wolfram call; session state does not persist between
    calls.
  - Label every claim **[Proof]**, **[Wolfram]**, **[Heuristic]** or **[Open]**.
  - **Never claim a negative result is proved without a proof.** "I found no route" is a
    `[Heuristic]`.
- **Lean tasks** follow `CLAUDE.md`:
  - lean-lsp loop; no whole-project build; one narrow `lake build` at the end;
  - targeted imports;
  - a `-- Theorem:` line on every theorem;
  - no `sorry`;
  - commit locally, and **never push**.
- **Uniform convention.** This is how impossibility statements are phrased (see
  `sheared-sine-intersections.md` §3). A construction "solves a family" if one configuration
  solves it for all values of the family parameter, changing only P-constructible data that
  does not depend on the unknown root.
- `Defs.lean` is fixed. If a task finds that a constructor's hypotheses block a step, it
  reports that and does not propose an axiom change.

## 2. Streams

| id | wave | kind | deliverable | depends on |
|---|---|---|---|---|
| W0 | 0 | tooling | `notes/offset-inversion/atlas.wl` + `W0.md`: Wolfram routines (spec below) | — |
| R0 | 0 | math vs `Defs` | `R0-foundations.md`: exactly when offset inversion is a legal construction | — |
| R5 | 0 | literature | `R5-named.md`: named problems in the angle–arc-length class | — |
| L0 | 0 | Lean (tiny) | `Pptc/OffsetInversion/Projectile.lean`: `θ* = arccot λ` | — |
| R1 | 1 | math | `R1-whewell-base.md`: Whewell catalogue of every base curve and its affine images | W0 |
| R2 | 1 | math | `R2-tower.md`: Whewell functions through the offset/affine tower | W0 |
| R3 | 1 | proof | `R3-separation.md`: intersections versus offset inversion, as theorems | R0 |
| L1 | 1 | Lean | `Pptc/OffsetInversion/Speed.lean`: speed of `offsetParam` | R0 |
| L2 | 2 | Lean | `Pptc/OffsetInversion/Parabola.lean`: the headline theorem | L1, R0 |
| R4 | 2 | math | `R4-combinations.md`: composites, parameters from outputs, non-uniform hits | R1, R2 |
| S | 3 | synthesis | `notes/offset-inversion/SUMMARY.md` + an update to the 0-section of this plan | all |

Wave-0 tasks run at once. Each later wave starts once its inputs exist.

### W0: Wolfram atlas (tooling)

A single `.wl` file that the other streams `Get[]` at the top of their one-call computations.
It provides:

- `whewell[curve, t]`: returns `{ψ(t), s(t)}` for a parametrized curve, symbolic where possible.
- `offsetArc[curve, d, {t0, t1}]`: numerical offset arc length, using `Abs[1 − dκ]` honestly.
- `offsetInvert[curve, d, t0, x]`: solves for the endpoint parameter, and reports any cusp
  crossed.
- `checkIdentity[lhs, rhs, pts]`: residuals at 40-digit working precision.

It must reproduce the parabola checks of the source note as a self-test.

### R0: foundations against `Defs.lean`

Read the `offset`, `arc_of_length`, `arc_length`, `box_xmax`/`box_ymax` and `restrict`
constructors, and `speed`, `unitNormal`, `offsetParam`, `arcLengthOf` (Defs.lean). Also read
`Pptc/Offset.lean` and `Pptc/BoxOffset.lean`. Answer each of these precisely:

1. **Speed identity.** Is `speed (offsetParam γ d) t = |1 − d κ(t)| · speed γ t` true with
   *these* definitions, including the sign convention of `unitNormal`? State the exact
   hypotheses: `C²`? nonvanishing speed?
2. **`arc_of_length` hypotheses.** Which offset arcs satisfy them (an injective,
   differentiable, integrable tracing)?
   - What happens at an offset cusp? Is the traced arc still injective? Is the tracing
     differentiable there?
   - So can an arc be laid **across** a cusp, where the arc length is `∫|1 − dκ|`? That
     doubles the reachable equation family to `R(ψ) − dψ` on each side.
3. **The starting point.** It must be P-constructible, as must `ψ` there. Which starting points
   qualify: vertices, points at P-constructible parameter, cusps?
4. **Readout.**
   - When is the laid arc monotone in a coordinate, so that `box_*` returns the endpoint?
   - Otherwise, can the endpoint be isolated by `restrict`, or by an intersection?
   - Give the parabola's readout explicitly: the endpoint abscissa `w(1 − d/√(1+w²))`
     determines `w` through a quartic.
5. **Statement.** Write the general **offset-inversion lemma** in `Defs` vocabulary, so that
   L1/L2 can state it verbatim.

### R1: Whewell catalogue of base curves

For every base curve, and every affine image of it, give:

- `R` in closed form, in the clean coordinate (`ψ`, `u = asinh(slope)`, or the natural
  parameter);
- whether `R` is elementary, and otherwise its genus and kind (first, second or third);
- the reachable equation `R − dψ = x`;
- whether that equation *collapses*, as Neile's does, to a form a single intersection already
  solves.

The curves:

- **Parabola**, including all affine images. These are all parabolas up to similarity, so
  check that nothing new appears beyond scale and the shift `ψ ↦ ψ − ψ₀`.
- **Polynomial graphs of degree ≤ 6** (rational coefficients, then scaled).
- **Power laws `y = a x^p`, all rational `p`.** Use Chebyshev's criterion to classify which
  are elementary: these are `p = 1 + 1/n` and `p = 1 + 1/(2k−1)`; confirm this, and list the
  incomplete-Beta forms for the rest. Then the affine images:
  - **Shears matter.** Slope `w ↦ w + m` mixes families.
  - **Non-conformal stretches** act on the angle by `tan ψ' = Möbius(tan ψ)`.
- **Cubic Bézier,** general. `R` is elliptic. Is the `ψ` term a new, independent function, or
  absorbed?
- **Ellipse:** `E` in the eccentric anomaly; `ψ = arctan((b/a)·cot φ)`.
- **`exp_two` and its affine images.** The source note found a junk term
  `√(1+w²) − ln(1 + √(1+w²))`. Is it unavoidable under every affine map?
- **Sheared sines,** in the normal form `(−bt + sin t, at)`: `Λ − d·arctan(a/(cos t − b))`.
- **Rectangle and lines:** trivial; say so.

Output: one table (curve → `R` → equation family → elementary? → collapses?), then a
derivation per row.

### R2: the tower

Drawable curves are built from base curves by affine maps and offsets, in any order and
repeated. Questions:

1. **Affine after offset.** The speed of `A(P_d)` is `|1 − dκ|·|Aγ'|`, so its arc length is
   `∫|Aγ'| − d∫(|Aγ'|/|γ'|) dψ`.
   - What is the second term? It is a *weighted* angle integral, and in general not
     elementary.
   - When is it a new function rather than a combination of known ones?
2. **Offset again.** Offsetting `A(P_d)` by `d₂` gives the equation
   `L_{A(P_d)} − d₂ ψ_{A}' = x`. Here `ψ_{A}'` is the tangent angle of `A(P_d)`, which equals
   that of `Aγ`: `arctan(Möbius(tan ψ))`.
   - So one equation can carry **two different angle functions**,
     `arctan(slope)` and `arctan(Möbius(slope))`. Determine exactly which pairs, or longer
     lists, of angle functions can appear together, with independent coefficients.
   - This is the most likely place for new equations.
3. **The family of reachable `(A, angle-combination)` data.** Does it ever contain:
   - `S(u) = cosh u` (catenary-like);
   - `S = const` (log-cosine-like);
   - or any equation with the same roots as `tan x = λx` or the beam equation, uniformly?

   The congruence argument (a Whewell function determines its curve) excludes a single
   *curve*. It does not exclude a tower arc whose equation is a different function with the
   same roots. Settle this or label it `[Open]`.
4. **Genus and kind** of the integrals that appear, so that R4 knows what it is combining.

### R3: separation theorems (proof stream)

Make the source note's `[Heuristic]` into theorems under the uniform convention.

1. **Tower normal form.** Every drawable curve is one of:
   - algebraic;
   - `(αt + A₁(e^{λt}), βt + A₂(e^{λt}))`;
   - `(αt + A₁(sin t, cos t), βt + A₂(sin t, cos t))`,

   where each `Aᵢ` is algebraic and, for the trig tower, bounded. Prove it by induction on
   the constructors (restrict, affine, offset, `arc_of_length` subsets).
2. **The intersection class.** Characterize the equations solved by one intersection of two
   tower curves, and by one box.
3. **Separation.** Prove that no single intersection, and no single box, solves the parabola
   family `sinh(2u)/4 + u/2 − d·gd u = x` uniformly in `x`. Reuse the analytic-continuation
   argument from `sheared-sine-intersections.md` §3b, as poles or accumulation of zeros. If
   it does not go through, say exactly where it fails.
4. **What remains possible.** Does a two-step construction (intersection, then intersection)
   escape the class? Give the composition-depth bookkeeping.

### R4: combinations

1. **Feeding outputs forward.** Offset-inversion outputs can become `d`, `x`, affine data or
   endpoints of later steps. Does that enlarge the class beyond "one equation of the form
   `R − dψ = x` at a time"? Extend the "parameters computed from u" collapse argument
   (`Pptc/Jacobi.lean`, Outlook) to this setting.
2. **Non-uniform targets.** Search for constructions whose root coincides with a root of
   `tan x = x`, the beam equation, or the goat equation, by any combination available.
   Report numerical near-misses only as evidence, never as results.
3. **`am`.** Confirm that `dψ` has zero residue at `∞±`, so that offsets cannot cancel the
   residue obstruction (`sheared-sine-inversion.md` §4). Also check whether R2's weighted
   angle integrals change that conclusion.

### R5: named problems (literature + Wolfram)

Find classical and applied equations that mix an angle with arc length or with `gd⁻¹`. For
each, give the equation, its source, a numerical root (Wolfram), and its status:

- reachable now (by which route);
- in the offset-inversion class (which curve);
- needs a missing curve (which one);
- or none of these.

Seed list:

- rhumb lines and Mercator problems (`gd⁻¹φ = kφ + c`);
- the gear involute function `inv α = tan α − α` and its inverse;
- Euler elastica and pendulum separatrix (intrinsic equations);
- tractrix and catenary problems with given length;
- clothoid / Cornu spiral;
- relativistic aberration and rapidity versus angle;
- the projectile arc-length problems;
- Robin / Biot eigenvalues `x tan x = Bi`;
- spherical-well and beam eigenvalues;
- the goat problem;
- caustics.

### L0: projectile corollary (tiny Lean task)

In `Pptc/OffsetInversion/Projectile.lean`, prove that the maximizing launch angle `θ*` is
P-constructible.

- State it as: the unique `θ ∈ (0, π/2)` with `sin θ · log(sec θ + tan θ) = 1` is
  P-constructible.
- Proof: `θ* = arctan(sinh z₀)`, where `z₀ tanh z₀ = 1`, and `λ = csch z₀` is the Laplace
  limit constant.
- Find what `Basic.lean` already has (search `laplace`) and reuse it.
- If proving uniqueness costs more than about 150 lines, state the theorem for the explicit
  `arctan(1/λ)` together with the identity, and note the gap.

### L1: speed of the offset

In `Pptc/OffsetInversion/Speed.lean`, prove R0's speed identity in exactly R0's hypotheses,
for `offsetParam` as defined, with `speed` as `√(x'² + y'²)` (do not "simplify" it to a
norm). Corollary: on a window with `1 − dκ > 0`,

  `arcLengthOf (offsetParam γ d) a b = arcLengthOf γ a b − d (ψ b − ψ a)`,

with `ψ` given as an explicit `arctan` or `Complex.arg` of `γ'`. Choose whichever lands more
easily, and record the choice.

### L2: headline theorem (parabola)

In `Pptc/OffsetInversion/Parabola.lean`:

> For P-constructible `d < 1` and `x ≥ 0`, the unique `w ≥ 0` with
> `(w√(1+w²) + asinh w)/2 − d·arctan w = x` is P-constructible.

Route:

1. the parabola `poly_graph`;
2. `offset`;
3. `arc_of_length` from the vertex image `(0, d)`;
4. `box_xmax` on the laid arc;
5. a quartic for `w` (`root_Pconstructible_le_six_coeffs`).

Add a corollary in the `u` form, `sinh 2u/4 + u/2 − d·gd u = x`.

### S: synthesis

The orchestrator merges R0–R5 into `SUMMARY.md`:

- the full catalogue;
- the separation theorems as proved;
- the dictionary of named problems;
- the list of missing curves, ranked by what each unlocks;
- the open problems.

Then update §0 of this plan, and hand the missing-curve ranking to `PLAN-ppt-tan-curves.md`
(stream M there).

## R4 results (2026-11-03)

Note: `notes/offset-inversion/R4-combinations.md`.

- **Feeding outputs forward is triangular [Proof, adapted from spiral `C.md`].** Outputs used as
  `d`, `x`, start points, crop bounds, scale or rotation only extend parameters. They add no new
  equation shapes.
  - Curve-level composition reduces by a cut-commutation lemma [Proof sketch].
  - Two offsets add (`d1+d2`) where `1 − d1κ > 0`.
  - Chains of two offset inversions are [Open].
- **R2's N1 is a legal construction:** restrict → offset → `scale_y` → offset → `arc_of_length`
  → two boxes.
  - Correction to R2: the speed is `(1−d1/s³)t − d2c/t²`, and the curve is cusp-free iff
    `1 − d1 − d2c > 0`. R2's eq. (2.3) and its tables stand.
- **Non-uniform targets** (`tan x = x`, beam, goat): nothing found; 288 PSLQ tests at 130 digits.
  - New [Proof sketch]: an offset sheared sine never meets an algebraic offset/affine word to give
    `tan x = x` uniformly.
- **`am`:** confirmed [Proof + Wolfram]. `dψ` and R2's weighted angle forms are holomorphic at
  `∞±`, so offsets cannot cancel the residue obstruction.

Next: S (synthesis).

## Status: complete (2026-11-03)

S is written: `notes/offset-inversion/SUMMARY.md`.
- Every stream is done: W0, R0–R5 and L0–L2. The Lean files were repaired to the whole-curve
  `offset` axiom.
- The named payoff is gated on the catenary and the log-cosine curve. That ranking has been
  handed to `PLAN-ppt-tan-curves.md`.
- Open items are listed in SUMMARY §7.

## R6 postscript (2026-11-10)

Open item 3, "chains of two offset inversions", is taken up in `notes/offset-inversion/R6-chains.md`
(issue 18). Result: a chain is not a new mechanism.

- Same-word chains collapse to one entry: lengths add, and an offset/affine between the links only
  adds a P-constructible constant (Props. 2.1–2.3).
- Re-based chains are one-step entries whose data lie in the field of the first root (Thm 3.1), so
  they add numbers, not equation shapes (Cor. 3.2).
- What they genuinely add is a *coupling curve* of data: the first laid arc, traversed at unit
  speed (Prop. 4.2), algebraic for an algebraic base (§4.3).
- Consequently there is no depth-6 separation theorem to prove; the remaining question is the
  data-dependence of one-step equations, i.e. R2 Q3.4 / R3 §3.9(2)–(3). This corrects R4 §2.1's
  depth framing.

## R7 postscript (2026-11-10)

Open item 1, "the `d = 0` separation case", is taken up in `notes/offset-inversion/R7-dzero.md`
(issue 18). Result: **separation fails at `d = 0`**, constructively.

- `F₀(u) = ¼sinh 2u + u/2 = (e^{2u}/8 + u/4) − (e^{−2u}/8 − u/4)`, an exact difference of two
  graph functions of affine images of `exp_two` (rates `+2` and `−2`).
- Intersecting the two curves, with the second translated vertically by `x`, gives the unique
  abscissa `u = F₀⁻¹(x)`. That is a single `inter_x`, output depth 1.
- So the branch-point method's silence at `d = 0` is correct, not a gap. The `gd` atom at `d ≠ 0`
  (infinitely many finite log branch points) is the entire obstruction.
- The graph of `F₀` is still not a drawable tower curve, but that was a sufficient, not necessary,
  condition; R3's Lemma 2.3 only needs a difference of graph functions.
- R3 §3.9(4) and §5.2 item 5 are updated; L2's `d = 0` instance remains true but is subsumed by the
  single intersection.

## R8 postscript (2026-11-10)

Following R7, `notes/offset-inversion/R8-missing-curve-audit.md` re-reads every "needs the missing
curve `X`" claim by **route**. Result: the `M` labels in R5 are **sufficiency** statements for the
offset route (Route O), not impossibility results.

- Route O (offset inversion) is depth 3; Route I (single intersection) is depth ≤ 2.
- Q2 (offset necessity, by R2 Q3.3 rigidity) is proved only for a fixed curve, fixed `d`, and a
  continuous interval of `x`; varying `d` is R2 Q3.4 [Open].
- Q3 (intersection status) is excluded by R3's log-monodromy count only for affine data on a
  continuous family. Discrete spectra (beam modes) are **not** covered; that is item 4.
- The involute, rhumb (fixed `k`), tractrix and Biot are genuinely outside Route I; the elastica is
  outside by non-elementarity. The `l = 0` well is **open** on Route I (`δ log δ` singularity).
- **`tan x = λx` is open on both routes.** Route O uses `d = λ` (Q3.4 open); Route I is not excluded
  because the target's singularities are `1/log`, not log. A `1/log` invariant is the concrete next
  question.
- The goat is a single target with a legality obstruction, not a separation result; the separatrix
  is pointwise `R`.



