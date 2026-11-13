# PLAN-forward-search: enumerate engine solutions by parameter, not by field

Planned 2026-11-13. **Stage A complete (2026-11-12, `F1.md`); stages B–E not started.** This stream replaces
P4′ of `PLAN-algebraic.md` Phase E-P.

Read first: `P1prime.md` (§1 engines, §3 the conjecture, §4.2 the canonical curve), `P2prime.md`
§0, `R3.md` (what a search over `K ⊗ L` can and cannot show), and the "Review corrections"
sections of `R1.md` and `R2.md`.

## 0. Why this search, and what it is for

The target is all `n`: every real algebraic number is P-constructible. After Phase E the position
is:

- every construction that treats all number fields `K` alike is blocked (C1 §5: it would bound
  resolvent degree; R1–R3 hit the same wall on the squares route);
- the non-uniform route has no mechanism (P2′: Stoll's conjecture restates the target; solvable
  base change does not reach the Mordell–Weil layer).

What is missing is a **mechanism**: a reason why, for a given `K`, a solvable `L` and an engine
parameter `λ ∈ L` exist. This stream looks for one in data.

R3 searched the wrong way round. It fixed `K`, fixed a small `L`, and looked for a point in a box
in `K ⊗ L` (14 rational coordinates already for quadratic `L` at `n = 7`). A null there is
expected whether or not the target is true. Here we do the opposite:

> **Enumerate the engine parameter `λ` over small solvable fields, compute the field each `λ`
> produces, and keep the cases where that field comes from a field `K` over ℚ.**

`K` is an output, not an input. The search is exhaustive in the parameter that matters, in a
space of dimension `m = [ℚ(λ):ℚ]` instead of `n·m`.

**What would count as success.** Not a proof. One of:

1. **A family.** Infinitely many solutions lying on a curve (or higher-dimensional subvariety) of
   parameter space. By the structure in §2, a family can only come from an algebraic identity
   between engine maps. An identity is a construction; it is the thing to find.
2. **A calibration.** Measured sizes of `L` and `λ` in a case where solutions are guaranteed
   (degree 5), which tells us whether any search by height can reach degree ≥ 9.
3. **A clean null with known coverage**, which says small `L` never suffices beyond the trivial
   solutions, and by how much.

Ground rules as in the main plan: research only, no `.lean` edits, no `Defs` changes. Labels
`[Proof]`, `[Computed, exact]`, `[Computed, filter only]`, `[Heuristic]`, `[Open]`. Every negative
is scoped to the box searched. Nothing here is a negative about `algebraic_Pconstructible`.

## 1. Objects

- **Engine maps.** A one-parameter engine is a rational map `g: ℙ¹ → ℙ¹` over ℚ of degree `d`
  whose real fibres are drawable (P1′ §1):
  - `pp(p, q)`: `g = x^p (1 − x)^q`, `p, q > 0` coprime, `d = p + q`;
  - `tri(D)`: `g = x^D / (1 − x)` up to constants (P1′ §1: `x^D + ax + b` is `pp(D, −1)` after an
    affine change), `d = D`.
  Both have monodromy `S_d` and three branch values `{0, ∞, λ*}`.
- **Fibre algebra.** For `λ` in a number field `L`, `A_λ = L[x]/(g(x) − λ)` (numerator). For
  `λ` off the branch values it is étale of degree `d` over `L`.
- **Solution.** A triple `(g, λ, K)` with `λ` algebraic, `K/ℚ` of degree `d`, and
  `A_λ ≅ K ⊗_ℚ ℚ(λ)`. If the Galois closure of `ℚ(λ)` is real and solvable, this is an instance
  of (T_β; R-solv) for every primitive `β ∈ K` (P1′ Theorem 1, with `M = L(β)`).
- **Trivial solution.** `λ ∈ ℚ`. Then `K = A_λ` is itself an engine field over ℚ.
- **Nontrivial solution.** `λ ∉ ℚ`. Sub-labelled **new** if `K` is not found among the fibres
  over rational `λ₀` up to a stated height (so `K` is not visibly an engine field over ℚ), and
  **redundant** otherwise.

## 2. Structure of the solution set [Proof sketch; to be written out in stage A]

Let `m ≥ 2` and let `h ∈ ℚ[y]` be the minimal polynomial of `λ`, of degree `m`. Write
`N_h(x) ∈ ℚ[x]` for the numerator of `h(g(x))`; it has degree `d·m`, and
`B_h = ℚ[x]/(N_h) = A_λ` viewed over ℚ.

- **Descent criterion.** `(g, λ)` is a solution iff the fibre algebras over all conjugates of `λ`
  are isomorphic compatibly with Galois. When `A_λ` is a field with no nontrivial
  `ℚ(λ)`-automorphism (true whenever its group is `S_d`, `d ≥ 3`), isomorphisms are unique, the
  cocycle condition is automatic, and the criterion is: **`B_h` contains a subfield `K` of degree
  `d` with `K ⊗ ℚ(λ) ≅ B_h`.** This is an exact, finite test.
- **Parameter space.** Solutions with `[ℚ(λ):ℚ] = m` are indexed by `h`, a rational point of
  `Sym^m ℙ¹ = ℙ^m`. They are the images of the rational points of a variety `W_m`, a twist of
  `Ĉ^m / S_d` (diagonal action; `Ĉ` the Galois closure of `g`), which is a finite cover of `ℙ^m`
  of degree `(d!)^{m−1}`. So **`dim W_m = m`**, and `W_m` does not depend on `K` or on `L`.
  - `m = 2`: `W_2` is a surface. For a fixed `K` and a fixed quadratic `L` the solutions lie on a
    curve (the `K`-twist of `Ĉ` over `L`) and are finite by Faltings; over all `K` and all
    quadratic `L` together they are the rational points of the surface `W_2`.
  - `W_m` is of general type for the `d` of interest (to be checked for small `d` in stage A).
    Bombieri–Lang then predicts that its rational points lie on finitely many proper
    subvarieties, in the simplest case curves of genus ≤ 1, plus finitely many extra points.
- **Why a family is a mechanism.** A positive-dimensional family of solutions is a rational or
  elliptic curve (or larger subvariety that is not of general type) inside `W_m`. Such a curve is
  an algebraic identity: a parametrised `λ(s)` over a solvable extension of `ℚ(s)` whose fibre
  algebra descends to `ℚ(s)`. The diagonal `λ ∈ ℚ` is the trivial one. The inclusion
  `tri(D) ⊂ pp(D, −1)` and the Bring–Jerrard reduction at `d = 5` are known nontrivial ones.
  **The search is a hunt for further special subvarieties of `W_m`.**
- **Caution.** The expected dimension of the solution set grows with `m`. If the target is true
  by a non-uniform mechanism, solutions for a generic `K` of degree `d ≥ 9` may exist only for
  `m` far beyond any enumeration. Stage B measures this at `d = 5`.

## 3. Stages

### Stage A: write-up and tooling (short)

- Write §2 out with proofs: the descent criterion, `dim W_m = m`, and the Kodaira dimension of
  `W_2` for `tri(5)`, `tri(6)`, `pp(3, 2)`, `pp(4, 3)`.
- Check tools at step 0 and record versions: `python-flint` (mod-`ℓ` factorisation), PARI/GP via
  `cypari2` or the `gp` binary (subfields, `polredabs`, Galois groups). Wolfram is not available
  in this environment; label accordingly.
- Write the three core routines with unit tests:
  1. `cycle_table(g, ℓ)`: for each residue `λ ∈ 𝔽_ℓ` off the branch values, the multiset of
     factor degrees of `g − λ` over `𝔽_ℓ`;
  2. `filter(h, g)`: for each prime `ℓ` in a fixed list at which `h` splits completely with
     distinct roots, check that the table entries at all roots of `h` agree. A solution must
     pass at every such prime `[Proof]`: `K ⊗ ℚ(λ)` looks the same at every prime above a split
     `ℓ`. A non-solution passes one prime with probability bounded away from 1;
  3. `certify(h, g)`: the exact test of §2 on `N_h`, returning `K` as a `polredabs` polynomial,
     its discriminant, signature and Galois group.

### Stage B: degree-5 calibration (positive control)

At `d = 5` every quintic field becomes a trinomial field over a solvable extension, by the
classical Bring–Jerrard reduction (a quadratic Tschirnhaus step, then a line on a quadric, then a
cubic). `Ĉ` for `tri(5)` has genus 4 with an `S₅`-action (the genus formula of P1′ §4.2).

- Implement Bring–Jerrard explicitly for 20 quintic fields: 10 with group `S₅`, 5 with `A₅`,
  5 totally real, by increasing discriminant.
- For each, output `λ`, `m = [ℚ(λ):ℚ]`, the Galois group of `ℚ(λ)`, whether it can be taken real,
  and the height of `h`.
- Run `filter` and `certify` on each output. **They must accept all 20.** This is the positive
  control for the pipeline; without it no null from stage C counts.
- Record the distribution of `m` and of the height of `h`. This is the calibration: it says how
  large solutions are where they are guaranteed to exist.

**Decision after B.** If the smallest Bring–Jerrard solutions already have `m ≥ 6` and heights
far beyond enumeration, say so plainly: stage C then tests only for *unexpectedly small*
solutions, and its null will be weak. Continue to C regardless, because a small family is exactly
the surprise being looked for.

### Stage C: enumeration

Enumerate primitive integer polynomials `h` of degree `m`, irreducible, by height `H`
(maximum absolute coefficient). Every `h` of degree ≤ 4 has solvable splitting field, so no group
filter is needed. Record the number of real roots of `h`; do not filter on it (complex `λ` cannot
be used in a construction but can reveal an identity).

| pass | `m` | engines | `d` | target height | size |
|---|---|---|---|---|---|
| C1 | 2 | `tri(d)`, all coprime `pp(p, q)` | 5–9 | `H = 300` | ≈ 10⁸ per engine |
| C2 | 3 | `tri(d)`, `pp(⌈d/2⌉, ⌊d/2⌋)` coprime | 5–9 | `H = 40` | ≈ 10⁷ per engine |
| C3 | 4 | `tri(d)` | 5–7 | `H = 12` | ≈ 10⁶–10⁷ per engine |
| C4 | 6, tower shape | `tri(5)`, `tri(6)` | 5, 6 | set after stage B | set after stage B |

- C4 enumerates `λ` in towers of the shape stage B finds (for example a cubic over a quadratic),
  parametrised by the tower, not by a general sextic `h`.
- Heights are targets. Tune them to the measured throughput and report the box actually
  completed. A partly searched box is reported as such.
- Every `h` that passes `filter` goes to `certify`. Report both counts. Only certified solutions
  are solutions; filter-only survivors are `[Computed, filter only]` and must not be counted.
- Alongside, enumerate rational `λ₀` to height 10⁴ for each engine and store
  `(polredabs, disc, signature)` of each fibre field. This table decides **new** versus
  **redundant** in §1.

### Stage D: analysis

For each engine and each `m`:

- the list of certified solutions: `h`, `K`, discriminant, signature, Galois group of `K`,
  Galois group of `ℚ(λ)`, real or not, new or redundant;
- **family detection.** For `m = 2`, plot the solutions in the plane of `(λ + λ', λλ')` and fit
  plane curves of degree ≤ 6 through subsets; for `m = 3, 4` fit low-degree hypersurfaces and
  curves. A fitted curve carrying ≥ 3 more solutions than its number of coefficients is a
  candidate family. Count growth of solutions with `H`: bounded count means sporadic, growth
  like a power of `H` means a family;
- **for every candidate family, derive the identity symbolically** and prove it. State which `K`
  it reaches: degree, Galois groups, signatures, how many parameters. A family that reaches only
  special `K` (imprimitive, small group) is recorded and scoped;
- **dependence on `m`.** Compare counts of new solutions at `m = 2, 3, 4` for the same engine and
  `d`. Does the count rise with `m` as the dimension count of §2 suggests?
- **dependence on `d`.** Do nontrivial solutions thin out or persist as `d` goes from 5 to 9?
- **cross-engine coincidences.** A field `K` that appears for two different engines, or for two
  different `(p, q)`, points at an identity between engine maps. List them.

### Stage E: follow-up, only if D finds a family

- Generalise the identity to all `d`. Count how many parameters of `K` it reaches against the
  `d` parameters of a general degree-`d` field.
- If it reaches a positive-dimensional set of `K` for every `d`, check it against C1 §5: a
  family uniform in `K` with a bounded engine would bound resolvent degree. Either the family is
  non-uniform, or it reaches only special `K`, or something in C1 §5 does not apply. Settle which
  before claiming anything.
- Check realness (P1′ §5, with P2′'s correction: real points at every real place of `L`).

## 4. Stop and kill criteria

- **Stage B fails** (pipeline rejects a known Bring–Jerrard solution): stop and fix. No stage C
  result is reported until B passes.
- **Stage C complete, no new solution at any `m`:** report the null with its exact boxes. Scoped
  conclusion: no nontrivial solution with `[ℚ(λ):ℚ] ≤ 4` in those boxes. Together with stage B's
  measured sizes, state whether the null was expected.
- **New solutions but no family:** report them as sporadic points. Record the fields. Do not
  extrapolate.
- **A family:** stage E. Stop and report to the user before building on it.
- The stream does not end E-P and does not decide anything about P3′ or P5′.

## 5. Resources and order

| stage | work | who | sessions |
|---|---|---|---|
| A | proofs of §2, tooling, unit tests | orchestrator-level (the descent and `W_m` statements are easy to get wrong) | 1 |
| B | Bring–Jerrard for 20 quintics, pipeline control | orchestrator-level | 1 |
| C | enumeration runs | computation; can be delegated with review once A and B are fixed | 1–2 |
| D | analysis and family detection | orchestrator-level | 1 |
| E | only if triggered | orchestrator-level | open |

Order: A, then B, then C1 and C2, then C3 and C4, then D. Review after B and after D.

## 6. Deliverables

- `notes/algebraic/F1.md`: the write-up, with a "Findings summary" first, every claim labelled,
  every null scoped to its box.
- `notes/algebraic/HANDOFF-alg-F1.md`: one line per step.
- `notes/algebraic/scripts/F1_*.py`: tables, filter, certify, Bring–Jerrard, enumeration.
- `notes/algebraic/scripts/F1_solutions_*.csv`: certified solutions, UTF-8 with LF.
- Reproduction commands as `python3 …`.
- An update to `PLAN-algebraic.md` and `SUMMARY.md` after stage D.

## 7. Things to carry in

- **Filter survivors are not solutions.** Agreement of cycle types at finitely many primes is
  necessary only. Certify everything.
- **Use exact arithmetic for every decision.** R3 found a floating-point false positive in its
  quadratic search.
- **A solution over a non-real or non-solvable `ℚ(λ)` is data, not a construction.** For `m ≤ 4`
  solvability is automatic; realness is not.
- **`d ≤ 8` solutions prove nothing new** (those degrees are already in P). They are there to
  expose the pattern. The claim that matters is whether a mechanism extends to `d ≥ 9`.
- **Do not read sparse data as a law.** Three points on a conic is not a family.
