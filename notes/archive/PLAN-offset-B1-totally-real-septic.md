# PLAN-offset-B1: a real root of a totally real septic, via offsets

Read `PLAN-offset-00-overview.md` (all of §4), `septicpaper_revised.tex` (the whole paper, which
is short), `pptc/Pptc/Offset.lean`, and `archived files/NONIC-notes.md`.
Log: `HANDOFF-offset-B1.md`. Deliverable: `NOTES-offset-B1.md`. Scripts: prefix `B1-`.

## Why

It is known that every real root of a septic over `K` **with a non-real root** is in `K`. The
totally real case is open, and it is exactly where Hermite's trace form becomes positive
definite. At that point, real Tschirnhaus maps can kill only `p₁`, and the power-law engine
`y⁷ = cubic` needs `p₁ = p₂ = p₃ = 0`. So a totally real septic needs an engine that tolerates
the remaining `p₂, p₃` freedom, or a route that avoids Tschirnhaus altogether.

For real closedness it suffices (Artin; see B2) that every odd-degree polynomial over `K` has
**one** root in `K`. **One** root of a totally real septic is therefore already the goal.

## Setup

Work with the monic, depressed (`p₁ = 0`) totally real septic `q`, which has 6 free
coefficients. Available freedoms:
* real Tschirnhaus maps (6-dimensional, but reality pins them down; only `p₁` can be killed
  exactly);
* Möbius maps with `K` coefficients;
* cofactors `g` (any real-root pattern: extra roots are cropped away);
* choosing *which* root to reach;
* every engine parameter.

## Questions

1. **The shape of the requirement.** For an engine family `E` of degree `N` and effective
   dimension `e`, write down the covering system for `q`. The unknowns are the engine
   parameters, the cofactor `g` of degree `N − 7`, and optionally `φ`. Tabulate unknowns against
   equations for:
   * the decic line family (`N = 10`, `e = 7`, cubic cofactor);
   * the offset-cubic × conic family (A2's F2, `N ≈ 20`);
   * the offset-cubic × Bézier family (F3);
   * the offset × offset family (A3).

   Derive the dimensions yourself; do not wait for A2 or A3. A quick Jacobian computation is
   enough.
2. **The decic line family, carefully.** Solve `q · g = c·(u²(u′² + v′²) − D²v′²)`
   * numerically, for ≥ 20 random totally real `q` with rational coefficients (homotopy /
     `NSolve` over ℂ, then keep the real solutions);
   * record how many **real** solutions exist, as a function of the root configuration of `q`;
   * check whether the obvious necessary conditions hold (e.g. the root of `q` must satisfy
     `u√(u′² + v′²) = ±Dv′` with a real sign).

   If real solutions always exist, compute the degree and Galois group of the auxiliary unknowns
   for a rational `q`. If that degree is ≤ 6, or the system triangulates, this is the theorem.
   If not, record exactly how far it misses, as was done for the nonic route in
   `archived files/HANDOFF-degree7-s2.md`.
3. **Exploit the slack as the septic paper does.** The paper turns a codimension problem into a
   *sign change along a rational segment* plus a degree-6 univariate polynomial (Prop. `phi-B`).
   Look for an analogue. Choose all but one unknown rationally (an open condition), in such a way
   that the last condition becomes a univariate polynomial of degree ≤ 6, or a member of a known
   engine (nonic family, degree-10 family, `root_Pconstructible_of_nonreal_root`), in the last
   unknown, with a certified sign change. **This is the most likely shape of a success.** Search
   for it systematically over the families from question 1.
4. **Bootstrap through the non-real case.** Look for a construction that turns the totally real
   septic `q` into an auxiliary polynomial over `K` of degree ≤ 7 **with a non-real root**, whose
   real root determines a root of `q` through operations already in `K`. For example, offsets
   give access to equations like `u√S = Dv′`, whose rationalization need not be totally real
   even when `q` is. Is there a mechanism by which an offset family "contains" `q` as a factor of
   a polynomial with non-real roots, so that `q · g ∈ E` with the covering system itself a septic
   (or lower) with a non-real root? Examine it concretely.
5. **Engines that avoid Tschirnhaus.** Is there an offset-based family containing an explicit
   **6-parameter** family of depressed septics (by cofactor), whose covering is triangular? For
   instance, fix the cofactor's roots at rational points and solve for the remaining parameters.
   Report every structured attempt, including failures, with how far each got.
6. **Small cases first, as calibration.** Run the same machinery on
   * totally real quintics and sextics (known to be in `K`; the machinery should reproduce this);
   * the totally real *octic over ℚ* (known in `K`).

   If the method cannot re-derive known results, fix it before trusting it on septics.

## Deliverable

1. The summary, stating clearly: solved, reduced to a specific sub-question, or blocked, and why.
2. For every family: the covering-system count, the real-feasibility statistics, and the
   auxiliary degree / Galois group.
3. Any construction, written as an explicit move tree, with the §5 standards of the overview:
   a 30-digit check on ≥ 5 random totally real septics, and a check of the side conditions.
4. A precise list of the sub-problems whose resolution would settle the totally real septic.
5. The Side discoveries and Leads sections.
