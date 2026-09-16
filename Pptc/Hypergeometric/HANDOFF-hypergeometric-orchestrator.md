# HANDOFF — hypergeometric ₂F₁ programme (for the next orchestrator)

## Where things stand

- Repo `C:\dev\Powerpoint\lean\pptc`; work lives in `Pptc/Hypergeometric/`.
- `HEAD = 2457810` (bounding-box work) sitting on top of `6c36a61` ("wave 2 of the 2F1
  programme, inbound complete"). Nothing pushed.
- Uncommitted at handoff: this file, `PLAN-hypergeometric-00-overview.md` (modified), and the
  R4/R5 notes + handoffs (see "Files to read").

## The inbound map is complete (formalized, sorry-free)

Every ₂F₁ family the programme can reach is in `main`:

- elementary cases (`Basic.lean`);
- elliptic class `(½+ℤ, ½+ℤ, 1+ℕ)` (`EllipticClass.lean`, `hyp_elliptic_class_Pconstructible`);
- graph family `(−½+ℤ, 1/m+ℤ, 1+1/m+ℕ)`, `m = 2n−2 ∈ {2,4,6,8,10}`
  (`GraphsClass.lean`, `hyp_graphFamily_class_Pconstructible`);
- `z = 1` denominator-24 Γ route (`Gauss.lean`, `hyp_one_Pconstructible_of_den_24`);
- fourth signature `₂F₁(¼,¼;1;·)` and Clausen's ₃F₂ (`Clausen.lean`);
- **conditional only:** the cubic/sextic/quartic Ramanujan signatures in `Signatures.lean`
  (the classical transformation is an explicit hypothesis).

Research (not Lean): **R4** — no other drawable arc length gives a new ₂F₁ family (Bézier →
incomplete `F`/`E`/`Π`; `offset` → base + elementary turning term; `sine` → incomplete `E`;
`exp_two`/`rectangle` → elementary). **R5** — B6 is unchanged.

## Open thread 1 — make L9 unconditional (inbound)

Target: prove the three transformations so `Signatures.lean` loses its hypotheses.

- **V7 (quartic), start here:**
  `hyp (1/4)(3/4)1 z = (1 + √z)^(-1/2) * hyp (1/2)(1/2)1 (2√z/(1+√z))`,
  then drop `hV7` from `hyp_quarter_three_quarter_Pconstructible`.
- **Why it is hard.** The project has no general `hypSeries a b c` ODE (only the hand-written
  `(1/4,1/4;1)` one in `Quadratic.lean`); in `w = √z` the left side satisfies a **Heun**
  equation, so `Quadratic.lean`'s polynomial-substitution template does not transfer; the
  coefficient route needs a Vandermonde/Gosper sum with half-integer binomials, which Mathlib
  lacks.
- **Suggested first step.** Add a general `hypSeries_ode (a b c)` lemma in a new file, then
  attack V7 via the ODE route. The cubic and sextic sit behind the same wall.
- The conditional theorems are deliberately **not** tagged `@[pconstructible_cond]`; tag V7's
  once the hypothesis is gone.

## Open thread 2 — B6 breakthrough (the stated frontier)

Wanted: a drawable construction realising the **first-kind** period, whose `m = 10` case is
`A = (1/10)B(1/10,2/5) = Γ(1/10)Γ(2/5)/(10√π) = 1.1905798216…` (new denominators 5, 10).

- **R5 sharpened it:** a *bounded* first-kind arc only gives the incomplete integral (`A` is
  `∫₀^∞`, a sup never attained). What is actually needed is a **closed drawable genus-≥2
  curve**, or a primitive whose complete period is first-kind.
- Such a primitive stays countable/sound if parameterised by P-constructible data (no free
  real, no `sSup`), so it is a design choice, not an inconsistency.
- The bounding box does **not** help here (it inverts a second-kind arc length and returns
  abscissae, not periods).
- Correction to record: R1's second `m = 10` period is misprinted; the genuine value is
  `(1/10)B(3/20,7/20) = 0.89354817…`.

## Bounding-box interaction

Read `Pptc/PLAN-bounding-box.md`. The box (`Defs.lean` `box_xmax`/`box_ymax`; `Box.lean`,
`BoxGraph.lean`, `BoxOffset.lean`) resolves the endpoint/offset-reachability debate: far
endpoints, extrema and arc-length inversion are now P-constructible, so R4's reachability
caveats are superseded. It adds **no new ₂F₁ family**, but is a new *outbound* mechanism (it
inverts the H6 ₂F₁ arc-length function, producing new numbers — e.g. the parabola/cubic/quartic
abscissae, the last being genus-2).

## Tooling note

The `lean-prover` subagent was returning empty completions because `empty-completion-nudge.ts`
(and `defs-guard.ts`, `lake-build-guard.ts`) **failed to load** — opencode's plugin loader
requires every export of a plugin module to be a plugin function, and the helper exports broke
it. Fixed (all three now `export default` only); opencode restarted and the new process logs no
load errors. The nudge trigger (`session.idle`) is **loaded but not yet exercised** — if a
subagent still stalls without being nudged, switch the trigger to `message.updated`. Also
`lake-build-guard`/`defs-guard` were inactive before the restart, so do not trust their prior
behaviour.

## Files to read

- `PLAN-hypergeometric-00-overview.md` — the programme plan and status (read first).
- `NOTES-hypergeometric-R4.md` (umbrella) + `R4a-bezier` / `R4b-offset` / `R4c-sine-exp`.
- `NOTES-hypergeometric-R5.md` — the B6 study.
- `Signatures.lean` (L9), `EllipticClass.lean` (L3b), `GraphsClass.lean` (L5b),
  `Quadratic.lean` (V6 template).
- `Pptc/PLAN-bounding-box.md` and `NOTES-defs-arc-endpoint-extraction.md`.
