# PLAN-routes: reachability by route, and the claims that follow

Status: **new (2026-11-10)**. Successor/companion to `notes/offset-inversion/PLAN-offset-inversion.md`,
following R7 (`d = 0`) and R8 (missing-curve audit).

Read first: `notes/offset-inversion/R7-dzero.md`, `notes/offset-inversion/R8-missing-curve-audit.md`,
`notes/offset-inversion/SUMMARY.md` §3–§7, `notes/offset-inversion/R3-separation.md`,
`notes/offset-inversion/R2-tower.md` Q3.

This plan exists because R7 and R8 changed what a "reachability claim" has to say. Before them the
programme asked *"is curve `X` drawable?"* After them there are **two routes**, three **loopholes**
in the separation theorems, and several named problems whose status is genuinely open rather than
gated on a missing curve. The plan's job is to make every claim route-explicit, settle the open
cases that can be settled, and keep a live index of what is actually known.

**Survey, not hunt.** A route that reaches nothing named is still a result. Report it in full.
Never drop a path because it misses a particular target.

---

## 0. The map going in

### 0.1 The two routes

| | Route O (offset inversion) | Route I (single intersection) |
|---|---|---|
| construction | `offset(d)` → `arc_of_length(x)` → `box` | `inter_x`/`inter_y` (plus affine/`restrict`) |
| equation | `R(ψ) − dψ = x` | `φ(x) = g_{C₁}(u) − g_{C₂}(u)` |
| depth | 3 | ≤ 2 |
| output | a root of a one-step equation | a difference of two graph functions |

R7 is the first target whose graph is **not** drawable but which is still Route I: the parabola's
`d = 0` family is `(e^{2u}/8 + u/4) − (e^{−2u}/8 − u/4)`, a difference of two affine images of
`exp_two`. So **graph reachability is strictly stronger than solvability**, and the old
"missing curve" framing was a sufficient-condition framing.

### 0.2 The three questions every claim must answer

- **Q1 (Route-O sufficiency).** Is there a legal Route-O construction once the curve is added?
- **Q2 (Route-O necessity).** Within the fixed-curve, fixed-`d` one-step class, is that curve forced?
  (R2 Q3.3 rigidity. Varying `d` → R2 Q3.4, open.)
- **Q3 (Route-I status).** Is Route I excluded? If not, the missing-curve label says nothing about
  whether the family is reachable.

### 0.3 The three loopholes

1. **Non-affine data.** The separation theorems assume the family parameter enters through affine
   data (R3 §3.9 item 2 is open otherwise).
2. **Parameter-dependent data.** `d`, the curve's affine data, or the start point may vary with the
   family parameter (R2 Q3.4; R3 §3.9 item 3). Q2 is then not proved.
3. **Discrete spectra.** A mode sequence gives a discrete set of roots, not an interval. A difference
   of graph functions can pass through infinitely many prescribed points (e.g. `sin`), so R3 does
   not apply to beam modes or `tan` branches.

R12 refines 1–2: loophole 1 is **value-side** and loophole 2 is **shape-side**. The value-side
loophole is A-robust for log points with real monodromy (Lemma 1.2 of `R12-convention.md`), but not
for `1/log`, `δlogδ` or complex-monodromy log points; the shape-side loophole is B0/B1. Loophole 3
is convention C. See `R12-convention.md` §1.5–1.6.

### 0.4 The open rows (from R8)

| target | Route O | Route I | status |
|---|---|---|---|
| `tan x = λx` | catenary `d=λ` (Q2 open) | open: `1/log` singularity | **open both** |
| `l = 0` well | no curve | open: `δ log δ` | **open both** |
| beams | log-cosine | continuous interpolation excluded; discrete open | mixed |
| involute, rhumb (fixed `k`), tractrix, Biot | missing curve | **excluded** (log monodromy) | intersection-impossible |
| elastica | missing curve | **excluded** by non-elementarity | intersection-impossible |
| goat | formal, illegal window | n/a (single target) | open, legality |
| separatrix | — | — | **R** |

---

## 1. Ground rules

- One agent, one deliverable, one file. Progress log `notes/reachability/HANDOFF-<id>.md`.
- Research streams write `notes/reachability/<id>.md` and never edit `.lean` files.
- Wolfram (`WolframLanguageEvaluator`) for every identity: ≥30 digits or a symbolic proof.
  One computation per call; session state does not persist. State the backend.
- Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**. Never claim a negative without a
  proof; "no route found" is `[Heuristic]`.
- **Every claim must name:** the route (O or I), the strength (sufficiency or necessity), the
  family kind (continuous/discrete), and the data class (affine/non-affine, fixed/varying).
  Use the template in §2.
- `Defs.lean` is fixed. A stream that finds a constructor's hypotheses block a step reports it; no
  axiom changes.
- Nothing goes into `Defs.lean` without the user's explicit decision.

---

## 2. The claim template (adopt everywhere)

Every reachability statement in this programme should fit this frame. It is deliberately short
enough to paste into a table.

```
Target:            <equation / named problem>
Family index:      <continuous λ, or discrete m; what is fixed>
Family kind:       continuous | discrete | single target

Route O:
  construction:    <curve C, offset d, length x; legality: cusp-free window?>
  necessity:       <fixed d + fixed curve -> parallel of C (R2 Q3.3) | varying d -> Q3.4 open>
Route I:
  decomposition:   <F = g1 - g2, with both g_i drawable graph functions>
  or exclusion:    <invariant used: log monodromy | singularity type | non-elementarity>
  hypotheses:      <affine data? continuous family? which tower class?>

Verdict:           R | N (offset-only) | M (missing curve, Q3 open) | O (outside)
Notes:             <whether the named curve is needed for any route, or only Route O>
```

The first deliverable of **R12** is to apply this template to R5's table so the index becomes
mechanical to maintain.

---

## 3. Streams

| id | wave | kind | deliverable | depends on |
|---|---|---|---|---|
| R12 | 1 | foundations | **landed**: `R12-convention.md` — B + C recommended, restatements, template and R5 table | R8, R3 §3.9, R2 Q3.4 |
| R9 | 1 | math/proof | `R9-singularity-spectrum.md`: the singularity classification and its two applications | R8, R3, R7 |
| R10 | 1–2 | math (positive) | `R10-decomposition-dictionary.md` + `decompose.wl`: a Route-I catalogue | R7, R8 |
| R11 | 2 | math/arithmetic | `R11-discrete-spectra.md`: formulation, scan, partial impossibility | R8, R3, R12 |
| R13 | 2 | math (small) | `R13-goat-legality.md`: a legal construction or a proof of illegality | R5 §2.11, R0 §3.4 |
| IDX | continuous | maintenance | update `R5`/`SUMMARY`/`PLAN-ppt-tan-curves` with route labels; keep the claim index | R8, R12 |

Waves: R12 first (it fixes the language); R9 and R10 can run in parallel; R11 after R12; R13 any
time. IDX is not a wave, it is the standing index.

### R12: convention and data-dependence (do this first)

**Why.** R8's caveats are not technicalities: if the convention allows arbitrary P-constructible
data to vary with the parameter, then the separation theorems may not speak to the named problems at
all. This stream decides what "solves a family" means *before* more impossibility proofs are written.

**Questions.**
1. Are the data slots allowed to be arbitrary P-constructible functions of the family parameter, or
   only affine functions? (R3 §3.9 items 2–3; R2 Q3.4.)
2. For a discrete spectrum, what is the family parameter (mode index `m`), and what does "one
   configuration solves the family" mean?
3. Does the convention change for Route O vs Route I?

**Options.**
- **(A) Permissive:** status quo. All P-constructible data allowed. Consequence: Q2/Q3 are open
  whenever data vary; the named claims are weaker.
- **(B) Affine-data:** data must be affine in the family parameter (or constant). Consequence: R3's
  theorems apply; the named spectra still need a discrete convention.
- **(C) Mode-index:** a separate convention for discrete spectra: one configuration per mode, data
  `x_m` a P-constructible sequence fixed by `m`; the question is then an interpolation/arithmetic one
  (R11), not an identity on an interval.

**Recommendation.** Adopt **B + C** as the default for impossibility claims, keep **A** as a
documented fallback for constructive results. State both in every claim. This is a prose decision,
not a `Defs` change; the user owns it.

**Deliverable.** A one-page decision plus the restated versions of R3's Theorem 3.4/3.5 and R2's
rigidity under the chosen convention, and the filled-in claim template for R5's table.

**Success.** Every later stream can say "under convention B/C" and be understood.

**Landed (2026-11-10).** `R12-convention.md`. Recommendation **B + C**, awaiting ratification
(note §2.5). Key findings: the value coordinate is the only free slot; A is genuinely stronger for
`1/log`, `δlogδ` and complex-monodromy log points (real `φ` resolve them), but log points with real
monodromy are A-robust (Lemma 1.2), so R3's log separation survives A. B1 Route-O necessity reduces
to a 4-function span condition on `R_C`; the catenary is the `tan` solution, the log-cosine is not,
the base catalogue is excluded by Wronskians, and the rest of the tower is open.

### R9: singularity spectrum of tower graph functions

**Why.** R3 counts finite **log** branch points. `tan x = λx` and the `l = 0` well have
singularities the count does not see: `1/log` and `δ log δ`. If the class of graph functions has
only Puiseux/pole singularities plus finitely many log points, then infinitely many `1/log`
(or `δ log δ`) points exclude Route I. That would settle `tan` **without** the catenary.

**Questions.**
1. What finite singularities can a graph function of a tower curve have, **without**
   `arc_of_length`? Proposed answer: algebraic (Puiseux), poles, and finitely many log points; no
   `1/log`, no `δ log δ`, no essential singularities at finite points.
2. Does an `offset` step (which introduces algebraic normal components) create new types? Does the
   trig tower? Does a `restrict` change anything?
3. Is the `1/log` type reachable by any composition (the positive counterexample would be a
   drawable curve whose graph function behaves like `1/log`)?

**Tasks.**
1. Write the normal form and the local analysis at a finite `u` (R3 Lemma 3.3 is the model).
2. Classify the singularities of `g_C` for C algebraic / exp-type / trig-type.
3. Prove or refute: infinitely many finite `1/log` points ⇒ not a graph function. Apply to
   `tan` (`h(u) = sinh u/(gd u + kπ)`) and `l = 0` (`R(u) ~ δ log δ`).
4. State the resulting Route-I exclusions in the claim template.

**Success.** A theorem with the two applications, or a constructive counterexample (which would be
a headline: a `1/log` curve would put `tan` in Route I).

**Risk.** The classification must handle algebraic branch points and the offset normal; a gap there
could invalidate the application. The fallback is to prove the result for the specific `h` rather
than for the whole class.

### R10: the Route-I decomposition dictionary (positive)

**Why.** R7 found one decomposition by hand. The positive counterpart of R3 is a catalogue: which
target families are differences of two drawable graph functions? Every hit is a cheaper (depth ≤ 2)
construction and a new `R` entry.

**Scope (bounded, to keep the search finite).**
- Graph functions from: lines; `e^{ku}` (`k ∈ ℚ`); `cosh/sinh`; `sin/cos`; polynomial and
  `power_law` graphs (including negative exponents); single offsets of these (which bring
  `√(1+z²)`-type algebraic terms); their affine images.
- Target forms: finite sums of ≤3 exponential rates; trig polynomials of degree ≤2; algebraic
  functions of degree ≤2; the `d = 0` family and the R5 named targets.

**Tasks.**
1. Build the catalogue of graph functions with exact forms and their asymptotic types.
2. For each target, attempt `F = g₁ − g₂`: symbolic ansatz first, then high-precision PSLQ.
3. Record hits, near-misses, and the obstruction for misses.
4. For each hit, write the exact construction in `Defs` vocabulary and check the depth.
5. Look for a *general pattern*: which finite exponential/trig sums split? (R7's is a two-rate
   odd function.)

**Success.** At least three catalogue entries, one of them Lean-able; a documented negative list.

**Risk.** Open-ended; keep the scope bound above. Do not turn this into a general function-fitting
exercise.

### R11: discrete spectra and arithmetic

**Why.** R8 shows the separation theorems do not apply to beam modes or `tan` branches. The
question is whether a finite-parameter graph difference can interpolate infinitely many prescribed
points. This is item 4 of issue 18, and it is the only honest way to close the beam rows.

**Questions.**
1. Formulate "one configuration solves a discrete family" (R12 option C).
2. Can a difference of two tower graph functions vanish at all `u_m` (or hit all `c_m`) for an
   infinite discrete set with no finite accumulation point?
3. Is there a transcendence/independence statement for the specific spectra (`x + gd x = (2m+1)π`,
   the `tan x = λx` branches)?

**Tasks.**
1. Write the precise interpolation problem.
2. High-precision PSLQ/independence scan on the first several modes for the candidate curve families.
3. Look for a theorem: e.g. a finite exponential sum cannot have the beam spectrum as zeros
   (or a counterexample via a `sin`-type difference).
4. Report `[Open]` honestly if no theorem is reachable.

**Success.** A formulation plus either an impossibility theorem or a construction; at minimum, a
precise statement that later work can attack.

### R13: goat legality (small case study)

**Why.** R8 downgraded the goat from an impossibility to an open legality question. It is also a
good test of the two-step machinery.

**Tasks.**
1. Start at `ψ = π` (avoids the pole), restrict, lay an arc across the fold; check `1 − dκ > 0` and
   the monotone readout.
2. Try a two-step construction (`R6`-style) that crosses the fold in two pieces.
3. If illegal, prove it from the `Defs` hypotheses (not from a numeric failure).

**Success.** A legal construction or a proof of illegality.

### IDX: the standing index

Keep a single table (start from R8 §2) with one row per named target and the four fields of the
claim template. Update it whenever a stream lands. `R5-named.md`, `SUMMARY.md` §4–5 and
`PLAN-ppt-tan-curves.md` point to it rather than duplicating the status.

---

## 4. Decisions the user owns

1. **Convention:** A (permissive), B (affine), C (mode-index), or **B+C (recommended; R12 has
   landed and analysed the alternatives)**. R12's finding: A is genuinely stronger for `tan`,
   `l=0`, the tractrix and Biot (real value-side `φ` resolve their singularities), but the log rows
   with real monodromy are A-robust. B+C is the uniform default; A would need a global argument for
   the non-log rows.
2. **Priority:** R9 first (settle `tan`) or R10 first (find new reachable families). The plan
   recommends R12 → R9, with R10 in parallel if there is a second worker.
3. **Scope of R11:** start it now as a formulation+scan, or defer until R9/R10 land.
4. **Whether `l = 0` and the goat are in scope**, or parked as case studies.

---

## 5. Success criteria

The plan is done when:

- every row of the R5 table carries a route-level verdict (`R`, `O-suff`, `I-excluded`, or `open`)
  under a stated convention;
- `tan x = λx` is settled on Route I (excluded by singularity type, or constructed), and its Route-O
  necessity is either proved or explicitly open under Q3.4;
- the `l = 0` well and the beam discrete spectra have precise statements (settled or open);
- the decomposition dictionary has at least three entries and one Lean-able construction;
- the convention is decided and the claim template is in use.

What it does **not** promise: settling the full-tower separation for the catenary/log-cosine
(that remains issue-18 item 2), or a Lean formalisation of the separation theorems (they need
complex analysis well beyond the current library).

---

## 6. Cross-references

- `notes/offset-inversion/PLAN-offset-inversion.md` — the parent programme.
- `notes/reachability/R12-convention.md` — the convention (B + C recommended), the A-analysis
  (`1/log`/`δlogδ` are B-only; log with real monodromy is A-robust), and the filled-in template.
- `notes/offset-inversion/R6-chains.md` — chains reduce to one-step entries.
- `notes/offset-inversion/R7-dzero.md` — the first positive Route-I construction.
- `notes/offset-inversion/R8-missing-curve-audit.md` — the route audit this plan builds on.
- `notes/offset-inversion/R3-separation.md` — the log-monodromy invariant and its hypotheses.
- `notes/offset-inversion/R2-tower.md` Q3 — rigidity and the varying-`d` gap.
- `notes/ppt-curves/PLAN-ppt-tan-curves.md` — the UI-side plan; R8 confirms its quartic/involute
  routes are Route I with different missing curves.
