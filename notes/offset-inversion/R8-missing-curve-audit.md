# R8: audit of the missing-curve claims — which route each one covers

Stream **R8** of issue 18, following R7. Research only: no `.lean` edit, no `lake`, no commit.

Purpose: R7 showed that **graph reachability is strictly stronger than solvability** — the `d = 0`
target's graph is not drawable, yet the family is a difference of two drawable graphs. So every
"needs the missing curve `X`" claim has to be re-read as a claim about a **route**, not about the
family. This note audits the table in `R5-named.md` §1 and the ranking in `SUMMARY.md` §5.

Labels: **[Proof]**, **[Wolfram]**, **[Heuristic]**, **[Open]**.
No new numerical work is needed; the audit is structural and cites the existing notes.

---

## 1. The two routes, precisely

**Route O (offset inversion).** A curve `C` (a "missing curve" if not in `Defs`) with Whewell
function `R`, offset by `d`, arc laid by `x`, read out:

```
R(ψ) − dψ = x .                                                              (O)
```

**Route I (single intersection).** Two drawable tower curves `C₁, C₂`, the family parameter entering
as P-constructible affine data, readout a coordinate (R3 Lemma 2.3):

```
φ(x) = g_{C₁}(u) − g_{C₂}(u) ,     u = the unknown .                        (I)
```

Route I needs **no** `arc_of_length`; it is depth ≤ 2. Route O is depth 3. R7's example is Route I.

Three separate questions per named problem:

- **Q1 (offset sufficiency).** Is there a legal Route-O construction once the curve is added?
- **Q2 (offset necessity).** Within the *fixed-curve, fixed-`d`* one-step class, is that curve forced?
- **Q3 (intersection status).** Is Route I excluded? If not, the "missing curve" label says nothing
  about whether the family is reachable.

The answers have different strengths, and the audit's main finding is that the `M` labels in R5 are
almost entirely **Q1** statements.

### 1.1 What Q2 actually proves

R2 §Q3.3 (rigidity): fix a curve `C` and `d`; if `R_C(ψ) − dψ = x` has the same solution for every
`x` in an **interval**, then `ρ_C − ρ_target ≡ const`, i.e. `C` is a parallel of the target curve.
So Q2 is proved only for:

- a **fixed** curve (not a family of curves whose affine data vary with the parameter);
- a **fixed** `d`;
- a **continuous interval** of `x`.

If `d` varies with the family parameter, R2 §Q3.4 is explicit: **open**. If the curve's data vary
with the parameter, the same gap applies (the data slot is what the uniform convention allows to
change). So Q2 is a statement about one constant-coefficient equation, not about every one-step
configuration.

### 1.2 What Q3 actually proves

R3's invariant counts **finite logarithmic branch points**: a graph function of a tower curve has
finitely many; `F_d` has infinitely many (`u = iπ(m+½)`). The argument needs:

- a **continuous** family (the identity must hold on an interval in `u`);
- the parameter to enter **affinely** (R3 §3.9 item 2 is open for non-affine data);
- the target's singularities to be **log** branch points.

Three consequences:

- **Discrete spectra are not covered.** A mode sequence `x_m` gives a discrete set `u_m` with no
  finite accumulation point; an analytic difference can pass through infinitely many prescribed
  points (e.g. `sin`). So the log test does **not** exclude discrete coincidences. That is item 4
  (arithmetic), and it is [Open] for every discrete spectrum.
- **A `1/log` singularity is not a log branch point.** If `f ~ 1/log ζ`, monodromy changes the
  branch but adds no constant, so R3's count is silent. This matters for `tan x = λx` (§3.1).
- **Elliptic targets are not log either.** The log test is silent for the elastica; a different
  invariant (non-elementarity) is needed (§3.5).

---

## 2. The audit table

`Fam` = continuous family, `Disc` = discrete spectrum, `Single` = one target number.
Columns: `O-suff` (Q1), `O-nec` (Q2), `I-status` (Q3).

| # | problem | Fam | O-suff | O-nec | I-status | verdict |
|---|---|---|---|---|---|---|
| 6 | `tan x = λx`, `j₁`, clamped–hinged, spherical `l=1` | continuous in `λ` | catenary, `d=λ` | **open** (`d=λ` varies; Q3.4) | **open** (log test silent; `1/log`, §3.1) | **offset-route-only**, and even that is open |
| 7 | gear involute `tan α − α = k` | continuous in `k` | catenary, `d=1`, `x=k` | proved (fixed `d`, `x` varies) | **excluded** (log monodromy) | **intersection-impossible** (affine data) |
| 8 | cantilever `cos x cosh x = −1` | discrete in `m` | log-cosine, `d=−1`, `x=(2m+1)π` | proved for the continuous interpolation; **open for the spectrum** | **excluded for the continuous interpolation**; **open for the discrete spectrum** | mixed |
| 9 | clamped–clamped `cos x cosh x = 1` | discrete in `m` | log-cosine, `d=1`, `x=2mπ` | as row 8 | as row 8 | mixed |
| 10 | rhumb `u − k gd u = c` | continuous in `c` (fixed `k`) | log-cosine, `d=k` | proved (fixed `k`, `c` varies) | **excluded** (log monodromy) | **intersection-impossible** (fixed `k`) |
| 11 | pendulum separatrix `θ = gd t` | single identity | — | — | — | **R** (pointwise: `gd t = 2 arctan(e^t) − π/2`; `arctan` and `rpow` are P-constructible, so `e^t` and `gd t` are) |
| 12 | goat grazing | single target | formal (OI), **legality open** (pole/fold) | — | **n/a** (single target) | **open** on both routes |
| 13 | tractrix | continuous in `x` (fixed `d`) | tractrix | proved (fixed `d`) | **excluded** (log monodromy from `−ln|sin ψ|`) | **intersection-impossible** |
| 14 | Euler elastica | continuous in `x` (fixed `d`) | elastica | proved (fixed `d`) | **excluded by non-elementarity**, not log (§3.5) | **intersection-impossible** [standard] |
| 15 | spherical well `l=0` | continuous in `R` | **no curve identified** | — | **open** (log test silent: `R(u) ~ δ log δ` at `u₀`, §3.2) | **open** on both routes |
| 16 | Biot `x tan x = Bi` | continuous in `Bi` | **not (OI)** | — | **excluded** (log monodromy; product contains `gd`) | **intersection-impossible**; no offset route |
| 19 | `tan x = x` via quartic / involute / quadratrix | single target | n/a | n/a | **not excluded** — these *are* Route-I constructions, needing a different missing curve | **intersection route with other missing curves** |
| 1–5, 20 | projectile, rainbow, catenary length, Neile, clothoid, Laplace | — | — | — | — | **R** |

Legend for the verdict column:

- **offset-route-only** — the missing curve is needed for the known Route-O construction; Route I is
  not excluded. The label carries no impossibility content.
- **intersection-impossible** — Route I is excluded (for affine data and a continuous family, unless
  stated). This is the strong label R5 should use sparingly.
- **mixed** — the continuous interpolation is excluded, the discrete spectrum is open.

---

## 3. Row-by-row corrections

### 3.1 `tan x = λx` (row 6) — open on both routes

Route I: solving `sinh u − λ gd u = λkπ` for `λ` gives

```
λ = h(u) := sinh u / (gd u + kπ) .
```

Near `u₀ = iπ/2`, `gd u` has a log singularity: `gd u = −i log(u−u₀) + O(1)`, so

```
h(u) ~ sinh(u₀) / (−i log(u−u₀) + O(1)) → 0 ,
```

a **`1/log` branch point**, not a log branch point. R3's finite-log count is silent. This is why
`tan` did not fall out of the R7 audit as "intersection-impossible": the obvious invariant does not
reach it.

Two open sub-questions, both sharper than "is the catenary drawable?":

1. Can a difference of two tower graph functions have infinitely many finite `1/log` singularities?
   Graph functions are built from algebraic/Puiseux data, exp, trig and (at most) finitely many logs;
   no `1/log` singularity is known in the class. If none is reachable, `tan` is
   **intersection-impossible by singularity type**, even though the log count is silent.
2. Route O: the catenary construction uses `d = λ`, varying with the parameter. R2 §Q3.4 is open
   here, so even the *offset-route necessity* for `tan` is not proved. The catenary is a sufficient
   route, not a forced one.

So R5's "**M** catenary" for `tan` is a **sufficiency** label, and a doubly-open problem. The new
priority is (1): a `1/log` invariant. It is the one place where `tan` differs structurally from the
rows that *are* excluded.

### 3.2 Involute, rhumb, tractrix, Biot (rows 7, 10, 13, 16) — genuinely excluded

Each target is a continuous family and contains `gd` **linearly**, or `−ln|sin|`:

```
involute :  sinh u − gd u = k                      (gd linear)
rhumb    :  u − k gd u = c                          (gd linear, k ≠ 0)
tractrix :  −ln|sin ψ| − dψ = x                     (log at ψ = kπ)
Biot     :  Bi = sinh u · (gd u + kπ)               (linear in gd)
```

Each has infinitely many finite log branch points, so Route I is excluded for affine data on a
continuous family. These are the rows where "the missing curve is needed" is strongest. The caveats:
non-affine data (R3 §3.9(2)) and, for a discrete parameter, item 4.

The **`l = 0` well (row 15)** is *not* in this list. Its `gd` is multiplied by `coth u`, which has a
zero at the same `u₀ = iπ/2`; the product is `R(u) ~ δ log δ`, whose monodromy is not additive. So
the log count is silent and row 15 is **open** on Route I, not excluded. (It remains open on Route O
too: no curve identified.)

### 3.3 Beams (rows 8, 9) — mixed

`x + gd x = c` has the log branch points, so the **continuous interpolation** `c ∈ ℝ` is excluded
from Route I. But the physical spectrum is the discrete set `c = (2m+1)π` (or `2mπ`). A difference of
two graph functions can pass through a discrete set without equalling the function, so the discrete
spectrum is **not** excluded. R5's "M log-cosine" is therefore a statement about Route O plus the
continuous interpolation; the discrete coincidence question is item 4.

### 3.4 Goat (row 12) — a single target, not a family

There is no family parameter, so Q2/Q3 do not apply. The issue is **legality**: `R(β) − β = π/2`
with `R = tan β − (π/2)sec β` has a pole and a fold on the natural window. R5 correctly leaves the
construction [Open]. Note also that the pole does **not** by itself obstruct Route I: `power_law`
with a negative exponent is a drawable algebraic curve with a pole, so a difference of two graph
functions can have one. The audit therefore downgrades the goat's "new obstruction" from an
impossibility to an open legality question.

### 3.5 Elastica (row 14) — excluded, but not by log monodromy

`F(φ|m) − dφ = x` has elliptic branch points, not log branch points, so R3's count is silent. Route I
is excluded by the **non-elementarity of the incomplete elliptic integral** (the same Liouville /
Chebyshev criterion R1 uses for power laws), because a depth-≤2 construction has no `arc_of_length`
and its graph functions are elementary. This is a standard result, not re-proved here; label it
[standard non-elementarity] rather than [Proof in this programme].

### 3.6 Separatrix (row 11) and `tan x = x` quartic route (row 19)

- The separatrix is `θ = gd t`, and `gd t = 2 arctan(e^t) − π/2` is a P-constructible **number**
  pointwise (`arctan` and `exp` are P-constructible). It is not an arc-length inversion and needs no
  missing curve for the number itself. R5 already says "reformulation only"; the audit records it as
  **R**, not M.
- The quartic / circle-involute / quadratrix constructions for `tan x = x` are **Route-I**
  constructions with *different* missing curves (they are not in `Defs`). They show that the
  `λ = 1` case has a genuine intersection route if one of those curves is added. They do not give a
  uniform-in-`λ` route, so they do not settle row 6.

---

## 4. What this changes

1. **The `M` label is a sufficiency label, not an impossibility result.** R5's legend should say so.
   `SUMMARY.md` §5 ("Missing curves, ranked by what each unlocks") is a ranking of *constructions*,
   not of *obstructions*. The phrase "None has a PowerPoint route yet" is true of the *curves*; for
   the *families*, only the rows in §3.2/§3.5 are known to be outside Route I.

2. **The strong rows are 7, 10, 13, 16 (and 14 by non-elementarity).** For these, the missing
   curve is needed for Route O *and* Route I is excluded (affine data, continuous family). For the
   beams (8, 9) the exclusion covers the continuous interpolation only; the discrete spectrum is
   item 4. Row 15 (`l = 0`) is open on both routes: its `gd` is multiplied by `coth`, giving a
   `δ log δ` singularity that the log count does not see.

3. **`tan x = λx` is the highest-value row open on both routes** (row 15 is also open, but it is not a
   classical family). The catenary is sufficient for Route O (with `d = λ`, whose necessity is open
   under Q3.4); Route I is not excluded because the target has `1/log` singularities, which the log
   count does not see. The concrete next step is a `1/log` invariant: can a difference of two tower
   graph functions have infinitely many finite `1/log` points? If not, `tan` is
   intersection-impossible by singularity type.

4. **The goat is a legality question, not a separation question.** The pole is drawable
   (`power_law` with negative exponent), so the pole/fold obstruction is about constructing the
   specific `(OI)` route, not about excluding intersections.

5. **Discrete spectra are item 4.** For the beams (and any mode-indexed problem) the separation
   theorems do not apply, because they need an interval. This is the same arithmetic/transcendence
   gap as R2 Q3.4, and it should be stated explicitly wherever the word "uniform" is used.

---

## 5. Revised one-line status of the missing-curve table

| curve | rows | what is actually proved |
|---|---|---|
| catenary | 6, 7 | **sufficient** for Route O. Route I excluded for row 7; **open** for row 6 (`1/log`) |
| log-cosine | 8, 9, 10, 11 | sufficient for Route O. Route I excluded for row 10 and the row-8/9 continuous interpolation; row 11 is pointwise R; discrete beam spectra open |
| goat curve | 12 | formal Route-O algebra, construction **open**; not a separation result |
| tractrix | 13 | sufficient for Route O; Route I **excluded** (log monodromy) |
| elastica | 14 | sufficient for Route O; Route I **excluded** by non-elementarity |
| none | 15 | Route I **open** (`δ log δ`, log test silent); Route O has no curve |
| none | 16 | Route I **excluded** (log monodromy); Route O is not (OI) |

**Bottom line.** The table was being read as "these families are gated on these curves". The correct
reading is: "these are the known **sufficient** constructions, and for rows 7, 10, 13, 14, 16 the
intersection route is also excluded." Rows 6 (`tan`) and 15 (`l = 0`) are open on Route I: `tan` has
`1/log` singularities, `l = 0` has `δ log δ`, and the log-monodromy count sees neither. Rows 8/9 have
the extra discrete-spectrum caveat of item 4.

---

## 6. Actions

1. **`R5-named.md` §0 legend**: change `M` from "requires a named missing curve" to "sufficient
   Route-O construction requires a named missing curve". Add a note that this is not an impossibility
   claim.
2. **`SUMMARY.md` §5**: retitle the ranking as "missing curves, ranked by what each Route-O
   construction unlocks", and add the Route-I status column above.
3. **Next research stream**: the `1/log` invariant for `tan x = λx` (§3.1). This is the one concrete
   question the audit opens, and it is narrower than "is the catenary drawable".
4. **Item 4**: state explicitly that the beam spectra are discrete, so the R3 separation theorems do
   not apply to them; the arithmetic question is genuinely separate.
