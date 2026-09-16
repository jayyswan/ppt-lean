# PLAN: the bounding-box constructor

Status: `PConstructible.box_xmax` / `box_ymax` are **landed in `Pptc/Defs.lean`** (after
`arc_length`). `Defs.lean` compiles clean. Nothing else in the project uses them yet.

This plan says how to wire them in, which existing proofs they shorten, and what new numbers
they are expected to yield. Labels follow the house convention: `[SY]` syntactic/from source,
`[NC n]` numeric to `n` digits, `[SP]` speculative.

Background and the original proposal: `Pptc/Hypergeometric/NOTES-defs-arc-endpoint-extraction.md`.
That note's §3 stated the rule on `γ '' Icc a b ⊆ S` with free `a, b`, which collapses
`PConstructible` to all of `ℝ` (take `S = {y = x²}`, `γ t = (t, t²)`, `b = r` arbitrary; the
box returns `r`, which no hypothesis constrains). The landed form pins the arc by requiring
it to be a `PConstructibleCurve` in its own right, and uses `IsCompact` for attainment
instead of a tracing. The note's §5.2 claim — that this makes the Jacobi amplitude
reachable — is **false** and is addressed in §5 below.

**Out of scope for this plan.** Non-constructibility / independence results (the project has
no tools for them and does not want them here), and Serret's generating-triangle curve
(not an operation a drawing program has).

---

## 0. What landed

```lean
| box_xmax {A : Set (ℝ × ℝ)} (hA : PConstructibleCurve A)
    (hcomp : IsCompact A) (hne : A.Nonempty) :
    PConstructible (sSup (Prod.fst '' A))
| box_ymax  -- same, with Prod.snd
```

Three design points, each load-bearing:

- **`PConstructibleCurve A`, not `⊆ S`.** "Is a subset of a constructible curve" holds of every
  subset of the parabola, so a `⊆` form admits uncountably many arcs. `arc_length` blocks the
  same collapse by pinning plane endpoints, `arc_of_length` by pinning start and length; the box
  pins by class membership. `[SY]`
- **`IsCompact` makes the sup a measurement, not a limit.** On a compact set it is attained
  (`IsCompact.sSup_mem`). Both failure modes are live: `poly_graph` is unbounded (`sSup` is not
  a real), and `power_law` omits `x = 0`, so `{(x, √x) : 0 < x ≤ 1}` has `sInf = 0` attained by
  no point of the curve. `[SY]`
- **Only the two maxima are axioms.** `scale_x` / `scale_y` carry no positivity hypothesis, so
  scaling by `-1` is legal and turns an infimum into a supremum. See W1.

---

## 1. Wiring (do this first — everything else depends on it)

### W1. The four-edge API
New file `Pptc/Box.lean`, importing `Pptc.Basic`.

- `box_xmin_Pconstructible : … → PConstructible (sInf (Prod.fst '' A))`, via `box_xmax` on
  `scale_x (-1) A`. Chain: `scale_x (-1) A = (fun p => (-p.1, p.2)) '' A`;
  `Prod.fst '' that = Neg.neg '' (Prod.fst '' A)`; then `sSup (-S) = -sInf S`
  (`Real.sInf_neg` / `csSup_neg` — confirm the exact name with `lean_loogle` before use).
  Compactness transfers by `IsCompact.image` (the reflection is continuous).
- `box_ymin_Pconstructible` — same with `scale_y`.
- `box_width_Pconstructible`, `box_height_Pconstructible` — the differences. These are what the
  drawing program actually reports and what the note's witnesses are phrased in.

Tag all four `@[pconstructible_cond]`: they carry side conditions (`IsCompact`, `Nonempty`),
so they must be unsafe rules, per `Pptc/Tactic.lean` §"Conditional leaves".

### W2. The compactness toolkit — highest leverage in the plan
Every single use of the box pays an `IsCompact` obligation. Prove it once:

- `isCompact_traced_arc : (∀ t ∈ Icc a b, DifferentiableAt …) → IsCompact (γ '' Icc a b)`
  — `hdiff` gives `ContinuousOn`, then `isCompact_Icc.image_of_continuousOn`.
  Both names confirmed present: `IsCompact.image_of_continuousOn`, `isCompact_Icc`.
- `nonempty_traced_arc : a ≤ b → (γ '' Icc a b).Nonempty` — `Set.nonempty_Icc.mpr`.
- Corollaries specialised to the exact hypothesis bundles of `arc_of_length` and `offset`, so a
  caller that has just applied either constructor can discharge both side goals by `exact`.

Without W2 every downstream theorem re-derives compactness and the ergonomics collapse.

### W3. Endpoint extraction for monotone arcs — the workhorse
```lean
theorem arc_xendpoint_Pconstructible
    (hA : PConstructibleCurve (γ '' Set.Icc a b)) (hab : a ≤ b)
    (hcont : ContinuousOn γ (Set.Icc a b))
    (hmono : MonotoneOn (fun t => (γ t).1) (Set.Icc a b)) :
    PConstructible (γ b).1
```
Proof: `sSup (Prod.fst '' (γ '' Icc a b)) = (γ b).1` by monotonicity, then `box_xmax`.
Plus the `y` version, and the antitone versions (which hit `box_xmin`).

### W4. Inverse arc length — the headline consequence
Compose W3 with `arc_of_length`:

> Given a constructible curve `S`, a tracing `γ`, a P-constructible start point, a
> P-constructible length `x`, and monotonicity of `γ` in a coordinate, the far endpoint of the
> laid arc is P-constructible in that coordinate.

Recovering the *other* coordinate, two routes — state both, they cover different curves:
1. **Monotone in both coordinates** — box twice. Covers monotone stretches of every graph.
2. **The arc is a graph** — get `X` from the box, then cross the vertical line `x = X` with
   `inter_y`. The vertical line is `poly_graph` of degree 1 rotated by `90`. Needs the usual
   isolation argument, but on a monotone arc it is immediate.

Deliverable: a single statement
`arcLength_inverse_Pconstructible` giving `PConstructible (γ b).1 ∧ PConstructible (γ b).2`.
Everything in §3 is an instantiation of it.

---

## 2. Proofs this makes easier

The pattern it kills is **"lay a complementary arc, prove the two arcs meet in exactly one
point, apply `inter_x`/`inter_y`"**. The uniqueness proof is the expensive part —
`inter_x`/`inter_y` require `S ∩ T = {(x,y)}` on the nose, so each use carries a bespoke
no-other-crossings argument. Where the endpoint is a coordinate extreme, the box replaces all
of it with one `box_xmax` application.

Known instances, in priority order:

| target | current proof | with the box |
|---|---|---|
| `ellipticEAm_Pconstructible_of_mem_Icc` (`Jacobi.lean:523-574`) | lays `ellipseParam` on `[0,φ]` **and** `ellipseCoParam` on `[0, π/2−φ]`, then ~25 lines of `Real.injOn_cos` to prove `hinter` | `ellipseParam b θ = (sin θ, b cos θ)`, and `sin` is strictly increasing on `[0,φ] ⊆ [0,π/2]`, so `box_xmax` returns `sin φ` directly; then `arcsin` |
| `ellipseCoArc_PConstructibleCurve` (`Jacobi.lean:494`) | exists **only** to be the complementary arc above | becomes dead code — delete |
| `cos_sin_Pconstructible` (`Basic.lean:2471-2485, 2578-2607`) | same complementary-arc pattern on the circle; `Basic.lean:2516` names the pattern explicitly | on `[0, x]` with `x ≤ π/2`, `y = sin θ` is increasing, so `box_ymax` gives `sin x`; `cos` by `√(1−sin²)` with the sign fixed by the quadrant |
| `ellipseParam_ellipticEAm_Pconstructible` (`Jacobi.lean:636`) | derived from the above plus trig | immediate from W4 |

**Estimated saving: 100–150 lines**, concentrated in the hardest-to-read parts of `Jacobi.lean`
and the `cos`/`sin` section of `Basic.lean`. `[SY]`

Sequencing note: do **not** rewrite these until W1–W3 are landed and green. Then do
`ellipticEAm` first — it is the cleanest and validates the whole API before touching the
`cos`/`sin` foundations that most of `Basic.lean` sits on.

The other `inter_x`/`inter_y` sites found by grep (`Basic.lean:161, 196, 527, 945, 2113, 2138,
2443, 2785`) are genuine curve-crossings, not endpoint extractions. The box does not touch them.

---

## 3. New numbers

### N1. The uniform theorem — state this before chasing individual constants
W4 instantiated says: **for every drawable curve admitting a coordinate-monotone tracing, the
arc-length parametrization `s ↦ γ(G⁻¹(s))` is P-constructible at every P-constructible `s`.**

`ellipseParam_ellipticEAm_Pconstructible` is exactly this theorem for the ellipse, proved the
hard way. The box generalises it in one stroke to `poly_graph` (deg ≤ 6), `power_law`,
`exp_two`, `sine`, and monotone Bézier pieces. Landing the general statement is worth more than
any individual constant below, and each of N2–N5 is then a corollary.

### N2. The parabola witness
`b = 0.44633388551759072893813142528262481720135752704286437386727212215` `[NC 50]`,
the abscissa at which `y = x²` has been traced to arc length `1/2` from the origin; box-width
of the `arc_of_length` stroke. Verified against `NIntegrate` (Wolfram, back-substitution returns
`0.5` to 30 digits).

Worth stating sharply, because it is the cleanest illustration of what the box adds:
`Basic.lean:1877-1899` **already mines this very curve's arc length in the forward direction** —
`parabolaAntideriv` is `(m/2)√(1+4m²) + (1/4)·arsinh(2m)`, and `log_Pconstructible` works by
choosing the special abscissa `m = (a²−1)/(4a)` at which the `arsinh` collapses to `log a`.
Forward you get to *pick* `m` so the transcendental part comes out clean. Backward you are
handed the length and must solve `(m/2)√(1+4m²) + (1/4)arsinh(2m) = 1/2`, with the algebraic
and transcendental parts inseparable. **General principle: `arc_length` gives elementary
functions evaluated; the box gives them inverted, and drawable curves' arc-length functions
are elementary while their inverses generally are not.** `log` was reachable only because
`arsinh`'s inverse happens to be drawable (`exp_two`); the box removes that side condition.

### N3. `sine` — a consistency check, and a second route to `ellipticEAm`
Arc length of `y = sin x` is `∫₀^X √(1 + cos²t) dt = √2 · E(X | 1/2)`, an incomplete
second-kind integral. So box-inverting the **sine graph** gives `ellipticEAm` at the
lemniscatic-adjacent parameter — a value the project already reaches off the **ellipse**.

Identity verified numerically at `X = 7/10`: both sides give
`0.95203326068729833739141511164856007118`, agreeing to 57 digits `[NC 57]`.

Do this one early and cheaply: it is a *cross-check on the axiom*, confirming the box
reproduces a known result by a new route rather than producing something inconsistent. If it
disagrees, the API in W1–W4 is wrong. `[SY]` for the identity, `[SP]` that the proof goes
through smoothly.

### N4. Higher graphs — elliptic, then genuinely beyond
Unit-length strokes from the origin. **Recomputed — the note's §4 table is wrong in both
entries.** It labels them `[NC 35]` but they are correct only to ~15 digits, the signature of a
machine-precision solve reported at arbitrary precision. Correct values, with back-substitution
into the arc-length integral returning `1.000…` to 47 digits (Wolfram, `WorkingPrecision -> 60`):

| graph | arc-length density | inverse at length 1 | note's value diverges at |
|---|---|---|---|
| `y = x³` | `√(1+9t⁴)` | `X = 0.790706893627604843078476035616…` `[NC 45]` | digit 16 |
| `y = x⁴` | `√(1+16t⁶)` | `X = 0.810451620058442235121609068479…` `[NC 45]` | digit 15 |

Use these, not the note's. The parabola witness `b` in N2 *was* re-verified and is correct as
the note gives it, so the error is confined to this table.

`y = x³` inverts an elliptic arc length — the H6/R4 territory, approached from the other side.
`y = x⁴` is the interesting one: the integral is **genus 2**, so its inversion is hyperelliptic
and lands outside everything the project's elliptic/Jacobi machinery covers. That is the most
exotic thing the box reaches and the best candidate for "a number nobody would have tied to
`PConstructible`", in the sense PLAN-hypergeometric §5 means it. `[SP]`

### N5. `exp_two`
Arc length of `y = 2^x` has the closed form
`(1/ln 2)·[√(1+u²) − ln((1+√(1+u²))/u)]` evaluated between `u = ln 2` and `u = ln 2 · 2^X`.
Forward it is already P-constructible by `arc_length`. Box-inverting gives `X` as the solution
of that transcendental equation at a prescribed length.

Note **this is not a route to `e` or `ln 2`** — `log_Pconstructible` (`Basic.lean:1899`) and
`exp_one_Pconstructible` (`Basic.lean:1926`) are already in the library, so both are reachable
today. Checked and dead: boxing a *rotated* `exp_two` yields `log₂(e · ln 2)`, which for the
same reason is already constructible. Recording it so nobody re-derives it. `[SY]`

### N6. The one algebraic lead: offset cusps
The offset's velocity is `(1 − d·κ(t))·γ'(t)` — **parallel to the base velocity** (Frenet:
`dN/dt = −κγ'`). So the offset's coordinate extrema sit at exactly two kinds of parameter:
where `x'(t) = 0` (the *base* curve's extrema — a quadratic for a cubic pair, nothing new), and
at the cusps `1 − d·κ(t) = 0`. That one observation disposes of everything else the note's §5.3
worried about, and also settles §5.3 negatively for every base curve: `poly_graph` extrema
solve `p'(x) = 0` with `p'` itself a drawable `poly_graph` (intersect it with `y = 0`);
rotated-`sine` extrema need only `arccos`, which exists.

The cusps are the exception. For a cubic pair, `x'y'' − y'x''` is a cubic and `x'² + y'²` a
quartic, so cusp parameters solve
```
(x'² + y'²)³ = d² · (x'y'' − y'x'')²
```
a degree-**12** equation in `t`. Given that `Offset.lean:398` already grinds a degree-10
rationalized crossing equation to reach all real quintic roots, and `DegreeSeven.lean` /
`Nonic/` are hunting specific degrees, it is worth checking whether cusp parameters land outside
what crossings reach.

Caveat, and it is a real one: a cusp is a local extremum only along the `γ'(t*)` direction, so
making it the *global* box extremum needs a window isolating it — and the note's §3b
counterexample shows the isolating bound can be the unknown itself. Investigate, but expect the
window argument to be the hard part, not the algebra. `[SP]`

### N7. `arc_of_length` becomes composable — the structural gain
Today, on an open curve, laying a string is a **dead end**: `Defs.lean:306-312` is explicit that
the far endpoint is not produced, so no second construction can start from it. With the box the
endpoint is recoverable on a monotone arc, so laying arcs becomes iterable: the marked points of
a drawable curve are closed under adding P-constructible arc lengths, with `arc_length`
inverting the operation.

This is arguably worth more than any individual constant, because it changes the *shape* of the
language rather than adding to it, and it is the part the note never mentions. Concretely, look
for numbers from **alternating** constructions the language could not express before — lay a
length on curve `C₁`, read the endpoint, draw `C₂` through it, lay a length on `C₂`, and so on.
Nothing of this form has ever been reachable on an open curve. `[SP]`

---

## 4. Re-audits the change forces

1. **`Jacobi.lean:687-745`, `#### Why the first kind resists`.** The prose enumerates "four
   things" the drawing program can do to produce a number; there are now five. **I audited the
   argument and its verdict is unchanged** — the box strengthens arc-length inversion (making it
   work on open curves, where previously only closed curves recovered the endpoint by
   complementary arc) rather than adding a new kind of inversion, and the load-bearing claim
   ("`F` is not the arc length of any drawable curve") is untouched. Needs a sentence saying so,
   not a rewrite. `[SY]`
2. **`Defs.lean` module docstring and `CLAUDE.md` § "Allowable primitives"** both enumerate the
   constructors and must gain the box. `CLAUDE.md` is the more important one — subagents read it
   as ground truth and will otherwise assume extrema are unreachable.
3. **The R1 and R4 value surveys** assumed no endpoint extraction (note §6.4). R4's standing
   caveat that an `arc_of_length` arc has no obtainable endpoint dissolves for monotone arcs.
4. **`NOTES-defs-arc-endpoint-extraction.md`** should get a correction header pointing here:
   §3's statement is unsound as written, §5.2 is false, §5.3 is resolved negatively except for
   offset cusps, §0's countability claim does not hold of the form it proposes, and **both
   numbers in the §4 table are wrong past ~15 digits despite carrying an `[NC 35]` label**
   (N4 above has the corrected values). The last one is worth a moment's thought about process:
   an `[NC n]` label is only worth what the computation behind it was, and a machine-precision
   root-find reported to 21 digits passes review unless someone re-runs it.

---

## 5. The Jacobi claim, closed

The note's §5.2 says `ellipticF` "is realised as a Bézier arc length" and that box-inverting it
gives `am`, hence `sn`/`cn`/`dn`. It is not. `Basic.lean:3514-3550` proves

```
F(φ) = (3·J(T) + (1+m²)/m²·E(φ) − tan φ·Δ(φ)·(1/cos²φ + (1+m²)/m²)) / 2,   T = tan φ
```

with `J` the Bézier arc length — `F` is a *combination* of an arc length, a second-kind
integral, and an algebraic boundary term. `Jacobi.lean:711-716` already states the refutation:
laying an arc of length `L` gives the `T` with `J(T) = L`, **not** the `T` with
`J(T) − (algebraic in T) = L`, and it is the second equation the amplitude solves. Having `J⁻¹`
and `E⁻¹` separately does not invert `3J − (stuff)`; that needs a fixed point, which is a limit,
not a finite construction.

The second half of §5.2 (inverting the *complete* integrals to get eccentricity from quarter
perimeter) fails differently: that inverts in the curve's **parameter** `c`, not in arc length
along one drawn curve, and you need a constructible `c` to draw the ellipse at all. No box
touches it.

What `J⁻¹` *is* remains an open and legitimate question — it is a new function at
P-constructible lengths. It is simply not `am`. `[SY]`

---

## 6. Suggested task split

One deliverable per subagent, per `CLAUDE.md` § Subagents, each with a
`HANDOFF-box-<topic>.md` log:

| task | file | depends on |
|---|---|---|
| B1 | `Pptc/Box.lean` — W1 four-edge API + W2 compactness toolkit | — |
| B2 | `Pptc/Box.lean` — W3 monotone endpoint extraction | B1 |
| B3 | `Pptc/Box.lean` — W4 `arcLength_inverse_Pconstructible` + N1 uniform statement | B2 |
| B4 | `Pptc/Jacobi.lean` — rewrite `ellipticEAm_Pconstructible_of_mem_Icc`, delete `ellipseCoArc_PConstructibleCurve` | B3 |
| B5 | `Pptc/Basic.lean` — rewrite `cos_sin_Pconstructible` (**do last**; most of `Basic.lean` sits on it) | B4 green |
| B6 | N3 sine cross-check | B3 |
| B7 | N6 offset-cusp investigation (research note first, no Lean) | B3 |

B1–B3 are one file and could be a single agent; B5 should not start until B4 has validated the
API on a smaller target.

## 7. Ledger

| claim | label |
|---|---|
| `⊆`-form of the box collapses `PConstructible` to `ℝ` | `[SY]` — witness in §0 |
| `Defs.lean` compiles with `box_xmax`/`box_ymax`; `lake build Pptc.Defs` green | `[SY]` |
| `Basic.lean` still compiles against the new `Defs` (`lake env lean`, exit 0, no output); no `cases`/`induction` on either inductive anywhere | `[SY]` — build + grep |
| note's `y=x³`, `y=x⁴` witnesses wrong past ~15 digits; corrected in N4 | `[NC 45]` Wolfram |
| arc length of `y = sin x` identity checked at `X = 7/10` | `[NC 57]` Wolfram |
| `scale_x`/`scale_y` carry no positivity hypothesis, so `-1` reflection is legal | `[SY]` `Defs.lean:267-272` |
| parabola witness `b = 0.446333885517590728938…` | `[NC 50]` Wolfram |
| box shortens `ellipticEAm`, `cos_sin`, kills `ellipseCoArc` | `[SY]` |
| arc length of `y = sin x` is `√2·E(X\|1/2)` | `[SY]` |
| `e`, `ln 2`, `log₂(e·ln 2)` already reachable — no new constants there | `[SY]` `Basic.lean:1899, 1926` |
| offset velocity `∥` base velocity, so extrema = base extrema ∪ cusps | `[SY]` Frenet |
| cusp parameters solve a degree-12 equation | `[SY]` degree count |
| cusps give algebraic values outside crossing reach | `[SP]` |
| `y = x⁴` inversion is genus-2 / beyond the elliptic machinery | `[SP]` |
| box does **not** reach `am`/`sn`/`cn`/`dn` | `[SY]` `Basic.lean:3540`, `Jacobi.lean:711` |
