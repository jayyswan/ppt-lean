# PLAN-offset: what the `offset` constructor can reach (read first, every task)

Programme goal: find out **exactly** what `PConstructibleCurve.offset` adds to `PConstructible`.
The main target is **higher-degree real algebraic numbers**: more families of them, and ideally
whole degrees. Other new numbers or techniques found along the way are also wanted, and every
task should record them in a section titled "Side discoveries".

Write `K` for the set of P-constructible reals. It is a subfield of `ℝ`.

## 1. The moves (from `pptc/Pptc/Defs.lean`; read that file, it is short)

Numbers: `1`, `+ − × ÷`, a coordinate of the **unique** crossing of two constructible curves,
and the arc length of an injectively traced piece of a constructible curve between endpoints
that are P-constructible *points of the plane*.

Curves:
* base curves: ellipse, rectangle boundary, polynomial graph of degree ≤ 6 with **rational**
  coefficients, `y = a x^b` for `x > 0` (rational `a, b`), `y = 2^x`, `y = sin x`, and the cubic
  Bézier with control points in `K`;
* closure operations: translate, scale each axis separately, rotate, restrict to a window,
  `arc_of_length`, `offset`. All parameters are in `K`.

**Every parameter may be a number computed earlier in the same construction.** Constructions
are finite trees.

`offset` (`Defs.lean:372`) takes an arc `γ` of a constructible curve on `[a, b]` that is
injective, differentiable, regular (`speed ≠ 0`) and has continuous velocity, plus `d ∈ K` of
either sign. It returns the set `{γ t + d·N(t)}`, where `N = (−y′, x′)/√(x′² + y′²)` is the
unit normal. The offset curve itself need **not** be injective or regular: cusps and
self-crossings are allowed.

## 2. What is already in `K` (usable as black boxes)

Algebraic numbers:
* `root_Pconstructible_le_six_coeffs` (Basic): every real root of a nonzero polynomial of
  degree ≤ 6 with coefficients in `K`.
* `root_Pconstructible_le_eight` (Basic): every real algebraic number of degree ≤ 8 over **ℚ**.
  This uses `y = x^n` against a degree-6 graph and a shift, and stops at 8 because of Hermite's
  trace form (see §4).
* `nonicVal_root_Pconstructible` (Basic): the real roots of `M³ + λM² + v²` with `M` a monic
  cubic, `v` a cubic, coefficients in `K`. This is a codimension-1 family of nonics; see
  `archived files/NONIC-notes.md`.
* `cubicGraph_cubic_cross_root_Pconstructible` (scratch; `archived files/HANDOFF-degree9engine.md`):
  the roots of `a(t) = c(b(t))` for cubics `a, b, c`.
* `root_Pconstructible_of_nonreal_root` (`Pptc/DegreeSeven.lean`; paper `septicpaper_revised.tex`):
  **every real root of a degree-7 polynomial over `K` that has at least one non-real root.**
  Method: a Tschirnhaus map killing `p₁, p₂, p₃`, then the power-law engine `y⁷ = cubic(y)`.
  **Totally real septics over `K` are open.** They are the first gap in "is `K` real closed?".
* `Pptc/Offset.lean` (**read the whole file**; it is the starting point of this programme):
  offset a cubic pair `γ = (x, y)` by `d` and cross it with the line `A X + B Y = C`. Clearing
  the square root gives the degree-10 polynomial

      u² · (u′² + v′²) − D² · v′²,    u = A x + B y − C  (cubic),  v′ = (B x − A y)′,  D² = d²(A² + B²)

  (`offsetCrossPoly_normalForm`). The parameter comes back through the **normal equation**
  `(X − x)x′ + (Y − y)y′ = 0`, a quintic. One explicit root family has Galois group `⊇ A₁₀`,
  hence lies outside every tower of degree-≤6 steps. But the family has image dimension 7 in
  the 10-dimensional space of monic decics: **codimension 3.**

Transcendental numbers and functions: `√`, `sin`, `cos`, `arcsin`, `arccos`, `arctan`, `π`,
`2^x`, `log`, `e`, `ellipticF`, `ellipticE`, the third-kind integral (partially), the inverse of
`E`, `√π`, and some gamma values. See `CLAUDE.md` and `PLAN-jacobi-X0-overview.md`.

## 3. Facts about offsets you may rely on (check them in your own setting)

* **(O1) Speed.** `speed(offset) = |v| · |1 − d κ|`, where `κ = (v × v′)/|v|³` is signed
  curvature. So the offset is singular exactly where `d = 1/κ` (a cusp, sitting on the evolute).
  For chains of offsets and linear maps, see F3 in `PLAN-jacobi-00-overview.md` (checked in
  `NOTES-jacobi-R1a.md` / `R1c.md`).
* **(O2) Length of a parallel curve.** Where `1 − dκ > 0`, `L_d = L − d·(θ(b) − θ(a))`, with `θ`
  the tangent angle.
* **(O3) Offsets commute with similarities** (rotation, translation; uniform scaling multiplies
  `d`). They do **not** commute with `scale_x` alone. Offsetting twice along the same normal is
  a single offset by `d₁ + d₂`. So iteration only adds something new when a non-similarity
  affine map sits in between.
* **(O4) Both signs are free.** `d ↦ −d` is allowed, so the norm (squared) form of a crossing
  equation, over `K(t)[w]` with `w = √(x′² + y′²)`, loses nothing. Its real roots with `w ≠ 0`
  are all genuine crossings for one sign of `d` or the other.
* **(O5) Implicit degrees.** Literature (Farouki–Neff 1990, *Algebraic properties of plane offset
  curves*, CAGD 7) gives degree `4n − 2` for the offset of a degree-`n` polynomial parametric
  curve. That is 10 for a cubic Bézier and 6 for a parabola; the parabola's 6 was checked in
  Wolfram this session. The general offset of an ellipse has degree 8. Verify any of these you
  use.
* **(O6) Rational offsets.** Parabolas and Pythagorean-hodograph (PH) cubics (the Tschirnhausen
  cubic and its similar images) have offsets that are **rational curves**. No square root is
  left, so crossings with them are exact polynomial equations. References: Farouki,
  *Pythagorean-Hodograph Curves* (Springer 2008); Pottmann, *Rational curves and surfaces with
  rational offsets*, CAGD 12 (1995). In Pottmann's dual picture (support function `h(θ)` of
  tangent lines `x cos θ + y sin θ = h`), **an offset is `h ↦ h + d`**, which is linear. Use it.
* **(O7) Recovery.** The offset crossing gives the point `(X, Y)`. The base parameter `t` is a
  root of the normal equation, which has degree `2n − 1` for a degree-`n` polynomial curve.
  That is ≤ 6 only for `n ≤ 3`. **But the coordinates `X, Y` are themselves new numbers**, so
  recovery matters only when the target is `t`.

## 4. The yardstick: when is a family "new", and when does it cover a degree?

Call a family of polynomials an **engine** when every real root of every member (subject to open
side conditions) is in `K`. A target polynomial `P` over `K` is **covered** if:

1. **Cofactor.** `P · g ∈ engine` for some `g` over `K`. Extra roots of `g` are cut away by
   `restrict`.
2. **Möbius.** Roots may be moved by `t ↦ (at + b)/(ct + e)` with `a, b, c, e ∈ K`, which maps
   `K` to `K`. So measure dimensions **modulo `PGL₂`**: degree-`N` binary forms up to `GL₂` have
   `N − 3` moduli.
3. **Tschirnhaus.** Replace `P` by the characteristic polynomial of `φ(companion(P))` for `φ`
   over `K` of degree ≤ 6. Undoing it is a degree-≤6 root. Only real `φ` are available.
   Hermite's trace form `Tr(φ²)` is positive definite when `P` is totally real, so over `ℝ` a
   totally real `P` can have at most **one** power sum killed (`p₁`). That is the obstruction
   behind degree 8 over ℚ and behind the totally-real septic.
4. **The covering system must itself be solved inside `K`.** Its unknowns (engine parameters,
   `g`, `φ`) have to be found by a sequence of steps, each of them field arithmetic, a root of
   degree ≤ 6, a root from an engine already in hand, or a free rational choice. A free
   rational choice is legitimate wherever the requirement is an open condition (density of
   `ℚ`), and through the intermediate value theorem along a rational segment, as in
   Prop. `phi-B` of the septic paper. **A parameter count that closes is not a proof.** The
   degree-10 offset family is a warning: counts looked slack, and the map was degenerate. The
   direct degree-9 route died because its auxiliary unknowns had degree 10
   (`archived files/HANDOFF-degree7-s2.md` ~l.860).

**"Genuinely new" checklist** for a specific number or family:
* degree over `K`, and minimal polynomial over ℚ for a rational instance;
* not a root of degree ≤ 8 over ℚ, not in the nonic family, not a septic with a non-real root,
  not in the codim-3 decic family;
* Galois evidence that it lies outside every tower of degree-≤6 steps (see the A₁₀ argument at
  `Offset.lean:738-773`).

**Wolfram 15 has no `GaloisGroup`.** Use cycle types of factorizations mod primes (Chebotarev
sampling: `FactorList[p, Modulus -> q]`, or sympy `factor_list(p, modulus=q)`), plus
transitivity, primitivity, and Jordan's theorem.

## 5. Rules for every `offset` task

* **Lean is encouraged, inside a private scratch file.**
  * **Scratch file.** Each task may create exactly one file, `pptc/Pptc/Scratch/Offset<ID>.lean`
    (e.g. `OffsetA2.lean`), imported by nothing.
  * **Library files are read-only.** Do not edit any other `.lean` file (`Defs`, `Basic`,
    `Offset`, …).
  * **Check through the LSP only:** `lean_diagnostic_messages`, `lean_goal` and
    `lean_multi_attempt`, with paths relative to `pptc/`. `lean_run_code` works for throwaway
    snippets. **Never run `lake build`**: it is broken for new modules and OOMs the machine.
  * **Memory.** Several tasks run in parallel. Import only what the snippet needs: pure algebra
    identities need a few Mathlib modules, not `Pptc.Offset`. Have at most one file importing
    `Pptc.Basic` or `Pptc.Offset` open at a time.

  What Lean is good for here:
  * **Certifying identities.** Normal forms (the `offsetCrossPoly_normalForm` pattern),
    rationalization / norm identities, recovery equations, and leading-coefficient and degree
    facts close with `ring`, `field_simp` and `linear_combination`. Mark a Lean-checked identity
    **[Lean]**; it outranks [symbolic] and [numeric].
  * **Settling legality.** State the `offset` / `crossing_Pconstructible` application for your
    construction and check that the side conditions can be discharged, or find which cannot.
  * **Pinning headline claims.** Write each headline as a precise Lean statement. A `sorry` proof
    is acceptable in scratch, but must be **reported as unproved** in NOTES.

  Lean is *not* the tool for Gröbner bases, elimination, Galois groups or dimension counts; use
  Wolfram and Python for those. Do not spend more than about a fifth of your effort on proofs:
  the deliverable is still the NOTES file.
* Deliverable: `NOTES-offset-<id>.md` at the repo root (`C:\dev\Powerpoint\lean`). Progress log:
  `HANDOFF-offset-<id>.md`. Create the log first and append one line after every step. **Update
  NOTES incrementally** so that an aborted run still leaves results on disk.
* Tools:
  * Python 3.12 with `sympy 1.12`, `mpmath`, `numpy`, `scipy` at
    `C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`.
  * Scripts go in `archived files/offset-scripts/`, with filenames prefixed by your task id
    (e.g. `A2-03-jacobian.py`). You may read other tasks' scripts; do not modify them.
  * **Wolfram MCP** (`WolframLanguageEvaluator`): stateless kernel, so put all definitions in
    each call. Use it for `GroebnerBasis`, `Resultant`, `Eliminate`, `Factor`, `NSolve`
    (homotopy-style root counts), `Reduce`, `CylindricalDecomposition` (real feasibility) and
    `MinimalPolynomial` / `RootReduce` (exact identification). Long jobs need `timeConstraint`.
    Cross-check anything decisive in a second system.
  * Web search for literature; cite URLs.
* Tag every identity **[symbolic]** or **[numeric, N digits]**. Tag dimension counts
  **[Jacobian rank at k random rational points, mod p / exact]**.
* **A positive claim** ("these numbers are in `K`") must include:
  1. the construction as an explicit tree of moves (curve, parameters, which crossing or
     length, the window);
  2. a numerical check to ≥ 30 digits that the tree outputs the claimed number;
  3. a check of the side conditions: the base arc is injective and regular with continuous
     velocity, the crossing is isolated, and the sign of `d`;
  4. the "genuinely new" checklist from §4.
* **A negative claim** must state exactly which class of constructions it excludes, and which
  assumption a construction would have to break to escape it.
* Put a plain-language summary of at most 12 lines at the top of NOTES. Put a "Leads for other
  tasks" section at the end.

## 6. Tasks

Wave 1: all independent, run in parallel.

| file | question |
|---|---|
| `PLAN-offset-A1-atlas.md` | Algebraic geometry of single offsets of every drawable base curve: degree, genus, rationality, singularities, recovery. |
| `PLAN-offset-A2-crossing-families.md` | Every "one offset × one curve" crossing family: normal form, image dimension mod `PGL₂`, and cofactor coverage of degrees 7–12. |
| `PLAN-offset-A3-offset-offset.md` | Crossings of two offsets, self-crossings of one offset, cusps: new extraction mechanisms and the families they give. |
| `PLAN-offset-A4-chains-rational.md` | Offset ∘ affine ∘ offset chains, rational (PH and parabola) offsets as new exact rational curves, and parameter growth. |
| `PLAN-offset-B1-totally-real-septic.md` | Attack the frontier: a real root of a totally real septic over `K`, via offsets. |
| `PLAN-offset-B2-theory.md` | Resolvent degree and Hilbert's 13th problem over ℝ, the Artin reduction for real closedness, and what an engine family would need. |
| `PLAN-offset-B3-beyond-algebraic.md` | Non-algebraic yield of offsets: lengths, `arc_of_length` on offsets, transcendental curves, named constants. |
| `PLAN-offset-B4-legality-formalization.md` | Which offset-based extractions are legal under `Defs.lean`, and the generic Lean lemmas the best results would need. |

Wave 2: after wave 1.

| `PLAN-offset-Z-synthesis.md` | Cross-check the strongest claims, reconcile the tasks, rank the results, draft the follow-up Lean and research plans. |
