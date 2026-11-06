# PLAN-septic-normform: the totally real septic, via the norm structure of offset crossings

**Goal.** Decide whether offset crossings can put every real root of a **totally real** septic over
`K` (the P-constructible reals) into `K`. That would close the only remaining degree-7 gap:
`root_Pconstructible_of_nonreal_root` already handles every septic with a non-real root. The
secondary goal is the same question for totally real nonics over ℚ, which hit the same wall.

**Honest prior: low odds.** The value of this task is either a real discovery or a clean, decisive
negative for a whole class of routes. A vague "reduced to a hard system" is **not** a useful
outcome, so aim for one of the two.

Read before starting:
* `NOTES-offset-B1.md`: the square covering system. **Its "deg Δ ≤ 5" evidence is invalid** (§1
  below).
* `NOTES-offset-B2.md` §3 and §5: the engine formalism, the Hermite obstruction, and the decic
  family's `PGL₂` codimension 1.
* `NOTES-offset-A2.md`: the offset-cubic × conic family.
* `pptc/Pptc/Offset.lean`: `offsetCrossPoly_normalForm`, `offsetCubicPairCross_root_Pconstructible`.
* `septicpaper_revised.tex`: the one successful template. Its key move is a **rational curve over
  `K` inside the solution set**, the stereographic line plus a sextic intermediate-value argument.

Log: `HANDOFF-septic-normform.md`. Deliverable: `NOTES-septic-normform.md`.
Scripts: `archived files/septic-scripts/`. Lean scratch: `pptc/Pptc/Scratch/SepticNormForm.lean`
(LSP only, never `lake build`, library read-only).
Tools: Python 3.12 (sympy, mpmath, numpy, scipy) at
`C:\Users\<user>\AppData\Local\Programs\Python\Python312\python.exe`, and the Wolfram MCP.
Tag claims **[Lean] / [proof] / [symbolic] / [numeric, N digits]**.

Test target throughout: the totally real septic `f = x⁷ − 14x⁵ + 49x³ − 36x + 1`, which has Galois
group `S₇` (B2).

## 1. Correction you must absorb first

B1 reported minimal-polynomial degrees 3–6 for the auxiliary unknowns, found by PSLQ at 120–200
digits with `maxcoeff` 10⁶⁰–10⁸⁰. **That is inside the regime where PSLQ finds a relation for any
real number.** Six numbers known to 200 digits always satisfy an integer relation with coefficients
around 10^(200/6). `archived files/septic-scripts/00-pslq-artefact.py` shows PSLQ, at B1's settings,
returning "degree-4 minimal polynomials" with coefficients around 10⁴⁴ for *random* numbers.

**Rule for this task:** accept a PSLQ relation of degree `d` with coefficients up to `H` only when
`(d+1)·log₁₀H ≤ digits/2`, and re-verify it at twice the precision. Prefer exact methods.

## 2. Phase 0: the kill test for the decic route (do this first, bounded)

Square system (B1 §1): `u = t³+at²+bt+c`, `v′ = pt²+qt+r`, `Δ`, with
`u²(u′²+v′²) ≡ Δ·v′² (mod f)`, which is 7 equations in 7 unknowns.

1. **Count the complex solutions** for `f`. Use Wolfram `NSolve` (total-degree homotopy) or a
   monodromy loop, remove the spurious components (`v′ ≡ 0`, `Δ = 0`), and cross-check with a second
   start system or random linear slices.
2. **The honest degree of `Δ`** over ℚ for `f`. Either do an exact elimination mod several primes
   (Wolfram `GroebnerBasis[..., Modulus -> p]` for the specific `f`; it is smaller than B1's generic
   run) and read off the degree, or run PSLQ at ≥ 1500 digits under the §1 rule. Also compute cycle
   types of the elimination polynomial mod primes.
3. **Verdict.** A K-point for every totally real septic needs, uniformly in `f`, a solution whose
   coordinates lie in towers of degree-≤6 steps (or come from existing engines, e.g. septics with a
   non-real root). If the solutions of the square system form one orbit of size `N > 6` under a
   large monodromy group, **the decic route is dead**. Write this as a theorem-level statement, with
   the monodromy / Galois evidence, and state exactly what it excludes.

## 3. Phase 1: the norm-form reformulation

The rationalized crossing polynomial is a norm: `u²S − Δv′² = (u√S − √Δ v′)(u√S + √Δ v′)`, where
`S = u′² + v′²`. Work in the étale algebra `A = K[t]/(f)`, which is `≅ ℝ⁷` over ℝ since `f` is
totally real.

The following derivation is **mine and unchecked**; verify it first.
* The covering condition is `S·u² = Δ·v′²` in `A`.
* Expanding `S`: `v′²·(Δ − u²) = u′²·u²` in `A`. So wherever `Δ − u² ∈ A` is invertible,
  **`v′² = u′²u²/(Δ − u²)` in `A`.**
* Consequences to test:
  * **Positivity.** Over ℝ this needs `Δ > u(rᵢ)²` at every root where `u′u ≠ 0`. That is an open
    condition, which would explain why B1 always found real solutions with `Δ > 0`.
  * **The K-structure.** Fix `u` (a monic cubic over `K`) and `Δ ∈ K`. The condition becomes:
    *the element `c = u′²u²/(Δ − u²)` of `A` is the square of an element represented by a
    polynomial of degree ≤ 2.* The real solutions choose a sign of `√c(rᵢ)` at each of the 7 roots,
    which should explain the many real solutions (up to `2⁶` sign branches). A `K`-point, however,
    needs `c = s²` **inside `A`**, with `s` of degree ≤ 2.
  * **Counting.** "Square of a degree-≤2 element" is a codimension-4 condition on `c ∈ A` (7
    dimensions against 3), matched by 4 unknowns `(a, b, c, Δ)`. The system is square again, but
    now with structure: squares in `A`, a norm map, a quadratic form `Tr(λ s²)`.

**Questions.**
1. Verify the reformulation [symbolic], including the non-invertible cases.
2. Use it to redo Phase 0's count by sign patterns, as a sanity check.
3. Search the **structure** for a rational curve over `K`:
   * Can `u` or `Δ` be chosen so that the condition becomes linear, or quadratic with a known point,
     in the remaining unknowns? The septic paper's cone-point-plus-stereographic-line trick is the
     model.
   * Is the variety `{(u, Δ, s) : u′²u² = (Δ − u²)s² in A}` rational or unirational over `K`? Does it
     contain lines through obvious points, such as `u′ ≡ 0 mod f` or `s` a constant?
   * Recast "is `c` a square in `A`" via the trace form `Tr(λ·x²)` (Serre's trace-form theory,
     Conner–Perlis). Totally real `A` means these forms are definite for totally positive `λ`, which
     is exactly the Hermite phenomenon seen from the other side. **Decide whether this gives a proof
     that the decic route cannot produce `K`-points uniformly.**

## 4. Phase 2: families with slack, in the same language

The offset-cubic × conic family has a covering system of 7 equations in 13 effective parameters.
Reformulate it the same way. **The crossing condition is linear in the conic's 6 coefficients**, so
covering `f` means the 7 sign-chosen offset points at the roots `rᵢ` lie on a common conic over `K`.
That is 2 determinantal conditions on the cubic pair and `d`.

1. Write this rigorously in `A[w]/(w² − S)`, including how Galois conjugation interacts with the sign
   choices. When is the conic defined over `K` rather than over the splitting field?
2. **Look for a rational curve over `K`** in the solution set of those 2 conditions: a one-parameter
   family, rational over `K`, along which a defect function of degree ≤ 6 changes sign. That is the
   septic-paper shape. Test candidate sub-families with extra structure: `d` tied to `u`, a
   symmetric cubic pair, a circle as the conic, or a conic through `K`-rational points.
3. Do the same for the degree-6 rational graph as the second curve (A2's F4; coverage is linear in
   the graph's coefficients), and for offset × offset if the linear structure survives.
4. For every family, say whether a trace-form positivity argument (in the style of Phase 1, question
   3) forbids `K`-points for totally real `f`. **A general obstruction theorem is a valuable
   result:** "no offset crossing whose covering condition is `X` can cover totally real septics
   uniformly".

## 5. Phase 3: transfer

Whatever Phase 1–2 finds (construction or obstruction), state what it implies for **totally real
nonics over ℚ**, the case excluded by `PLAN-nonic-meyer.md`. Rational coefficients allow the degree-8
closure over ℚ, and Meyer / Hasse–Minkowski isotropy for rational forms; say whether either changes
the verdict.

## 6. Stop rules and deliverable

* **Stop Phase 0** once the degree / monodromy verdict is firm. Do not let it expand.
* **If Phase 1 question 3 yields an obstruction proof**, tighten it, test its scope on Phase 2's
  families, and write it up. That is a complete result.
* **If a construction appears**, it must meet the full standard: an explicit move tree; an exact
  `K`-point for `f` (not merely a real one); a 30-digit check that the tree outputs a root of `f`;
  the side conditions (regularity, isolation, the sign of `d`); and a uniformity argument for **all**
  totally real septics over `K`, not just `f`.

`NOTES-septic-normform.md` must contain:
1. a plain summary of at most 12 lines;
2. the Phase 0 verdict, with its numbers;
3. the verified reformulation;
4. the rational-curve search results, or the obstruction theorem with its exact scope;
5. the Phase 2 findings;
6. the transfer to nonics;
7. Side discoveries and Leads.

**Never report the septic as solved on numerical evidence.**
