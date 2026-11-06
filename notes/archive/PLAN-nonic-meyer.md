# PLAN-nonic-meyer: real roots of rational nonics with a non-real root

**Goal.** Prove, or refute with a precise reason, the following:

> **Conjecture N.** Every real root of a polynomial of degree 9 with **rational** coefficients and at
> least one non-real root is P-constructible.

This would lift `root_Pconstructible_le_eight` (all real algebraic numbers of degree ≤ 8 over ℚ)
past degree 8 for every non-totally-real nonic. It is the rational-coefficient analogue of
`root_Pconstructible_of_nonreal_root` (septics over `K` with a non-real root), one degree higher.
Totally real nonics are **not** in scope: Hermite's trace form rules the method out for them (§2).

Read before starting:
* `pptc/Pptc/Basic.lean` ~l.455-680: the degree-8 section and its Hermite paragraph,
  `powerLaw_root_Pconstructible`, `root_Pconstructible_le_eight`;
* `septicpaper_revised.tex`, the template, which uses the same trace-form / Tschirnhaus pattern
  over `K`;
* `root_Pconstructible_le_six_coeffs` (`Basic.lean` ~l.1372).

Log: `HANDOFF-nonic-meyer.md` (create it first, append one line per step).
Deliverable: `NOTES-nonic-meyer.md`, plus `nonicpaper.tex` if the proof closes.
Scripts: `archived files/nonic-scripts/`. Lean scratch: `pptc/Pptc/Scratch/NonicMeyer.lean`
(imported by nothing; LSP only; never `lake build`; library files are read-only).
Tools: Python 3.12 with `sympy`, `mpmath`, `numpy`, `scipy` at
`C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`, and the Wolfram MCP.
Tag every claim **[Lean] / [proof] / [symbolic] / [numeric, N digits]**.

## 1. The proposed argument (a sketch to be checked, not a result)

Let `q ∈ ℚ[x]` be monic of degree 9, `β` a real root, `A = ℚ[x]/(q)`, and `Tr` the trace
`A → ℚ`. The form `B(f,g) = Tr(fg)` has rational Gram entries (power sums of the roots).

1. **Pick a rational `ψ`** of degree ≤ 6 and put `z = ψ(β)`. Assume `z` generates the root field
   `ℚ(β)`; see §3.3 for when it does not.
2. **Pick a rational, nonzero `φ` of degree ≤ 6** with `Tr(φ(z)) = 0` and `Tr(φ(z)²) = 0`.
   Existence: on the 6-dimensional ℚ-space `V_ψ = {φ(z) : deg φ ≤ 6, Tr = 0}`, the form
   `Q(f) = Tr(f²)` is a **rational** quadratic form in 6 variables. **Meyer's theorem**: an indefinite
   rational quadratic form in ≥ 5 variables has a nonzero rational zero. So it suffices that `Q|V_ψ`
   is **indefinite**.
3. **Resolvent.** `R(Y) = charpoly of multiplication by φ(z)` on `A` is monic of degree 9 with
   rational coefficients. Newton's identities turn `p₁ = p₂ = 0` into `e₁ = e₂ = 0`, so
   `R(Y) = Y⁹ − p(Y)` with `p ∈ ℚ[Y]` of degree ≤ 6. `y := φ(z)` is a real root of `R`.
4. **`y ∈ K`.** Cross `y = x⁹` (`power_law`) with the rational graph of `p`, using
   `powerLaw_root_Pconstructible` (it needs `n = 9 > 6` and a nonzero root; `y = 0` is trivial).
5. **`z ∈ K`.** `z` is a real root of `φ(X) − y`, which has degree ≤ 6 and coefficients in `K`, and
   is nonzero because `φ` is nonconstant: a nonzero constant has trace `9c ≠ 0`. Apply
   `root_Pconstructible_le_six_coeffs`.
6. **`β ∈ K`.** `β` is a real root of `ψ(X) − z`, of degree ≤ 6 over `K`; apply the same lemma.

Why this was not done before: the graph in step 4 must have rational coefficients, so `φ` and `ψ`
must be rational. The real cone-point argument of the septic paper gives only a real `φ` (a root of
a quadratic), and it is Meyer's theorem that supplies a rational one.

## 2. Why totally real nonics are excluded

If `q` is totally real, `Q` is positive definite on `{Tr = 0}` (Hermite), so step 2 forces `φ = 0`.
Record this as a precise negative statement, and say whether **any** variant (different
Tschirnhaus degree, a different engine for step 4) could avoid it.

## 3. Questions

### 3.1 Check the chain rigorously
* Steps 3–6 with every edge case: `q` not separable; `q` reducible (then every factor has degree
  ≤ 8, so `root_Pconstructible_le_eight` applies; check it); `y = 0`; `φ(z)` having repeated
  eigenvalues (the charpoly argument does not need distinct eigenvalues, but confirm it); the
  sign handling for negative `y` in `powerLaw_root_Pconstructible`.
* **Is `φ` really allowed to be a polynomial in `z = ψ(β)`?** The resolvent is the charpoly of the
  element `φ(ψ(x))` of `A`, which is what matters for step 3. Write this out properly.

### 3.2 Indefiniteness: the mathematical core
Let `r₂` be the number of conjugate pairs of `q` (so `r₂ ≥ 1`), and `r₁ = 9 − 2r₂`.
* **`r₂ ≥ 3`, with `ψ = x`.** Claimed automatic: `B` on `A` has signature `(r₁+r₂, r₂)`, degree-≤6
  polynomials form a codimension-2 subspace (losing at most 2 negative directions), and the
  `Tr = 0` complement of `1` removes only a positive direction. Prove it.
* **`r₂ = 2` and `r₂ = 1`.** Seed numerics (`archived files/nonic-scripts/00-seed-signature.py`,
  float signatures at random root configurations; rerun it first):

  | pattern | indefinite with `ψ = x` |
  |---|---|
  | `r₂ = 0` | 0/2000 |
  | `r₂ = 1` | 1987/2000 |
  | `r₂ = 2` | 2000/2000 |
  | `r₂ = 3, 4` | 2000/2000 |

  In a longer search, `ψ = x` failed 2 times for `r₂ = 2` and 200 times for `r₂ = 1`. A random small
  integer `ψ` fixed both `r₂ = 2` failures and 194 of the 200 `r₂ = 1` failures; the other 6 were
  not fixed within the search budget. **Prove** that for every real root configuration with
  `r₂ ≥ 1` some rational `ψ` of degree ≤ 6 makes `Q|V_ψ` indefinite.

  A suggested mechanism, not a proof: choose `ψ` so that `ψ(r₁) ≈ ψ(r₂)` and `ψ(r₃) ≈ ψ(r₄)` for
  four of the real roots. Then take `φ` vanishing at the remaining distinct real `z`-values with
  `φ(ψ(z_c)) = iM` at a complex root. The near-collisions let 7 coefficients satisfy 9 value
  constraints approximately, which gives `Q ≈ −2M² < 0`. A positive vector is easy. Rational `ψ`
  is fine by density, since indefiniteness is an open condition. Make this rigorous, or find a
  cleaner argument. Watch for: `z` must still generate the field; `ψ(z_c)` must stay away from the
  real `z`-values; the case where every real root is needed.
* Look for a single choice of `ψ` that works for **all** configurations with a given `r₂`. If there
  isn't one, a case split is fine.

### 3.3 When `z` does not generate
If `ℚ(z) ⊊ ℚ(β)`, the root field has a proper subfield, so its degree over ℚ is 3. Then `β` has
degree 3 over a cubic field. Show `β ∈ K` directly (a tower of two steps of degree ≤ 6), or show
`ψ` can always be chosen to generate. Settle which.

### 3.4 Meyer's theorem
* State it exactly (Serre, *A Course in Arithmetic*, Ch. IV; it follows from Hasse–Minkowski). Confirm
  it covers **degenerate** forms: a nonzero radical vector is already a zero.
* Give an **effective** route to an actual rational zero, for the worked example: Simon's algorithm,
  `qfsolve`-style reduction, or LLL. Wolfram may manage it with `FindInstance` over the integers for
  small coefficients.

### 3.5 Worked examples (the evidence standard for a positive claim)
For **three** rational nonics:
* one with Galois group `S₉` and `r₂ = 1` (7 real roots, the hardest non-totally-real case);
* one with `r₂ = 2`;
* one with `r₂ = 4`.

For each: an explicit rational `ψ` and `φ` with `Tr φ(z) = Tr φ(z)² = 0` checked **exactly**
[symbolic]; the resolvent `Y⁹ − p(Y)` with `p` rational of degree ≤ 6, checked exactly; and a
30-digit numerical check that the chain in §1 recovers `β`. Galois evidence (cycle types mod primes;
Wolfram 15 has no `GaloisGroup`) that the example's roots have degree 9 and are not in any earlier
class.

### 3.6 Scope
* Does the same argument give anything for **degree 10** over ℚ? That needs `p₃ = 0` too: a rational
  zero of a quadric and a cubic form together, for which Meyer has no analogue in this many
  variables. Give the precise obstruction. Check whether Tschirnhaus maps of degree ≤ 6 in two
  different generators, or other engines, help.
* Does Meyer-style isotropy over ℚ improve **any other** existing result where a rational
  Tschirnhaus map was the blocker? For example: octics over ℚ without the shift; mixed engines that
  need a rational graph.
* **Novelty.** Search the literature: "Tschirnhaus transformation" together with "Hasse–Minkowski",
  "rational Bring–Jerrard", or "Meyer's theorem"; Serre's and Kraft–Procesi's work on
  trace forms; the Hilbert-13 literature over ℚ. Give URLs.

### 3.7 Lean feasibility (report only; not a proof deliverable)
* Does Mathlib have Hasse–Minkowski, Meyer's theorem, or isotropy of rational quadratic forms?
  Search with `lean_local_search` / `lean_loogle` / `lean_leansearch`. Do not scan the Mathlib tree.
* If not: estimate the cost of formalizing it for rank ≥ 5, or of a special-case proof for the
  trace form. Could the local conditions for this particular form be checked directly?
* Draft the final Lean statement in the scratch file, marked **stated (sorry)**, together with a
  lemma list that reuses `DegreeSeven.lean`'s trace-form infrastructure (`companion7`, Hermite
  matrix, Newton identities). How much of that file generalizes from 7 to 9?

## 4. Deliverable

`NOTES-nonic-meyer.md`, containing:
1. a plain summary of at most 12 lines: proved, reduced to a named gap, or refuted;
2. the full proof (or proof with explicitly marked gaps) of Conjecture N;
3. the indefiniteness theorem for each `r₂`;
4. the three worked examples;
5. the scope and novelty findings;
6. the Lean feasibility report;
7. Side discoveries and Leads.

If the proof is complete, also write `nonicpaper.tex` in the style of `septicpaper_revised.tex`.
**Do not claim Conjecture N on numerics alone.**
