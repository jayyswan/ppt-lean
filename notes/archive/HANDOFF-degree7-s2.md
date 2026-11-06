# HANDOFF: degree-7, s >= 2 (issue #6)

## Goal
Real root of a monic septic `q : ℝ[X]` with P-constructible coefficients and at least two
conjugate pairs of non-real roots is P-constructible.  Route (Bring–Jerrard/Tschirnhaus):
produce a P-constructible `φ` (deg ≤ 6) with the resolvent `charpoly (aeval (companion7 q) φ)`
having vanishing `X^6, X^5, X^4` coefficients; then `resolvent_powerLaw` +
`eval_root_Pconstructible` finish.  (`s = 0, 1` are handled by the existing
`root_Pconstructible_le_seven`/one-pair reductions.)

## Status (up to date)
All of the following compile via `lake env lean Pptc/<file>.lean` (exit 0):
`ScratchD`, `ScratchE`, `ScratchF`, `ScratchG`, `ScratchC`, `ScratchC2`, `ScratchAB`,
`ScratchH`, `ScratchK`.

- `Pptc/ScratchF.lean` — companion charpoly (`companion7_charpoly`,
  `aeval_companion7_self`), cyclicity argument.
- `Pptc/ScratchG.lean` — spectral identity (`companion7'_trace_pow`,
  `companion7'_trace_aeval`, `companion7_trace_aeval`), eigenvector basis,
  `exists_linear_eval`, `conjQuad`, `conjQuad_dvd_of_root`.
- `Pptc/ScratchE.lean` — `hermiteForm`, `hermiteForm_eq_trace_sq`,
  `trace_aeval_polyOfVec_sq`, `traceForm_neg_of_poly`, `polyOfVec`.
- `Pptc/ScratchD.lean` — `companion7`, `charpoly_coeff_Pconstructible`,
  `resolvent_powerLaw`, `companion7_charpoly_aeval_isRoot`.
- `Pptc/ScratchC.lean` — binary cubes / isotropic plane (`form22`, `planeVec`),
  `exists_diagonal_isotropic_vectors`.
- `Pptc/ScratchAB.lean` — `cubic_exists_root`, `binary_cubic_zero`.
- `Pptc/ScratchH.lean` (**NEW, completed**) — the Bring–Jerrard directions.
  - `conjQuad_map_eq_prod`, `eval_map_conj`.
  - `exists_poly_value_at_root`: for monic separable septic `q`, non-real root `z` of
    `qC = q.map (algebraMap ℝ ℂ)`, and any `c : ℂ`, there is `f : ℝ[X]` with
    `f.natDegree ≤ 6`, `fC(z) = c`, `fC(z̄) = conj c`, and `fC(x) = 0` at every other root.
  - `algebraMap_trace_eq_of_value`, `trace_aeval_eq_zero_of_vanishes`,
    `exists_neg_trace`, `exists_pos_trace`.
  - `exists_neg_pair` / `exists_pos_pair`: for two roots from distinct conjugate pairs there
    are `f, g` with `trace = 0, 0`, `trace(N²) = -2, -2`, `trace(N f * N g) = 0`
    (resp. `trace = 2, 2`, `trace(N²) = 2, 2`, cross `0`).
- `Pptc/ScratchC2.lean` (**MODIFIED**) — the diagonalization now returns an *invertible*
  congruence matrix: `exists_diag_congruence` and `exists_diag_congruence_fintype_aux` have the
  extra conjunct `U.det ≠ 0`. New helpers `hyperInv`, `hyper_mul_hyperInv`,
  `hyper_det_ne_zero`. (`exists_diagonal_isotropic_vectors` already existed here/ScratchC.)
- `Pptc/ScratchK.lean` (**NEW, completed**) — elementary Sylvester inertia.
  - `qform A x := x ⬝ᵥ (A *ᵥ x)`, `bilin A x y := x ⬝ᵥ (A *ᵥ y)`.
  - `qform_congr : qform (Uᵀ * A * U) y = qform A (U *ᵥ y)`.
  - `qform_diag : qform D z = ∑ i, D i i * z i^2` for diagonal `D`.
  - `two_neg_of_negDef` / `two_pos_of_posDef`: negative (positive) definiteness along two
    explicit combinations forces two negative (positive) diagonal entries.
  - `two_neg_diag_of_pair` / `two_pos_diag_of_pair`: the congruence version.  Given
    `Uᵀ * A * U = D`, `U.det ≠ 0`, `D` diagonal, and
    `∀ a b, (a≠0 ∨ b≠0) → qform A (a • v1 + b • v2) < 0` (resp. `> 0`), conclude `D` has two
    negative (positive) diagonal entries (with distinct indices).

## Remaining (in order)
1. **Instantiate the direction signs (bridge H+K).**  Define
   `H : Matrix (Fin 7) (Fin 7) ℝ := fun i j => Matrix.trace (M ^ (i.val + j.val))` with
   `M = companion7 q` (entries P-constructible via `traceH_Pconstructible`), `s i := trace (M^i)`,
   and the Schur-complement form `H' i j := H i j - (1/7) * s i * s j`.  Then
   `qform H' x = hermiteForm q x - (1/7) * (p1 x)^2` where `p1 x = ∑ s i * x i
   = trace (aeval M (polyOfVec x))`, and `{p1 x = 0} = e0^⊥` for `e0` the constant polynomial.
   - From `exists_neg_pair` (ScratchH) get `f, g`, set `v1 i := f.coeff i.val`,
     `v2 i := g.coeff i.val`.  Prove `p1 (a•v1 + b•v2) = 0` and
     `qform H (a•v1 + b•v2) = trace ((a Nf + b Ng)^2) = -2 (a² + b²)`, using
     `hermiteForm_eq_trace_sq`, `polyOfVec (fun i => f.coeff i.val) = f`, and linearity of
     `aeval`.  Hence the `two_neg_diag_of_pair` hypothesis for `H'`.
   - From `exists_pos_pair` get `f, g` with `trace = 2`; set `g₁ := f - C (2/7)`,
     `g₂ := g - C (2/7)`, coefficient vectors `w1, w2`.  Then `p1 wᵢ = 0`,
     `qform H (a•w1+b•w2) = (2/7) * (5 a² - 4 a b + 5 b²) > 0`.  Hence the
     `two_pos_diag_of_pair` hypothesis.
2. **Diagonalize and extract the isotropic plane (Step 3 assembly).**
   `exists_diag_congruence H' hsym hP` gives `U, D` with `U.det ≠ 0`, `D` diagonal.
   Apply the two immediately preceding sign results to get `∃ i j` negative and
   `∃ i j` positive diagonal entries of `D`.  Feed them to
   `exists_diagonal_isotropic_vectors (fun i => D i i)` to get P-constructible `v, w`.
   Map to coefficient vectors `cv := P *ᵥ (U *ᵥ v)`, `cw := P *ᵥ (U *ᵥ w)` where
   `P = 1 - (1/7) • (fun i j => s i * (H *ᵥ e0) j)`-style orthogonal projection onto `e0^⊥`
   (equivalently `P = 1 - (1/7) • e0 ⊗ (H e0)`; entries P-constructible; `P` self-adjoint).
   Then `qform H cv = qform H cw = bilin H cv cw = 0` and `p1 cv = p1 cw = 0`.
   The restriction of `p3` to `span{cv, cw}` is a binary cubic; `binary_cubic_zero`
   (ScratchAB) on `A := Tr(N_cv^3)`, `B := 3 Tr(N_cv^2 N_cw)`, `C := 3 Tr(N_cv N_cw^2)`,
   `D := Tr(N_cw^3)` gives P-constructible `s, t` with a zero, and
   `φ := polyOfVec (s • cv + t • cw)` has `p1 = p2 = p3 = 0`.
   (`p2 = hermiteForm`, `p3 = trace of cube`; all coefficients P-constructible.)
3. **Newton (Step 4).**  `Matrix.trace_eq_neg_charpoly_coeff` gives `coeff 6 = -trace`.
   For `coeff 5, 4` the identities
   `coeff 5 = (trace² - trace(N²))/2`,
   `coeff 4 = -(trace³ - 3 trace * trace(N²) + 2 trace(N³))/6`
   are **not** in Mathlib for general `n`.  Recommended route:
   - extend the eigenbasis result in `ScratchG` to
     `(aeval (companion7' q) φ).charpoly = ∏_{z ∈ q.roots} (X - C ((φ).eval z))`
     (in the eigenbasis the matrix is `diagonal (fun z => φ.eval z)`; use
     `Matrix.charpoly_diagonal` and `LinearMap.charpoly`/`Matrix.toLin'`), then
   - over `ℂ`, `Multiset.prod_X_sub_X_eq_sum_esymm`
     (`Mathlib.RingTheory.Polynomial.Vieta`) writes the product's coefficients as
     `Multiset.esymm`, and the MvPolynomial Newton identities
     (`MvPolynomial.mul_esymm_eq_sum`, `MvPolynomial.psum_eq_mul_esymm_sub_sum`,
     `MvPolynomial.aeval_esymm_eq_multiset_esymm`) evaluated on the roots give
     `e1 = 0`, `e2 = 0`, `e3 = 0` from the three zero power sums.
   - Closed alternative for `Fin 7`: `Matrix.charpoly_coeff_eq_sum_minors` plus the
     principal-minor/trace identities (combinatorial, longer).
4. **Final (Step 5).**  `resolvent_powerLaw` (ScratchD) turns `hkill` + `q.eval β = 0` into
   `φ.eval β ^ 7 = cubicVal …`, and `root_Pconstructible_of_powerLaw` / `eval_root_Pconstructible`
   (DegreeSeven) recover `β`.  Need the main theorem statement (monic septic, P-constructible
   coefficients, ≥ 2 distinct conjugate pairs); separability is required by the spectral identity
   in ScratchG, so either assume it or handle repeated roots separately.

## Environment
`lake env lean Pptc/ScratchX.lean` (run from `pptc/`). `lake`, `lean`, `rg` and `git` are
on the bash PATH via the `lake-build-guard` plugin's `shell.env` hook, so no manual
`$env:PATH = "C:\Program Files\Git\cmd;..."` prefix is needed. Never `lake build` the
whole project (OOM). 100-char lines. `rg -n` works but do NOT use `-r` (it is the replace
flag and mangles matches). The lean-lsp MCP tools are the fast loop; `lean_local_search`
needs `rg` visible to the MCP server, so if it errors with "ripgrep was not found", fall
back to `lean_leansearch`/`lean_loogle`/`mathlib_search`.

---

# Review pass (Claude, 2026-09-12): assessment + insights for s = 1 and s = 0

Scope of this pass: read `Pptc/DegreeSeven.lean`, all nine Scratch files (statement level,
plus the proofs of `ScratchAB`, `ScratchC`, the tail of `ScratchC2`, and the sextic engine in
`Basic.lean`), and this handoff. No Lean was edited. Symbolic claims marked **[verified]**
were checked in a CAS; the rest are derivations done by hand and should be re-checked before
being turned into Lean statements.

## 0. Verdict

The `s >= 2` programme is **sound and close to done**. I re-derived every numeric constant in
"Remaining, step 1" and they are right. The remaining work is assembly, not mathematics, with
three concrete defects listed in section 1.

The `s = 1` and `s = 0` extensions are a different story, and the important content of this
review is that **they are not "the same argument, harder"**:

* `s = 0` (totally real septic) is **provably out of reach of Bring-Jerrard**, not merely hard.
  Not only can the top three coefficients of the resolvent not be killed -- the top *two*
  cannot. See 2.1. Do not spend agent time on it in this frame.
* `s = 1` is solvable at the value level (that is what `DegreeSeven.lean` part 2 records), but
  the structure that makes it solvable is **logically equivalent to already having solved the
  problem**. Section 3 makes that precise. The existing prose says the two halves "do not
  meet"; the reason they do not meet is that they are the same statement.
* Both blocked cases have the same escape hatch, and it is not in the Tschirnhaus direction at
  all: **enlarge the curve-intersection engine**. Section 4 gives a specific, verified, and (by
  the standards of this file) cheap new engine that reaches degree 9 and whose admissibility
  condition has *no definiteness obstruction* -- so it is satisfiable at `s = 0`, unlike the
  present one. This is the single highest-value lead in this review.

## 1. `s >= 2`: three defects to fix before assembly

**(a) The projection matrix in step 2 is written wrong.** The handoff says

> `P = 1 - (1/7) • (fun i j => s i * (H *ᵥ e0) j)`-style orthogonal projection

but `(H *ᵥ e0) j = s j`, so that formula is `1 - (1/7) • (s ⊗ s)`, which is not idempotent and
is not a projection. The correct map is the one the *next* parenthetical gets right,
`P = 1 - (1/7) • e0 ⊗ (H *ᵥ e0)`, i.e.

```
P i j = (if i = j then 1 else 0) - (1/7) * (e0 i) * (s j)      -- e0 = (1,0,0,0,0,0,0)
P x   = x - (p1 x / 7) • e0
```

With that `P`, both facts you need hold and are one-line `ring` computations once
`p1 x = ∑ s i * x i`, `s 0 = 7` and `qform H x = p2 x` are in place:

```
p1 (P x)            = p1 x - (p1 x / 7) * 7                    = 0
qform H (P x)       = p2 x - 2 (p1 x/7)(p1 x) + (p1 x/7)^2 * 7 = p2 x - (p1 x)^2/7 = qform H' x
bilin H (P x) (P y) = bilin H' x y                               (same computation, polarised)
```

**(b) `cv`, `cw` independent is a real gap, and it has a short proof.** `φ` must be
nonconstant for `eval_root_Pconstructible`, so you need `s • cv + t • cw ≠ 0`, and `P` has a
one-dimensional kernel `ℝ e0` (because `H'` is singular: `H' *ᵥ e0 = 0`). The proof:

* `D` is diagonal, so `ker D = span {e i | D i i = 0}`.
* `H' *ᵥ e0 = 0` and `Uᵀ H' U = D` give `D *ᵥ (U⁻¹ *ᵥ e0) = 0`, so `U⁻¹ *ᵥ e0 ∈ ker D` and is
  therefore supported on the zero-diagonal indices.
* `exists_diagonal_isotropic_vectors` builds `v` supported on `{p1, n1}` and `w` on
  `{p2, n2}`, all four of which have `D i i ≠ 0`, with `v p1 = √(-lam n1 / lam p1) > 0` and
  `w p2 > 0`.
* So `α (U *ᵥ v) + β (U *ᵥ w) = γ • e0` forces `α = β = γ = 0` by reading the `p1` and `p2`
  coordinates. Hence `cv, cw` are independent and `s • cv + t • cw ≠ 0` whenever `(s,t) ≠ 0`,
  which `binary_cubic_zero` already delivers.

**Cheaper alternative, and I would take it:** skip `H'` and the radical entirely. Since
`s 0 = trace (M^0) = 7 ≠ 0`, the six vectors `b j := e j - (s j / 7) • e0` for `j = 1..6` are a
P-constructible basis of `{p1 = 0}`. Form the `6 × 6` Gram matrix `G j k := bilin H (b j) (b k)`
(entries P-constructible by `traceH_Pconstructible`), diagonalise *that*, and push the
isotropic pair forward along the injective map `ℝ⁶ → ℝ⁷`. `G` is nondegenerate of signature
`(4,2)` for `s = 2` and `(3,3)` for `s = 3`, there is no kernel to dodge, independence is free,
and `two_neg_diag_of_pair` / `two_pos_diag_of_pair` apply verbatim. It also removes the need
for `H'` and for the `P` matrix altogether.

**(c) Separability is not an extra hypothesis -- it is free, and worth a two-line lemma.**
Step 4 says "either assume it or handle repeated roots separately". Handle it, cheaply: if a
monic septic `q` has a repeated root then its radical `q / gcd(q, q')` has degree `≤ 6`, has
exactly the same real roots, and has P-constructible coefficients (the Euclidean algorithm uses
only field operations on coefficients). So `root_Pconstructible_le_six_coeffs` closes the
non-separable case outright, and the main theorem may assume `q.Separable` with no loss. The
only Lean work is "gcd of two polynomials with P-constructible coefficients has P-constructible
coefficients", which is a clean standalone lemma (induct on the Euclidean algorithm, or go via
`Polynomial.modByMonic` after normalising leading coefficients).

**Numerics I re-derived and confirm.** For `exists_neg_pair` with value `i` at each of two
distinct pairs, `trace = 0` and `trace (N_f * N_g) = ∑_roots f g = 0` (disjoint support), so
`qform H (a•v1 + b•v2) = -2 (a² + b²) < 0`. For `exists_pos_pair` with value `1` and
`g₁ = f - C (2/7)`: `trace = 2 - 2 = 0`, `trace (N_{g₁}²) = 2 - 8/7 + 4/7 = 10/7`,
`trace (N_{g₁} N_{g₂}) = 0 - 4/7 - 4/7 + 4/7 = -4/7`, hence
`qform H = (1/7)(10a² - 8ab + 10b²) = (2/7)(5a² - 4ab + 5b²)`, positive definite (discriminant
`16 - 100 < 0`). Both match the handoff exactly.

**Step 3 (Newton) is over-engineered.** You do not need the `MvPolynomial` Newton identities.
Once `ScratchG` is extended to
`charpoly (aeval (companion7' q) φ) = ∏_{z ∈ roots} (X - φ.eval z)`, enumerate the root
multiset as a `Fin 7 → ℂ` tuple (legitimate: `card = 7`) and prove `e₁ = e₂ = e₃ = 0` from
`p₁ = p₂ = p₃ = 0` by `ring` on the explicit seven-variable expansions of `e₁ = p₁`,
`2e₂ = p₁² - p₂`, `6e₃ = p₁³ - 3p₁p₂ + 2p₃`. Seven variables is well within `ring`'s comfort.
Keep `Multiset.prod_X_sub_C_coeff` only for the Vieta step.

## 2. Two hard facts that redirect `s = 1` and `s = 0`

### 2.1 `s = 0`: Bring-Jerrard is impossible, and so is killing even two coefficients

Let `q` be separable with seven **real** roots `x₁..x₇`, and `φ` any real polynomial of degree
`≤ 6`. Then

```
p₂(φ) = ∑ᵢ φ(xᵢ)² ≥ 0,  with equality iff φ(xᵢ) = 0 for all i
                        iff q ∣ φ  iff φ = 0   (deg φ ≤ 6 < 7).
```

So `p₂(φ) = 0` forces `φ = 0`. Consequences:

* there is **no** degree-`≤ 6` real Tschirnhaus map killing the `y⁶` and `y⁵` coefficients of
  the resolvent, let alone `y⁶, y⁵, y⁴`;
* the only reduction available to a totally real septic is the ordinary depression `p₁ = 0`,
  which leaves `y⁷ = (quintic in y)` -- nowhere near the `y⁷ = (cubic in y)` the engine wants.

This is a two-line Lean theorem and belongs in `DegreeSeven.lean` next to
`lightCone_cubic_no_projective_zero`, for exactly the same reason that one is there: it stops
an agent from grinding on an impossible sub-goal. Suggested shape:

```lean
theorem totallyReal_no_tschirnhaus {q φ : ℝ[X]} (hq : q.Monic) (hdeg : q.natDegree = 7)
    (hsplit : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hsep : q.Separable) (hφ : φ.natDegree ≤ 6)
    (h : Matrix.trace (aeval (companion7 q) φ ^ 2) = 0) : φ = 0
```

### 2.2 `s` is a Tschirnhaus invariant, so there is no bootstrapping

`s` is half the negative index of the trace form of the **ℝ-algebra** `A = ℝ[X]/(q)`, and an
invertible Tschirnhaus map does not change `A` -- it changes the presentation, not the algebra.
Concretely: real roots map to real values and a conjugate pair maps to a conjugate pair, so
`(r, s)` is preserved, and `s` can only *drop* (if `φ` collapses a pair onto the reals), never
rise. In particular the two tempting moves both fail: "apply a preliminary Tschirnhaus to
manufacture a second conjugate pair" is impossible; and "pass to `q · (X² + 1)`, which has
`s + 1` pairs" does change the algebra, but the extra trace contributions are exactly the ones
you then have to cancel again, and cancelling them returns you to the original `(r+s-1, s)`
form.

### 2.3 `s = 1` is *equivalent* to splitting off the real quadratic factor

`s = 1` means `r = 5`: five real roots and one conjugate pair `a ± b i`. Write `q = g · q₅` with
`g = X² - 2aX + (a² + b²)` and `q₅` the totally real quintic. Then:

* if `g` has P-constructible coefficients then so does `q₅`, and every real root of `q` is a
  root of the **quintic** `q₅`, hence P-constructible by `root_Pconstructible_le_six_coeffs`
  with nothing else needed;
* conversely, if one real root is P-constructible then all five are
  (`root_Pconstructible_of_other_root`, already proved), so `∏ (X - xᵢ)` is P-constructible and
  therefore so is `g = q / ∏ (X - xᵢ)`.

So: **`s = 1` holds iff `a` and `b` are P-constructible, iff the non-real root is a
P-constructible point of the plane.** This is a strictly better goal statement than the
cone/cubic one -- it is one square root away from a two-dimensional target instead of a point
on a four-dimensional light cone -- and it is the form in which any future idea (resolvents,
spectral projectors, Sturm/subresultant data, transcendental methods) should be tested.

## 3. Why `DegreeSeven.lean` part 2 cannot be "carried into `φ`'s coordinates": it is circular

That file says the value-level solution is robust but "not visibly P-constructible". The
obstruction is sharper than that, and naming it should stop the agents attacking it head-on.

Let `V = {p₁ = 0} ⊂ ℝ⁷` (dimension 6), `Q = p₂|V` of signature `(5,1)`, `C = p₃|V`. Complex
conjugation on the `ℂ` factor of `A ≅ ℝ⁵ × ℂ` is an **ℝ-algebra automorphism `σ` of `A`**,
hence preserves every trace form, hence preserves `Q` and `C`. Its fixed space meets `V` in a
5-dimensional `V₊` on which `Q` is positive definite, and its `(-1)`-eigenspace is a single
`Q`-negative line `ℝe` -- so `σ|V` is precisely the reflection in the hyperplane `e^⊥`, an
element of `O(5,1)`. Writing `v = x + β e` with `x ∈ V₊`:

* `σ`-invariance of the cubic `C` says `C(x - βe) = C(x + βe)`, i.e. `C` is **even in `β`**:
  `C(x + βe) = C₃(x) + β² C₁(x)` -- no `β³` term, no `β · (quadratic)` term;
* `Q(x + βe) = Q₊(x) - λβ²`, so on the cone `β² = Q₊(x)/λ` and
  `C|cone = C₃(x) + Q₊(x) C₁(x) / λ =: G(x)`, an **odd cubic form on `V₊ ≅ ℝ⁵`**.

That is exactly `septicOnePairCubic`. **[verified]** In the value model `x = (u, a)`, `β = b`,
one gets `C = ∑uᵢ³ + 2a³ - 6ab²` and `Q = ∑uᵢ² + 2a² - 2b²`, and eliminating gives
`∑uᵢ³ + S³/2 + (3/2) S T` -- the file's cubic, on the nose. So part 2 is a shadow of `σ`.

Now the circularity. Knowing `e` (up to scale) means knowing the line `ℝ j` with `j = i · e_pair`
in `A`; then `j² = -e_pair` recovers the idempotent `e_pair` of the `ℂ` factor; `e_pair`
recovers the quadratic factor `g`; and by 2.3 that *is* the theorem. So:

> The only known reason `p₃` vanishes somewhere on the `(5,1)` light cone is the reflection
> symmetry `σ`, and producing `σ` P-constructibly is equivalent to the goal.

Any `s = 1` proof must therefore find a zero of `C` on the cone **without** using `σ`. That is
a genuine constraint on proof strategy, and it is what section 4 is for.

## 4. The lead: a second curve-intersection engine, reaching degree 9

This is the part I would put an agent on next.

### 4.1 What the present engine is, and why it caps the problem at three conditions

`powerLaw_cubic_root_Pconstructible` intersects `power_law y = x⁷` with a **cubic Bézier graph**
(`cubicGraph`, arbitrary P-constructible cubic coefficients). Bézier is cubic, so the reachable
normal form is `y⁷ = (cubic in y)` -- three coefficients of the resolvent must be killed, which
is what forces `p₁ = p₂ = p₃ = 0` and hence the whole signature story.

`root_Pconstructible_le_six_coeffs` uses a *different* engine: a cubic Bézier
`Γ(t) = (a(t), b(t))` crossed with a curve `Δ ⊆ {F = 0}` where `F` is the **parabola**
`A + B² + a₃B`. Since `deg F = 2` and `Γ` has parameter-degree 3, `F(Γ(t))` has degree
`2 · 3 = 6` -- that is where "sextic" comes from. The crossing gives one coordinate
`y₀ = b(β)` P-constructibly, and `β` is recovered from the cubic `b(t) - y₀`.

**The generalisation is immediate: replace the parabola by a cubic.** `Δ = {(c(y), y)}` for a
P-constructible cubic `c` is already constructible -- it is a `cubicPairArc` with `x`-part `c`
and `y`-part the identity, the same constructor the parabola uses. Take `F(A,B) = A - c(B)`.
Then `F(Γ(t)) = a(t) - c(b(t))` has degree `3 · 3 = 9`, and recovery of `β` from `y₀ = b(β)` is
the same cubic solve. So:

> **Proposed engine (degree 9).** If `a, b, c : ℝ[X]` all have degree `≤ 3` and P-constructible
> coefficients, `b` is genuinely cubic, and `β : ℝ` satisfies `a.eval β = c.eval (b.eval β)`,
> then `β` is P-constructible.

The Lean proof is the body of `root_Pconstructible_le_six_coeffs` (`Basic.lean` around lines
1290-1355) with the parabola swapped for a cubic graph and the degree bookkeeping changed from
6 to 9. This is the cheapest new capability in sight, and it is worth building **whether or not**
the rest of section 4 pans out, because it also subsumes the sextic case.

### 4.2 Exactly which degree-9 polynomials it reaches -- and the payoff

Normalise: `P` monic of degree 9, depressed (`p₈ = 0`) by a shift. Write
`P = b³ + ν b² + (cubic)` with `b = t³ + β₁ t + β₀` monic. Matching coefficients:

```
t⁷ : 3β₁ = p₇                 ->  β₁ = p₇/3            (rational in P)
t⁶ : 3β₀ + ν = p₆             ->  one-parameter family, β₀ free
t⁵ : 3β₁² = p₅                ->  CONDITION 1 :  p₅ = p₇²/3
t⁴ : 2β₁ (3β₀ + ν) = p₄       ->  CONDITION 2 :  p₄ = (2/3) p₆ p₇
```

**[verified]** in a CAS: the family satisfies both conditions identically, and conversely `b`
and `ν` are *rational* in `P`'s coefficients -- no auxiliary equation is solved to find them.
So the reachable set is exactly a **codimension-2** subvariety of monic degree-9 polynomials,
cut out by two explicit equations.

Translated into power sums of the nine roots, **[verified]**:

```
p₁ = 0 ,        p₄ = p₂² / 6 ,        p₅ = (5/18) · p₂ · p₃ .
```

**This is the point of the whole section.** Compare with the present engine's requirement
`p₁ = p₂ = p₃ = 0`. The new conditions

* are still homogeneous (degrees 1, 4, 5), so rescaling `φ` is free;
* **do not force `p₂ = 0`** -- and `p₂ = 0` is the single fact that killed `s = 0` in 2.1.

So the definiteness obstruction simply does not apply. Concretely, a totally real solution
exists: the nine values `(1,1,1,-1,-1,-1,0,0,0)` give `p₁..p₅ = (0,6,0,6,0)` and satisfy both
conditions **[verified]**; the corresponding polynomial is `(t³ - t)³`. Perturbing by a cubic
keeps all nine roots real and simple, so non-degenerate totally real members of the family
exist in abundance.

### 4.3 How to use it, and the one measurement that decides the lead

A septic is degree 7, the engine wants degree 9, and that gap is free: multiply by any real
quadratic `t² + u t + w` with P-constructible `u, w`. Extra real roots are harmless -- the
crossing is isolated to a window anyway, exactly as `exists_rat_isolating` already does. So the
target is:

> find P-constructible `u, w` (and, if needed, a Tschirnhaus `φ`) such that the depressed
> `q_φ(t) · (t² + u t + w)` satisfies `p₅ = p₇²/3` and `p₄ = (2/3) p₆ p₇`.

I measured the naive version (no Tschirnhaus, `u, w` only): two equations in two unknowns, and
**[verified]** the elimination has degree 10 for a generic septic -- 10 complex solutions, of
which 2-3 were real in the samples I ran (including the totally real `∏(t-k), k = 1..7`, where
the resultant happens to factor and `(u,w) = (-8, 9)` is *rational*). Degree 10 is above the
degree-6 ceiling, so the naive version does not close on its own.

That leaves exactly one question, and it is the measurement to ask the next agent for:

> **Add the Tschirnhaus freedom back.** With `φ` of degree `≤ 6` (7 parameters, 1 lost to
> scaling) plus `u, w`, there are 8 effective parameters against 2 equations -- a
> 6-dimensional solution variety, versus the 3 conditions and the *empty* solution set the old
> engine gives at `s = 0`. Does that system triangularise into steps of degree `≤ 6`
> (equivalently: is there a P-constructible point on the solution variety)?

The conditions are again power-sum conditions, so the machinery already built here applies:
`traceH_Pconstructible` gives `p_k` as P-constructible polynomial functions of `φ`'s
coefficients via `trace (M^k)`, and `exists_diag_congruence`,
`exists_diagonal_isotropic_vectors` and `binary_cubic_zero` are all reusable. What changes is
the *shape* of the variety: instead of `{quadric} ∩ {cubic}` it is
`{p₄ = p₂²/6} ∩ {p₅ = (5/18) p₂ p₃}` inside `{p₁ = 0}`, with `p₂` free -- and one may normalise
`p₂ = 6` by scaling (legitimate whenever `p₂ > 0`, which for `s = 0` is automatic), turning the
conditions into the much friendlier

```
p₁ = 0 ,   p₂ = 6 ,   p₄ = 6 ,   p₅ = (5/3) p₃ .
```

### 4.4 A smaller, independent idea for `s = 1` that also fits the budget

Even inside the old engine, the `s = 1` case is being under-spent. The `s >= 2` route only ever
solves a **cubic** (`binary_cubic_zero`), but `root_Pconstructible_le_six_coeffs` means a
**sextic** is equally free. A sextic's worth of budget buys a rational parametrisation of the
whole light cone:

* `exists_diag_congruence` plus square roots puts `Q` into standard Lorentzian form on
  `{p₁ = 0}` P-constructibly: coordinates `y₁..y₅, y₆` with `Q = ∑ y² - y₆²`;
* `exists_pos_quadratic_root` (already in `DegreeSeven.lean`) gives a P-constructible point
  `P₀` on the cone;
* stereographic projection from `P₀` parametrises the *entire* cone with **no further square
  root**: for a direction `d`, the second intersection of the line `P₀ + t d` with `{Q = 0}` is
  `v(d) = Q(d) · P₀ - 2 · B(P₀,d) · d`, quadratic in `d`. (No square root appears because the
  `t = 0` root is already known, so the other root is linear.)
* restrict `d` to a P-constructible line `d₀ + m d₁`. Then `C (v (d₀ + m d₁))` is a **binary
  sextic in `m` with P-constructible coefficients**, and any real root of it is P-constructible
  for free.

So `s = 1` reduces to: *exhibit one P-constructible line in `d`-space along which that sextic
changes sign.* And it does change sign somewhere: in the `σ`-coordinates of section 3, `C` on
the cone is the **odd** cubic `G`, so `Φ(d) := C (v d)` takes both signs on `ℝ⁵`. The remaining
gap is only that the known sign-change certificate is again `σ`. But this is a much smaller gap
than the current one -- it asks for a *sign*, not for a solution -- and it is the one place
where a semialgebraic/Sturm-style argument, or a `d₀, d₁` built from `M`'s own traces, might
land without `σ`. `Φ` is explicit: with `C = A₃(y) + A₂(y) y₆ + A₁(y) y₆² + A₀ y₆³` one has
`Φ = Q(d)³ · C(w(d))` away from `Q(d) = 0`, and `Φ(d) = -8 B(P₀,d)³ C(d)` on `{Q(d) = 0}`; the
latter is a closed form that costs nothing to evaluate at a P-constructible `d`, and two such
`d` of opposite sign finish the argument.

## 5. Suggested order of work

1. Fix 1(a), adopt 1(b)'s "explicit 6-dimensional basis" simplification, add 1(c). Finish
   `s >= 2`. It is the only branch that is actually close.
2. Add the two "stop" theorems to `DegreeSeven.lean`: 2.1 (`s = 0` impossible for
   Bring-Jerrard) and 2.3 (`s = 1` iff the quadratic factor is P-constructible). Cheap, and
   they permanently redirect effort. Add a prose paragraph recording section 3 (the `σ`
   circularity) next to the existing part 2 of that file, since that file currently invites
   exactly the attack that cannot work.
3. Build the degree-9 engine of 4.1 by editing a copy of the sextic proof. Independent of
   everything else and useful on its own.
4. Only then attack the 4.3 measurement, and 4.4 in parallel for `s = 1`.

## 6. Caveats on this review

* Section 1's numerics, section 3's identity, 4.2's two conditions, their power-sum form, the
  totally real witness, and the degree-10 elimination were all machine-checked. 2.1, 2.2, 2.3
  and 4.1 are short hand arguments I am confident in but which have not been formalised.
* 4.3 and 4.4 are **leads, not results**. In particular I have not checked that the 4.3 system
  triangularises, and 4.4's missing ingredient (a `σ`-free sign certificate) is exactly the
  kind of thing that has resisted so far. Neither should be written into a later handoff as
  settled.
* I did not run `lake` or the LSP in this pass, so nothing here is a claim about what currently
  compiles; the "Status" section above is taken at its word.

---

# Progress (opencode session, 2026-09-12): `s ≥ 2` assembly, `Pptc/ScratchS.lean`

`Pptc/ScratchS.lean` is **new and compiles cleanly** (`lake env lean Pptc/ScratchS.lean`,
exit 0). It imports `ScratchH`, `ScratchK`, `ScratchE`, `ScratchC`, `ScratchC2`, `ScratchAB`
(all now have `.olean`s — built one target at a time; `lake build Pptc.ScratchS` was not run).
It contains the *entire* algebraic core of the handoff's "Remaining step 1 and 2" in the
`b`-basis form recommended by review 1(b), plus proof infrastructure. **No `sorry`.**

Key declarations (namespace `Pconstructible`):

* Trace-form data: `Hmat q i j = trace (M^(i+j))`, `svec q i = trace (M^i)`,
  `p1vec q v = ∑ sᵢvᵢ`, `p3vec q v = trace ((aeval M (polyOfVec v))^3)`; lemmas
  `Hmat_Pconstructible`, `Hmat_symm`, `svec_zero : svec q 0 = 7`, `p1vec_eq_trace`,
  `qform_Hmat_eq_hermiteForm`.
* Bilinear-form calculus: `bilin_comm`, `bilin_add_left/right`, `bilin_smul_left/right`,
  `qform_eq_bilin`, `qform_add`, `qform_eq_sum`, `bilin_sum_left/right`, `bilin_eq_sum`,
  `bilin_Pconstructible`, `qform_smul`, `bilin_smul_smul`, `qform_smul_add`, `bilin_congr`,
  `bilin_diag`.
* The explicit basis of `{p1 = 0}`: `bvec q j = e_{j+1} - (s_{j+1}/7) e₀`, `coeff6`,
  `Lcomb q x = ∑ xⱼ • bⱼ`, `Gram q j k = bilin (Hmat q) (bvec q j) (bvec q k)`. Lemmas
  `p1vec_bvec`, `p1vec_Lcomb`, `Lcomb_coeff6` (every `p1vec`-zero vector is `Lcomb q (coeff6 v)`),
  `Lcomb_injective`, `Lcomb_smul_add`, `qform_Hmat_Lcomb : qform H (Lcomb x) = qform Gram x`,
  `bilin_Hmat_Lcomb`, `Gram_Pconstructible`, `Gram_symm`.
* Polynomial/vector bridge: `vecOf f = (f.coeff 0,…,f.coeff 6)`, `polyOfVec_vecOf`,
  `polyOfVec_smul_add` (general), `aeval_C_mul_smul`, `p1vec_vecOf`, `qform_Hmat_smul_add_vecOf`.
* Trace expansions: `trace_sq_smul_add`, `sq_smul_add`, `cube_add` (via `noncomm_ring`),
  `smul_pow`, `cube_smul_add`, `trace_cube_smul_add`, `trace_sq_sub_scalar`, `aeval_sub_C`,
  `aeval_sub_C_smul_add`.
* **Step 1 sign directions**: `neg_dir_of_pair` and `pos_dir_of_pair`. Both take the abstract
  two-pair data (`z,w` non-real roots in distinct conjugate classes) and produce `v1 v2 : Fin 6 → ℝ`
  with `qform (Gram q) (a•v1+b•v2) < 0` (resp. `> 0`) for all `(a,b) ≠ 0`. They use
  `exists_neg_pair` / `exists_pos_pair` from `ScratchH`, then `vecOf`/`coeff6`/`Lcomb_coeff6`,
  `trace_sq_smul_add` and `trace_sq_sub_scalar`. Note the witnesses need **not** be
  P-constructible — they are only used for the definiteness hypotheses of
  `two_neg_diag_of_pair` / `two_pos_diag_of_pair`, exactly as review 1(b) intended.

### What is left (mechanical, no new mathematics)

1. **Finish `ScratchS.exists_tschirnhaus_traces`** (not yet written). Using
   `neg_dir_of_pair`, `pos_dir_of_pair`, `exists_diag_congruence (Gram q)`, the two
   `two_*_diag_of_pair` lemmas and `exists_diagonal_isotropic_vectors (fun i => D i i)`, obtain
   `v w : Fin 6 → ℝ`; set `cv := Lcomb q (U *ᵥ v)`, `cw := Lcomb q (U *ᵥ w)`. Need
   (`hUD : Uᵀ * Gram q * U = D`, `hDdiag`):
   * `qform (Hmat q) cv = 0`: `qform_Hmat_Lcomb`, `← qform_congr`, `hUD`, `qform_diag`, `hqv`.
   * `qform (Hmat q) cw = 0`, `bilin (Hmat q) cv cw = 0` (same with `← bilin_congr`,
     `bilin_diag`, `hqw`, `hbvw`), `p1vec q cv = p1vec q cw = 0` (`p1vec_Lcomb`).
   * `¬ ∃ c, cw = c • cv`: `Lcomb_injective` + `mulVec_eq_zero_of_det_ne_zero` from `hUdet`
     (helper not yet written; use `nonsing_inv_mul` as in `ScratchC2`).
   * `binary_cubic_zero (p3vec q cv) (3*trace (Ncv^2*Ncw)) (3*trace (Ncv*Ncw^2)) (p3vec q cw)`
     (all P-constructible: `aeval_entries_Pconstructible`, `matrix_pow_entries_Pconstructible`,
     `polyOfVec_coeff_Pconstructible`, `trace_pow_Pconstructible`,
     `trace_mul_Pconstructible`) gives `s,t`; set `φ := polyOfVec (s • cv + t • cw)`.
   * `φ` has P-constructible coeffs (`polyOfVec_coeff_Pconstructible`), `natDegree ≤ 6`
     (`polyOfVec_natDegree_le`), and the three traces vanish: use `p1vec_smul_add`
     (`p1vec` linearity, via `p1vec_eq_trace` + `aeval_polyOfVec_smul_add`), `qform_smul_add`
     (`Hmat_symm`) and `trace_cube_smul_add` (with `aeval_polyOfVec_smul_add`). `φ ≠ 0` is not
     needed for the trace theorem.
   Helper lemmas still to add: `bilin_eq_sum`, `bilin_Hmat_Lcomb`, `polyOfVec_coeff_Pconstructible`,
   `polyOfVec_natDegree_le`, `polyOfVec_ne_zero`, `mulVec_eq_zero_of_det_ne_zero`,
   `Lcomb_sub`, `Lcomb_smul`, `mulVec_Pconstructible`, `Lcomb_Pconstructible`,
   `polyOfVec_smul_add`, `aeval_polyOfVec_smul_add`, `p1vec_smul_add`,
   `trace_pow_Pconstructible`, `trace_mul_Pconstructible`. (`polyOfVec_vecOf` already exists, so
   `vecOf`/`coeff6` are done.)

2. **Newton (step 3).** Still entirely open. A first subagent run produced only a research plan
   (recorded in its own failed session), no file. Recommended route (validated by name lookup
   only): general lemma `F.charpoly = ∏ᵢ (X - C (zᵢ))` for `F : Module.End K V` with an eigenbasis
   `b`, via `Matrix.charpoly_toLin'`, `LinearMap.charpoly_toMatrix`, `Matrix.charpoly_diagonal`;
   apply to `Matrix.toLin' (companion7' qC)` with the eigenbasis `idx := qC.roots.toFinset`
   (`companionVecC`) to get over `ℂ`
   `(aeval (companion7' qC) φC).charpoly = (qC.roots.map (fun z => X - C (φC.eval z))).prod`;
   transfer to `ℝ` via `Matrix.charpoly_map` + `(algebraMap ℝ ℂ).injective` and the `hmap` trick
   already in `ScratchG.companion7_trace_aeval`. Then Vieta
   (`Multiset.prod_X_add_C_coeff'` + `Multiset.esymm_neg`) writes coeffs of `X^(7-k)` as `(-1)^k e_k`,
   and `MvPolynomial.mul_esymm_eq_sum` / `MvPolynomial.aeval_esymm_eq_multiset_esymm` (k = 1,2,3)
   gives `e₁ = e₂ = e₃ = 0` from the three zero power sums. Deliverable:
   ```lean
   theorem charpoly_aeval_coeff_6_5_4_eq_zero {q φ : ℝ[X]} (hmon) (hnat) (hsep)
     (hp1 : trace (aeval (companion7 q) φ) = 0)
     (hp2 : trace ((aeval (companion7 q) φ)^2) = 0)
     (hp3 : trace ((aeval (companion7 q) φ)^3) = 0) :
     (aeval (companion7 q) φ).charpoly.coeff 6 = 0 ∧ … 5 … ∧ … 4 … ∧
   ```
   Put it in `Pptc/ScratchN.lean` (import `Pptc.ScratchG`). The review's §1 says the
   `MvPolynomial` route is over-engineered and suggests enumerating the seven roots and closing
   `e₁=p₁`, `2e₂=p₁²-p₂`, `6e₃=p₁³-3p₁p₂+2p₃` by `ring`; either is fine.

3. **Final assembly in `DegreeSeven.lean`.** Combine `exists_tschirnhaus_traces`,
   `charpoly_aeval_coeff_6_5_4_eq_zero` (as `hkill`), `resolvent_powerLaw` (ScratchD) and
   `root_Pconstructible_of_powerLaw` to get the real root `β`. Separability is required by the
   spectral identity, so either assume `q.Separable` (as above) or add review 1(c)'s radical
   reduction (divide by `gcd(q,q')`; still open, needs "gcd of P-constructible-coefficient
   polynomials has P-constructible coefficients").

### Environment notes hit this session
* `lake_check`/`lake env lean` work; the LSP `lean_diagnostic_messages` reports
  `diagnostics_unavailable` for `ScratchS.lean` because it wants oleans it will not build
  automatically — use `lake env lean Pptc/ScratchS.lean` (via `lake_check`) for the loop.
* `lean_local_search` and `lean_loogle` **do** work in this session.
* `lake build` with several targets at once is blocked by the guard; build one target per call.
* Build order used: `Pptc.ScratchH`, `Pptc.ScratchE`, `Pptc.ScratchK`, `Pptc.ScratchAB`,
  `Pptc.ScratchC`, `Pptc.ScratchC2` (each `lake build Pptc.X`).

---

# UPDATE (later in the same opencode session): steps 1–2 are DONE; only Newton + final assembly left

Both `Pptc/ScratchS.lean` and `Pptc/ScratchN.lean` compile cleanly (`lake env lean`, exit 0,
no `sorry`).

## Done in `ScratchS.lean`
* Everything listed in the "Progress" section above, **plus the main theorem**:
  ```lean
  theorem exists_tschirnhaus_traces (q : ℝ[X]) (hmon : q.Monic) (hnat : q.natDegree = 7)
      (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k)) {z w : ℂ}
      (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
      (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
      (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) :
      ∃ φ : ℝ[X], (∀ k, PConstructible (φ.coeff k)) ∧ φ.natDegree ≤ 6 ∧
        Matrix.trace (aeval (companion7 q) φ) = 0 ∧
        Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0 ∧
        Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0
  ```
  It is the full assembly described in "What is left" item 1: `neg_dir_of_pair`/`pos_dir_of_pair`
  → `exists_diag_congruence` → `two_neg_diag_of_pair`/`two_pos_diag_of_pair` →
  `exists_diagonal_isotropic_vectors` → `cv := Lcomb q (U *ᵥ v)`, `cw := …` → `binary_cubic_zero`
  → `φ := polyOfVec (s • cv + t • cw)`. The helper lemmas named in that item all exist now
  (`Lcomb_sub/smul`, `mulVec_Pconstructible`, `Lcomb_Pconstructible`,
  `mulVec_eq_zero_of_det_ne_zero`, `bilin_eq_sum`, `bilin_Hmat_Lcomb`, `coeff_finset_sum`,
  `polyOfVec_coeff_Pconstructible`, `polyOfVec_natDegree_le`, `polyOfVec_ne_zero`,
  `aeval_polyOfVec_smul_add`, `p1vec_smul_add`, `trace_pow_Pconstructible`,
  `trace_mul_Pconstructible`). Note `polyOfVec_smul_add` for *polynomials* already existed
  (`f - C c` shift); the vector version is `aeval_polyOfVec_smul_add`.

## Done in `ScratchN.lean` (created this session, 6 lemmas, clean)
* `charpoly_eq_prod_of_eigenbasis {K ι V} [Field K] [AddCommGroup V] [Module K V]
  [Module.Free K V] [Module.Finite K V] [Fintype ι] (F : Module.End K V) (b : Basis ι K V)
  (z : ι → K) (hv : ∀ i, F (b i) = z i • b i) : F.charpoly = ∏ i, (X - C (z i))`.
* `pow_mulVec_eigenvector_gen`, `aeval_mulVec_eigenvector_gen` (general-field copies of the
  ScratchD real lemmas).
* `companion7'_charpoly_aeval_eq_prod {K} [Field K] [IsAlgClosed K] (q φ : K[X]) (hmon) (hnat)
  (hsep) : (aeval (companion7' q) φ).charpoly = (q.roots.map (fun z => X - C (φ.eval z))).prod`.
* `companion7_aeval_map_eq (q φ : ℝ[X])` — the factored `hmap` from `ScratchG`.
* `companion7_trace_pow_aeval (q φ : ℝ[X]) (hmon) (hnat) (hsep) (k) :
  algebraMap ℝ ℂ (trace ((aeval (companion7 q) φ)^k)) = (qC.roots.map (fun z => (φC.eval z)^k)).sum`.

## Remaining: the Newton helper + `charpoly_aeval_coeff_6_5_4_eq_zero` (step 3), then final assembly

The one missing theorem (to go in `ScratchN.lean`):
```lean
theorem charpoly_aeval_coeff_6_5_4_eq_zero {q φ : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable)
    (hp1 : Matrix.trace (aeval (companion7 q) φ) = 0)
    (hp2 : Matrix.trace ((aeval (companion7 q) φ) ^ 2) = 0)
    (hp3 : Matrix.trace ((aeval (companion7 q) φ) ^ 3) = 0) :
    (aeval (companion7 q) φ).charpoly.coeff 6 = 0 ∧
    (aeval (companion7 q) φ).charpoly.coeff 5 = 0 ∧
    (aeval (companion7 q) φ).charpoly.coeff 4 = 0
```
Proof sketch (all surrounding lemmas are already proved in `ScratchN`):
1. Let `qC := q.map (algebraMap ℝ ℂ)`, `φC := φ.map (algebraMap ℝ ℂ)`,
   `y : Multiset ℂ := qC.roots.map (fun z => φC.eval z)`.
2. `hchar : ((aeval (companion7 q) φ).charpoly).map (algebraMap ℝ ℂ) = (y.map (X - C ·)).prod`
   from `← Matrix.charpoly_map`, `companion7_aeval_map_eq`, and
   `companion7'_charpoly_aeval_eq_prod qC φC …` (mind `Multiset.map_map`).
3. `hpsum : ∀ k, (y.map (·^k)).sum = 0` for k=1,2,3 from `companion7_trace_pow_aeval` and
   `hp1/hp2/hp3` (`algebraMap ℝ ℂ` of 0) and `Multiset.map_map`.
4. Newton: `y.esymm 1 = y.esymm 2 = y.esymm 3 = 0`. **This is the fiddly step.**
   The attempt that failed was evaluating `MvPolynomial.psum_eq_mul_esymm_sub_sum σ ℂ k` under
   `MvPolynomial.aeval f` with `σ := qC.roots.toFinset`, `f := φC.eval ∘ Subtype.val`:
   `simp` does not unfold `Finset.antidiagonal` (there is no `Finset.antidiagonal_one/two`), so
   the antidiagonal sums stayed symbolic. Two workable alternatives:
   * use `MvPolynomial.mul_esymm_eq_sum` instead, or evaluate `Finset.antidiagonal 1/2/3`
     explicitly with `Finset.antidiagonal_eq_map` / `Finset.mem_antidiagonal` + `Finset.sum_eq`
     on the two/three-element set, then `ring`;
   * or prove `e1 = p1`, `2 e2 = p1^2 - p2`, `6 e3 = p1^3 - 3 p1 p2 + 2 p3` for `Multiset`
     directly (by induction using `Multiset.powersetCard_cons`, or via `Finset.esymm_map_val`
     and `Finset.sum_powersetCard`), then specialise.
   To connect `y.esymm k` to the enumerated `σ`, use
   `MvPolynomial.aeval_esymm_eq_multiset_esymm` with `Finset.univ.val = (qC.roots.toFinset).attach.val`
   and `Finset.attach_val` + `Multiset.attach_map_val'`.
5. Coeffs: `Multiset.prod_X_sub_C_coeff y (k := 6/5/4) (by …) ` gives
   `coeff 6 = -y.esymm 1`, `coeff 5 = y.esymm 2`, `coeff 4 = -y.esymm 3`, using
   `y.card = 7` (`Multiset.card_map` + `(IsAlgClosed.splits qC).natDegree_eq_card_roots`).
6. Descend: `(algebraMap ℝ ℂ).injective`, with `Polynomial.coeff_map`.

## Final assembly (step 4, in `DegreeSeven.lean`)
Once `charpoly_aeval_coeff_6_5_4_eq_zero` exists, combine it (as `hkill`) with
`exists_tschirnhaus_traces` (from `ScratchS`), `resolvent_powerLaw` (`ScratchD`) and
`root_Pconstructible_of_powerLaw` (`DegreeSeven`) to prove: for monic separable septic `q` with
P-constructible coefficients and two non-real roots `z,w` in distinct conjugate classes, every
real root `β` of `q` is P-constructible. Separability is still assumed; review 1(c)'s radical
reduction for the non-separable case is not formalised.

## Suggested next action
One focused subagent (or session) on step 4 above, then a short final assembly. The mathematical
content of `s ≥ 2` is complete and machine-checked; what remains is Newton bookkeeping.

---

# DONE (opencode session, 2026-09-12): steps 1–4 complete; `s ≥ 2` is proved

All four remaining steps are finished, machine-checked, and `sorry`-free.

## Main theorem
`Pconstructible.root_Pconstructible_of_two_conjugate_pairs` in `Pptc/DegreeSeven.lean`:

```lean
theorem root_Pconstructible_of_two_conjugate_pairs {q : ℝ[X]} (hmon : q.Monic)
    (hnat : q.natDegree = 7) (hsep : q.Separable) (hq : ∀ k, PConstructible (q.coeff k))
    {z w : ℂ} (hz : (q.map (algebraMap ℝ ℂ)).eval z = 0) (hzim : z.im ≠ 0)
    (hw : (q.map (algebraMap ℝ ℂ)).eval w = 0) (hwim : w.im ≠ 0)
    (hzw : z ≠ w) (hzw' : z ≠ starRingEnd ℂ w) {β : ℝ} (hβ : q.eval β = 0) :
    PConstructible β
```

`lean_verify` reports only `propext`, `Classical.choice`, `Quot.sound`.  `lake build
Pptc.DegreeSeven` succeeds.  `Pptc/DegreeSeven.lean` now imports `ScratchD`, `ScratchN`,
`ScratchS` and has `open Polynomial Matrix`.

The only remaining hypothesis separating this from the literal issue statement is
`q.Separable` (review 1(c)); the radical reduction is still not formalised.  Everything else in
the `s ≥ 2` branch is unconditional.

## Step 3 (Newton) — `Pptc/ScratchN.lean`
Instead of `MvPolynomial` Newton identities, the low coefficients are obtained from the
elementary-symmetric/power-sum recurrence for `Multiset.esymm`:

* `esymm_zero`, `esymm_cons` (`(a ::ₘ s).esymm (n+1) = s.esymm (n+1) + a * s.esymm n`),
  `esymm_one_eq_sum`, `two_mul_esymm_two`, `three_mul_esymm_three`,
  `esymm_eq_zero_of_powerSums_zero`.
* `charpoly_aeval_coeff_6_5_4_eq_zero` (the step-3 deliverable): for monic separable septic `q`
  and `φ` with vanishing first three trace power sums at `companion7 q`, the resolvent
  `(aeval (companion7 q) φ).charpoly` has `coeff 6 = coeff 5 = coeff 4 = 0`.  It maps to `ℂ`,
  uses `companion7'_charpoly_aeval_eq_prod` (eigenbasis product), the multiplicity-safe Newton
  recurrence above, and `Multiset.prod_X_sub_C_coeff`.

## `Pptc/ScratchS.lean` (strengthened)
* New `smul_add_smul_eq_zero_of_not_parallel`: if `v ≠ 0` and `w` is not parallel to `v`, then
  `s • v + t • w = 0` forces `s = t = 0`.
* `exists_tschirnhaus_traces` now additionally returns `φ ≠ 0`.  Both `cv = Lcomb q (U *ᵥ v)`
  and `cw = Lcomb q (U *ᵥ w)` are nonzero (`Lcomb_injective` + `mulVec_eq_zero_of_det_ne_zero`),
  and `binary_cubic_zero`'s `(s,t) ≠ 0` then gives `ψ = s • cv + t • cw ≠ 0`, hence
  `polyOfVec ψ ≠ 0`.

## `Pptc/ScratchC2.lean` (strengthened)
`exists_diagonal_isotropic_vectors` now also returns `v ≠ 0 ∧ w ≠ 0` (its construction has
`v n1 = 1`, `w n2 = 1`).  One caller: `ScratchS`.

## Final assembly details
* `natDegree_ne_zero_of_trace_zero`: a nonzero `φ` with `trace (aeval (companion7 q) φ) = 0` is
  nonconstant (a nonzero constant `C c` would have trace `7 c`).  This supplies the
  `φ.natDegree ≠ 0` hypothesis of `root_Pconstructible_of_powerLaw`.
* The theorem then runs `exists_tschirnhaus_traces` → `charpoly_aeval_coeff_6_5_4_eq_zero` (as
  `hkill`) → `resolvent_powerLaw` → `root_Pconstructible_of_powerLaw`.

## What is *not* done (and why)
* **Separability.**  Removing `hsep` needs "the gcd/radical of P-constructible-coefficient
  polynomials has P-constructible coefficients".  Mathlib's `Polynomial.gcd` / `radical` is
  defined through `UniqueFactorizationMonoid`, not an explicit Euclidean recursion, so this
  needs a bespoke well-founded Euclidean-algorithm induction on `Polynomial.modByMonic`.  Not
  attempted here.
* **`s = 0`, `s = 1`.**  Still blocked exactly as review §2–§3 describes.
* **Review §4 leads** (degree-9 engine, `s = 1` cone parametrisation) are untouched.

## Review 2.1 — done (new file `Pptc/StopTotallyReal.lean`)
`Pconstructible.totallyReal_no_tschirnhaus` is proved (no `sorry`, axioms only
`propext`, `Classical.choice`, `Quot.sound`; `lake build Pptc.StopTotallyReal` succeeds):

```lean
theorem totallyReal_no_tschirnhaus {q φ : ℝ[X]} (hq : q.Monic) (hdeg : q.natDegree = 7)
    (hsplit : ∀ z : ℂ, (q.map (algebraMap ℝ ℂ)).IsRoot z → z.im = 0)
    (hsep : q.Separable) (hφ : φ.natDegree ≤ 6)
    (h : Matrix.trace (aeval (companion7 q) φ ^ 2) = 0) : φ = 0
```

i.e. for a totally real septic there is no degree-`≤ 6` Tschirnhaus map killing even the top
two resolvent coefficients.  Proof: `companion7_trace_pow_aeval` writes the trace as
`∑_{z ∈ qC.roots} (φC.eval z)^2`; every root is real, so this is a sum of nonnegative real
squares equal to `0`; hence `φ` vanishes at the `card = 7` distinct real roots, more than its
degree.  (The private helper `ofReal_multiset_sum` promotes a real multiset sum through the
`ℝ → ℂ` coercion.)  Note: the `: ℂ` annotation directly on `φ.eval r` mis-elaborates the
polynomial as `ℂ[X]`; write `((φ.eval r : ℝ) : ℂ)`.

Still open from the review: 1(c) separability/radical, 2.3 (`s = 1` iff the quadratic factor is
P-constructible), and the §4 engine leads.


## Environment
Build order used: `lake build Pptc.ScratchC2`, `lake build Pptc.ScratchS`,
`lake build Pptc.ScratchN`, `lake build Pptc.DegreeSeven` (each separately, one target at a
time).  `Pptc/ScratchNt.lean` was a transient scratch file and has been deleted.

---

# UPDATE (opencode session, 2026-09-12, later): separability removed, `s ≥ 2` unconditional;
# degree-9 engine; `s = 1` stop theorem

## 1. Separability is gone — the `s ≥ 2` theorem is unconditional

New file `Pptc/ScratchSep.lean` (imports `Pptc.Basic`), `sorry`-free, axioms only
`propext`, `Classical.choice`, `Quot.sound`:

* `coeff_C_Pconstructible`, `C_mul_coeff_Pconstructible`, `coeff_mul_Pconstructible`.
* `divModByMonic_coeff_Pconstructible`: if `d` is monic with P-constructible coefficients
  then `p /ₘ d` and `p %ₘ d` have P-constructible coefficients.  Proof: strong induction on
  `p.natDegree` plus `Polynomial.div_modByMonic_unique` (rather than unfolding
  `divModByMonicAux`), with the `d = 1` case split off because then `p - d * z` can be `0`
  without the degree dropping.
* `divByMonic_coeff_Pconstructible`, `modByMonic_coeff_Pconstructible` (the two projections).
* `gcd_coeff_Pconstructible`: `EuclideanDomain.gcd` of P-constructible-coefficient
  polynomials has P-constructible coefficients, via `EuclideanDomain.GCD.induction` and
  `Polynomial.mod_def` (`b % a = b %ₘ (a * C a.leadingCoeff⁻¹)`).
* `root_Pconstructible_of_nonSeparable`: for monic `q` with `q.natDegree ≤ 7`, P-constructible
  coefficients and `¬ q.Separable`, every real root of `q` is P-constructible.  Route:
  `d := gcd q q'` is nonconstant and of degree `≤ 6`; normalise to the monic
  `d₀ := d * C (leadingCoeff d)⁻¹` (same degree and roots, coeffs still constructible).  If
  `d₀.eval β = 0` apply the sextic engine to `d₀`, otherwise to the exact quotient `q /ₘ d₀`,
  whose degree is `≤ 6` because `d₀` is nonconstant.  (This sidesteps needing "radical has the
  same roots": whichever of `d₀`, `q /ₘ d₀` kills `β` is degree `≤ 6`.)

`Pptc/DegreeSeven.lean` now imports `ScratchSep`, and `root_Pconstructible_of_two_conjugate_pairs`
has **no `hsep`**: it cases on `q.Separable` and sends the non-separable branch through
`root_Pconstructible_of_nonSeparable`.  The `s ≥ 2` half of issue #6 is therefore unconditional,
which was the last gap in that branch.  `lake env lean Pptc/DegreeSeven.lean` is clean.

## 2. Degree-9 cubic-graph engine (review §4.1) — `Pptc/ScratchNine.lean`

```lean
theorem cubicGraph_cubic_cross_root_Pconstructible
    {a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ c₀ c₁ c₂ c₃ β : ℝ}
    (ha : ∀ k, PConstructible (match k with | 0 => a₀ | 1 => a₁ | 2 => a₂ | _ => a₃))
    (hb : ∀ k, ...) (hc : ∀ k, ...) (hb₃ : b₃ ≠ 0) (hc₃ : c₃ ≠ 0)
    (hroot : cubicVal a₀ a₁ a₂ a₃ β = cubicVal c₀ c₁ c₂ c₃ (cubicVal b₀ b₁ b₂ b₃ β)) :
    PConstructible β
```

It crosses the cubic pair `Γ t = (a t, b t)` with the cubic graph `Δ = {(c s, s)}`, so the
crossing polynomial `a t - c (b t)` has degree 9; the crossing yields `y₀ = b β`, and `β` is
then a root of the genuine cubic `b t - y₀`.  Caveat: `hc₃ : c₃ ≠ 0` is necessary — without it
the literal statement is false (`a = b = t³`, `c = s` makes `a β = c (b β)` for every real
`β`).  This engine is independent of the degree-7 route and is the capability the §4.3 lead
needs.  Axioms clean.

## 3. The `s = 1` stop theorem (review §2.3) — `Pptc/ScratchQuad.lean`

Both directions of "real roots constructible ↔ quadratic factor constructible", `sorry`-free
and axiom-clean:

* `roots_Pconstructible_of_quadratic_factor`: if `q = g * q5` with `g` monic and
  P-constructible, `q5 ≠ 0` of degree `≤ 6`, then every real root of `q5` is P-constructible
  (`q5 = q /ₘ g` via `ScratchSep`, then the sextic engine).  Actionable direction: finishing
  `s = 1` **reduces to** exhibiting `g = X² - 2aX + (a² + b²)` P-constructibly.
* `quadratic_factor_coeff_Pconstructible_of_real_roots`: conversely, if `q5` is monic with all
  complex roots real (`hsplit`) and every real root is P-constructible, then `g` has
  P-constructible coefficients.  So the `s = 1` target is exactly "make `g` P-constructible",
  as review §2.3/§3 asserted.

## 4. Status after this session

* **Issue #6, `s ≥ 2`:** done, unconditional.
* **Issue #6, `s = 1`:** still open; by §3 it is equivalent to making the quadratic factor
  P-constructible, and review §3 argues the only known zero of `p₃` on the `(5,1)` light cone
  comes from the conjugation symmetry `σ`, whose P-constructible production *is* the goal.
  The §2 engine and the §4.4 stereographic route both still need a `σ`-free sign certificate
  or a P-constructible point on the §4.3 solution variety.
* **`s = 0`:** `StopTotallyReal.totallyReal_no_tschirnhaus` remains the stop theorem.
* Review §4.3's central measurement (does the degree-9 system triangularise in degree ≤ 6?)
  remains untouched.

## 5. Environment notes

* Builds, one target per command: `lake build Pptc.ScratchSep` (40 s),
  `lake build Pptc.ScratchNine` (16 s), `lake build Pptc.ScratchQuad` (12 s; this also builds
  `Pptc.DegreeSeven`).
* `lake_check` clean on `ScratchSep`, `ScratchNine`, `ScratchQuad`, `DegreeSeven`.
* `ScratchSep` must be **built** (`lake build Pptc.ScratchSep`) before `DegreeSeven` can import
  it — `lake env lean` alone does not write the olean.
* `lean_verify` on `root_Pconstructible_of_nonSeparable`,
  `cubicGraph_cubic_cross_root_Pconstructible` and both `ScratchQuad` theorems reports only
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry`/`axiom` in any of the new files.

---

# §4.3 measurement (computational, same session): the direct degree-9 route does **not**
# triangularise in degree ≤ 6

The review's §4.3 asked whether the degree-9 lead yields a constructible solution.  Here is a
clean measurement of the *direct* cubic-cross analogue, done in a CAS (not Lean, flagged as
evidence): to use `cubicGraph_cubic_cross_root_Pconstructible` on a septic `q`, one needs
cubics `a, b, c` with `q ∣ (c∘b - a)`.  Normalise `b = X³ + pX² + rX + s` (monic is wlog:
`c(λ·b̃) = c'(b̃)` for a cubic `c'`).  Writing `c = α₀ + α₁Y + α₂Y² + α₃Y³`, the degree-`4,5,6`
coefficients of `c∘b mod q` must vanish; `α₀, α₁` do not contribute, so this is a `3 × 2`
linear system in `(α₂, α₃)` whose matrix has columns the degree-`6,5,4` parts of `b²` and
`b³ mod q`.  A nonzero `(α₂, α₃)` with `α₃ ≠ 0` (needed: `c` genuinely cubic) exists iff the
three `2 × 2` minors vanish — three polynomial equations in `(p, r, s)`.

Measured for two septics (one with a rational quadratic factor `X² + 1`, one generic):

```
q₁ = (X²+1)(X-1)(X-2)(X-3)(X-4)(X-5)
q₂ = X⁷ + 2X⁶ + 3X⁵ + 5X⁴ + 7X³ + 11X² + 13X + 17
```

In both cases the lex Gröbner basis of the three minors eliminates to a **degree-`10`
irreducible polynomial in `r`** (for `q₁`:
`259308 r¹⁰ - 24131520 r⁹ + 988864119 r⁸ - … + 6955175665488575`, irreducible over `ℚ`;
for `q₂` the same degree with `259308 r¹⁰ - 2063880 r⁹ + … + 46270`).  In `q₂` the auxiliary
variable `s` is free and `p` is linear in `r`, giving `{p, r}` finite of degree `10`.

So the *auxiliary* Tschirnhaus data of the direct cubic-cross route is a degree-`10`
algebraic number for generic septic coefficients — above the degree-`6` ceiling of
`root_Pconstructible_le_six_coeffs`, and beyond every tower of degree-≤6 steps (subject to a
Galois-group check not run here).  Caveat: it is **not** an impossibility proof, because the
`offset` engine (`Pptc/Offset.lean`) does reach some genuine degree-`10` numbers; but the
reachable degree-`10` family is a proper subfamily, and there is no reason to expect these
particular degree-`10` auxiliaries to lie in it.  Combined with the review's independent
degree-`10` elimination for the multiply-by-a-quadratic version, the §4.1/§4.3 degree-9 lead
should be regarded as **constructively dead in its naive/direct form**, not merely unmeasured.

This does not touch the `s ≥ 2` result, which uses a different mechanism (the isotropic plane
in the septic's own trace form) and is unconditional.
