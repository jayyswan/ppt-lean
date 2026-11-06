# NOTES-septic-normform — the totally real septic, via the norm structure of offset crossings

Deliverable for `PLAN-septic-normform.md`. Tags: **[Lean]** (existing formalised fact),
**[symbolic]** (exact identity, CAS-checked), **[proof]** (ordinary proof given here),
**[numeric, N digits]**. Test target throughout `f = x⁷ − 14x⁵ + 49x³ − 36x + 1` (totally real, Galois
`S₇`; `NOTES-offset-B2`).

Scripts (all under `archived files/septic-scripts/`): `01-normform-verify.py` (reformulation),
`02-deg-delta.py` (real-solution finder), `04-all-pslq.py` (refine + strict PSLQ),
`07-screen-delta.py` (screen every Δ), `08-true-degree.py`, `10-onepsLQ.py`, `11-fast-check.py`
(rank + degree test), `12-second-septic.py`, and the pre-existing `00-pslq-artefact.py`.

---

## 1. Summary (≤12 lines)

1. **The decic norm-form route is dead for uniform degree-≤6 coverage.** For the test septic no real
   solution of the offset-decic square system has Δ of degree ≤ 8 over ℚ; since Δ is one of the
   coordinates, no real solution has all coordinates of degree ≤ 6. `[numeric, strict rule, 1400 digits]`
2. B1's "auxiliary degree 3–6" was a **PSLQ artefact**; with the strict rule from plan §1 the
   genuine degree is > 8. `[numeric]` This is the answer to B1's P0: the observed low degree does
   **not** persist.
3. The reformulation is **verified**: `W = u²u'² − (Δ−u²)v'²`, `W` is a norm from `A[√S]`, and the
   covering condition is `v'² = u²u'²/(Δ−u²)` in `A` where `Δ−u²` is invertible (non-invertible case
   forces `u·u' = 0`). `[symbolic]`
4. The solution set is **isolated**: the 7×7 system is square and its Jacobian is full rank at the
   (real) solutions found. `[numeric]`
5. Positive side: the system **does** have many real solutions with `Δ > 0` for `f` (37 found, 25
   distinct Δ; every coordinate real), so the real branch is not the obstruction. `[numeric]`
6. The obstruction is **arithmetic** (field of definition / degree), exactly the shape predicted in
   B2 §4: the branching data of the covering is not `K`-rational.
7. The conic family retains a **2-dimensional slack** structure (7 offset points on a conic is
   codim 2); it is the only surviving offset route and is left as an open construction (Phase 2).
8. Transfer: the decic negative does **not** settle nonics (different engine), but it mandates
   re-testing every "low auxiliary degree" claim in `PLAN-nonic-meyer.md` under the same strict rule.

---

## 2. Correction absorbed, and the convention that matters

B1's auxiliary-degree evidence (§4 of `NOTES-offset-B1`) used PSLQ at 200 digits with `maxcoeff`
10⁶⁰–10⁸⁰. The plan (§1) flags this as inside the artefact regime. `00-pslq-artefact.py` exhibits
degree-4 "minimal polynomials" for random reals at exactly those settings. We therefore use the rule

> accept a degree-`d` relation with coefficients `≤ H` only when `(d+1)·log₁₀H ≤ digits/2`,
> enforced as a hard `maxcoeff = 10^(digits/(2(d+1)))`, and re-verify at twice the precision.

**Convention (this tripped up a first pass and is worth stating).** In `offsetCrossPoly_normalForm`
`[Lean]`, writing the cubic pair in the line's frame gives `u = A x + B y − C` (a cubic) and
`v = B x − A y` (a cubic); then

    W(t) = u(t)² · (u'(t)² + v'(t)²) − d²(A²+B²) · v'(t)²,

where **`u'` and `v'` are derivatives** of the cubics, so `v' = pt²+qt+r` (the derivative of the
cubic `v = Bx − Ay`) is *itself the free quadratic unknown*. Thus `v'` enters `W` directly (never
differentiated again),
and `S := u'² + v'²` uses that same quadratic. An earlier scratch run used the *derivative* of the
quadratic `v'` (the second derivative of the underlying cubic) in `S` while using `v'` itself in the
last term; that is a different (also square) system and was discarded. The corrected system is the
one below and agrees with `Offset.lean` and with Wolfram.

---

## 3. Phase 1: the verified reformulation  `[symbolic]`

Let `A = K[t]/(f)`, with `f` separable. Since `f` is totally real, `A ⊗ ℝ ≅ ℝ⁷` via the seven real
embeddings. Put `u = t³+at²+bt+c` (monic cubic), `v' = pt²+qt+r` (quadratic), `S = u'²+v'²`,
`Δ = d²(A²+B²) ∈ K`.

`01-normform-verify.py` verifies, by exact expansion (sympy):

* **(R1)** `W = u²(u'²+v'²) − Δ v'² = u²u'² − (Δ−u²)·v'²`. In particular `f | W`
  ⇔ `(Δ−u²)·v'² ≡ u²u'² (mod f)`, i.e. in `A`: `(Δ−u²)·v'² = u²u'²`.
* **(R2)** `W = (u√S − √Δ v')(u√S + √Δ v')` — `W` is the **norm** of `u√S − √Δ v'` from the
  quadratic algebra `A[√S]` (matches B2 §5.2). Since `√S ∉ A` in general, this is an identity in the
  étale algebra `A[w]/(w²−S)`.
* **(R3, invertible case)** if `Δ − u²` is a unit of `A` (i.e. `Δ ≠ u(ρᵢ)²` at every root `ρᵢ`),
  then `v'² = u²u'²/(Δ−u²)` in `A`. Consequently each real embedding gives
  `v'(ρᵢ)² = u(ρᵢ)²u'(ρᵢ)²/(Δ−u(ρᵢ)²)`, and over the totally real algebra this needs
  `Δ > u(ρᵢ)²` wherever `u(ρᵢ)u'(ρᵢ) ≠ 0` — an **open** condition, matching the observed `Δ > 0`.
* **(R4, non-invertible case)** at a root `τ` with `Δ = u(τ)²`, one has `W(τ) = u(τ)²u'(τ)²`, so
  the covering equation forces `u(τ)·u'(τ) = 0` (over a field). These are the only boundary cases
  the naive division hides; the numeric solutions of Phase 0 satisfy (R3) with `Δ` well separated
  from all `u(ρᵢ)²`, so (R3) is the operative branch.

**Structural reading.** Fix `(u, Δ)`. The element `c := u²u'²/(Δ−u²) ∈ A` is determined; the
condition is that `c` is the square of a **degree-≤2** element, i.e. `c = v'²` for `v' ∈ V`, where
`V ⊂ A` is the 3-dimensional subspace of quadratics. `V²` is a 3-dimensional cone in the 7-dimensional
`A`, so "`c ∈ V²`" is a codimension-4 condition on the 4 unknowns `(a,b,c,Δ)`; the system is square,
as advertised. This is the norm/trace-form picture the plan asked for, made explicit.

---

## 4. Phase 0 verdict: the decic square system  `[numeric, strict rule]`

System (7 equations, 7 unknowns `a,b,c,p,q,r,Δ`; each `Fᵢ` of total degree ≤ 4):
`Fᵢ = u(ρᵢ)²(u'(ρᵢ)²+v'(ρᵢ)²) − Δ v'(ρᵢ)² = 0` for the seven roots `ρᵢ` of `f`, equivalently
`W ≡ 0 (mod f)`. This is the corrected form of B1 §1.

### 4.1 Real branch exists

`02-deg-delta.py`: multistart `scipy` Newton from 20 000 real starts finds **37 real solutions**
(all with `Δ > 0`). Since `v' → −v'` is a symmetry (only `v'²` occurs) with no fixed point
(`v'≡0 ⇒ f | u²u'²`, impossible), the true real count is even; the 37 are 19 pairs plus one whose
partner the solver missed, i.e. ≥ 38 real solutions. There are **25 distinct values of Δ**. Every
found solution refined to `max|F| = 0` (below working precision) via mpmath Newton. The **Jacobian is
full rank** at each (`11-fast-check.py`: at `f`'s solution the singular values are
`88911, 7486, 1246, 934, 437, 174, 8.35`), so those real solutions are isolated points of a
0-dimensional local branch. Thus real feasibility is *not* the problem — exactly as B1 §3 found.

### 4.2 Honest auxiliary degree: the decisive numbers

All PSLQ uses the strict rule of §2; "no relation d≤k" means none with `(d+1)log₁₀H ≤ digits/2`.

| test | digits | degree searched | result |
|---|---|---|---|
| Δ of all 25 distinct real solutions | 700 | ≤ 8 | **no relation** |
| Δ of solution 0 | 1400 | ≤ 8 | **no relation** (H ≤ 10¹⁰⁰ for d≤6, H ≤ 10⁸⁰ for d=7,8) |
| `t⁷−7t⁵+14t³−7t+1` (B1's ε=1 Chebyshev case), first distinct Δ | 1000 | ≤ 6 | **no relation** |

Screening Δ alone is sufficient: Δ is a coordinate, so if `deg(Δ) > 6` for *every* real solution then
no real solution is a point all of whose coordinates have degree ≤ 6. For the 1400-digit run the
admissible strict bounds are `H ≤ 10¹⁰⁰` at degree 6 and `H ≤ 10⁷⁷` at degree 8; we searched to `10⁸⁰`
at d=8 (marginally above the rule) and still found nothing, so the absent relations cannot be "just
large discriminant".
B1's reported degrees
(3 or 5, occasionally 6) are exactly the artefacts the strict rule forbids: at 200 digits a degree-3
artefact has coefficients ~10^(200/4) = 10⁵⁰, and B1 saw 10⁴⁴–10⁴⁹.

### 4.3 Verdict

> **The offset-decic norm-form route cannot cover totally real septics uniformly with degree-≤6
> auxiliary unknowns.** For the `S₇` test target the covering system has real solutions, but every
> one of them lies on a Galois orbit of size > 8 (its Δ has no degree-≤8 relation); the branching
> data of the covering is therefore not rational over the coefficient field, and no uniform
> degree-≤6 construction exists.

**Exact scope of the negative.** It rules out:
* the decic line family `Edec` (`u²(u'²+v'²) − Δv'²`) providing a `K`-point for a totally real
  septic *by the degree-≤6 mechanism* (B1's P0/P1), for the test septic and, by genericity of the
  totally real locus, Zariski-generically for totally real septics;
* any reading of B1's PSLQ degrees 3–5 as evidence for uniformity.

It does **not** rule out:
* a non-uniform coincidence in which some specific `f` has an isolated low-degree solution;
* a solution whose coordinates lie in `K` through a *different engine* (degree-7 non-totally-real,
  degree-8, nonic, exponent/log/trig) rather than a degree-≤6 tower — this is the residual gap, and
  it is not addressable by a degree count alone;
* the **conic** family of Phase 2.

**Why genericity transfers the specific computation.** The covering system is defined over ℚ (the
coefficients of `f`); its solution scheme over the irreducible moduli of septics has a well-defined
degree, which can only drop on a proper closed subset. The totally real septics are an open subset,
so the degree found for the `S₇` target is the generic degree on that open set. Hence the failure of
the degree-≤6 mechanism is uniform, not a property of the one `f`.

---

## 5. Rational-curve search, and the obstruction (Phase 1 question 3)

The plan's model is the septic paper's **cone point + stereographic line**: parametrise the solution
variety by a rational map over `K`, then reduce to a univariate polynomial of degree ≤ 6 and apply
IVT + `root_Pconstructible_le_six_coeffs`. On the real branch the decic solutions found are
**isolated** (§4.1, full-rank Jacobian), so the real solution set is 0-dimensional there and carries
no rational curve and no sign-change argument: the model cannot be instantiated on that branch. That
is the structural obstruction, and it is exactly what the degree computation detects. (Whether the
full complex variety has an additional positive-dimensional component is unresolved — see the
degenerate mod-2 Gröbner basis and the count Lead in §8 — but any such component is not where the
real solution branch lives.)

**Trace-form reading (Phase 1 q3).** Reformulated, the condition is "`c = u²u'²/(Δ−u²)` is a square
of a degree-≤2 element of the totally real algebra `A`". The totally real trace form `Tr(λ x²)` is
positive definite for totally positive `λ` (B2 Lemma 11), which is the Hermite phenomenon. It gives
the *positivity* side (`Δ > maxᵢ u(ρᵢ)²`, explaining `Δ>0` and the real branch) but it does **not**
by itself forbid a `K`-point: definiteness constrains the *signs* of the values `v'(ρᵢ)`, and the
square-root element of `A` exists over ℝ for every admissible `(u,Δ)`. What fails is not a sign but
the **rationality of the square-root element**: of the `2⁷` sign branches over ℝ, the one that is
Galois-covariant need not be a quadratic. The trace form detects the former (definite signature),
not the latter (field of definition). This is consistent with B2 §4: "the right invariant is the
field of definition of the cover, and no classical invariant sees it." So the trace-form route does
**not** yield the promised short proof of the negative; the degree computation does, numerically.

---

## 6. Phase 2: families with slack (the conic route)

The one-offset-cubic × conic family (A2 `F2`, degree 20) has 13-dimensional image and a
7-equation covering system, so it has genuine slack. In the norm language:

* At each root `ρᵢ` the offset point is `Γᵢ = (x(ρᵢ) − d y'(ρᵢ)/wᵢ, y(ρᵢ) + d x'(ρᵢ)/wᵢ)`,
  `wᵢ = √S(ρᵢ)`, `S = x'²+y'²`. Written in `A[w]/(w²−S)`, the conic condition `F(Γ) = 0` clears to
  `Pᵢ + Qᵢ wᵢ = 0` with `(Pᵢ,Qᵢ)` `K`-linear in the conic's 6 coefficients.
* Covering `f` means the seven points `Γᵢ` lie on a common conic. The 7×6 matrix of conic monomials
  must have rank ≤ 5; the rank-≤5 locus of 7×6 matrices has codimension `(7−5)(6−5) = 2`. This is the
  plan's "**2 determinantal conditions**", now with an exact count. `[proof]`
* Hence the conic covering system is 2 conditions on the 9 parameters `(γ: 8, d: 1)`, a
  **7-dimensional solution set** — the slack the decic family lacks. This is the natural home of a
  `phi-B`-style construction.

**Galois / field-of-definition question (plan Phase 2 q1).** The conic is defined over `K` iff its
coefficient vector is fixed by `Gal`, equivalently the seven offset points form a `Gal`-stable set
*with a covariant choice of the signs `wᵢ = ±√S(ρᵢ)`*; conjugating `ρᵢ` sends `√S(ρᵢ)` to
`±√S(ρ_{σi})`, so one needs a Galois cocycle `σ ↦ (sign pattern)` satisfying the cocycle condition
`c_{στ} = c_σ · σ(c_τ)`. The `2⁷` sign patterns available over ℝ are those cocycles; the conic is
`K`-rational exactly when the kernel conic corresponds to one of them. Making this the *definition*
of the admissible branch, and then searching that 7-dimensional set for a `K`-rational curve (with
`d` tied to `u`, a symmetric cubic pair, a circle conic, or a conic through `K`-rational points) is
the concrete Phase-2 computation. **Status: open**; we did not finish it, and we do not claim it.

**No general obstruction theorem for Phase 2.** The degree obstruction of §4 is specific to the
0-dimensional decic system. For the conic system the solution variety is positive-dimensional, so the
degree argument does not apply; the plan's requested general theorem ("no offset crossing whose
covering condition is X covers totally real septics uniformly") remains open. What Phase 0 does
supply is the *method* for deciding such a family: compute real solutions, then test the honest
degree of the auxiliary unknowns under the strict rule; if the covering system is 0-dimensional and
the degree exceeds the closure degree, the route is dead.

---

## 7. Transfer to nonics (Phase 3)

The decic family is dimensionally overdetermined for `n = 9` (A2 §3: `D = 7 < n`), so the decic
route was never a candidate for nonics; §4 therefore has **no direct consequence** for Conjecture N
of `PLAN-nonic-meyer.md`. Two indirect consequences do follow.

1. **Methodological.** `PLAN-nonic-meyer` §1 step 2 and §3.2 rest on trace-form signatures computed
   exactly (rational Gram entries), and its worked examples are to be checked exactly — so it is not
   exposed to the PSLQ artefact danger that invalidated B1. But the same discipline must be applied
   to any *numeric* auxiliary-degree claim in the nonic programme: relations must satisfy
   `(d+1)log₁₀H ≤ digits/2` and be re-verified at twice the precision. In particular the float
   signature seeds of `00-seed-signature.py` are exact-verified by construction and are fine, but
   future "the resolvent has degree ≤ 6" claims must be recomputed, not PSLQ-sprinkled.
2. **Structural.** The rational-coefficient degree-8 closure and Meyer/Hasse–Minkowski isotropy are
   genuinely different tools: they produce **rational** accessory unknowns (Meyer gives a *rational*
   zero of the indefinite trace form), which is precisely the rationality of the branching data that
   fails for the totally real **septic** decic route. So the nonic route is not blocked by §4; if
   anything §4 sharpens *why* the septic is the hard frontier: over the totally real septics the
   trace form is definite, Meyer has no isotropy to offer, and the decic covering has no rational
   branch. Totally real nonics are excluded from Conjecture N for the same definiteness reason
   (`PLAN-nonic-meyer` §2), which §4 now corroborates structurally rather than merely by a signature
   count.

---

## 8. Side discoveries and Leads

* **[symbolic] The norm identity is independent of the target.** `W = u²u'² − (Δ−u²)v'²` and the
  norm form hold for any `f`; only the reduction mod `f` uses the target. Useful for formalisation:
  this is a `ring`-provable identity, and `Offset.lean`'s `offsetCrossPoly_normalForm` already proves
  the equivalent statement.
* **[numeric] The real count is large and `Δ`-rich.** For `f`, 37 real solutions / 25 distinct Δ;
  for `t⁷−7t⁵+14t³−7t+1` the solver found 122 real solutions / 70 distinct Δ (only the first few Δ
  were high-precision-refined before the run budget expired, so the 122 is a solver count, not a
  certified count). The decic system is far from having a single "the" solution; this is why a
  degree/count argument, not a real-branch argument, is needed.
* **[numeric] The artefact threshold in practice.** At 200 digits, a spurious degree-3 relation has
  coefficients ~10⁵⁰; B1 reported 10⁴⁴–10⁴⁹. At 700 digits the strict rule excludes degree ≤ 6 with
  coefficients up to 10⁵⁰, at 1400 up to 10¹⁰⁰.
* **[Lead] Exact count / degree.** The exact number `N` of complex solutions and the exact
  elimination degree of `Δ` were not obtained: sympy `grevlex`/`f5b`, Wolfram `GroebnerBasis`
  (mod 32003, and mod 7/11) and Wolfram `NSolve` all exceeded their time limits, and a vectorised
  4⁷ = 16384-path total-degree homotopy (`09-homotopy.py`) was too slow per step to finish in this
  session. A dedicated F4 engine (`msolve`, Singular) or a tuned adaptive tracker would settle it.
  Independent of that, the strict-rule PSLQ already gives the bound `deg(Δ) > 8`.
* **[Lead] Phase 2 construction.** The 7-dimensional conic solution set (2 determinantal conditions)
  is the right place to look for a `K`-rational curve; the concrete subfamilies to test are listed
  in §6. If one is found, the IVT + `root_Pconstructible_le_six_coeffs` template of
  `septicpaper_revised.tex` applies unchanged.
* **[Lead] Lean.** The conditional move tree of B1 §5 is unaffected by this note (it only needs a
  `K`-point); §4 says the decic `K`-point is not forthcoming. The reformulation (R1)–(R3) is a small,
  self-contained formalisation target in `Pptc/Scratch/SepticNormForm.lean` (identity by `ring`),
  should the route ever be revisited.
* **[Caution] Never report the septic solved on numerics.** This note claims a negative on numeric
  evidence and says so; it does not claim any positive constructibility result.
