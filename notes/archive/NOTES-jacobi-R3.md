# NOTES-jacobi-R3 — the composition route

Research task `PLAN-jacobi-R3-compositions.md`. No `.lean` file was created or edited.
All numerics use `mpmath`/`sympy`/`numpy` under Python 3.12
(`C:\Users\jason\AppData\Local\Programs\Python\Python312\python.exe`), scripts archived in
`archived files/jacobi-scripts/`. Every identity below is tagged **[N]** (verified
numerically, with the number of good digits) or **[P]** (proved symbolically / in Lean).
`mpmath.ellipfun(kind, u, m)` takes the **parameter** `m = k²`; this convention was
confirmed in `R3-01-basics.py`. All script paths are relative to the repo root.

**Verdict in one line.** The derivative test is correct and reduces every *fixed-parameter*,
*fixed-shape* composition to the single-curve route; no candidate composition formula for
`jacobiAm` survived numerical testing. The test does **not** close three loopholes —
parameter-dependent curves, multi-stage compositions, and its own transcendence input — and
those are ranked at the end. No breakthrough; no impossibility claim.

---

## 0. What was asked and what is delivered

The brief asks: (step 1) a precise derivative-test lemma with explicit hypotheses and a
proof; (step 2) each loophole either closed or turned into a tested candidate; (step 3)
partial facts on `u` for which `am` is known constructible; (step 4) this note with the
lemma, a loophole table with verdicts, candidates, and the open loopholes ranked.
Sections 2–6 do exactly that.

---

## 1. Conventions and the class of "drawable data"

Fix `c < 1`. Write

- `Δ_c(θ) = √(1 − c sin²θ)`, so `ellipticEIntegrand c θ = Δ_c(θ)`;
- `F_c(φ) = ∫₀^φ dθ/Δ_c(θ)` (first kind), `E_c(φ) = ∫₀^φ Δ_c(θ) dθ` (second kind);
- `am_c(u) = F_c^{-1}(u)` is `jacobiAm c u` (`Pptc/Jacobi.lean:173`);
- `s_γ(T) = arcLengthOf γ T₀ T = ∫_{T₀}^{T} speed γ` for a tracing `γ`;
- `speed γ = √(x'² + y'²)` (`Pptc/Defs.lean:68`).

For `T ≥ T₀` the function `s_γ` is `C¹` and increasing wherever `speed γ > 0`.

**Drawable data.** A *drawable speed* is a function `σ(T) = speed γ(T)` where `γ` traces a
piece of a `PConstructibleCurve` (`Pptc/Defs.lean`). Inspecting the constructors, `σ²` is
always an expression built from `T`, the point `γ(T)`, `sin`/`cos` of things, `2^{·}` of
things, `+ − × ÷`, and square roots; `offset` adds the factor
`(1 − d·(v×v′)/Q^{3/2})` of formula (F3) and stays in the same class. **No drawable speed
contains `F_c` or `am_c`**, provided the curve was built before the amplitude. That proviso
is the definitional-circularity loophole (L4, §6).

Call `𝒜` the **allowed class** of functions on a real interval: constants, the identity, and
closure under `+ − × ÷`, `√`, `sin, cos, tan, arcsin, arccos, arctan`, `2^{·}`, `log`, the
*forward* incomplete integrals `F_c, E_c, ellipticPiInc`, and the *inverse* `ellipticEAm_c`
(which is P-constructible for fixed constructible `c`, `Pptc/Jacobi.lean:602`). It does
**not** contain `am_c` or any inverse of `F_c` or of `ellipticPiInc`. This is the class from
which the functions `G`, `L` of a candidate composition may be drawn.

Throughout, subscripts like `T(u)` mean `T` evaluated at `u`; `T'` is `dT/du`.

---

## 2. The derivative test

### 2.1 The setup and the master identity

**Setup (S).** Let `I ⊆ ℝ` be a nondegenerate open interval and `J` an interval. Suppose

- **(S1)** `T : I → J` is `C¹` with `T'(u) ≠ 0` on `I`;
- **(S2)** `γ : J → ℝ²` is a `C¹` tracing of a piece of a P-constructible curve with
  `speed γ > 0`, and `L : I → ℝ` is `C¹` with
  `s_γ(T(u)) = L(u)` for `u ∈ I` (equivalently `T = s_γ^{-1}∘L` on `I`, where the inverse
  is taken on the range of `s_γ`);
- **(S3)** `G : J → ℝ` is `C¹` and `am_c(u) = G(T(u))` for `u ∈ I`.

(S2) says precisely that `T` is obtained by **one** application of the inverse of a drawable
arc length, which is the only inversion a construction has besides `ellipticEAm` (already
absorbed into `𝒜`). (S3) says the amplitude is read off the parameter `T` by a fixed
function.

**Lemma 1 (master identity). [P]** Under (S), with `φ := G(T)`:
1. `G'(T(u)) · T'(u) = Δ_c(G(T(u)))`;
2. `speed γ(T(u)) · T'(u) = L'(u)`;
3. hence
   `L'(u) = speed γ(T(u)) · Δ_c(G(T(u))) / G'(T(u))`.   **(MT)**
4. Writing `w := F_c(G(T))` for the new independent variable, `T = T(w)` is the inverse of
   `w ↦ F_c(G(T))`, so `G(T(w)) = am_c(w)` and `R(T) := speed γ(T) Δ_c(G(T))/G'(T)`
   satisfies
   `L'(w) = R(T(w))`.   **(MT′)**
   In particular here `w = u`, but the point of (MT′) is that the right side is the fixed
   function `R` composed with the *inverse of the elliptic integral* `F_c∘G`.

*Proof.* Since `am_c(u) = G(T(u))` and `F_c(am_c(u)) = u`

  `u = F_c(G(T(u)))`.   (★)

Differentiating (★): `1 = F_c'(G(T))·G'(T)·T' = (G'T')/Δ_c(G(T))`, which is 1. Then
`s_γ(T(u)) = L(u)` differentiated gives `speed γ(T)·T' = L'(u)`, which is 2. Dividing 2 by 1
(or substituting `T' = Δ_c(G)/G'`) gives (MT). For (MT′), `w=F_c(G(T))=u` by (★); invert
`T ↔ w` from `w = F_c(G(T))` (possible since `F_c` and `G` are locally invertible by (S1))
and note `G(T(w)) = F_c^{-1}(w) = am_c(w)`, so `w = u` and (MT′) is (MT) with `u` renamed. ∎

Note that (★) alone already says `u` is an elliptic integral of the angle `G(T)`. The whole
content of the test is what this forces on `L`.

### 2.2 The collapse when `L` is affine (rigorous)

**Lemma 2 (collapse to one curve). [P]** In the setup (S), if `L(v) = αv + β` then

  `s_γ(T) = α·F_c(G(T)) + β′` for a constant `β′`.

That is: the drawn curve `γ` has an arc length which is, up to an additive constant, a
constant multiple of an incomplete *first-kind* integral of the angle `G(T)`. This is
exactly the "single-curve route" of `PLAN-jacobi-00-overview.md` §1.

*Proof.* (MT) with `L'(u)=α` gives `speed γ(T) = α·G'(T)/Δ_c(G(T))`. Integrating from `T₀`
to `T`:

  `s_γ(T) − s_γ(T₀) = α∫_{T₀}^{T} G'(s)/Δ_c(G(s)) ds = α(F_c(G(T)) − F_c(G(T₀)))`. ∎

So the derivative test says: **a successful affine-`L` composition is equivalent to
exhibiting a drawable curve with first-kind arc length** — the object R1/R2 investigate.

### 2.3 The test (conditional)

**Lemma 3 (derivative test). [P, modulo the transcendence input (T3)]** Assume (S), that
`G` is locally invertible with `G^{-1} ∈ 𝒜`, that `L' ∈ 𝒜`, and

> **(T3)** *If `M ∈ 𝒜` and the composite `u ↦ M(am_c(u))` also lies in `𝒜`, then
> `M(am_c(·))` is constant.*

Then `L` is affine, and Lemma 2 applies.

*Proof.* By (MT′) and `G(T(w)) = am_c(w)`,

  `L'(w) = speed γ(G^{-1}(am_c(w))) · Δ_c(am_c(w)) / G'(G^{-1}(am_c(w))) = M(am_c(w))`,

where `M(φ) := speed γ(G^{-1}(φ))·Δ_c(φ)/G'(G^{-1}(φ))` lies in `𝒜` because `G^{-1} ∈ 𝒜`,
`speed γ` is drawable data, and `Δ_c` is elementary. By hypothesis `L' ∈ 𝒜` and equals
`M∘am_c`, so (T3) forces `M∘am_c` constant, i.e. `L'` constant. ∎

**Where it fails.** The proof consumes exactly one unproved input, **(T3)**, and one
structural assumption, that the curve and its parametrisation do not depend on `u`. Both are
real. §2.4 and §3 dissect them; §6 ranks them.

The classical fact behind (T3) is that `am_c` is not an elementary function: it is a
nonconstant elliptic (doubly periodic) function after continuing `sn` to `ℂ` (DLMF 22.2,
22.16), and nonconstant elliptic functions are not elementary. **(T3)** is the
*compositional* strengthening needed here, and the strengthening is nontrivial: an
elementary function can have a rank-two lattice of poles (e.g. `1/(sin z · sinh z)`), so the
naive "elementary functions have at most one period" argument does **not** establish (T3)
for composites `M∘am_c`; those composites are generally not periodic at all. We regard (T3)
as expected but **not proved here**. This is the single most important gap in the test.

### 2.4 The three failure modes, made explicit

**(F-i) Parameter dependence.** If the curve `C_{p(u)}` and its tracing depend on `u`
through a parameter `p = p(u)`, then `T = T(u,p(u))`, `s_{p(u)}(T) = L(u)`, and
differentiating gives the modified identity

  `speed_{p}(T)·(∂T/∂u) + (∂/∂p s_{p}(T))·p'(u) = L'(u)`,   **(MT-param)**

while (★) becomes `1 = (G_T·∂T/∂u + G_p·p')/Δ_c(G)`. The extra term `∂s/∂p` is where
**complete** integrals live (for an ellipse, `∂/∂b` of the arc length produces `K(c)`, `E(c)`
and the incomplete ones at the boundary). The test of §2.3 no longer applies: (MT-param) can
be solved for `L'` with a nonconstant right side that is *not* of the form `M(am_c(w))`.
This is loophole (L1), §6.

**(F-ii) Several inversions in sequence.** Suppose
`am_c = G(T₂)`, `T₂ = s_{C₂}^{-1}(L₂(T₁,u))`, `T₁ = s_{C₁}^{-1}(L₁(u))`. Expanding as in
§2.1 and eliminating `T₁` produces, instead of (MT),

  `L₂(T₁(F_c(G(T₂))), F_c(G(T₂))) = s_{C₂}(T₂)`,

and differentiating w.r.t. `T₂` gives the same shape as (MT) with `L'` replaced by the
*composite derivative*

  `H := ∂₁L₂·T₁' + ∂₂L₂`,

where `T₁' = L₁'(u)·Δ_c(G(T₂))/speed_{C₁}(T₁)`. So the test generalises: one applies (T3)
to `H` rather than `L'`, and provided no stage hides `F_c`/`am_c`, multi-stage collapses to
the same alternative. The residual loophole is a **nonlinear** `L₂` whose `u`-derivative
cancels against `∂₁L₂·T₁'`; we found no candidate (L2, §6). This "composite derivative"
replacement is the precise answer to the brief's request to say what the test does for a
sequence of inversions.

**(F-iii) The transcendence input (T3).** Already discussed. Note that when `G` involves
`ellipticEAm_{c'}`, the computation of `M` uses `E_{c'}`, and (T3) reduces to the assertion
that `E_{c'}(am_c(w))` is not in `𝒜` unless constant. §4.3 tests this: there is **no**
identity `E_{c'}(am_c) = A E_c(am_c) + B u + (algebraic)` for `c' ≠ c`. So the known ways to
build `am_c` from `E`-inversions all violate (T3), but (T3) in full is unproved.

---

## 3. Loophole table with verdicts

| # | Loophole | What the test says | Verdict |
|---|---|---|---|
| L0 | `L` affine | Then `s_γ = αF_c∘G + β` (Lemma 2): the **single-curve route**. | Not a loophole; it is the target of R1/R2 |
| L1 | Curve/parametrisation depends on `u` (parameter `p(u)`) | (MT) gains `∂s/∂p·p'`; complete integrals `K(c)`, `E(c)` enter; (T3) inapplicable | **Open — top candidate.** No formula found |
| L2 | Several inversions in sequence | Collapses to (T3) applied to composite derivative `H`; only a nonlinear `L₂` cancellation escapes | **Open but reduced.** No candidate |
| L3 | Mixed `E`/`F` at **different** moduli (Landen, Gauss, reciprocal) | `F` pulls back to `F` (holomorphic → holomorphic); `E` pulls back to `E + const·F` with nonzero `F`-coefficient, plus an algebraic boundary term | **Killed.** Inverting `E+const·F` is not available. Verified §4.2 |
| L4 | Mixed `E`/`F` at the **same** angle | `E_{c'}(am_c)` for `c'≠c` is a new elliptic integral, not a combination of `E_c(am_c)`, `u`, algebraic | **Killed** (§4.3). `c'=c` gives the epsilon (still not `𝒜`) |
| L5 | Third-kind `ellipticPiInc` | `Π` is forward-only (no inverse constructor). `Π(n=0)=F`, `Π(n=c)=(E−elementary)/(1−c)`, `Π(n=1)=F+elementary` (Lean) | **Killed as an inversion** (§4.4) |
| L6 | `ellipticEAm` (an allowed inverse) inside `G` or `L` | Using `EAm_c` needs `L = E_c(am_c)` = the epsilon, already containing `am_c`: circular. Other moduli need L4's identity | **Open but circular/generically killed** (§4.5) |
| L7 | Transcendental `G` (`log`, `2^T`, `EAm`) | Then `G'/Δ_c(G)` involves `sin(G)` or `Δ_c(G)` of a transcendental, not a drawable speed; reduces to the curve `w²=(1−h²)(1−ch²)`, `h=sin G`, in general not drawable | **Killed generically** |
| L8 | Algebraic `G` (`arcsin` of a rational function) | Then `G'/Δ_c(G)` is a holomorphic differential on an algebraic curve; success iff that curve has a drawable arc length | **Not a loophole:** this *is* the single-curve route (L0) |
| L9 | Non-uniform construction | Each constructor term is a fixed function; a finite term gives finitely many smooth pieces on a bounded interval, and the test applies piecewise. Branch choices (`inter_x`, `restrict`, floor) are themselves constructible | **Reduced** to L1 if the parameter depends on `u` |
| L10 | Definitional circularity: a drawn curve whose geometry already contains `am_c` | Forbidden by the construction rules, but worth naming: if allowed it would trivially supply `F_c` | **Excluded by definition** |
| L11 | Singular (CM) moduli, where extra `E`↔`F` relations may exist | Tested only generically here; the self-dual modulus `k=1/√2` is the prime suspect | **Open, low priority** (R2 owns the moduli catalogue) |

---

## 4. Candidate formulas tested

All candidates were checked against `mpmath` at **3 moduli** `k ∈ {0.3, 0.7, 0.93}` and
**5 arguments** (or 5 angles) unless stated; `-2.5` and `1.3/1.7/2.5` are extra moduli for
the addition and reciprocal-modulus tests.

### 4.1 Descending Landen transformation (modulus change) — **[N] 40 digits**

Script `R3-02-landen.py`, `R3-03-landen-E.py`. With `k′ = √(1−k²)` and
`k₁ = (1−k′)/(1+k′)` (the DLMF `k₁`, which is the `ℓ` of the brief), for
`z = (1+k₁)v`:

  `sn(z,k) = (1+k₁)·sn(v,k₁)/(1 + k₁ sn²(v,k₁))`,
  `cn(z,k) = cn(v,k₁)dn(v,k₁)/(1 + k₁ sn²(v,k₁))`,
  `dn(z,k) = (1 − k₁ sn²(v,k₁))/(1 + k₁ sn²(v,k₁))`,
  `k = 2√k₁/(1+k₁)`.

[P] DLMF 22.7.1–22.7.4; [N] worst residual `≈ 7·10⁻⁴¹` over 3 moduli × 5 arguments. The
amplitude form is `sin(am(z,k)) = (1+k₁)sn(v,k₁)/(1+k₁ sn²(v,k₁))`, so Landen changes the
modulus and the argument *algebraically* but leaves the difficulty in place. Since
`k₁ → 0` only in the limit (the only fixed point is `k=0`: solving `k=(1−k′)/(1+k′)`
gives `k(k²+3k+4)=0`), finitely many Landen steps never reach modulus `0`, where `am` is
elementary. **Verdict: no construction, and it is an exact identity, not an approximation.**

### 4.2 Mixed `E`/`F` at different moduli — **[N] 40 digits**

**(a) Reciprocal modulus (the brief's example).** For `k > 1` and `k sin φ = sin β`,
script `R3-04-candidates.py` verifies to 40 digits at `k ∈ {1.3, 1.7, 2.5}`, 5 angles:

  `E(φ,k) = k·E(β,1/k) − (k − 1/k)·F(β,1/k)`,
  `F(φ,k) = (1/k)·F(β,1/k)`.   (the second is exact to all digits; ratio `= 1/k` exactly)

So a first-kind integral transports to a first-kind integral (holomorphic → holomorphic),
as expected, while a second-kind integral acquires a **nonzero** first-kind coefficient
`k − 1/k`. Inverting `E + const·F` is not something any constructor does. **Killed.**

**(b) Descending Landen for `E`.** A pure two-term fit
`E(φ,k) = a·E(φ₁,k₁) + b·F(φ₁,k₁)` (φ₁ the Landen-transformed angle) leaves a residual that
does **not** shrink with precision; there is an additional algebraic boundary term. The
first-kind coefficient in any such representation is nonzero (the reciprocal case above is
the clean check). **Killed.**

**(c) Complete integrals.** `K(k) = (1+k₁)K(k₁)` holds to 40 digits. (The naive guess
`E(k) = (1+k₁)E(k₁) − k₁K(k₁)` is **false** — residual 0.03–0.27 — and is not used.)

### 4.3 Mixed `E`/`F` at the same angle — **[N], decisive negative

Script `R3-06-mixedEF.py`. Question: is there `A, B` and a rational `R` with

  `E_{c'}(am_c(u)) = A·E_c(am_c(u)) + B·u + R(sin(am_c(u)))` ?

Differentiating (with `s = sin(am_c)`, `u = F_c(am_c)`) this is equivalent to

  `√(1−c′s²) = A√(1−cs²) + B/√(1−cs²) + R′(s)√(1−s²)`.   (†)

- `c′ = c` fits exactly (`A=1, B=0, R′=0`, residual `0`, and `1.1·10⁻⁴¹` at `c=0.09`),
  which is the identity `E_c(am_c) =` epsilon, not constructible.
- `c′ ≠ c`: fitting (†) with a polynomial `R′` of degree ≤ 8 on 14 points and evaluating
  **off-grid** on 12 fresh points leaves a residual floor that does not go to zero as the
  basis grows: `≈10⁻⁸` for `c′=1−c`, `≈10⁻⁶` for `c′=c/2`. The exact value `0` for
  `c′=c` confirms the test is not merely under-determined.
- Symbolically: after multiplying (†) by `√(1−cs²)`, the left side involves
  `√((1−c′s²)(1−cs²))` while the basis spans `1−cs²`, `1`, and `s^j√((1−s²)(1−cs²))`.
  For `c′=1−c` one gets `√(c+(1−c)y²)` with `y²=1−s²`, an independent square root over the
  function field of `y²=1−s², z²=1−cs²`; not in the span. **Killed.**

Note `c′=c` and `c′=0` are the only cases with a true relation, and both are circular
(epsilon / identity); `c′=1` gives `sn_c`, also equivalent to `am_c`.

### 4.4 Third kind — **[P] in Lean**

`Pptc/ThirdKind.lean` proves (symbolically) that

  `ellipticPiInc c 0 φ = F_c(φ)` (line 103),
  `ellipticPiInc c c φ = (E_c(φ) − c sinφ cosφ/Δ_c(φ))/(1−c)` (line 117),
  `ellipticPiInc c 1 φ = F_c(φ) + (tanφ·Δ_c(φ) − E_c(φ))/(1−c)` (line 167).

So even the special cases reduce to `E` and `F` plus an elementary boundary term; none is a
pure first-kind integral, and there is no inverse constructor for `ellipticPiInc`. The
`n=1` case makes the "`s−B`" obstruction explicit: recovering `φ` from `Π_c(1,φ)` means
inverting `F_c(φ) + (elementary in φ)`, which no constructor does. **Killed.**

### 4.5 The `ellipticEAm` route — **[N] 40 digits**

Script `R3-07-eps.py`. To reach `am_c` through `ellipticEAm_c` one needs a constructible
`L` with `ellipticEAm_c(L(u)) = am_c(u)`, i.e. `L(u) = E_c(am_c(u))`. But

  `E_c(am_c(u)) = ∫₀^u dn_c(t)² dt` (DLMF 22.16.17) = Jacobi's epsilon,

verified to 40 digits over 3 moduli × 5 arguments. Epsilon is **not** in `𝒜` (its derivative
`dn_c² = 1 − c sn_c²` already needs `am_c`), and it is nonaffine (second divided difference
`−0.053` and `−0.285` at `k=0.3,0.7`). So this route is exactly the (T3)-failure /
circularity case. At any other modulus `c′` it needs the nonexistent identity of §4.3.

### 4.6 Positive calibration: why the `E` route *does* work — **[N] 40 digits

Script `R3-07-eps.py`. `ellipticEAm_c` is P-constructible (`Pptc/Jacobi.lean:602`).
`ellipticEAm_c(E_c(φ)) = φ` verified to 40 digits. In the language of Lemma 2 this is the
affine-`L`, `G=id`, `s_γ = E_c` case: the curve (the ellipse) has arc length `E_c` *exactly*
on the nose. The test therefore calibrates correctly: it passes a genuine construction and
declines `am_c` exactly because no drawable curve is known with `s_γ = αF_c∘G + β`.

---

## 5. Partial facts: for which `u` is `am_c(u)` already constructible

Throughout this section `c` is P-constructible and `< 1`.

1. **Presented first-kind integrals. [P]** If `u = F_c(φ)` with `φ` P-constructible then
   `PConstructible (am_c(u))`, because `am_c(F_c(φ)) = φ`
   (`Pptc/Jacobi.lean:659`). This includes the dense set `{F_c(φ)}`. **[N]** `F_c(am_c(u))=u`
   to 40 digits (`R3-01-basics.py`).
2. **`u = 0`** and, more generally, `u = n·F_c(π)` for `n ∈ ℤ`, by half-turn
   quasi-periodicity `am_c(u + n F_c(π)) = am_c(u) + nπ` (`Pptc/Jacobi.lean:246`).
3. **Addition closure. [P] (F4) + [N] 50 digits.** If `am_c(u)` and `am_c(v)` are
   P-constructible and `u, v` are P-constructible, so is `am_c(u+v)`: the addition theorem
   (F4) gives `sn(u+v)`, `cn(u+v)` algebraically from the data at `u` and `v`, and
   `jacobiAm_Pconstructible_of_cn` (`Pptc/Jacobi.lean:300`) recovers the angle. Tested in
   `R3-05-partial.py` at 3 moduli × 4 pairs to `≈2·10⁻⁵¹` (mod `2π`). So the set
   `S_c := {u : PConstructible (am_c u)}` is closed under `+`, `−`, and integer multiples.
4. **Halving and dyadic multiples. [P] algebraic + [N] 14+ digits.** With
   `S = sn(2u)`, `y = sn(u)²` is a root of the quartic
   `S²(1−cy²)² = 4y(1−y)(1−cy)`, i.e.
   `c²S²y⁴ − 4c y³ + (4(1+c) − 2cS²) y² − 4y + S² = 0`.
   (This is the square of the exact duplication formula
   `sn(2u) = 2 sn u cn u dn u/(1−c sn⁴u)`, verified to 50 digits, `R3-05-partial.py`.)
   Hence `sn(u)`, and so `am_c(u)` up to branch, is a real root of a polynomial of degree
   ≤ 6 with P-constructible coefficients, hence P-constructible
   (`Pptc/Basic.lean`, real roots of degree ≤ 6). Starting from `am_c(K) = π/2` and halving
   repeatedly gives `am_c(K/2ⁿ)`; verified against `mpmath` to `≈10⁻¹⁴…10⁻²¹` for
   `n = 1…6` at 3 moduli.
5. **Combining 1, 3, 4.** `S_c` contains `F_c(φ)`, is closed under `+ −` and under `u ↦ u/2`,
   and contains `K = F_c(π/2)` (P-constructible by `ellipticF_Pconstructible`). Hence it
   contains every dyadic multiple `r·K` (`r = m/2ⁿ`), every integer multiple of `2K`, and
   every finite sum of these with `F_c(φ)` terms. `S_c` is a countable dense subgroup of `ℝ`
   (countable because `PConstructible` is), and the question is whether a construction can
   push it to all of `PConstructible`.

Fact 3 is the one task L2 formalises in Lean; fact 4's degree `≤6` is why the halving route
is legal at all.

---

## 6. Remaining open loopholes, ranked

1. **Parameter-dependent curves (L1).** The derivative identity (MT-param) has an extra
   `∂s/∂p · p'` term whose right side is *not* of the form `M(am_c)`. This is the most
   plausible place for a genuine composition: choose the curve's modulus/scale as a
   P-constructible function of the argument so that `∂s/∂p` supplies the missing
   `F`-dependence. Complete integrals `K(c)`, `E(c)` are exactly the objects that appear in
   `∂s/∂p`, and they are themselves P-constructible (their values, as numbers, for
   P-constructible `c`). We found no candidate, but we cannot exclude one, and the test in
   its fixed-parameter form simply does not speak to this case.
2. **Composite cancellation in a multi-stage system (L2).** After collapsing, the test needs
   (T3) for `H = ∂₁L₂·T₁' + ∂₂L₂`. A nonlinear `L₂` could in principle make `H` an
   `am_c`-free nonconstant function, which would be a construction. No candidate; not
   excluded.
3. **The transcendence input (T3) itself.** Even in the fixed-parameter, single-stage case,
   the conclusion "`L'` affine" rests on (T3). (T3) is expected but not proved, and the
   usual pole-lattice heuristics are *insufficient* because elementary functions can have
   rank-two pole sets. A rigorous proof would need a differential-algebraic independence
   theorem for `am_c` over the allowed class.
4. **Singular/CM moduli (L11).** The tests above are generic in `c`. At a singular modulus
   (notably `k = 1/√2`, where `K′ = K`) there may be extra relations between `E` and `F`.
   Even a success here would only cover countably many moduli, but it would be a genuine
   partial result and is worth a dedicated check. (R2's Serret catalogue is the natural
   place.)
5. **Definitional circularity (L10).** A drawn curve whose geometry already encodes `am_c`
   would give `F_c` directly. The constructors do not allow it, but any future primitive
   (polar plotting, a "Jacobi curve") must be audited against this.

**Not loopholes, for the record:** the ordinary single-curve route (L0/L8) is the positive
target and is owned by R1/R2; the mixed `E`/`F` transformations through different moduli
(L3/L4) and the third kind (L5) are closed to the precision tested here.

---

## 7. Scripts and references

**Scripts** (in `archived files/jacobi-scripts/`):

| script | contents |
|---|---|
| `00-overview-checks.py` | pre-existing overview checks |
| `R3-01-basics.py` | `mpmath` convention; `F(am)=u`, `sn=sin am`, `dn=Δ`; (F4) below; 40 digits |
| `R3-02-landen.py` | search for the Landen amplitude relation |
| `R3-03-landen-E.py` | Landen `sn/cn/dn` confirmed; incomplete-`E` fit; Legendre relation |
| `R3-04-candidates.py` | reciprocal-modulus mixed `E`/`F`; complete `K`; first mixed-`E`/`F` fit |
| `R3-05-partial.py` | duplication, halving quartic, addition closure, dyadic `K/2ⁿ` |
| `R3-06-mixedEF.py` | decisive off-grid test of mixed `E`/`F` at the same angle |
| `R3-07-eps.py` | `E_c(am_c)=` epsilon; non-affineness; `EAm` calibration |

**References used (literature budget kept small):**

- DLMF §22.7 Landen transformations, https://dlmf.nist.gov/22.7 (22.7.1–22.7.4 confirmed
  numerically).
- DLMF §22.16 Related functions, https://dlmf.nist.gov/22.16 (22.16.1 `am = Arcsin sn`;
  22.16.9 Fourier series in the nome — an *infinite* series, not a finite composition;
  22.16.14–22.16.31 Jacobi epsilon, `E(am(x,k),k)=ℰ(x,k)`).
- Wolfram MathWorld, "Jacobi Amplitude",
  https://mathworld.wolfram.com/JacobiAmplitude.html.
- `Pptc/Jacobi.lean`, `Pptc/ThirdKind.lean`, `Pptc/Defs.lean`, `Pptc/Basic.lean` for the
  Lean-level facts cited by line.

---

## 8. Independent arithmetic re-check (pre-finish)

Every numerical claim above was re-run from the archived scripts on this machine with
`mp.dps = 40` (or 50 in `R3-05`). The two decisive numbers were independently regenerated:
the reciprocal-modulus identity residual `≤ 2.1·10⁻⁴¹` at all three `k`; and the mixed-`E`/`F`
off-grid residual at `c′=c` is `0.0` while at `c′=1−c` it plateaus at `≈10⁻⁸` and at
`c′=c/2` at `≈10⁻⁶`. No result depends on a single script; the only `[N]` items reported at
fewer than 15 digits are the root-recovery and dyadic-halving checks (`≈10⁻¹⁴`), which are
limited by quartic root isolation and are algebraic consequences of the 50-digit duplication
formula, not independent identities.
