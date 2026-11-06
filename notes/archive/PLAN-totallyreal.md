# Totally real septics and octics over 𝒫: complete proof and Lean plan

**Status (2026‑09‑25).**

- The mathematical argument below is complete. The analytic step that was left open in the doc (the "real‑line lemma") is now closed by an **exact rational certificate** plus a continuity/IVT argument. No normal‑bundle or Fano‑variety theory is needed.
- Every numerical check is reproducible from the scripts in `work5/` and `work6/` of the bundle.
- Nothing is in Lean yet. Section 4 is the formalization plan.

**What the proof gives.**

- **Theorem 7.** Every real root of a degree‑7 polynomial with P‑constructible coefficients is P‑constructible. The totally real case is new here, and `root_Pconstructible_of_nonreal_root` covers the rest.
- **Theorem 8.** Every real root of a *totally real* degree‑8 polynomial with P‑constructible coefficients is P‑constructible.

With the Abel/half‑trick pipeline, these unlock Γ at denominators 15 and 17 respectively.

---

## 1. The idea in one paragraph

DegreeSeven.lean Tschirnhaus‑reduces to the form y⁷ = cubic(y), which needs e₁ = e₂ = e₃ = 0. For a totally real septic e₂ = 0 is impossible, since p₂ = Σβᵢ² > 0. Rolle also rules out every "xⁿ = cubic" engine, because xⁿ − cubic has at most 5 real roots.

Instead, make the **odd** power sums vanish: p₁ = p₃ = p₅ = 0. These carry no sign constraint for real roots. Newton's identities then give e₁ = e₃ = e₅ = 0. The characteristic polynomial of β becomes "even part + one odd term", and the substitution x = t² turns it into a crossing of two curves that are already drawable:

| n | χ_β(t) after reduction | crossing (x = t²) | curves |
|---|---|---|---|
| 7 | t·R(t²) − e₇, R monic cubic | R(x) = e₇·x^(−1/2) | cubic Bézier graph × `scale_y e₇ (power_law 1 (−1/2))` |
| 8 | Q(t²) − e₇·t, Q monic quartic | Q(x) = e₇·x^(1/2) | quartic graph (drawable, §2.3) × `scale_y e₇ (power_law 1 (1/2))` |

Then β = ±√x, and α is a real root of φ(X) − β, where β = φ(α). That polynomial has degree ≤ 6 when n = 7 and ≤ 7 when n = 8, so Theorem 7 finishes the octic case.

---

## 2. The mathematics

### 2.1 Notation and the "y‑space" reformulation (no field theory needed)

Let q ∈ ℝ[X] be monic of degree n ∈ {7, 8} with P‑constructible coefficients. Assume it is separable and totally real, with real roots α₁ < … < αₙ, and let α be one of them.

For b ∈ ℝⁿ put φ_b(X) = Σₖ bₖ Xᵏ, and define the **y‑vector** y(b) := (φ_b(α₁), …, φ_b(αₙ)) ∈ ℝⁿ.

- b ↦ y(b) is a linear isomorphism, with matrix the Vandermonde matrix of the distinct αᵢ.
- The power sums pₖ(y(b)) = Σᵢ φ_b(αᵢ)ᵏ are polynomials in b whose coefficients are power sums of the αᵢ. Those are polynomials in the coefficients of q, hence P‑constructible. So **if b is P‑constructible, every pₖ(y(b)) is P‑constructible.**
- χ(t) := ∏ᵢ (t − yᵢ) has P‑constructible coefficients, by Newton's identities or as the charpoly of `aeval (companion q) φ_b` as in DegreeSeven. And β := φ_b(α) is a real root of χ.

Everything below is phrased in y‑space, where the relevant forms Σyᵢ, Σyᵢ³, Σyᵢ⁵ **do not depend on q**.

**Lemma N (Newton, odd pattern).** If p₁ = p₃ = p₅ = 0 then e₁ = e₃ = e₅ = 0.

*Proof.* e₁ = p₁. Also 3e₃ = e₂p₁ − e₁p₂ + p₃, and 5e₅ = e₄p₁ − e₃p₂ + e₂p₃ − e₁p₄ + p₅. ∎

### 2.2 Degree‑7 engine

**Lemma E7.** Let R(x) = x³ + r₂x² + r₁x + r₀ and c be P‑constructible. If β ∈ ℝ, β ≠ 0 and β·R(β²) = c, then β is P‑constructible.

*Proof.*

- If c = 0, then R(β²) = 0, so β² is a root of a cubic and β = ±√(β²).
- If c ≠ 0, put x = β² > 0. Then R(x) = c/β = sgn(β)·c·x^(−1/2). So (x, R(x)) lies on:
    - the cubic graph T = {y = R(x)}, drawable as a cubic Bézier exactly as in `powerLaw_cubic_root_pos_Pconstructible`;
    - S = `scale_y (sgn β · c) (power_law 1 (−1/2))`.
- Common points of S and T have x = t² with t·R(t²) − c = 0. That is a nonzero polynomial, so there are finitely many; isolate with `exists_rat_isolating` and `restrict`. `inter_x` gives x, and `sqrt_Pconstructible` together with a sign gives β. ∎

### 2.3 Degree‑8 engine and quartic graphs

**Lemma Q (quartic graphs are drawable).** For P‑constructible c₀…c₃, the graph of y = x⁴ + c₃x³ + c₂x² + c₁x + c₀ is a `PConstructibleCurve`.

*Proof.*

1. Put z = x + c₃/4. Then the quartic equals z⁴ + a z² + b z + c with a, b, c P‑constructible.
2. If a ≠ 0, set λ = √|a|. Then z⁴ + a z² = λ⁴(w⁴ ± w²) with z = λw.
3. Start from `poly_graph (X⁴ + X²)`, or X⁴ − X², or X⁴ when a = 0. These have rational coefficients.
4. Apply `scale_x λ`, then `scale_y λ⁴`, then the shear (x, y) ↦ (x, y + b·x), which is `linearMap_PConstructibleCurve` with entries 1, 0, b, 1.
5. Finish with `translate_y c` and `translate_x (−c₃/4)`. ∎

**Lemma E8.** Let Q be a monic quartic and c be P‑constructible. If β ∈ ℝ and Q(β²) = c·β, then β is P‑constructible.

*Proof.*

- If c = 0, then β² is a root of a quartic.
- Otherwise, if β ≠ 0, cross the Lemma Q graph with `scale_y (sgn β · c) (power_law 1 (1/2))` at x = β², and isolate as in E7.
- If β = 0, there is nothing to prove. ∎

### 2.4 The odd Tschirnhaus lemma (the core)

Let V = {y ∈ ℝⁿ : Σyᵢ = 0} and S_k(y) = Σyᵢᵏ. We want a P‑constructible b such that y(b) ∈ V, S₃(y(b)) = S₅(y(b)) = 0, and the yᵢ are pairwise distinct.

**The construction.** Every step solves one real polynomial equation of degree ≤ 6. Its inputs are six vectors a, b, g, w₁, w₂, w₃ ∈ V.

| step | equation | degree | output |
|---|---|---|---|
| 1 | S₃(a + λb) = 0 | 3 | λ₀; set P = a + λ₀b (so P ∈ X := V ∩ {S₃ = 0}) |
| — | project wⱼ into N_P = {v ∈ V : Σ Pᵢ² vᵢ = 0} along g: w̃ⱼ = wⱼ − (⟨P², wⱼ⟩/⟨P², g⟩)·g | linear | needs ⟨P², g⟩ ≠ 0 |
| 2 | Q(w̃₁ + x w̃₂) = 0, where Q(u) = Σ Pᵢ uᵢ² | 2 | x₂; set q₀ = w̃₁ + x₂w̃₂ (a point of the conic) |
| 3 | S₃(pt(μ)) = 0, where pt(μ) = Q(d)·q₀ − 2B(q₀, d)·d, d = μw̃₁ + w̃₃ and B(u, v) = Σ Pᵢuᵢvᵢ | 6 | μ₀; set v = pt(μ₀) |
| 4 | S₅(P + κv) = 0 | 5 | κ₀; set β‑vector y = P + κ₀v |

**Why the final vector has vanishing odd power sums.**

- For v ∈ N_P, both Q(v + sP) = Q(v) and S₃(v + sP) = S₃(v) + 3sQ(v) hold. Hence P + κv ∈ X for all κ exactly when v ∈ N_P, Q(v) = 0 and S₃(v) = 0.
- pt(μ) is the second intersection of the line q₀ + s·d with the conic, so Q(pt(μ)) ≡ 0. Step 3 then forces S₃(v) = 0, so the whole line lies in X.
- Step 4 adds S₅ = 0. So S₁ = S₃ = S₅ = 0 exactly.

**Why each step has a real root: an exact rational certificate.** Because the forms live in y‑space, which does not depend on q, it is enough to exhibit **one** configuration where every step has a *simple real root* and the output is non‑degenerate. Continuity (§2.5) then gives an open set of good inputs, and density (§2.6) puts P‑constructible inputs inside it.

The certificate below was built by reverse engineering, so that *every root is rational*. Start from a rational point β\* with vanishing odd power sums, and a rational line through it inside X:

- **n = 7.**
    - β\* = (1, −1, 2, −2, 3, −3, 0), v\* = (−6, −5, 3, 2, 3, −4, 7), P = β\* + v\*.
    - Centre inputs: a = P = (−5, −6, 5, 0, 6, −7, 7), b = (6, −1, 1, 0, 3, 0, −9), g = (2, 1, −1, −6, 1, −2/3, 11/3).
    - w₁ = (−495/74, −379/74, 1489/444, 293/148, 565/148, −397/148, 593/111)
    - w₂ = (51/37, 9/37, −157/222, 3/74, −121/74, −195/74, 368/111)
    - w₃ = (239/148, −535/74, 425/148, 463/148, −1901/148, −8071/444, 13603/444)
    - Roots: λ₀ = 0, x₂ = 1/2, μ₀ = 8064/617, κ₀ = −9136536/1150016105. Output y = β\* (distinct entries).
    - Derivatives at the roots, all nonzero: −582, 21595/111, −108084339737784597018125/8236327287823872, −5750080525/761378. Also ⟨P², g⟩ = 244.
- **n = 8.**
    - β\* = (1, 2, 3, 4, −1, −2, −3, −4), v\* = (−5, −4, −1, −5, 2, 6, 4, 3).
    - Centre inputs: a = P = (−4, −2, 2, −1, 1, 4, 1, −1), b = (0, 3, 0, 2, 1, −1, −6, 1), g = (1, −2/3, 0, −1, 1, 3/2, 2/3, −5/2).
    - w₁ = (−143/21, −113/21, −22/21, −452/63, −18/7, 170/21, −24/7, 1154/63)
    - w₂ = (38/35, 29/35, 1/35, 137/105, 96/35, −44/35, 156/35, −193/21)
    - w₃ = (167/35, −89/35, 184/35, −272/105, −501/35, −186/35, −101/35, 370/21)
    - Roots: λ₀ = 0, x₂ = 5/3, μ₀ = −5322/2915, κ₀ = −160325/27427952. Output y = β\* (distinct entries).
    - Derivatives at the roots, all nonzero: −18, 2332/21, −98878323721972460544/179928739375, −1316541696/6413. Also ⟨P², g⟩ = 71/2.
- Both are verified exactly in sympy (`work6/ratcentre.py`). The step‑3 polynomial has degree exactly 6 and the step‑4 polynomial degree exactly 5.
- The rational points came from a search: β\* ranges over "odd‑symmetric" vectors, and v\* over small integer solutions of Σv = 0, Σβ\*²v = 0, Σβ\*v² = 0, Σv³ = 0 with Σβ\*⁴v ≠ 0 (`work6/vsearch*.py`).

**Independent checks.**

- An interval‑arithmetic certificate (`mpmath.iv`, outward rounding) at random rational centres passes every sign test uniformly over input boxes of radius 10⁻⁴⁵ (`work6/cert.py`; `cert7.json`, `cert8.json`).
- Perturbing the rational centre inputs by up to 10⁻⁶ succeeded in 20/20 runs for each n (`work6/perturb.py`).

### 2.5 Chain openness (pure analysis)

**Lemma C.** Let F₁(p; x₁), F₂(p, x₁; x₂), …, F_m(p, x₁, …, x_{m−1}; x_m) be continuous. Suppose at (p\*, x\*₁, …, x\*_m) each Fₖ vanishes and has a *strict sign change* on [x\*ₖ − εₖ, x\*ₖ + εₖ] for suitable εₖ. Then, after shrinking the εₖ, there is a neighbourhood U of p\* such that for every p ∈ U there are x₁, …, x_m with |xₖ − x\*ₖ| < εₖ and Fₖ(p, x₁, …, xₖ) = 0 for all k.

*Proof.*

1. Work backwards. The endpoint values Fₖ(·; x\*ₖ ± εₖ) are continuous and nonzero at the centre, so their signs persist on a neighbourhood of (p\*, x\*₁, …, x\*_{k−1}). Shrink ε_{k−1}, …, ε₁ and U so that everything lies inside those neighbourhoods.
2. Work forwards: apply the IVT at each step. ∎

At the rational centres, sign changes follow from the nonzero derivatives. Concretely, pick rational εₖ and check Fₖ(centre; x\*ₖ ± εₖ) with `norm_num`: these are polynomials with **rational** coefficients at the centre.

Add the open conditions ⟨P², g⟩ ≠ 0 and "the yᵢ are pairwise distinct" (the latter for the output, i.e. a continuous function of the chain). The conclusion: **every input tuple in some open box U around the centre yields a valid β‑vector.**

### 2.6 Density: P‑constructible inputs exist in U

Inputs must be y‑vectors of P‑constructible b's that lie in V. Take any b ∈ ℚⁿ and replace b₀ by b₀ − p₁(y(b))/n. The result is still P‑constructible, and its y‑vector lies in V: it is the orthogonal projection of y(b) onto V, since y of the constant polynomial 1 is (1, …, 1).

The map ℚⁿ → V, b ↦ proj_V(y(b)), has dense image, because ℚⁿ is dense and b ↦ y(b) is a linear isomorphism. So some rational choice of the six inputs lands in U.

The roots λ₀, x₂, μ₀, κ₀ are then **real** roots of degree ≤ 6 polynomials whose coefficients are P‑constructible: they are built from inputs, power sums of the αᵢ, and earlier roots. So they are P‑constructible by `root_Pconstructible_le_six_coeffs`, which says *every* real root is. The final b‑vector is P‑constructible, because the inverse Vandermonde map is never needed: every step is written directly in b‑coordinates, as polynomial identities in b with P‑constructible coefficients.

### 2.7 Assembly

**Theorem 7 (totally real part).** Let q be monic of degree 7, separable, split over ℝ, with P‑constructible coefficients, and let α be a root.

1. By §2.4–2.6, get P‑constructible b with p₁ = p₃ = p₅ = 0 for y = y(b), and yᵢ pairwise distinct.
2. By Lemma N, χ(t) = t·R(t²) − e₇ with R, e₇ P‑constructible.
3. Let β = φ_b(α). It is one of the yᵢ, hence a real root of χ. If β = 0 it is trivially P‑constructible; otherwise Lemma E7 applies. Either way β is P‑constructible.
4. φ_b(X) − β is nonzero (the yᵢ are distinct, so φ_b is nonconstant), has degree ≤ 6, has P‑constructible coefficients and has α as a root. `root_Pconstructible_le_six_coeffs` finishes. ∎

**Full Theorem 7.** Combine as follows:

- Non‑separable q: `root_Pconstructible_of_nonSeparable`.
- q with a nonreal root: `root_Pconstructible_of_nonreal_root`.
- Totally real q: as above.
- natDegree < 7: existing theorems.

**Theorem 8 (totally real octics).** Same as Theorem 7, with χ(t) = Q(t²) − e₇·t and Lemma E8. The recovery polynomial φ_b(X) − β has degree ≤ 7, so the full Theorem 7 applies. Separability and lower‑degree cases reduce as before.

No irreducibility or field‑degree argument is used anywhere. The only non‑degeneracy needed is that the yᵢ are distinct, which is part of the certificate.

---

## 3. What each piece reuses from the repo

| need | existing declaration (file) | status |
|---|---|---|
| real roots of deg ≤ 6 with P‑constructible coefficients | `root_Pconstructible_le_six_coeffs` (Basic.lean:1372) | reuse |
| √ of positives, rpow | `sqrt_Pconstructible` (Basic:214), `rpow_Pconstructible` (Basic:1759) | reuse |
| isolate a crossing | `exists_rat_isolating` (Basic:278), `crossing_Pconstructible` (Basic:345), `restrict`, `inter_x` | reuse |
| cubic graph as a curve | the construction inside `powerLaw_cubic_root_pos_Pconstructible` (Basic:921), `cubicPairArc_PConstructibleCurve` (Basic:1225) | extract a lemma |
| affine maps of curves | `linearMap_PConstructibleCurve` (Basic:3190), `scale_x/y`, `translate_x/y` | reuse |
| charpoly/trace coefficients P‑constructible | `charpoly_coeff_Pconstructible`, `trace_pow_companion7_Pconstructible`, `aeval_entries_Pconstructible` (DegreeSeven) | generalize 7 → n |
| resolvent root | `companion7_charpoly_aeval_isRoot` (DegreeSeven:209); Nonic has `companion9'` | generalize to `companionN` |
| e's from power sums | `esymm_eq_zero_of_powerSums_zero` (DegreeSeven:1127) | add the odd‑pattern variant |
| nonreal / non‑separable cases | `root_Pconstructible_of_nonreal_root` (DegreeSeven:4488), `root_Pconstructible_of_nonSeparable` (DegreeSeven:2219) | reuse |

---

## 4. Proposed Lean structure

A new directory `Pptc/TotallyReal/`, imported by a top‑level `Pptc/TotallyReal.lean`. Files are listed in dependency order, and the declarations are sketches rather than final signatures.

### 4.1 `Pptc/TotallyReal/Engines.lean` (no Tschirnhaus; about 400 lines)

```lean
/-- graph of a cubic with P-constructible coefficients (extracted from Basic) -/
theorem cubicGraph_PConstructibleCurve {c₀ c₁ c₂ c₃ : ℝ} (h : …) :
    PConstructibleCurve {p | p.2 = cubicVal c₀ c₁ c₂ c₃ p.1}

def quarticVal (c₀ c₁ c₂ c₃ c₄ x : ℝ) : ℝ := c₄*x^4 + c₃*x^3 + c₂*x^2 + c₁*x + c₀

/-- Lemma Q: via poly_graph (X^4 ± X^2 or X^4), scale_x/y, linearMap shear, translates -/
theorem quarticGraph_PConstructibleCurve {c₀ c₁ c₂ c₃ : ℝ} (h : …) :
    PConstructibleCurve {p | p.2 = quarticVal c₀ c₁ c₂ c₃ 1 p.1}

/-- Lemma E7 -/
theorem negHalf_cubic_root_Pconstructible {r₀ r₁ r₂ c β : ℝ} (h… : PConstructible …)
    (heq : β * cubicVal r₀ r₁ r₂ 1 (β^2) = c) : PConstructible β

/-- Lemma E8 -/
theorem half_quartic_root_Pconstructible {q₀ q₁ q₂ q₃ c β : ℝ} (h… : PConstructible …)
    (heq : quarticVal q₀ q₁ q₂ q₃ 1 (β^2) = c * β) : PConstructible β
```

Proof notes:

- The sign split on β, and the degenerate cases c = 0 or β = 0, go first.
- For the crossing, reuse the `restrict` + `exists_rat_isolating` pattern from `powerLaw_root_pos_Pconstructible`. The point‑set membership needs `Real.rpow_neg`/`Real.sqrt_eq_rpow`. Finiteness comes from `Polynomial.finite_setOfPred_isRoot` applied to X·R(X²) − c.
- These are the easiest wins and can be done first. Nothing downstream is needed to test them.

### 4.2 `Pptc/TotallyReal/Newton.lean` (about 150 lines)

```lean
theorem esymm_odd_eq_zero_of_psum_odd_zero (s : Multiset ℝ)
    (h1 : (s.map id).sum = 0) (h3 : (s.map (·^3)).sum = 0) (h5 : (s.map (·^5)).sum = 0) :
    s.esymm 1 = 0 ∧ s.esymm 3 = 0 ∧ s.esymm 5 = 0
```

Proof: Mathlib's `Multiset.esymm`/`MvPolynomial.psum` Newton identities (`MvPolynomial.mul_esymm_eq_sum`), or copy DegreeSeven's `two_mul_esymm_two` / `three_mul_esymm_three` style and add k = 4, 5.

### 4.3 `Pptc/TotallyReal/YSpace.lean` (about 500 lines)

The bridge between coefficient vectors and power sums.

```lean
variable {n : ℕ} (αs : Fin n → ℝ)   -- the distinct real roots of q

def yvec (b : Fin n → ℝ) : Fin n → ℝ := fun i => ∑ k, b k * αs i ^ (k : ℕ)
def psumY (y : Fin n → ℝ) (m : ℕ) : ℝ := ∑ i, y i ^ m

/-- power sums of y(b) are polynomials in b with P-constructible coefficients -/
theorem psum_yvec_Pconstructible (hq : q.Splits …) (hcoef : ∀ k, PConstructible (q.coeff k))
    (hb : ∀ k, PConstructible (b k)) (m : ℕ) : PConstructible (psumY (yvec αs b) m)

/-- ∏ (t - y_i) has P-constructible coefficients (charpoly of aeval (companion q) φ_b) -/
theorem prod_sub_yvec_coeff_Pconstructible …

/-- Vandermonde: y is a linear equivalence when the αs are distinct -/
def yEquiv (hdist : Function.Injective αs) : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ)

/-- density: trace-corrected rational vectors hit every open subset of V -/
theorem exists_Pconstructible_near (U : Set (Fin n → ℝ)) (hU : IsOpen U)
    (hne : (U ∩ {y | ∑ i, y i = 0}).Nonempty) :
    ∃ b, (∀ k, PConstructible (b k)) ∧ yvec αs b ∈ U ∧ ∑ i, yvec αs b i = 0
```

The easiest route for P‑constructibility of power sums of the αᵢ is Newton's identities from the coefficients of q, via Mathlib's `Polynomial.sum_roots_pow…`, or the companion‑matrix trace that DegreeSeven already has.

### 4.4 `Pptc/TotallyReal/Certificate.lean` (the core; about 800 to 1200 lines)

```lean
/-- the four step polynomials, as functions of inputs and earlier roots (explicit formulas) -/
def step1 (a b : Fin n → ℝ) (λ : ℝ) : ℝ := psumY (a + λ • b) 3
def projN (P g w : Fin n → ℝ) : Fin n → ℝ := w - ((∑ i, P i^2 * w i) / (∑ i, P i^2 * g i)) • g
def step2 … ; def conicPt … ; def step3 … ; def step4 …

/-- algebra: along the constructed line all odd power sums vanish -/
theorem line_subset_X (hP : psumY P 3 = 0) (hv : v ∈ N_P) (hQ : Q P v = 0) (hC : psumY v 3 = 0) (κ) :
    psumY (P + κ • v) 3 = 0
theorem conicPt_on_conic (hq0 : Q P q₀ = 0) (μ) : Q P (conicPt P q₀ w₁ w₃ μ) = 0

/-- Lemma C, abstract version (continuity + IVT) -/
theorem chain_roots_of_sign_changes … 

/-- the rational centres (n = 7 and n = 8) and their sign changes, by norm_num -/
def centre7 : Inputs 7 := ⟨![-5,-6,5,0,6,-7,7], …⟩
theorem centre7_signs : step1 … (0 - ε₁) < 0 ∧ 0 < step1 … (0 + ε₁) ∧ … := by norm_num [...]

/-- existence: an open box of good inputs around the centre -/
theorem exists_open_good_inputs (n = 7 or 8) : ∃ U, IsOpen U ∧ centre ∈ U ∧ ∀ inp ∈ U, ∃ λ x₂ μ κ, … ∧ Function.Injective (βvec inp λ x₂ μ κ)

/-- the odd Tschirnhaus lemma -/
theorem exists_oddTschirnhaus (hq : q.Monic) (h7 : q.natDegree = 7 ∨ q.natDegree = 8)
    (hsplit) (hsep) (hcoef) :
    ∃ b : Fin n → ℝ, (∀ k, PConstructible (b k)) ∧ psumY (yvec αs b) 1 = 0 ∧
      psumY (yvec αs b) 3 = 0 ∧ psumY (yvec αs b) 5 = 0 ∧ Function.Injective (yvec αs b)
```

Proof notes:

- **Stating the steps in b‑coordinates.** The step polynomials are stated on y‑vectors. The P‑constructible inputs come from §4.3, so each step's coefficients are P‑constructible by `psum_yvec_Pconstructible`.
- **Keeping the new data P‑constructible.** The new vector P = a + λ₀b stays a y‑vector of a P‑constructible b‑vector, because y is linear. The same holds for w̃ⱼ, q₀, v and the final β.
- **Choice of roots.** Each root is taken inside its certificate interval, and its P‑constructibility follows from `root_Pconstructible_le_six_coeffs` applied to that step's polynomial. The polynomials are nonzero because of the sign change.
- **`norm_num` load.** The degree‑6 step‑3 polynomial at the centre has large rational coefficients; see the derivative sizes in §2.4. Evaluate symbolically once, then check signs at the two rational endpoints. If `norm_num` is slow, precompute the univariate polynomial as a literal and prove the equality separately with `ring_nf`, or use `decide` on ℚ.
- **A risk to plan for.** Lemma C needs continuity of rational functions such as projN, which has a denominator. That is fine near the centre because ⟨P², g⟩ ≠ 0 there. Use `ContinuousAt.div` and state the chain on a neighbourhood.

### 4.5 `Pptc/TotallyReal/Main.lean` (about 300 lines)

```lean
theorem root_Pconstructible_totallyReal_seven {q : ℝ[X]} (hmon : q.Monic) (h7 : q.natDegree = 7)
    (hsplit : q.Splits (RingHom.id ℝ)) (hsep : q.Separable)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) : PConstructible α

theorem root_Pconstructible_deg7_coeffs {q : ℝ[X]} (hq : q ≠ 0) (h7 : q.natDegree ≤ 7)
    (hcoef : ∀ k, PConstructible (q.coeff k)) {α : ℝ} (hα : q.eval α = 0) : PConstructible α
  -- cases: natDegree ≤ 6; non-separable; nonreal root (DegreeSeven); totally real (above)

theorem root_Pconstructible_totallyReal_eight … : PConstructible α
  -- recovery uses root_Pconstructible_deg7_coeffs
```

### 4.6 Suggested order of work

1. **Engines** (§4.1). These are self‑contained and quickly give reusable "√x crossing" lemmas.
2. **Newton odd pattern** (§4.2).
3. **Generic companion matrix** `companionN`, generalized from DegreeSeven/Nonic, plus y‑space P‑constructibility (§4.3).
4. **Certificate and Lemma C** (§4.4). This is the largest file. Start with n = 7; n = 8 is the same code with different data.
5. **Assembly** (§4.5), then the Γ corollaries (denominators 15 and 17) in `Gamma.lean`.

Rough size: 2,000 to 2,800 new lines, comparable to DegreeSeven after its cleanup.

---

## 5. Caveats

- **Octics with nonreal roots.** They are not covered. The same method probably works, because the real forms change but real lines are still plentiful, but I have not checked. The Γ targets are totally real, so this is not on the critical path. Concretely, the missing result is the degree‑8 analogue of `Pptc.DegreeSeven.root_Pconstructible_of_nonreal_root`:
  `∀ {q : ℝ[X]}, q.natDegree = 8 → (∀ k, PConstructible (q.coeff k)) → {z : ℂ} → (q.map (algebraMap ℝ ℂ)).eval z = 0 → z.im ≠ 0 → {β : ℝ} → q.eval β = 0 → PConstructible β`.
  The septic proof is the Bring–Jerrard reduction `root_Pconstructible_of_one_conjugate_pair` / `root_Pconstructible_of_two_conjugate_pairs_monic`, and *every* ingredient of that reduction is dimension‑fixed to degree `7`: `Gram`, `stereo`, `p1vec`, `p3vec`, `Lcomb`, `qform`, `Hmat`, `hermiteForm`, the `Fin 6` vectors and the sextic `exists_sextic_along_line`. A degree‑8 version needs all of those rebuilt in dimension `7`, and is a new result rather than a re‑run of an existing proof. Accordingly `Main.lean` proves only the totally real / splitting octic case (`root_Pconstructible_totallyReal_eight`); the general octic statement `root_Pconstructible_deg8_coeffs` was removed rather than left with a `sorry`.
- **Degree 9.** It would also need p₇ = 0, which requires a line on {p₁ = p₃ = p₅ = 0}. Those lines form only a 2‑dimensional family, and quintic graphs with P‑constructible coefficients are not drawable. The engine stops at 8.
- **Numerical status.** The end‑to‑end runs on the four targets (f₇ and f₈ over ℚ(√2, √3), and the Γ N = 15 and N = 17 polynomials) plus 50 random totally real targets all succeeded. They are evidence, not part of the proof. The proof rests on the exact rational certificate (§2.4) and Lemmas C, N, E7, E8 and Q.

---

## 6. File map (bundle)

| path | content |
|---|---|
| `work5/oddkill_n.py`, `run_targets.py`, `robust.py` | end‑to‑end pipeline on the targets and on random polynomials |
| `work6/ratcentre.py`, `centre7.json`, `centre8.json` | exact rational certificates (§2.4) |
| `work6/vsearch.py`, `vsearch2.py` | search for the rational line through β\* |
| `work6/cert.py`, `cert7.json`, `cert8.json` | independent interval‑arithmetic certificates |
| `work6/perturb.py` | openness check around the rational centres |