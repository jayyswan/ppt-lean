# Y1b: the rank-one square deformation — conic, obstruction, verdict

Status: **done** (2026-11-10). Stream Y1b of `pptc/PLAN-algebraic.md`; background in `Y1a.md`,
`Z5.md`, `A1.md`. No Lean edits. Labels: [Proof], [Wolfram], [Heuristic], [Open].

Every obstruction below is scoped to the **distance-only deformation of the rank-one square**.
Nothing here is a negative about `algebraic_Pconstructible`. In particular the conclusion is not
"β ∉ P"; it is "this pencil does not produce the square forms unless P already contains the target
field".

Notation is Y1a's.
- q ∈ ℚ[X] irreducible of degree n, β₁ a real root, K = ℚ[X]/(q).
- L ⊂ ℝ ∩ P a field closed under square roots of positive elements; K_L = K ⊗ L, assumed a field.
- u(s) = (s, −1), Q_B(s) = u(s)ᵀBu = b₁₁s² − 2b₁₂s + b₂₂.
- V_τ = {[ρ] ∈ ℙ(K_L) : ρ² ∈ ⟨1,τ,τ²⟩}, ℓ_τ = ℙ⟨1,τ⟩.
- ℓ ∈ L² is a linear form, ℓ(τ) := ℓ₁τ − ℓ₂; B₀ = ℓℓᵀ rank one, A := ℓ(τ)² ∈ K_L.

## 0. Verdict

**The deformation is not a descent condition. It is a re-description of SS, and its arithmetic
constants are the target field.**

1. **The exact conic.** With C := Q_{B₁}(τ) and B_t = B₀ + tB₁ (B₁ ≻ 0, t > 0), the square
   condition is the conic
   C_{B₀,B₁} : r² − Cts − As² = 0 ⊂ ℙ²_{(t:r:s)},   A = ℓ(τ)².
   It is smooth (det = −C²/4 ≠ 0), has the K_L-point (0:ℓ:1), and is parametrized by
   t = C/m² − 2ℓ/m, r = C/m − ℓ (m ∈ K_L^×). **The point (0,ℓ) already has t = 0 ∈ L and
   r ∈ K_L**, so the class in H¹(L,μ₂) is zero and there is no descent obstruction to compute.
2. **The curve.** Imposing t ∈ L turns the conic into the *pencil curve*
   X_C = {r ∈ R_{K_L/L}𝔸¹ : r² − A ∈ L·C} ⊂ V_τ,
   a (ℤ/2)ⁿ-cover of the t-line, geometrically irreducible, of genus
   g = 1 + (n−3)2^{n−2} = 129, 321, 769 at n = 7, 8, 9.
3. **Equivalence [Proof].** Every positive-definite form is B₀ + tB₁ with B₀ = ℓℓᵀ ⪰ 0 (small ℓ),
   B₁ ≻ 0, t = 1; and every point of the conic with t > 0 gives the PD square form B_t. Hence
   Y1b.1 ⇔ *V_τ(L) meets the positive-definite chamber*, i.e. the first step of SS. Varying B₁
   sweeps V_τ, so no pencil is special.
4. **Arithmetic [Proof + Wolfram].** X_C is the K-twist of the split (ℤ/2)ⁿ-cover: the n double
   covers r_i² = ℓ(τ_i)² + tQ_{B₁}(τ_i) are permuted by Gal(K^gal/ℚ) = S_n (or A_n). The fibre at
   t = 0 is the **S_n-resolvent scheme** of q: n+1 components of degrees C(n,0), …, C(n,n). The
   k = 1 component is *exactly* K [Proof; Wolfram n = 5]. Consequently the arithmetic Galois
   closure of X_C → ℙ¹_t has S_n as a quotient and is not solvable for n ≥ 5; the natural
   "solvable-step" shortcut (A1 Theorem G) does not apply, and neither does any Kummer vanishing.
   The relevant class is the S_n-torsor K/ℚ itself, not a class in H¹(L,μ₂).
5. **Scoped negative.** Over L = P, no free construction (degree ≤ 8 or solvable steps) produces a
   point of the pencil with t ≠ 0: the t = 0 fibre already needs K, and the arithmetic closure
   carries S_n. So the rank-one deformation supplies no square forms to Theorem R, and **Y1b.4 is
   not launched**. Y1b.2 is vacuous (the shapes are already free, §6). Y1b.3 is answered: there is no
   μ₂-obstruction to kill; the obstruction is the target field itself (§7).
6. **By-products.** The exact conic and parametrization; the pencil curve X_C with its genus and
   its place in Z5's π: V_τ → ℙ² picture; the t = 0 resolvent table; a correction to the
   applicability clause of A1 Theorem G; and the genus coincidence g(X_C) = g(C_B) at J = n−1.

## 1. The exact conic and its parametrization [Proof]

Data: ℓ ∈ L² with ℓ(τ) ≠ 0, B₀ = ℓℓᵀ, B₁ ≻ 0 over L, A = ℓ(τ)², C = Q_{B₁}(τ) ≠ 0,
B_t = B₀ + tB₁.

- **Positivity.** B₀ ⪰ 0 has rank one, B₁ ≻ 0; a sum of a PSD and a PD form is PD. So B_t ≻ 0 for
  every t > 0. No further condition is needed.
- **Square condition.** Q_{B_t}(τ) = A + tC. So the condition is
  r² = A + tC, (t ∈ L, r ∈ K_L).
- **Conic.** Homogenizing with s:
  r² − Cts − As² = 0, matrix
  [[0, 0, −C/2], [0, 1, 0], [−C/2, 0, −A]], determinant −C²/4 ≠ 0.
  It is a smooth conic in ℙ². Its point (0:ℓ:1) is K_L-rational.
- **Parametrization.** Lines r = ℓ + mt through the known point:
  (ℓ + mt)² = ℓ² + tC  ⟹  t(2ℓm + m²t − C) = 0  ⟹  t = C/m² − 2ℓ/m, r = C/m − ℓ,
  and conversely r + ℓ = C/m. [Wolfram: the identity (C/m − ℓ)² − (ℓ² + (C/m² − 2ℓ/m)C) = 0.]

**Why there is no H¹(L,μ₂) obstruction.** The conic is K_L-isomorphic to ℙ¹ and already has a
point with t ∈ L (t = 0) and r ∈ K_L. "t ∈ L" is *not* a Galois-invariance condition on the points of
the conic: r is allowed to be in K_L, so the conic's L-points are not what is being asked for. The
correct formulation is pointwise in t:

  for t ∈ L, the class c(t) := [A + tC] ∈ K_L^× / K_L^{×2}; a point exists iff c(t) = 1.

The question is whether the curve t ↦ c(t) in the Kummer group hits the identity at t ≠ 0. That is
the *pencil curve* below. In particular there is no single class to compute and no Hilbert-90
vanishing hypothesis that could be imposed: the trivial point t = 0 is already there.

## 2. The pencil curve X_C [Proof]

Definition:

  X_C := {r ∈ R_{K_L/L}𝔸¹ : r² − A ∈ L·C}.

The equations are the n coefficients of r² − A − tC = 0 (t eliminated); they have coefficients in L
(in ℚ for rational data). Since A, C ∈ W_τ = ⟨1,τ,τ²⟩, X_C ⊂ V_τ.

- **Geometry over L̄.** K_L ⊗ L̄ ≅ L̄ⁿ, r ↦ (r_i); X_C becomes
  {r_i² = A_i + tC_i, i = 1..n}, the fibre product of n double covers of the t-line. The n sign
  flips act on the 2ⁿ sheets as (ℤ/2)ⁿ, transitively; so X_C is geometrically irreducible and
  X_C → ℙ¹_t has degree 2ⁿ.
- **Branch points.** t_i = −A_i/C_i (i = 1..n), plus t = ∞; assume A_i ≠ 0 (i.e. ℓ(τ_i) ≠ 0 for all
  i; otherwise branch points collide with t = 0 and the cover degenerates). At t_i the fibre has
  2^{n−1} points, each of ramification index 2 (r_i² ≈ C_i(t − t_i)); at ∞ there are 2^{n−1} points,
  each of index 2 (r_i² ≈ tC_i, so s = r_1²/C_1 + … is a square of the local parameter).
- **Genus.** Riemann–Hurwitz:
  2g − 2 = −2·2ⁿ + (n+1)·2^{n−1}  ⟹  **g = 1 + (n−3)2^{n−2}.**

  | n | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
  |---|---|---|---|---|---|---|---|
  | g(X_C) | 1 | 5 | 17 | 49 | **129** | **321** | **769** |
  | degree over ℙ¹ | 8 | 16 | 32 | 64 | 128 | 256 | 512 |

- **Relation to Z5's picture.** Z5 reads V_τ as the (ℤ/2)^{n−1}-cover
  π: V_τ → ℙ² = ℙ(binary quadratics), [ρ] ↦ Q with Q(τ) = ρ², branched along the conic
  Δ = {Q : Q = (linear)²}, with π^{-1}(Δ) = the 2^{n−1} lines l_ε = {z_i = ε_i(α + βτ_i)}.
  The pencil ⟨B₀, B₁⟩ is a line L_B ⊂ ℙ² through B₀ ∈ Δ. Then X_C maps 2:1 to π^{-1}(L_B) away
  from r = 0 (the two points over a point of π^{-1}(L_B) are ±r): X_C is the "square-root
  normalization" that fixes the A-coefficient to be 1 instead of a square class. In particular the
  2ⁿ points of X_C over t = 0 map 2:1 onto the 2^{n−1} points of the l_ε over B₀.
- **No special pencil.** For r ∈ V_τ(L) with r² = ℓ² + w, w ∈ W_τ, put C := w. Then
  r ∈ X_C. Hence ∪_{B₁} X_C(L) = V_τ(L) ∖ {r : r² = ℓ²}. The pencils fill V_τ; there is no
  distinguished direction.
- **Genus coincidence.** g(X_C) = 1 + 2^{n−2}(n−3) equals Y1a's g(C_B) at J = n−1. (RH for C_B:
  degree 2^{n−1}, 2(n−1) branch points.)

## 3. Y1b.1 is exactly the first step of SS [Proof]

Let B ≻ 0 be a positive-definite binary form over L with Q_B(τ) = ρ², ρ ∈ K_L (a "square form").

- **(Square form ⟹ conic point.)** Choose ℓ ∈ L² with ℓℓᵀ ≺ B (possible: B ≻ 0 is open and a
  small multiple of any rank-one PSD form lies below B). Put B₁ := B − ℓℓᵀ ≻ 0, t := 1,
  C := Q_{B₁}(τ) = ρ² − ℓ(τ)². Then B = B₀ + 1·B₁ and (t,r) = (1,ρ) is a point of the conic with
  t > 0 and B_t = B ≻ 0.
- **(Conic point ⟹ square form.)** A point (t,r) with t > 0 gives B_t ≻ 0 and Q_{B_t}(τ) = r².
- **(All PD forms occur.)** The above two bullets are inverse at the level of forms: the family
  {B₀ + tB₁ : ℓ ∈ L², B₁ ≻ 0, t > 0} is *the whole positive-definite cone*.

Hence:

  **Y1b.1 ⇔ V_τ(L) ∩ {positive-definite forms} ≠ ∅.**

This is the first step of SS: SS needs n−1 PD points of V_τ, and Y1b.1 is the statement that even
one exists. It is not a weakening in the sense that a deformation could bypass: the pencil family is
the whole PD cone, so Y1b.1 is precisely the first half of SS, not a substitute for it. A positive
Y1b.1 was the prerequisite for Y1b.4; §4 shows that no free construction supplies it.

## 4. Arithmetic: the K-twist and the t = 0 resolvent fibre

### 4.1 The twist [Proof]

Over L̄, X_C = {r_i² = A_i + tC_i}. The data A_i = σ_i(A), C_i = σ_i(C) are the conjugates of
A, C ∈ K; Gal(K^gal/ℚ) permutes the n double covers through its action on the roots τ_i (the
subgroup Gal(K^gal/K) acts trivially on the labels). Hence the
**arithmetic monodromy** Γ := Gal(closure / ℚ(t)) maps onto Gal(K^gal/ℚ) = S_n (or A_n). In
particular Γ is not solvable for n ≥ 5, even though the *geometric* monodromy is the solvable group
(ℤ/2)ⁿ. This is the whole point: the pencil carries the target field in its constants.

Equivalently: the geometric class of X_C is the n-tuple of quadratic characters
χ_i(t) = [ℓ(τ_i)² + tQ_{B₁}(τ_i)] ∈ ℚ̄(t)^×/ℚ̄(t)^{×2}, and Galois acts on the tuple by the
standard permutation action on the n roots. So the twist class is the image of the S_n-cocycle of
K/ℚ; it lies in H¹(ℚ, S_n), not in H¹(L, μ₂).

### 4.2 The fibre at t = 0 is the resolvent scheme [Proof + Wolfram]

At t = 0, r² = ℓ², so the L̄-points are r_ε = (ε_i ℓ_i), ε ∈ {±1}ⁿ. Galois acts by permuting the
coordinates, so the geometric points split into n+1 orbits indexed by k = #{i : ε_i = −1}:

  orbit k ↔ the fixed field E_k of S_k × S_{n−k} in K^gal,  [E_k : ℚ] = C(n,k).

These are exactly the S_n-resolvent fields of q. Since Σ_k C(n,k) = 2ⁿ, this accounts for the whole
fibre.

- **k = 1 is K.** The point with ε₁ = −1 and ε_i = +1 (i ≥ 2) has interpolating polynomial
  p = 1 − 2L₁ with L₁(t) = q(t)/(q'(τ₁)(t − τ₁)). The numerator q(t)/(t − τ₁) has coefficients in
  ℚ(τ₁) (elementary symmetric functions of the other roots are polynomials in τ₁), and
  q'(τ₁) ∈ ℚ(τ₁); so p ∈ K[t] and the point is K-rational. Conversely p's coefficients generate K
  for a generic S_n field. So E₁ = K.
- **Wolfram check, n = 5** (q = ∏_{i=1}^{5}(x − i) + 1, disc 38569 prime, totally real, S₅):
  - k = 1: the coordinates of x = V^{-1}ε lie in K; the exact coefficient list of 1 − 2L₁ matches
    the numerical interpolant to 10⁻¹⁹⁸.
  - k = 2: the coordinate field has degree **10 = C(5,2)**, irreducible minimal polynomial
    (verified to 10⁻¹⁶⁸).
- **Degrees.**

  | n | 3 | 4 | 5 | 6 | 7 | 8 | 9 |
  |---|---|---|---|---|---|---|---|
  | degrees C(n,k) | 1,3,3,1 | 1,4,6,4,1 | 1,5,10,10,5,1 | 1,6,15,20,15,6,1 | 1,7,21,35,35,21,7,1 | 1,8,28,56,70,56,28,8,1 | 1,9,36,84,126,126,84,36,9,1 |

### 4.3 Consequence for L = P [Proof + Heuristic]

Three statements, in increasing order of strength.

1. **[Proof]** A P-point of X_C over t = 0 exists iff an embedding E_k ⊂ P exists (compatible with
   ℚ ⊂ P). For k = 1 that is exactly K ⊂ P, i.e. the target; for k ≥ 2 the field E_k has degree
   C(n,k) and Galois closure K^gal with group S_n/A_n.
2. **[Proof]** The arithmetic closure of X_C → ℙ¹_t has S_n (or A_n) as a quotient (it comes from
   the permutation of the n conjugate double covers and is independent of t). Hence the
   function-field extension is not solvable, and the "solvable-step" criteria — the tower lemma for
   algebraic steps, A1's Theorem G — do **not** apply. This removes the only general mechanism in
   the project's toolkit that would produce a P-point of X_C with t ≠ 0.
3. **[Heuristic]** A P-point with t ≠ 0 would therefore have to come from outside those criteria,
   i.e. from a genuinely new L-point of V_τ in the PD chamber. That is SS itself. No such mechanism
   is visible: the t = 0 fibre already realises K, and the higher fibres only add the S_n-action.

So no free construction in the toolkit produces a point of X_C with t ≠ 0; the t = 0 fibre already
requires K, and the deformation produces no square form by any construction we have.

**The "class".** The correct statement is: X_C is the K-twist of the split (ℤ/2)ⁿ-cover, i.e. the
twist class is the S_n-torsor K/ℚ. It is nonzero for K ≠ ℚ and cannot be killed by a Kummer or
Hilbert-90 argument. This answers the handoff's Y1b.1 question ("identify the obstruction class"):
there is no class in H¹(L,μ₂); the obstruction is the S_n-extension itself.

### 4.4 The negative rank-one variant [Proof]

Take B₀ = −ℓℓᵀ instead (indefinite rank one). Then B_t = −ℓℓᵀ + tB₁ ≻ 0 for t large, and the
condition is r² = −A + tC. At t = 0, r = ±iℓ: no real point and residue field K(i). The real points
sit at t > λ(B₁, ℓ), and the fibre at infinity has the same resolvent structure. So this variant
changes nothing.

## 5. Computations [Wolfram]

All inputs are reproduced here; no Python was used.

1. **Conic identity.** `Simplify[Expand[(C/m - l)^2 - (l^2 + (C/m^2 - 2 l/m) C)]]` → `0`.
   The homogenized quadratic form `r² − C t s − A s²` has matrix determinant `−C²/4 ≠ 0`.
2. **Genus and degree table.** `gen[n_] := 1 + (n - 3) 2^(n - 2)` → 0, 1, 5, 17, 49, 129, 321, 769
   for n = 2..9.
3. **Resolvent degrees.** `Table[Binomial[n, k], {k, 0, n}]`, sums 2ⁿ.
4. **n = 5, k = 1 / k = 2.** q = x⁵ − 15x⁴ + 85x³ − 225x² + 274x − 119 (totally real, disc 38569
   prime). Roots to 150–200 digits; `V = Table[roots[[i]]^j, ...]`; `x = LinearSolve[V, eps]`.
   - k = 1 (`eps = {-1,1,1,1,1}`): `MinimalPolynomial[RootApproximant[s, 6]]` has degree 5;
     the exact `CoefficientList[1 - 2 L1, t]` (with `L1 = PolynomialQuotient[q, t - tau, t] /
     (q' /. t -> tau)`, `tau = Root[q,1]`) matches the numerical interpolant to 10⁻¹⁹⁸.
   - k = 2 (`eps = {-1,-1,1,1,1}`): degree 10, irreducible, residual 10⁻¹⁶⁸.
5. **Rational-point search on X_C.** A = 1, C = τ² + 1, B_t = diag(t, 1+t);
   a point is rational iff, for some sign tuple, `LinearSolve[V, eps Sqrt[1 + t(roots² + 1)]]`
   has all coordinates rational.
   - n = 3 (q = x³ − 4x + 1): none for 0 < t < 3, denominators ≤ 6, |numerator| ≤ 40.
     (The pencil is an elliptic curve; this is consistent with rank 0.)
   - n = 4: none for 0 < t < 2, denominators ≤ 4, |numerator| ≤ 8.
   - n = 5 (q above): none for 0 < t < 2, denominators ≤ 3, |numerator| ≤ 6.
   - n = 7 (q = ∏_{i=-3}^{3}(x − i) + 1, disc 17·3457·15601·669577): none for 0 < t < 2,
     denominators ≤ 4, |numerator| ≤ 12.
   - Sanity control: at t = 0 the harness returns (1,0,…,0) for the all-plus tuple.
   - These searches are evidence only. The proof of §4.3 is the Galois argument.

## 6. Y1b.2: variable affine layers are vacuous [Proof]

The plan's count "3J parameters against J square conditions and n linear equations" does not apply:

- Each B_j is already an arbitrary positive-definite form: 3 coefficients over L, 2 projectively.
  There is nothing to "let vary" — Y1a's Theorem R already quantifies over all of them.
- The square conditions Q_j(τ) = ρ_j² are not equations on B_j: they are solved by introducing
  ρ_j ∈ K_L. Each costs n linear conditions in ρ_j but no condition on B_j.
- The only constraint is the linear system Φ: L^{J+2} → K_L, i.e. J + 2 unknowns against
  [K_L : L] = n equations. A nonzero kernel exists iff J ≥ n − 1 (generically).

  | J | kernel dimension (generic) |
  |---|---|
  | n − 2 | 0 (one determinant condition) |
  | n − 1 | 1 |
  | n | 2 |
  | n + k | k + 2 |

  For n = 9..13 this is 1, 2, 3, … for J = n−1, n, n+1.

So variable shapes do not absorb the obstruction; they are the same data, and the obstruction of
§4 lives in the field, not in a parameter count. **Y1b.2 adds nothing.**

## 7. Y1b.3: the descent statement, and the correction to A1's criterion

**Statement.** Let A = ℓ(τ)², C = Q_{B₁}(τ). The condition "Q_{B_t}(τ) is a square in K_L for some
t ∈ L" is equivalent to X_C(L) ∋ (t, r) with t ≠ 0. There is no H¹(L,μ₂) class attached to this:
the conic is split at t = 0. The "descent theorem" therefore has a negative answer:

> The pencil gives a point with t ∈ L and t ≠ 0 iff the curve X_C has an L-point other than
> r = ±ℓ. Over L = P the free constructions produce no such point: the t = 0 fibre already requires
> K and the arithmetic closure carries S_n. No hypothesis on a Kummer class expresses this.

**Correction to A1 Theorem G.** A1's criterion allows a step with "a solvable Galois closure of
function fields". The geometric monodromy of X_C → ℙ¹ is (ℤ/2)ⁿ, which is solvable, so at first
sight Theorem G applies and gives dense P-points. It does not: the *arithmetic* Galois closure over
ℚ(t) has S_n as a quotient (the k = 1 residue field at t = 0 is K), so it is not solvable for
n ≥ 5. The hypothesis must be checked on the arithmetic closure over the ground field (or the
closure must be regular), not on the geometric monodromy alone. With that reading, Theorem G is
correct and does not apply here. This also explains the boundary n ≤ 4: S_n is solvable exactly
then, and for those degrees the pencil *does* pass the solvable-step test (consistent with the
route being unconditional for n ≤ 4 by other means). This also explains Y1a's remark that "the
rank-one line is the only obvious source of K_L-points": the other points of the pencil are the
resolvents.

**Consistency check with Z5.** Z5 excludes L-curves of genus 0 or 1 on V_τ for n ≥ 9. X_C has genus
769 at n = 9, so it is not excluded — indeed it *is* a curve on V_τ, with the (ℤ/2)ⁿ-structure that
Z5's inequality permits (Z5 rules only on the genus, not on solvability over ℂ).

## 8. Scope and next steps

- **Scoped negative.** The distance-only rank-one deformation does not change the arithmetic of SS:
  it is the same problem, and its constants are the S_n-resolvent fields of the target. The
  kill criterion of the plan is met: "every tested B₁ gives no positive-definite L-point and the
  obstruction is nonzero" — with "obstruction" = the S_n-torsor.
- **Not launched.** Y1b.4 (end-to-end) has no input. Y1b.2 is vacuous (§6). Y1b.3 is answered (§7).
- **Fallbacks, unchanged by this note.**
  - Overshoot (degree > n) is a different engine; this negative does not touch it.
  - Variable-shape *layers* are already free; a different base (rational sextic graph, power law
    with b = 1 ± 1/k, circle partner) is a genuinely different route, and Y1a §4.6(d) already
    counts its cost.
  - The circle partner makes the system quadratic; it lies outside the linear crossing and is not
    helped by the pencil.
- **What would make this route positive.** An L-rational curve of positive rank on V_τ meeting the
  PD chamber, or one L-point of V_τ in the PD chamber (SS itself). Z5 excludes genus 0/1 curves on
  V_τ for n ≥ 9; the pencil curves are solvable over ℂ but twist to the target field. No mechanism
  is visible.

## Other things noticed

- The rank-one fibre is the **S_n-resolvent scheme** of q. This is a clean geometric statement that
  was not in the notes: the whole "rank-one boundary" of V_τ is, at τ, the collection of fixed
  fields of S_k × S_{n−k}. It explains why the boundary supplies only the trivial L-points.
- The pencil curve X_C is a 2:1 "square-root normalization" of the preimage of a line in Z5's
  π: V_τ → ℙ² picture, and its genus equals that of C_B at J = n−1.
- The equivalence "PD square form ⟺ a point of the conic" is exact and does not use the
  separability of the pencil: it is a change of coordinates on the PD cone.
