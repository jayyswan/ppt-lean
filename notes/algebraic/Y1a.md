# Y1a: offset towers through support functions, and the simultaneous-squares problem

Stream Y1a of `pptc/PLAN-algebraic.md`. No `.lean` edits. Labels: [Proof], [Cited], [Wolfram], [Heuristic],
[Open]. Every number below was computed with Wolfram (`WolframLanguageEvaluator`); no Python was used.
Every obstruction is scoped to the route it blocks. Nothing here is a negative about the target.

Notation.
- q ∈ ℚ[X] is irreducible of degree n, β₁ is a real root, K = ℚ[X]/(q).
- L ⊂ ℝ ∩ P is a field closed under square roots of positive elements, for example
  F = P ∩ ℝ_alg or ℚ^solv ∩ ℝ. Write K_L = K ⊗ L and assume it is a field.
- u(s) = (s, −1) is the normal with "normal slope" s.
- A binary form is Q_B(s) = uᵀBu = b₁₁s² − 2b₁₂s + b₂₂, with B = [[b₁₁, b₁₂], [b₁₂, b₂₂]] positive
  definite over L.
- "Q is a square at τ" means Q_B(τ) ∈ K_L^{×2}.

## 0. Findings summary

1. **The reformulation is correct, and it needs no convexity or Minkowski sums [Proof + Wolfram].**
   Parametrize every layer by the normal slope s of the *final* curve. On any s-interval where all
   intermediate arcs are regular, the drawn tower is
   x(s) = G(s) + Σ_j d_j ε_j B_j u(s)/√Q_j(s) + b, with B_j = P_jP_jᵀ (§1, Prop. T).
   - Signed d, orientation reversal and non-convex bases are absorbed into signs ε_j = ±1. These signs
     are locally constant and flip only at cusps.
   - Wolfram: a depth-2 parabola tower built by the literal `offsetParam` recursion matches the closed
     form to 10⁻⁵⁰ at 9 parameters. With d₁ = 3, ε₂ flips across the cusps exactly as predicted.
   - Layer order is irrelevant: any tuple of P_j is realisable.
2. **Correction to the count [Proof].** Against a line ℓ·x = c, the crossing equation is linear in the
   unknowns because it is D_ℓ[H](τ) = c with the linear operator D_ℓh = (ℓ₁+ℓ₂s)h′ − ℓ₂h (§2).
   - D_ℓ kills linear support functions (translations). So after normalisation **a parabola base
     contributes only one linear unknown** (its scale a, through the function s²), not two.
   - The linear unknowns are therefore (c′, a, δ₁..δ_J), J + 2 of them, against n L-linear equations.
   - **No nonsingularity is needed.** For J ≥ n − 1, an L-dependence exists by dimension alone. The
     orchestrator's "J + 1 ≥ n" is right.
3. **Theorem R (reduction) [Proof].** Suppose there are:
   - τ ∈ K_L;
   - J ≥ n − 1 pairwise non-homothetic positive-definite forms over L, each a square at τ;
   - two nondegeneracy conditions, (ND1) regularity and (ND2) the crossing point not in L².

   Then β₁ ∈ P. Notes:
   - realness is automatic, including for **totally real** q, so the route has no Descartes or
     even-power-sum obstruction;
   - `restrict` isolation, regularity, injectivity, read-out and gcd recovery are all proved in §2;
   - an ellipse base instead of a parabola needs n square forms.
4. **One square [Proof].**
   - By Hilbert 90, Q_z(τ) = |τ−z|² is a square in K_L ⟺ τ − z ∈ K_L^×·M^{×2}, where M = K_L(i).
     This holds ⟺ τ = x + y·φ(m) with m ∈ K_L and φ(m) = (1−m²)/(2m).
   - Positive-definiteness is y ≠ 0, and realness is automatic.
   - **Simultaneous squares is a twisted rational-distance problem:** find T = (τ, 0) with τ ∈ K_L and
     n − 1 points P_j ∈ L² off the axis, not mirror images, with |T P_j| ∈ K_L (§3).
5. **Two or more squares: geometry [Proof].**
   - (i) **Fixed τ.** The forms that are squares at τ are the L-points of V_τ = {ρ : ρ² ∈ ⟨1,τ,τ²⟩}.
     It is a *smooth complete intersection of n − 3 diagonal quadrics* in ℙ^{n−1}, with
     K_{V_τ} = O(n−6). So V_τ is:
     - a quadric for n = 4;
     - a del Pezzo surface of degree 4 for n = 5;
     - a K3 surface for n = 6;
     - **of general type for n ≥ 7**.

     It contains the L-line ℓ_τ = ℙ⟨1, τ⟩ of degenerate forms, and **ℓ_τ is its only L-line** for
     n ≥ 5. For n ≤ 5, V_τ is L-rational, so the route is unconditional there. That is a consistency
     check; it is not new.
   - (ii) **Fixed forms.** The τ-curve C_B is a (ℤ/2)^J-cover of ℙ¹ with genus 1 + 2^{J−1}(J−2):
     0, 1, 5, 17, … for J = 1, 2, 3, 4. For J = 2 its Jacobian has full L-rational 2-torsion.
6. **(a)–(d) [Proof unless marked].**
   - **(a)** Pencils turn J + 1 squares into the classical "V + c₀, …, V + c_J all squares". For three
     squares this is halving on an elliptic curve [Cited]. There is no genus saving, and no
     automorphisms survive the K-twist.
   - **(b)** The incidence variety has the right dimension, n + 2J − 2 after symmetries. Its fibres
     over τ are V_τ^J and its fibres over B are R_{K_L/L}C_B. Neither has a rational structure for
     n ≥ 7 or J ≥ 2. Choosing ρ first *is* V_τ.
   - **(c)** X1's descent argument is tight. Splitting the compositum by square classes shows that
     only layers with Q_j(τ) ∈ K_L^{×2} enter the equation that carries c′ and a. Shared radicals
     give separate homogeneous equations that only add constraints. Enlarging L changes nothing
     (Kummer).
   - **(d)** The base and the affine data give exactly 2 linear unknowns. A circle partner (W1's +2)
     makes the system *quadratic*, so it leaves the linear route. With fewer than n − 1 squares, the
     remaining n − 1 − J determinantal conditions fall on an arithmetic set, a finitely generated
     group or finite set over number fields. That is worse, not better.
7. **Tests [Wolfram].**
   - **n = 5 end to end:** a totally real S₅ quintic. τ = β; 32 rational positive-definite square forms
     were found through the dP4 parametrisation, and 4 of them were used. The ℚ-kernel is 1-dimensional,
     and the read-out has an irreducible quintic minimal polynomial. The literally drawn tower passes
     through the predicted crossing at all 5 real roots to 10⁻⁵⁰, and every intermediate arc is
     regular.
   - **n = 9 (totally real S₉) and n = 10 (W1's triangular decic, H5's decic):** no rational point of
     V_β off ℓ_β was found in the height-≤2 (n = 9) and height-1 (n = 10) searches. That is the
     expected outcome for a general-type surface [Heuristic]. No n = 10 hit.
8. **Verdict (§6).**
   - Proved: the reduction to SS_{n−1}, and the route for n ≤ 5.
   - Open: SS_{n−1} for n ≥ 7, which is about L-points on general-type surfaces V_τ (or K_L-points on
     curves of genus ≥ 5).
   - Not conditional on any named conjecture. Bombieri–Lang-type expectations make *Zariski-dense*
     point sets unlikely, but the route needs only n − 1 points, so they do not rule it out.

## 1. The tower in normal-slope coordinates

Conventions from `Defs.lean`: `unitNormal γ t = (−y′, x′)/speed` is the left normal, and
`offsetParam γ d t = γ t + d·unitNormal γ t`. The `offset` constructor needs C¹ velocity with
nonvanishing `speed` on [a, b], injectivity on [a, b) (plus `hseam`), and accepts d of either sign.

**Lemma 1 (offset) [Proof].**
- *Hypotheses.* x: I → ℝ² is C², regular, with x′(s) ⊥ n(s) for a continuous nonvanishing
  n(s) ∝ N(s) := Mᵀu(s)/|Mᵀu(s)|, for a fixed M ∈ GL₂.
- *Claim.* For any C¹ tracing of x(I), `unitNormal` equals ε·N(s) with ε ∈ {±1} constant on I. The
  offset arc is x(s) + d·ε·N(s), and its tangent is again ⊥ N(s).
- *Proof.*
  - `unitNormal` is a continuous unit vector ⊥ x′. So does N(s). In ℝ² these agree up to a sign, and
    the sign is continuous, hence constant.
  - Reparametrising by a decreasing map flips ε; the set {x ± dN} is then described by −d.
  - The derivative of x + dεN is x′ + dεN′, and N′ ⊥ N because |N| = 1. So the tangent stays ⊥ N. ∎

**Lemma 2 (affine map) [Proof].** If the arc x has normal ∝ n, then Ax has normal ∝ A^{−T}n.

**Proposition T (tower formula) [Proof].**
- *Setting.*
  - The tower is: the base G₀, then A₁, offset d₁, A₂, offset d₂, …, offset d_J, A_{J+1}, plus
    translations, all with P-entries.
  - Put P₀ = A_{J+1}⋯A₁ and P_j = A_{J+1}⋯A_{j+1}.
  - Parametrise by the normal slope s of the final curve: the final normal is u(s), and the layer-j
    curve, before the later maps, has normal ∝ P_jᵀu(s) (Lemma 2).
- *Claim.* On any s-interval where the base arc and every intermediate arc are regular,

  x(s) = P₀·g₀(P₀ᵀu(s)) + Σ_j d_j ε_j P_jP_jᵀu(s)/|P_jᵀu(s)| + b = ∇H(u(s)),

  with H(u) = h₀(P₀ᵀu) + Σ d_jε_j√Q_j(u) + ⟨b, u⟩, Q_j = |P_jᵀu|², B_j = P_jP_jᵀ, and g₀(w) the base
  point with normal ∝ w.
- *Proof.*
  - Induct on layers with Lemma 1, using M = P_j, and Lemma 2.
  - The displacement d_jε_j·n_j in the layer-j frame is mapped by P_j to
    d_jε_jP_jP_jᵀu/|P_jᵀu| = d_jε_j∇|P_jᵀu|.
  - For the base: h₀(w) := ⟨g₀(w), w⟩, extended 1-homogeneously along the branch. Then
    dh₀ = ⟨dg₀, w⟩ + ⟨g₀, dw⟩ = ⟨g₀, dw⟩ because dg₀ ⊥ w, so ∇h₀ = g₀. The chain rule gives
    ∇_u h₀(P₀ᵀu) = P₀g₀. ∎

Remarks [Proof].
- **No convexity is used.** The formula holds branch by branch. It agrees with the Minkowski-sum
  picture A₀(base) ⊕ Σ d_j·E_j only where everything is convex and d_j > 0.
- **Signs.** ε_j is locally constant. It changes only where an intermediate arc stops being regular,
  i.e. at cusps. The orientation of a tracing is free, and offset accepts ±d, so the drawn sign of each
  layer is at our disposal.
- **Realisability.** Every tuple (P₀, P₁, …, P_J) of invertible P-matrices occurs: take
  A_{J+1} = P_J, A_j = P_j^{−1}P_{j−1}, and A₁ = P₁^{−1}P₀. Hence:
  - layer order is irrelevant;
  - only B_j = P_jP_jᵀ enters x(s);
  - every positive-definite B over L occurs, because Cholesky needs square roots of positive elements
    of L, and those lie in P.
- **Regularity.** In final coordinates x_k′(s) = r_k(s)·(1, s), where
  r_k(s) = r_G(s) + Σ_{j≤k} d_jε_j det B_j / Q_j(s)^{3/2}.
  This holds because d/ds[(b₁₁s−b₁₂)/√Q] = det B / Q^{3/2}. In particular the x-coordinate of a
  regular arc is strictly monotone, hence injective.
- **[Wolfram]** Depth 2: base (t, t²), A₁ = [[2,1],[−1,3]]/3, A₂ = [[1,−2],[3,1]]/2, A₃ = [[3,1],[1,1]],
  d₂ = −2/7.
  - The recursion uses the literal `unitNormal` with symbolic derivatives.
  - With d₁ = 1/5, the closed form with (ε₁, ε₂) = (1, 1) matches at t ∈ {−1, −1/3, 1/2, 2}, with error
    0 at 30 digits.
  - With d₁ = 3 it matches at 9 values of t (error ≲ 10⁻⁵²). The pattern is (1,1) for |t| ≥ 1 and (1,−1)
    for |t| ≤ 1/2, the flip coming from the cusps of layer 1. The final tangent is exactly ⊥ u.

## 2. The crossing equation and Theorem R

**The operator D_ℓ [Proof].**
- Write h(s) := H(s, −1). By 1-homogeneity, x = ∇H gives x₁ = h′(s) and x₂ = s·h′(s) − h(s).
- So ℓ·x = (ℓ₁+ℓ₂s)h′ − ℓ₂h =: D_ℓ[h], which is linear in h.
- The kernel of D_ℓ contains every linear h, i.e. every translation; a translation contributes only
  the constant ℓ·b.

**Normalisation.**
- An outer L-affine map takes ℓ to e₂ (the line y = c) and puts the parabola's axis vertical, so the
  pole of its normal-slope parametrisation is at s = ∞.
- For a vertical-axis parabola h(s) = α(s−λ)² + const, so D_{e₂}[h] = αs² + const. **The linear term
  cannot be produced**:
  - y = κx² + μx + ν at slope s has y = (s² − μ²)/(4κ) + ν;
  - so the parabola gives the single function s² with a free nonzero scale a = 1/(4κ).
- D_{e₂}[√Q_B] = (b₁₂s − b₂₂)/√Q_B(s), and D_{e₁}[√Q_B] = (b₁₁s − b₁₂)/√Q_B(s).

**Theorem R [Proof].**

*Data:*
- τ ∈ K_L;
- positive-definite, pairwise non-proportional B₁..B_J over L;
- ρ_j ∈ K_L with ρ_j² = Q_j(τ).

Put N_j := b₁₂^{(j)}τ − b₂₂^{(j)} and Φ(c′, a, δ) := c′ + aτ² + Σ_j δ_j N_j/ρ_j ∈ K_L.

*Claim.* Every nonzero kernel vector of Φ (over L) with the nondegeneracies below yields β₁ ∈ P.
- If J ≥ n − 1, a nonzero kernel vector exists: Φ is an L-linear map L^{J+2} → K_L ≅ L^n.
- (ND1): r_k(τ) ≠ 0 in K_L for the partial sums k = 0..J. (This is equivalent to nonvanishing at β₁,
  because K_L is a field and r_k(τ) is the image of a K_L-element.)
- (ND2): X := 2aτ + Σ δ_j(b₁₁^{(j)}τ − b₁₂^{(j)})/ρ_j ∉ L, and L(X) = K_L. The second part is
  automatic when Gal(K_L/L) is primitive, e.g. ⊇ A_n (X1/X2 Lemma N).

*Proof.*
1. *Drawing.*
   - If a ≠ 0, the base is the parabola y = x²/(4a). It is a `poly_graph` scaled by a P-number;
     a < 0 is fine.
   - If a = 0, some δ_j ≠ 0 and that ellipse serves as base. This is the `ellipse` constructor plus
     affine maps; its support function √Q_j is one of the layers.
   - Let τ₁ = τ(β₁) ∈ ℝ. Restrict the base to a rational s-window around τ₁ (an x-window on the
     graph, since s = x/(2a)) on which every r_k is nonzero. Such a window exists by (ND1) and
     continuity.
   - Apply A₁, then `offset_open` with d₁ := ±δ₁, …, as in Prop. T. The sign is chosen so that
     d_jε_j·sgn ρ_j(β₁) = δ_j. Each intermediate arc is regular and injective by the Regularity remark.
2. *Crossing.*
   - At s = τ₁, √Q_j(τ₁) = sgn(ρ_j(β₁))·ρ_j(β₁), and Prop. T gives y(τ₁) = Φ(c′, a, δ)(β₁) − c′ + b₂.
   - Choose b₂ − c := c′, i.e. the line y = b₂ − c′ with c ∈ L ⊂ P. Then Φ = 0 in K_L gives
     Φ(β₁) = 0, so the point x(τ₁) lies on the line.
3. *Isolation.*
   - The final arc is analytic and not contained in the line, since y′ = s·r_J(s) ≢ 0. On a compact
     sub-arc it meets the line finitely often.
   - A rational box around x(τ₁) that excludes the other meeting points, applied with `restrict`,
     makes the intersection a singleton. `inter_x` then gives X(β₁) ∈ P.
4. *Recovery.*
   - Write X = R(β) with R ∈ L[Y] of degree < n. Its conjugates X(β_i) are distinct by (ND2), so
     gcd(q(Y), R(Y) − X(β₁)) over L(X(β₁)) is linear (H3/X1).
   - Hence β₁ ∈ L(X(β₁)) ⊂ P. ∎

Remarks [Proof].
- **Realness is free.** Positive-definite Q gives Q(τ_i) > 0 at real places. Only the target place
  β₁ is drawn, so a totally real q causes no trouble. This contrasts with X2 §3.2, where routes with
  even power sums fail for s = 0.
- **The other conjugates are never drawn.** They enter only through the requirement that the
  certificate Φ = 0 holds in K_L, which is what makes c, a, d_j lie in L.
- **Count.** We need J + 2 ≥ n + 1, i.e. **J ≥ n − 1 square forms with a parabola base, or n square
  forms with an ellipse base** (unknowns c′, δ₀..δ_J). For J < n − 1, the vectors 1, τ², N_j/ρ_j must
  be L-dependent, which is n − 1 − J determinantal conditions.

## 3. One square, and the rational-distance form

**Lemma S1 [Proof].**
- Write a positive-definite Q as Q = b₁₁·|s − z|² with z = x + iy ∈ L(i) and y ≠ 0. This uses
  √b₁₁ ∈ L.
- Put M = K_L(i). Q(τ) ∈ K_L^{×2} ⟺ N_{M/K_L}(τ−z) ∈ K_L^{×2} ⟺ τ − z ∈ K_L^×·M^{×2}.
  - (⇐) is clear.
  - (⇒): if N(α) = c², then N(α/c) = 1. Hilbert 90 gives α/c = w/w̄ = w²/N(w), so
    α = (c/N(w))·w².
- Writing w = p + iq and m = p/q gives **τ = x + y·φ(m), φ(m) = (1−m²)/(2m), ρ = ±y(1+m²)/(2m)**, with
  m ∈ K_L ∪ {∞}.
- *Constraints.*
  - Positive-definiteness is y ≠ 0.
  - Realness is automatic.
  - τ is primitive iff m is, when K_L/L has no quadratic subfield, because [L(m) : L(τ)] ≤ 2.
- *Invariance.* For γ ∈ GL₂(L), (τ, z) is good iff (γτ, γz) is good.
  - γτ − γz = det γ·(τ−z)/((cτ+d)(cz+d)), and cτ + d ∈ K_L^×.
  - L(i)^× ⊂ L^×·L(i)^{×2}, since cos(θ/2) = √((1+cos θ)/2) ∈ L.

**Rational-distance form [Proof].** Q_z(τ) ∝ (τ−x)² + y² = |T − P|² with T = (τ, 0) and P = (x, y). So
SS_J asks for a point T on the x-axis, with abscissa τ ∈ K_L, and J points P_j ∈ L² (y_j ≠ 0, pairwise
not equal or mirror images) such that every distance |TP_j| lies in K_L. Equivalently, the direction
from P_j to T is a K_L-rational point of the unit circle.

## 4. Two or more squares

### 4.1 Fixed τ: the surface V_τ [Proof]

- Let W_τ = ⟨1, τ, τ²⟩_L and V_τ := {[ρ] ∈ ℙ(K_L) : ρ² ∈ W_τ}.
- The map [ρ] ↦ (Q with Q(τ) = ρ²) is a bijection from V_τ(L) ∖ ℓ_τ onto the homothety classes of
  nondegenerate forms that are squares at τ. Here ℓ_τ = ℙ⟨1, τ⟩ gives rank-1 forms (Minkowski
  segments, not drawable).
- **Smooth complete intersection.**
  - Over L̄, K_L ⊗ L̄ ≅ L̄ⁿ, and V_τ = {Σ_i a_{ki} z_i² = 0, k = 1..n−3}, where the rows of A span
    W_τ^⊥.
  - Jacobian criterion: at a point with support S, the equations force the columns a_{·i} (i ∈ S) to
    be dependent. If every (n−3)-minor of A is nonzero, then |S| ≥ n−2 and any n−3 of those columns
    have full rank, so the point is smooth.
  - By Gale duality, the (n−3)-minors of A are, up to one common factor, the complementary 3-minors of
    the Vandermonde rows (1, τ_i, τ_i²). These are nonzero because the τ_i are distinct.
  - Adjunction then gives K = O(−n + 2(n−3)) = O(n−6), and deg V_τ = 2^{n−3}.
- **Only one line, for n ≥ 5.**
  - An L-line is ℙU with U·U ⊂ W_τ, U = ρ₀⟨1, ν⟩, so ρ₀²⟨1, ν, ν²⟩ = W_τ.
  - The n evaluation points (1 : ν_i : ν_i²) and (1 : τ_i : τ_i²) then differ by a projectivity, which
    preserves the unique conic through ≥ 5 points. So ν = Möbius_L(τ) and U = κ⟨1, τ⟩ with κ²W_τ = W_τ.
  - If κ² ∉ L, then W_τ would be a K_L-module of dimension 3 < n. Hence κ² ∈ L, so κ ∈ L, since K_L
    has no quadratic subfield.
- **Projection from ℓ_τ (search method).** Write ρ = α + βτ + w with w ∈ K_L/⟨1, τ⟩. The equations are
  linear in (α, β): 2λ(w(α+βτ)) + λ(w²) = 0.
  - So V_τ is birational to {[w] ∈ ℙ^{n−3} : rk[λ(w), λ(wτ), λ(w²)] ≤ 2}.
  - For n = 5 this is all of ℙ², so **V_τ is L-rational and the route works unconditionally for
    n ≤ 5** (n = 4 is a quadric with an L-point). Real density holds because the number of real
    components is a birational invariant.
  - For n = 6 it is a quartic K3 surface in ℙ³.
  - For n ≥ 7 it is general type.

### 4.2 Fixed forms: the curve C_B [Proof]

- C_B = {(τ, ρ₁..ρ_J) : ρ_j² = Q_j(τ)} is a (ℤ/2)^J-cover of ℙ¹ branched at the 2J points z_j, z̄_j.
  These points are distinct: a common branch point means proportional forms.
- Riemann–Hurwitz gives g = 1 + 2^{J−1}(J−2).
- For J = 2 the pencil λ(ρ₁² − Q₁) + μ(ρ₂² − Q₂) has singular members at λμ·det(λB₁ + μB₂) = 0. All
  four are L-rational: the generalised eigenvalues of a pair of positive-definite forms are real, and
  L has the needed square roots. So Jac(C_B) has full L-rational 2-torsion.
- The variety I_J of all (τ, B, ρ) has dimension n + 3J, or n + 2J − 2 after the affine τ-symmetry and
  the J scalings. Its fibres:
  - over τ: V_τ^J;
  - over B: R_{K_L/L}(C_B).

### 4.3 (a) Clever families

- **Pencils.**
  - Simultaneously diagonalise two forms over L and apply an L-Möbius to τ. Every form in the pencil
    becomes a_jτ̃² + b_j.
  - With V := τ̃², the conditions become: V square, and a_jV + b_j square for j = 1..J.
  - That is the classical problem of shifts that are all squares, and its genus is still
    1 + 2^{J−1}(J−2) [Proof].
  - For three conditions, V − e₁, V − e₂, V − e₃ all squares ⟺ V = x(2P), P ∈ E(K_L), on
    E: Y² = ∏(X − e_i) [Cited: B. M. Bekker, Yu. G. Zarhin, *The divisibility by 2 of rational points
    on elliptic curves*, arXiv:1702.02255, Thm 2.1, a classical criterion]. So three squares cost
    exactly one K_L-point of E beyond E(L). This relocates the problem; it does not solve it.
- **Automorphisms.**
  - An L-automorphism of V_τ or of the configuration needs a Möbius γ ∈ PGL₂(L) with
    γ(τ) a conjugate of τ. Aut(K_L/L) = 1 for S_n or A_n with n ≥ 4, so γ fixes τ and n ≥ 3 of its
    conjugates, hence γ = 1.
  - Of the deck group (ℤ/2)ⁿ, only ρ ↦ −ρ is L-rational.
  - So Fermat-type symmetry exists over L̄ (V_τ is a quotient of C × C̄, C the generalised Fermat
    curve σ_i² = τ_i − w), but **none of it survives the K-twist** [Proof].
- **Torsion.** Division points generate groups inside AGL₂(ℤ/m), whose nonabelian factors are PSL₂(p)
  (H4). These are not A_n for n ≥ 9 [Heuristic, as in X1 §3.1].

### 4.4 (b) Using the freedom of τ

- "Choose ρ_j first and solve linearly": ρ_j² ∈ W_τ is n − 3 linear conditions on (b₁₁, b₁₂, b₂₂).
  The ρ_j that pass form exactly V_τ, so this is §4.1.
- With τ also free, the incidence has the expected dimension. **There is no dimension obstruction;
  the cost is the L-points** (as W1 found).
- A rational component would need a rational curve in V_τ over L(t), or in R_{K_L/L}C_B.
  - Neither exists generically for n ≥ 7 or J ≥ 2: V_τ is of general type, and ℙ¹ does not map
    nonconstantly to a curve of genus ≥ 1.
  - Whether V_τ contains *some* L-rational curve of genus 0 or 1 other than ℓ_τ is [Open]. Such a curve
    would solve SS outright. Lines are excluded by §4.1; conics and twisted cubics were not studied.
- The "multiplicative" device fails for the same reason: if ρ_a², ρ_aρ_b, ρ_b² ∈ W_τ, then the whole
  pencil (sρ_a + tρ_b)² lies in W_τ, but this is a line on V_τ, so it is ℓ_τ.

### 4.5 (c) Galois-class enlargement: X1 is right, the loopholes close [Proof]

- Let M = K_L(ρ₁, …, ρ_J) and let C be the subgroup of K_L^×/K_L^{×2} generated by the classes
  [Q_j(τ)]. Then M = ⊕_{𝔠∈C} K_L·r_𝔠, and Φ = 0 splits into one equation per class.
  - **Class 1:** c′ + aτ² + Σ_{[Q_j]=1} δ_jN_j/ρ_j = 0.
  - **Each 𝔠 ≠ 1:** Σ_{j∈𝔠} δ_jN_jκ_j/Q_j = 0 (κ_j = ρ_j/r_𝔠), a homogeneous system in K_L.
- **Shared radicals** therefore only add homogeneous constraints. They never feed the class-1
  equation, which is where c′ and a live.
- **The all-ellipse variant in one nontrivial class** has c′ = 0 and needs |𝔠| ≥ n + 1 forms.
  - The curve becomes C_B/(−1), of genus 1 + 2^{J−2}(J−2); the involution is free because the forms
    have no common zero.
  - With n + 1 forms that is more genus than the n − 1 squares of class 1.
- **Enlarging L** to a real L′ cannot make Q(τ) a square: K_L(√Q(τ)) ⊂ K_{L′} forces
  Q(τ) ∈ L^×K_L^{×2} (Kummer, no quadratic subfield). The L-factor is positive at β₁, hence a square
  in L.

### 4.6 (d) How small can J be?

- **Linear unknowns** [Proof]: c′ (line and translations), a (base scale), and one δ_j per square
  form.
  - Any base gives one scale. Rational-support bases are those with birational Gauss map:
    parabolas, and `power_law` with b = 1 ± 1/k, i.e. (t^k, t^{k+1}). Their shape parameters are
    nonlinear.
  - Only one base can be present, since there is no union or Minkowski sum of two arbitrary curves.
  - So J_min = n − 1 for the automatic route.
- **Circle partner** [Proof]: |x(τ) − p|² = r² is quadratic in (δ, p). W1's +2 is real, but it buys
  n quadrics over L instead of n linear equations. Finding L-points on those is the X2 / Real-Wooley
  regime (bound about 2200 variables for quadrics).
- **J < n − 1:** the extra n − 1 − J determinantal conditions must hold on K_L-points of C_B. For
  J ≥ 3 and L a number field these points are finite (Faltings); for J = 2 they form a finitely
  generated group. That is n − 3 conditions on a discrete set at J = 2, so **small J is harder, not
  easier** [Proof of the structure; Heuristic as to difficulty]. At n = 10, J = 2–3 has no free
  structure.
- **J = 2 only** [Heuristic]. For E = C_B with B rational, E(K) ⊋ E(ℚ) is a rank-growth question for
  the twist E ⊗ ρ_std(K). Parity and BSD expectations suggest it holds for about half of the 2-moduli
  family. That would give two squares, not n − 1. No theorem is claimed.

## 5. Concrete tests [Wolfram]

**n = 5, end to end.**
- *Field.* q = x⁵ − 5x³ + 4x − 1. It is irreducible with 5 real roots. Its discriminant is 38569, a
  prime. Cycle types 5 and (2,3) occur (mod 3 and mod 19), so Gal = S₅.
- *Forms.*
  - With τ = β, the plane construction of §4.1 over 89 directions w gave 32 rational positive-definite
    forms.
  - The four used, as (b₁₁, b₁₂, b₂₂), were (4, 5/2, 9/4), (49/4, 3, 5), (41/4, 27/4, 101/4) and
    (105/16, 67/16, 73/16).
  - The matching ρ_j are 1/2 + 3β − 3β² − β³ + β⁴, 1 + 9β/2 − 2β² − β³,
    −11/2 + 7β/2 − 2β² − 2β³ + β⁴ and −9/4 + 11β/4 − 2β² − β³ + β⁴. All ρ_j² − Q_j(β) ≡ 0 mod q
    exactly.
- *Linear system.* The 5×6 ℚ-system has a 1-dimensional kernel:
  - a = −16065865961025768/8747550174256193;
  - c′ = 250788322040186689/34990200697024772.
- *Read-out.* X ∈ K has an irreducible quintic minimal polynomial with distinct real conjugates
  −0.1149, 2.3098, −4.3703, −4.7703, 8.1897. So the gcd recovery is linear at every root.
- *Drawing.*
  - Base: parabola (t, t²/(4a)). Then A₁ = P₁⁻¹, A_j = P_j⁻¹P_{j−1}, A₅ = P₄, with P_j = Cholesky(B_j).
    The four offsets use `unitNormal` by 600-digit central differences.
  - For each real root i, some sign pattern of (d_j) = (±δ_j) puts the final curve at the predicted
    point (X(β_i), −c′), at base parameter t = 2aβ_i, to within 10⁻⁵⁰–10⁻⁵³. The patterns, root by
    root: (−,+,−,−), (+,+,+,+), (−,+,+,+), (−,+,−,−), (−,+,+,−).
  - All partial radii r_k(β_i) are nonzero (|r| ≥ 1.4), so (ND1) holds.
- This checks Prop. T, Theorem R and the realness claim on a totally real field.

**n = 9.**
- *Field.* q = ∏_{i=−4}^{4}(x − i) + 1. It is irreducible and totally real, with nonsquare
  discriminant.
- *Galois group S₉ [Proof from the cycle types].*
  - A (1,1,7) element cannot act on 3 blocks of size 3, so the group is primitive.
  - A (4,5) element's 4th power is a 5-cycle, and 5 ≤ n − 3, so Jordan's theorem gives ⊇ A₉.
- *Search.* With τ = β, w ranged over 15625 directions of height ≤ 2 in ⟨x²..x⁸⟩. **No point of V_τ(ℚ)
  off ℓ_τ was found.**
- *Harness check.* At n = 5 the same code finds a point for 46 of 49 directions.

**n = 10.**
- *Fields.* W1's triangular decic ∏(x − a) + 7x + 3 (totally real, S₁₀) and H5's
  x¹⁰ − 10x⁸ + 35x⁶ − 50x⁴ + 25x² − x − 3.
- *Search.* 2187 height-1 directions each: no point.
- **No n = 10 hit.** This is consistent with V_τ being of general type with K = O(4). It is not a
  negative: only a small box was searched, for a single τ, over L = ℚ.

## 6. Verdict

**Proved.**
- Prop. T: normal-slope tower formula with signs, cusps, orientation and non-convex bases.
- The operator D_ℓ and the linear-unknown count (J + 2).
- Theorem R: SS_{n−1} plus (ND1, ND2) ⟹ β₁ ∈ P, with realness free.
- Lemma S1 and the rational-distance form.
- The geometry of V_τ: a smooth complete intersection of diagonal quadrics, K = O(n−6), unique line.
- The genus of C_B.
- The class decomposition, which closes the X1 loopholes.
- The route for n ≤ 5, unconditionally; this is not new.

**Conditional.** Nothing beyond SS_{n−1} is needed: Theorem R is unconditional *given* the
squares.

**Open.**
- **SS_{n−1}(K):** τ ∈ K_L and n − 1 distinct nondegenerate L-points of V_τ in the positive-definite
  region, for each K of degree n ≥ 9 (≥ 7 for the route itself). Equivalently: K_L-points with
  primitive τ on a genus-(1 + 2^{n−2}(n−3)) curve C_B, for *some* B.
- The specific question that would unlock it: does V_τ, for suitable τ, contain an L-curve of genus
  0 or 1 other than ℓ_τ, or is there a family of B with explicit K_L-points?
- At n = 6 the K3 case is interesting but already covered by the degree-8 theorem.

**Scope.** All of the above concerns the linear crossing of an offset tower with a line, with parabola
or ellipse bases. Circle and other partners are quadratic and lie outside it. No statement is made
about the target.

## Other things noticed

- **Two corrections to the setup.**
  - The parabola contributes one linear unknown, not "base parameters" in the plural: D_ℓ kills the
    linear part of h.
  - "Nonsingular system" is not needed. Dependence is automatic at J = n − 1, and the right
    nondegeneracy conditions are (ND1, ND2).
- The rational-distance picture (§3) ties this route to classical problems: points at rational distance
  from many points, and Euler's "all shifts square". For three squares it is exactly elliptic halving.
- Cholesky shows only B_j matters. A layer and its "conformal" neighbour merge because proportional B
  give proportional √Q, which matches G2/W1.
- Radii of curvature add along the tower (r_k is a partial sum). So cusps are predictable in closed
  form, which makes the drawing side easy to formalise once squares exist.
- In the n = 5 test the sign pattern needed differs from root to root. This is expected: each target
  root is drawn separately, and the K-certificate is common to all of them.
