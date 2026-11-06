# N1a: realness certificates for real nonics with s = 3, 4 conjugate pairs, and a Lean breakdown

Stream N1a of `pptc/PLAN-algebraic.md`. Labels: [Proof] derived here by hand, [Wolfram] computed in
Wolfram (exact unless stated), [Heuristic], [Open]. All obstructions are scoped to the route they block.

## Findings summary

1. **The exact rational certificate was NOT found.** No configuration was found in which all eight
   root steps of the chain below have rational centre roots. What was found instead (all [Wolfram]
   unless marked):
   - a precise 8-step chain, every step a real root of a polynomial of degree <= 6 (section 1);
   - a clean reformulation that explains where rational pencil roots come from and removes the need
   to formalize any signature (section 2) [Proof];
   - explicit rational centre data for the first three steps for both s = 3 and s = 4 (section 3), with
   the rank-4 pencil member of signature (2,2);
   - two concrete obstructions to completing a fully rational centre, each scoped to its sub-route
   (section 4): the quaternary discriminant is never a square in ~80 candidates, and the "pairing
   line" centre makes the conic sextic degenerate (a triple root);
   - a list of concrete next attempts, with what each would need (section 5).
2. **Lemma C transfers, but not verbatim** (section 6). The existing `exists_chain_roots_local` is
   hard-wired to four steps over `ChainYInputs`, and `exists_open_good_of_centre` is `private`. The
   nonic needs an abstract k-step version (statement given). The (2,2) signature condition need not be
   formalized: it is implied by the real-root sign changes of steps R4-R6.
3. **Density transfers with one new ingredient** (section 6): the root-value map `T_q : b -> z` for
   q with nonreal roots, in place of `yvec`.
4. **Lean breakdown** (section 7): 9 files under `Pptc/NonicReal/`, critical path marked. The
   certificate file(s) are the only blocked part; everything else can start now.

---

## 1. The chain (design) [Proof of algebra; realness is the certificate's job]

Work in root-value coordinates z in R^9 (THREE-PAIRS section 6): r = 9-2s real coordinates and s pairs
(u_l, v_l) for u_l + i v_l. p_k(z) = sum y^k + 2 sum Re (u+iv)^k. Fix inputs that are vectors in
V = {p_1 = 0}. Write B for the polar of p_2, Q(x) = p_2(x), C for the polarization of p_3.

| step | unknown | equation | degree |
|---|---|---|---|
| R1 | lam0 | p_2(u1 + lam0 u2) = 0, call it q0 | 2 |
| R2 | t1 | p_3(P0(t1)) = 0 where P0(t) = q0 - (2B(q0,d)/B(d,d)) d, d = t w1 + w3 (cleared: sextic) | 6 |
| R3 | lam* | det of Q + lam*C_2 on W = N/P0 (5x5) = 0 | 5 |
| R4 | s1 | M(r1) = 0, r1 = Te1 + s1 Te2, M = Q + lam* C_2 | 2 |
| R5 | s2 | M(r2) = 0, r2 = f1 + s2 f2, f_i in the M-tangent space of r1 | 2 |
| R6 | s3 | Q(x0) = 0, x0 = r1 + s3 kappa (kappa = kernel vector of M) | 2 |
| R7 | t2 | p_3(x(t2)) = 0, x(t) = x0 - (2B(x0,d)/B(d,d)) d, d = t kappa + r2 | 6 |
| R8 | tau | p_4(P0 + tau x) = 0 | 4 |

Here N = {x : p_1(x) = B(P0,x) = C(P0,P0,x) = 0} (6-dim, contains P0), W = N/P0, C_2(x) = C(P0,x,x),
and T is the projection onto N along two input vectors g1, g2 (a 2x2 Cramer solve, the analogue of
`chainProjN`). Inputs: u1,u2,w1,w3,e1..e5,g1,g2 (11 vectors in V, reusing e_i for the tangent step).

Why it works [Proof]:
- After R1, R2: p_1 = p_2 = p_3 = 0 at P0 (second intersection of a line with the cone p_2 = 0 is on the cone).
- Q and C_2 are well defined on W (shown by expanding at x + cP0 using B(P0,x) = C(P0,P0,x) = 0, p_2(P0) = p_3(P0) = 0).
- kappa spans the kernel of M on W; M(kappa,.) = 0 and M(r1) = M(r1,r2) = M(r2) = 0 give M == 0 on
  Pi = span(kappa, r1, r2).
- On Pi, Q = -lam* C_2. So Q(x) = 0 forces C_2(x) = 0 (needs lam* != 0, an open condition).
- With R7 giving p_3(x) = 0, the whole line P0 + tau x lies in {p_1 = p_2 = p_3 = 0}, by
  p_2(P+tau x) = p_2(P) + 2 tau B(P,x) + tau^2 Q(x) and
  p_3(P+tau x) = p_3(P) + 3 tau C(P,P,x) + 3 tau^2 C(P,x,x) + tau^3 p_3(x).
- R8 then gives p_4 = 0. Nonvanishing phi = P0 + tau x (open: x not parallel to P0).

This differs from THREE-PAIRS 2(c) only in replacing "diagonalize to X1^2+X2^2-X3^2-X4^2 and pick a
rational mu" by the two quadratic steps R4, R5 (a point on the cone, then a line through it). The
reason: a diagonalization needs square roots of positive numbers, which would become extra chain steps
anyway; R4, R5 are already of the form certified by sign change.

**[Open]** R4-R6 need real roots for the chosen inputs. In a random-input numerical trial the R5
quadratic had complex roots (discriminant < 0), so inputs must be chosen, not random; this is exactly
what a centre certificate does.

## 2. Structural facts that shaped the search [Proof]

**Pencil determinant = a derivative.** Put E(lam) = prod_j (1 + lam phi_j) over the 9 root values phi of
P0 (complex pairs included). In root coordinates M_lam(x) = sum_j (1 + lam phi_j) x_j^2 (a twisted
trace form) and N = {sum phi_j^k x_j = 0, k = 0,1,2}. A Hankel argument gives that M_lam has corank 2 on N
exactly when sum_j phi_j/(1 + lam phi_j) = 0, i.e. E'(lam) = 0. Since p_1 = p_2 = p_3 = 0 means
e_1 = e_2 = e_3 = 0, E = 1 + e_4 lam^4 + ... + e_9 lam^9 and
E'(lam) = lam^3 (4e_4 + 5e_5 lam + 6e_6 lam^2 + 7e_7 lam^3 + 8e_8 lam^4 + 9e_9 lam^5).
The quintic of R3 is the second factor. [Wolfram] check: for P0 = (1,-1,0,-2,0,2,0,0,3) (s = 3) the
determinant is 15552 (2 lam - 1)(2 lam + 1)(24 lam^2 - 19), consistent with the even-quartic prediction.

**Rational pencil roots come from repeated root values.** E has a double root at -1/phi when phi occurs
twice among the phi_j, so E' has the rational root lam* = -1/phi. The cheap source is a pair with
v_l = 0 (then phi takes the real value u_l at both conjugate roots): lam* = -1/u_l and the kernel
vector is e_{v_l}. A real coordinate repeated twice works the same way (kernel e_a - e_b).

**No signature formalization is needed.** The (2,2) signature of the singular member is only used to
guarantee real isotropic points; that is exactly what the real roots of R4, R5, R6 certify. The
remaining non-degeneracy is a finite list of nonvanishing conditions (kappa != 0 and well defined,
r2 not in span(kappa,r1), lam* != 0, the Cramer determinants, B(d,d) != 0).

**Degrees are all <= 6**, so `root_Pconstructible_le_six_coeffs` is the only root engine needed, as in
THREE-PAIRS section 2.

## 3. Exact rational data found [Wolfram]

Rational points of {p_1 = p_2 = p_3 = 0} with v_1 = 0 (so lam* = -1/u_1 is a pencil root, kernel
e_{v_1}). Coordinates are listed in the order (y_1,y_2,y_3, u_1,v_1, u_2,v_2, u_3,v_3).

s = 3 (r = 3), found by a search over y in [-6,6], u1 in [1,6], u2 in [-6,6] with u3 from p_1 and v_2^2,
v_3^2 from the two linear equations in (v_2^2, v_3^2) given by p_2, p_3:
(-6,-5,3,2,0,-5,8,7,7), (-6,-4,4,3,0,-1,6,1,3), (-6,1,5,3,0,-6,6,3,7), (-5,-1,6,2,0,-3,3,1,6),
(-2,-1,3,1,0,-2,2,1,3), (-1,2,3,1,0,-3,1,0,4), and the swapped-pair variants. 13 in this box.

s = 4 (r = 1), coordinates (y, u_1,v_1, u_2,v_2, u_3,v_3, u_4,v_4), 68 in the box
u in [-6,6], w = |v_4| in [1,14]:
(-2,1,0,-2,2,1,2,1,1), (-2,1,0,-2,2,1,1,1,2), (-2,2,0,-2,1,0,3,1,1), (-4,2,0,-1,3,0,2,1,1),
(-6,3,0,-2,4,-1,4,3,3), (-12,4,0,-3,7,-1,9,6,2), and others.

Example, s = 3, P0 = (-6,-5,3,2,0,-5,8,7,7). [Wolfram, exact]
- Pencil determinant: -313456656384 (1+2 lam)(6733 - 62491 lam - 235543 lam^2 + 1364811 lam^3 + 3532410 lam^4).
- Five real roots: -0.5 (rational), -0.41876, -0.25119, 0.09724, 0.18635 (numeric).
- Signature of M on N/(P0) (eigenvalue signs, floating point): lam = -0.5, -0.41876, 0.18635 give (2,2);
  lam = -0.25119 and 0.09724 give (3,1). So three of five real members have signature (2,2) in this
  example; THREE-PAIRS section 4 reports "exactly one" for its 6 random pencils. These are different
  samples, so no contradiction, but the "exactly one" statement should not be relied on.
- At the rational root lam* = -1/2 the kernel is e_{v_1} and the 4-dim quotient form has signature (2,2).

Both s = 3 and s = 4 therefore have rational centres through R3 with a (2,2) member at a rational root.
Counts for the (2,2) property at lam* = -1/u_1, on the 13 / 68 candidates above: most have
(2 negative, 2 null) eigenvalues on N (the null space is P0 and kappa), as needed.

## 4. Obstructions found (scoped to their routes)

**O1. Quaternary discriminant never a square [Wolfram]: obstructs the "all-rational R4-R6" route.**
For r1 to lie on a *rational* line of the cone one needs the rank-4 form M on N/(P0,kappa) to have a
square discriminant (then the two rulings and the lines through any rational point are rational).
- On all 80+ candidates above (s = 3: the 13 listed, s = 4: all 68), the discriminant was not a rational
  square.
- For the one-parameter pairing family P0 = (m^2-2n^2, -(m^2-2n^2), 0, 2mn, 0, -2mn, 0, 0, m^2+2n^2)
  (s = 3, a point of the cone y^2 + 2u^2 = z^2 with v_1 = v_2 = 0), lam* = -1/(2mn), the discriminant is,
  modulo squares, d(m,n) = m^8 - 56 m^4 n^4 + 16 n^8 = F^2 - 48 k^2 type [Wolfram, symbolic].
  d is a square only on a high-genus curve in (m^4, n^4); no small point exists (searched m,n <= 14).
- This does not show a rational centre is impossible. It shows that *these* families give lines on the
  cone defined only over Q(sqrt d), e.g. for (m,n) = (3,1), d = 2041 = 13 * 157.

**O2. The pairing-line centre is degenerate at R7 [Wolfram]: obstructs "x* in the iota-fixed plane".**
For a rational pairing line L inside the iota-fixed subspace Sigma (P0 and x* both fixed by the involution
that negates and swaps coordinates), p_1 and p_3 vanish identically on Sigma, and the rational line is
cheap to produce (3918 b's for P0 = (7,-7,0,4,0,-4,0,0,9), 1109 for P0 = (7,-7,0,6,0,-6,0,0,11)).
But with P0 = (7,-7,0,6,0,-6,0,0,11), lam* = -1/6, x* = (1,-1,0,-29,19,29,-19,0,-31), kappa = e_{v_1}
and r2 = f1 + s2 f2 with s2 = (-5993 - 147 sqrt 2041)/377904, the R7 polynomial has degree 5 and its only
real root is t0 = -107.89... with **multiplicity 3** (other roots +-57.01 i). Triple root means no sign
change, so this centre does not certify R7. Also the pencil determinant is even in lam there (degree 4,
roots +-1/6 and +-sqrt(...)), and p_1 = p_3 = 0 is automatic on Sigma, which is the cause.

**O3. A rational point x\* on the curve {Q = C_2 = p_3 = 0} through a generic rational P0 was not
found by search.** This is the degree-12 curve of THREE-PAIRS 2(b); rational points on it need
structure (a rational line in {p_2 = p_3 = 0}). Without symmetry none was found.

## 5. Next attempts, in order of expected value [Open]

1. **Q(sqrt d) centre (accept one quadratic irrationality).** Choose P0 with v_1 = 0 from section 3.
   Let a non-pairing rational line be supplied by (3) below; then R5 introduces s2 in Q(sqrt d) and
   R7's t0 = -B(x0,r2)/B(x0,kappa) in Q(sqrt d). Sign changes are evaluated at *rational* t0 +- delta
   (as in O2, `s2` enters through `a + b sqrt d` and the sign is decided by a rational bound on sqrt d),
   and R8 is evaluated at rational x*. Lean cost: a helper file `QuadSqrt.lean` (sign of a + b sqrt d).
2. **Robust last step.** If R7's root is irrational but isolated in a rational interval [t1,t2], R8 only
   needs p_4(P0 + tau_pm x(t)) of opposite fixed signs for all t in [t1,t2] at two fixed rational tau_pm:
   a one-variable polynomial inequality on an interval, provable in Lean (Taylor or Sturm style).
3. **Rational non-pairing lines.** Search for pairs (P0, phi*) with all mixed moments of order <= 3 of the
   nine points (P0_j, phi*_j) in the plane vanishing and p_4(phi*) = 0, using a 3-fold or other
   sub-symmetry (not the ones in O2). Counting: after fixing P0 the equations are linear in x on N,
   quadratic for Q and C_2, cubic for p_3.
4. **Different repeated-value patterns** to make M diagonal (so every pencil root is rational and the
   quaternary form splits into 1-dim blocks): P0 with y_1 = y_2, v_1 = v_2 = 0 and w_1 = w_2. The
   resulting one-parameter family reduces to the plane cubic
   10U^3 + 26U^2 u + 16 U u^2 + 4u^3 + 16 U^2 Y + 24 U u Y + 8 u^2 Y + 8 U Y^2 + 7 u Y^2 + Y^3 = 0
   (where u = u_3, Y = y_1) [Wolfram]. No integer point with |U|,|u| <= 30, |Y| <= 60 was found.
5. **Interval (box) certificate fallback.** `exists_chain_roots_at_centre` already takes box-uniform sign
   hypotheses, so a rational non-root centre with certified margins also feeds Lemma C. The cost is
   proving polynomial sign claims over boxes in Lean; this is the worst option for a 9-dimensional,
   eight-step chain.

Reproduction snippets: all searches are the loops described in section 3 (solve p_1 for the last
coordinate, p_2 and p_3 as a linear system in v^2, then require rational squares); pencil, signature and
tangent-plane computations use `NullSpace` of the three gradient rows at P0, the 6x6 Gram of M on that
basis, and `Eigenvalues`.

## 6. How Lemma C and density transfer

### 6.1 Chain openness

`Pconstructible.exists_nhds_forall_lt_of_continuousAt` and `exists_nhds_forall_ne`
(`TotallyReal/OpenTube.lean`) and `exists_zero_of_sign_change_on`, `signChange_of_simpleRoot`
(`SignChange.lean`) are dimension-free and reusable.

Not reusable: `exists_chain_roots_local` (`Certificate.lean:606`) is stated for the four fixed step
functions over `ChainYInputs n = (Fin n -> R)^6`, and `exists_open_good_of_centre` (`:2064`) is
`private`. Needed: an abstract k-step version.

```lean
theorem chain_local {E : Type*} [TopologicalSpace E] (k : ℕ)
    (F : (i : Fin k) → E → (Fin i → ℝ) → ℝ → ℝ)          -- step i: input, earlier roots, own variable
    (D : (i : Fin k) → E → (Fin i → ℝ) → Prop)             -- open pole conditions (denominators != 0)
    (e₀ : E) (c : Fin k → ℝ) (ε : Fin k → ℝ) (hε : ∀ i, 0 < ε i)
    (hcont : ∀ i, ContinuousAt (fun p : E × (Fin i → ℝ) × ℝ => F i p.1 p.2.1 p.2.2) ...)
    (hD : ∀ i, D i e₀ (fun j => c (j.castLT ...)))
    (hsign : ∀ i, ∀ δ, 0 < δ → δ < ε i →
        F i e₀ (c ∘ castLE) (c i - δ) * F i e₀ (c ∘ castLE) (c i + δ) < 0) :
    ∃ U ∈ 𝓝 e₀, ∀ e ∈ U, ∃ x : Fin k → ℝ, (∀ i, |x i - c i| < ε i) ∧
        (∀ i, F i e (x ∘ castLE) (x i) = 0) ∧ (∀ i, D i e (x ∘ castLE))
```

Proof plan: induction on k via `Fin.snoc`, each step using the tube lemma
(`IsCompact.eventually_forall_of_forall_eventually`, as in `exists_nhds_forall_lt_of_continuousAt`) to make the
endpoint sign changes uniform over the earlier roots, then `intermediate_value_Icc`. This is the same
proof as `exists_chain_roots_local`, with the four steps replaced by an induction.
Estimated 300-500 lines. Pole conditions: R2 (B(d,d)), the Cramer 2x2 determinants, R4/R5
tangent normalisations, R7 (B(d,d)). The step functions R1-R8 are polynomial in the inputs once
the denominators are cleared (`chainStep3Cleared` pattern).

A fully rational centre makes every `hsign` a `norm_num` over Q (9-vectors, bounded degree).
A Q(sqrt d) centre makes the R5-R7 hypotheses use `Real.sqrt`; see 5.1.

### 6.2 What the certificate must supply (for each s in {3,4})

- the 11 input vectors in Q^9 (each in V: p_1 = 0);
- centre roots c_1..c_8 and radii eps_i, with the 8 sign-change inequalities of `hsign` (exact rational);
- the pole values (Cramer determinants, B(d,d), kappa != 0 as an explicit 9-vector, lam* != 0);
- the output distinctness: only phi != 0 (not "pairwise distinct entries", which TotallyReal needed
  for the odd engine).

### 6.3 Density

`exists_PC_inputs_s1` (`Certificate.lean:3307`) is stated for six slots and `ChainBtoY αs` with real
roots. Needed: the same for 11 slots, with `T_q` replacing `yvec αs`:

```lean
-- root-value map for q with r real roots and s conjugate pairs
def zvec (q : ℝ[X]) (r s : ℕ) (h : r + 2*s = 9) : (Fin 9 → ℝ) →ₗ[ℝ] (Fin 9 → ℝ)
theorem zvec_bijective (hsep : q.Separable) : Function.Bijective (zvec q r s h)
theorem trace_pow_eq (b) (k) : Matrix.trace (aeval (companionN q) (bPoly b) ^ k)
    = P r s k (zvec q r s h b)         -- P r s k z = Σ y^k + 2 Σ Re (u+iv)^k
```

then `T_q^{-1}(U)` is open, `Q^9` is dense, and each input is corrected by subtracting its trace/9 times
the constant polynomial 1 (this is `correctSlot`). Estimated 400 lines, mostly adapting the YSpace
density argument; the new part is the real structure of the root list.

## 7. Lean breakdown: new files under `Pptc/NonicReal/`

Names confirmed by `rg` in the repo (2026-11-04). Reuse list:
`root_Pconstructible_le_six_coeffs` (Basic:1375), `powerLaw_cubic_root_Pconstructible (n := 9)`
(Basic:976), `quarticGraph_general_PConstructibleCurve` and `powerLaw_quartic_root_PConstructible`
(`Octic/Engine.lean:51,140`), `charpoly_aeval_companionN_coeff_Pconstructible`
(`TotallyReal/YSpace:353`), `companionN_charpoly_aeval_isRoot` (YSpace:168), `companionN'_trace_pow`
(YSpace:189), `esymm_one_eq_sum'`, `two_mul_esymm_two'`, `three_mul_esymm_three'` (Newton), `psumY` (YSpace:437),
`binary_cubic_zero` (DegreeSeven:1416), `exists_rat_vec_pos` (DegreeSeven:2641),
`root_Pconstructible_deg8_coeffs` (`Octic/Main.lean:110`), `exists_nonreal_root_of_not_splits`
(`TotallyReal/Main:158`), `root_Pconstructible_of_nonSeparable_eight` (Main:434).

| file | content | depends on | effort |
|---|---|---|---|
| `Engine9.lean` | `powerLaw_quartic_root_PConstructible9 : β^9 = quarticVal c₀..c₄ β -> PConstructible β`. Reflection for odd n is `(c₀,c₁,c₂,c₃,c₄) ↦ (-c₀, c₁, -c₂, c₃, -c₄)` (since `(-β)^9 = -β^9`), different from the octic `(c₀,-c₁,c₂,-c₃,c₄)`. `c₄ = 0` case is `powerLaw_cubic_root_Pconstructible (n := 9)`. | Octic.Engine | 0.5 day |
| `Resolvent9.lean` | `charpoly_aeval_coeff_8_7_6_5_eq_zero` (new `four_mul_esymm_four'` Newton lemma), `resolvent_quarticPowerLaw9`, `root_Pconstructible_of_tschirnhaus9`: from φ with Tr φ^k = 0 for k=1..4 and φ nonconstant, β is a root of the octic φ - φ(β), apply `root_Pconstructible_deg8_coeffs`. | Engine9, Octic.Main, Newton | 1 day |
| `RootsSplit9.lean` | from q monic separable of degree 9 with a nonreal root: split `q.roots` into r real roots and s conjugate pairs; prove s ∈ {1,2,3,4}, case `s ≥ 3` gives (r,s) ∈ {(3,3),(1,4)}; build the enumeration used by `zvec`. | TotallyReal.Main (`roots_eq_pair_add_real`-style lemmas, port to n=9) | 1.5 days |
| `ZCoords.lean` | `zvec`, `zvec_bijective`, `trace_pow_eq`; forms `p_k`, `B`, `C` on z-space and as polynomials in b with PC coefficients. | RootsSplit9, YSpace | 2-3 days |
| `Chain9.lean` | the eight step functions in z-space, `Chain9Good`, algebra lemmas (line lies in {p₁=p₂=p₃=0}, M vanishes on Pi, Q = -lam C₂ on Pi, W-quotient well defined), b-lift `chain9BLift_zvec`, step polynomials with PC coefficients (`exists_stepR_poly`, 8 of them, degree ≤ 6) and `stepRoots9_Pconstructible`. **Largest file; split into `Chain9Defs`, `Chain9Algebra`, `Chain9Poly`.** | ZCoords, Certificate (patterns) | 8-12 days |
| `ChainOpen.lean` | `chain_local` (6.1), generic and dimension-free. | OpenTube, SignChange | 3 days |
| `Density9.lean` | `exists_PC_inputs9` (6.3). | ZCoords, Chain9 | 3 days |
| `Certificate3.lean`, `Certificate4.lean` | centre data, `chain9_centre_signs`, `exists_open_good93/94`. **Blocked on the rational centre (section 5).** Each is 500-1500 lines of `norm_num` over Q^9. | ChainOpen, Chain9 | 5-10 days each after the data exist |
| `Main.lean` | `exists_tschirnhaus_nonic_three_pairs`, then `root_Pconstructible_nonic_three_pairs` for q with s ≥ 3, with the same case split as `root_Pconstructible_deg8_coeffs` (non-separable via gcd, as in `root_Pconstructible_of_nonSeparable_eight`; degree < 9 by `deg8`). | all | 2 days |

**Critical path:** RootsSplit9 -> ZCoords -> Chain9 (3 sub-files) -> Density9 -> Certificate3/4 -> Main.
`Engine9`, `Resolvent9`, `ChainOpen` are off the critical path and can run in parallel from day one.
Parallel workers: (A) Engine9 + Resolvent9, (B) ChainOpen, (C) RootsSplit9 + ZCoords, (D) Chain9 once ZCoords
exists, (E) the certificate search (sections 4-5), which is the long pole and does not need Lean.
Total without the certificate: about 3-4 weeks of worker time; the certificate files add 1-2 weeks once the data exist.

## Other things noticed

- The plan's claim "pencils with a real (2,2) member: 2 of 2" (THREE-PAIRS section 4) vs the 3-of-5 here:
  see section 3. [Wolfram, floating-point eigenvalue signs]
- The Wolfram MCP kernel keeps no state between calls and returns HTTP 504 after roughly 60 s. Searches
  with more than about 500k loop iterations must be split.
- `exists_open_good_of_centre` being `private` blocks reuse from outside `Certificate.lean`; if a worker
  prefers not to re-prove it, removing `private` is a one-word change, but that is an edit to an existing
  file and not part of this stream.
- For q with exactly r = 1 (s = 4), `V` has signature (4,4) and the Witt index is 4, so `s = 4` has the
  most slack for the real-root steps; `s = 3` has V of signature (5,3). Both gave real (2,2) members.
- The cheap source of rational structure (repeated root values) always forces a *non-generic* P0. Centres
  of this kind are legitimate for an openness certificate (the open set contains generic points) but they
  put the chain on symmetric loci where degeneracies like O2 appear; check simple-root conditions for each
  new family before investing in Lean data.
