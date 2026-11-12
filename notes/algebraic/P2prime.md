# P2′: finite abelian descent under solvable base change

Stream P2′ of `PLAN-algebraic.md`, Phase E-P (2026-11-12). Paper only: no `.lean` edits, no `Defs`
changes, no computation (nothing here needed one beyond one-line arithmetic; Wolfram was not
available in this session). Labels: [Proof], [Proof sketch], [Cited from memory] (reference not
re-opened in this session; verify before quoting), [Heuristic], [Open]. Every obstruction is scoped
to the route it blocks. Nothing here is a negative about `algebraic_Pconstructible`.

Notation as in P1′. β real algebraic of degree n ≥ 9, K = ℚ(β). L a real number field (σ₀: L ⊂ ℝ),
M ⊂ ℝ a finite extension of L containing β, d = [M:L]. For coprime p, q > 0 with p + q = d,
g_{p,q}(x) = x^p(1 − x)^q, Ĉ = Ĉ_{p,q} its Galois closure (a Belyi curve over ℚ with an S_d-action,
genus g), and

    X = X_L^{M,p,q} := the M-twist of Ĉ over L          (P1′ §4.2)

the canonical curve: its L-points off the three branch fibres are exactly the pp-engine solutions
for M (P1′ Theorem 2). J = Jac(X). For a number field k, 𝔸_k its adeles, X(𝔸_k)_• the adelic
points with each archimedean component replaced by its connected component (Stoll's convention),
X(𝔸_k)^{f-ab} the set surviving every finite abelian descent, X(𝔸_k)^{n-ab} the set surviving
descent by n-coverings.

## 0. Verdict

1. **Stoll's conjecture does not imply the target; it restates it (§2) [Proof].** Under the strong
   form X(𝔸_L)^{f-ab}_• = X(L) for these curves, (T_β; 𝓛) is *equivalent* to "for some L ∈ 𝓛, M,
   (p, q), the f-ab set of X_L^{M,p,q} contains a point off the three branch fibres". No
   unconditional technique proves non-emptiness of the f-ab set of a curve of genus ≥ 2 other than
   exhibiting a point, so the conditional statement has the same difficulty as the target.
2. **Local solubility is free in full, at every place (§3) [Proof sketch].** After a totally real
   solvable base change, X is locally soluble at every finite place; at real places it is soluble
   iff each real place of M over it is counted at most 3 times, which is uniform over the real
   places of L if the lift constant c is taken in ℚ. This corrects P1′'s "only σ₀ matters", which is
   true for drawability but not for the existence of an L-point.
3. **The plan's literal question has a negative answer (§4, Proposition B) [Proof].** For an adelic
   point x over k, base change to L ⊇ k can remove the abelian descent obstruction only if
   [L:k]·c(x) = 0, where c(x) is the class of x in the compact group ∏_v J(k_v)_• / \hat{Sel}(J/k).
   An adelic point whose class has infinite order stays obstructed over **every** finite extension,
   solvable or not. The proof is the norm on Selmer groups; nothing about solvability enters.
4. **Each odd level can be cleared by totally real solvable base change; all levels together cannot
   be cleared this way (§5) [Proof, given a rational degree-1 divisor class].** For each odd n there
   is a totally real solvable L_n with X(𝔸_{L_n})^{n-ab} ≠ ∅. The construction needs local degrees
   at small primes that grow like log n, and a number field has bounded local degrees. By
   compactness, X(𝔸_L)^{f-ab} ≠ ∅ iff every level is non-empty over the *same* L. That is exactly
   the uniformity the plan flagged, now located.
5. **The precise place (§6).** The obstruction splits into two layers:
   - **Layer 1 (cohomological):** the class of Pic¹_X in H¹(L, J) must vanish. This is a
     finite-period torsor class, the higher-genus version of the problem Ciperiani–Wiles solved in
     genus 1 by solvable base change. [Open; plausible; the only place base change can act.]
   - **Layer 2 (non-cohomological):** an adelic point must have Abel–Jacobi image in \hat{Sel}(J/L).
     If Sha(J/L) is finite, that set is the closure of J(L). This is a Chabauty / Mordell–Weil-sieve
     condition on the *position* of X(L_w) relative to a global group. Lemma LS chooses the fields
     L_w but says nothing about that position. Proposition B shows base change cannot move it for a
     fixed point. **This is where solvable base change cannot help.**
6. **Sub-questions (§7).** (a) Selmer sets grow in towers, but for a fixed adelic point growth is
   useless (Proposition B); the growth that matters is rank growth versus the Chabauty dimension
   g·[L:ℚ], and in totally real solvable towers ranks are expected, and in the model case known, to
   lag far behind [Heuristic; Cited]. (b) The conic gives nothing: over L it is ℙ¹, with no étale
   covers and constant Brauer group [Proof]. One prime ℓ is not easier: the ℓ-primary descent
   already contains the full ℓ-adic Chabauty problem [Proof sketch]. (c) Varying the member of the
   countable family does not change the logic: under Stoll each member is separately equivalent to
   having a point. The members' Jacobians are ρ-twists of a fixed finite list of abelian varieties
   over ℚ, which organises the question but gives no handle [Proof sketch; Heuristic].
7. **Kill criterion.** E-P's first half ("P2′ shows the obstruction cannot be removed by solvable
   base change for these curves") is **met in a scoped form**: removed for a fixed adelic point only
   in the torsion case (Proposition B), and level-by-level only with unbounded local degree (§5).
   It is not shown that no L ∈ R-solv has a non-empty f-ab set; that would be a negative about the
   target, which nothing here supports or claims.

## 1. Background used

- **Finite abelian descent [Cited from memory: M. Stoll, *Finite descent obstructions and rational
  points on curves*, Algebra & Number Theory 1 (2007) 349–391].** An n-covering of X is an étale
  cover Y → X that is a torsor under a finite abelian group scheme killed by n, geometrically a
  pull-back of [n]: J → J along an Abel–Jacobi map. X(𝔸_k)^{n-ab} is the set of adelic points that
  lift to some twist of every n-covering. These sets are closed in the compact space X(𝔸_k)_•, and
  decrease along divisibility of n, and X(𝔸_k)^{f-ab} = ⋂_n X(𝔸_k)^{n-ab}. For curves the f-ab set
  equals the Brauer set X(𝔸_k)^{Br}_• (as the plan states). Stoll's main conjecture:
  X(𝔸_k)^{f-ab}_• = X(k) (closure in X(𝔸_k)_•; X(k) is finite for g ≥ 2, so the closure is X(k)).
- **Selmer form [Cited from memory: Stoll 2007; the easy inclusion is proved in §4].** If D is a
  k-rational divisor of degree e ≥ 1 and ι_e(x) = [e·x − D] ∈ J, then
  ι_e(X(𝔸_k)^{f-ab}) ⊆ \hat{Sel}(J/k), where \hat{Sel}(J/k) = lim_n Sel^{(n)}(J/k), mapped into
  ∏_v J(k_v)_•. If Sha(J/k) has trivial divisible part, the image of \hat{Sel}(J/k) is the closure
  \overline{J(k)} of J(k) in ∏_v J(k_v)_•. With e = 1 the inclusion is an equality (Stoll).
- **Lemma LS, Lemma U (P1, P1′).** Totally real solvable base change can make any finite list of
  local fields appear as completions, and make M/L split completely above any finite set of primes.

## 2. What Stoll's conjecture buys

**Proposition 2.1 [Proof].** Fix a base class 𝓛 (P1′ §2). Suppose that, for every L ∈ 𝓛 and every
(M, p, q) in the family, X = X_L^{M,p,q} satisfies X(𝔸_L)^{f-ab}_• = X(L). Then (T_β; 𝓛) holds iff
there are L, M ∋ β, (p, q) such that X(𝔸_L)^{f-ab} contains a point outside the fibres over the
three branch values {0, ∞, λ*}.
- ⇒: an L-point off the branch fibres gives the engine solution (P1′ Theorem 2, form (I)), and
  global points survive every descent.
- ⇐: by hypothesis that adelic point is an L-point; off the branch fibres it is an engine solution.
- The branch fibres contribute finitely many L-points at most, all excluded.
- The real-place condition is automatic: an L-point gives τ ∈ M ⊂ ℝ, and the domain D_pp = ℝ ∖ {0, 1}
  excludes exactly the branch fibres over 0 and ∞ (P1′ Proposition 5.1). ∎

**Remark 2.2 (why this is not "Stoll ⇒ target").** The proposition replaces "X(L) has a good point"
by "X(𝔸_L)^{f-ab} has a good point" for some L. To use it one must show the f-ab set is non-empty
without a point. For curves of genus ≥ 2, every known non-emptiness proof exhibits a point; the
known theorems about f-ab sets go the other way (emptiness, e.g. by the Mordell–Weil sieve) [Heuristic
literature statement; Cited from memory: Stoll 2007 §§8–9; B. Poonen, *Heuristics for the
Brauer–Manin obstruction for curves*, Experiment. Math. 15 (2006)]. So the conjecture converts the
target into a statement of the same difficulty. The question becomes whether solvable base change
gives any unconditional purchase on non-emptiness. Sections 3–6 answer: on the local and
cohomological parts yes, on the part that matters no.

## 3. Everywhere local solubility

**Lemma 3.1 (finite places) [Proof sketch].** There is a totally real solvable L₀ such that for every
real solvable L ⊇ L₀ (and M ⊇ L(β) of the shape in P1′), X_L^{M,p,q}(L_w) ≠ ∅ for every finite
place w of L.
- Ĉ has good reduction outside the primes p ≤ d: a G-cover of ℙ¹ branched over three points with
  |G| = d! has good reduction at primes not dividing |G| (Beckmann) [Cited from memory]. Twisting
  by an unramified cocycle preserves good reduction.
- Let S be the primes ≤ d, the primes ramified in K, and the primes p with p ≤ 4g². Outside S, make
  M/L unramified (Lemma U). Then X has good reduction at w, and its reduction is a smooth
  geometrically connected curve of genus g over a field of size q_w ≥ p > 4g². The Weil bound
  gives q_w + 1 − 2g√q_w > 0 points, and Hensel lifts them.
- At w above S, Lemma U makes M/L split, so X_{L_w} ≅ Ĉ_{L_w}. Ĉ has a point over some number field
  F₀. Lemma LS gives a totally real solvable L₀ whose completions above S contain the completions
  of F₀. ∎

**Lemma 3.2 (real places) [Proof].** At a real place τ of L, X(L_τ) ≠ ∅ iff the number r_τ of real
places of M above τ is at most 3 (for coprime pp; P1′ Proposition 5.2), with r_τ ≡ d mod 2.
- An L-point needs real points at **every** real place of L, not only σ₀. P1′ §5 states the
  real-place condition for σ₀ alone. That is right for drawability, but it is not sufficient for the
  existence of the point, and an adelic point needs all real places.
- For M = L(β) with L totally real: r_τ is the number of real conjugates of β, the same at every τ
  (q ∈ ℚ[x]). For M = L(√(β − c)), take **c ∈ ℚ** strictly between the two largest real conjugates of
  β. Then r_τ = 2 at every real τ. With c ∈ L ∖ ℚ the value r_τ can differ between real places and
  can exceed 3 [Proof: r_τ = 2·#{real conjugates β_i > τ(c)}].
- With r_τ ≤ 3 everywhere, X(L_τ) is a non-empty real curve.

So X_L(𝔸_L) ≠ ∅ costs nothing beyond P1′'s choices, after the c ∈ ℚ adjustment. Every remaining
obstruction is global.

## 4. Base change of a fixed adelic point: Proposition B

Fix a number field k, X/k a curve, D a k-rational divisor of degree e ≥ 1 on X, ι_e as in §1. (The
twisted curves have such D with e | d!/lcm(2, pq, d) by the fibres over the branch values; the
exact index is not needed.) Write

    Q(J/k) := ∏_v J(k_v)_• / S(J/k),   S(J/k) := image of \hat{Sel}(J/k),

a compact abelian group, and c_e(x) ∈ Q(J/k) for the class of ι_e(x), x ∈ X(𝔸_k)_•.

**Lemma 4.1 (the easy inclusion) [Proof sketch].** If x ∈ X(𝔸_k)^{f-ab}, then c_e(x) = 0.
- For each n, pull back [n]: J → J along ι_e. This is an n-covering of X. Its twists are the
  pull-backs of the n-coverings J^ξ → J, ξ ∈ H¹(k, J[n]). If x lifts to the ξ-twist, then for each
  v the Kummer class of ι_e(x_v) in H¹(k_v, J[n]) is loc_v(ξ). So the image of ι_e(x) in
  ∏_v J(k_v)/n is the localisation of a Selmer element. Passing to the limit over n gives
  ι_e(x) ∈ S(J/k). ∎

**Proposition B [Proof].** Let L/k be finite and x ∈ X(𝔸_k)_•, with base change x_L ∈ X(𝔸_L)_•
(x_{L,w} = x_v for w | v). If x_L ∈ X(𝔸_L)^{f-ab}, then [L:k]·c_e(x) = 0 in Q(J/k).
- By Lemma 4.1 over L, ι_e(x_L) ∈ S(J/L) (the same D, base-changed).
- Corestriction cor_{L/k}: H¹(L, J[n]) → H¹(k, J[n]) maps Sel^{(n)}(J/L) into Sel^{(n)}(J/k). On local
  Kummer images it is the sum over w | v of the local norms N_{L_w/k_v}: J(L_w) → J(k_v). This is the
  standard compatibility of corestriction with Shapiro's lemma and the Kummer sequence. Passing to
  the limit, N_{L/k} := ∏_v Σ_{w|v} N_{L_w/k_v} maps S(J/L) into S(J/k).
- For a point P ∈ J(k_v), N_{L_w/k_v}(P) = [L_w:k_v]·P. Hence
  N_{L/k}(ι_e(x_L)) = ∏_v Σ_{w|v}[L_w:k_v]·ι_e(x_v) = [L:k]·ι_e(x).
- So [L:k]·ι_e(x) ∈ S(J/k), i.e. [L:k]·c_e(x) = 0. ∎

**Corollary B′ [Proof].** If c_e(x) has infinite order in Q(J/k), the base change of x is obstructed
over every finite extension of k. If c_e(x) has finite order m, it can become unobstructed only over
fields L with m | [L:k]. That condition is necessary, not sufficient.

**How often is c_e(x) torsion? [Heuristic].** c_e(x) is torsion iff m·ι_e(x) ∈ S(J/k) for some m,
i.e. ι_e(x) lies in the saturation of S(J/k). If Sha(J/k) is finite, S(J/k) = \overline{J(k)}, of
ℤ_p-rank ≤ rank J(k) at each p, inside ∏_{v|p} J(k_v) of ℤ_p-rank g·[k:ℚ]. The curve's image has
dimension [k:ℚ]. The saturation has the same dimension as \overline{J(k)}, so the torsion-class points
are cut out by the same Chabauty count as the unobstructed ones. Hence they are as rare as
unobstructed points. The plan's literal question, "is there L′ over which the base change of
(x_v) survives every descent", thus reduces to an f-ab-type condition over k with \hat{Sel} replaced
by its saturation. It is no easier.

## 5. One level at a time, and why the levels do not combine

**Lemma 5.1 (compactness and monotonicity) [Proof].**
- (i) X(𝔸_L)^{f-ab} ≠ ∅ iff X(𝔸_L)^{n-ab} ≠ ∅ for every n. The n-ab sets are closed in the compact
  space X(𝔸_L)_• and form a directed decreasing family (n | n′ ⇒ n′-ab ⊆ n-ab), so the finite
  intersection property applies.
- (ii) Suppose X has an L-rational divisor class of degree 1. If X(𝔸_L)^{n-ab} ≠ ∅ and L′ ⊇ L, then
  X(𝔸_{L′})^{n-ab} ≠ ∅. With a degree-1 class, every n-covering of X is dominated by a twist of
  the single covering Y = ι^{-1}([n]^{-1}ι(X)) (Stoll). If x lifts to the twist Y_ξ over L, then
  x_{L′} lifts to (Y_ξ)_{L′} = Y_{res ξ}, hence to a quotient of it for every n-covering over L′.
  [Proof for degree 1; the general case is Open, minor.]

So for each n the set U_n := {L ∈ 𝓛 : X(𝔸_L)^{n-ab} ≠ ∅} is upward closed, U_n ⊇ U_{n′} for
n | n′, and Stoll's conjecture makes (T_β; 𝓛) equivalent to ⋂_n U_n ≠ ∅ (for some member).
Non-emptiness of each U_n does not give a non-empty intersection: the compositum of L_n ∈ U_n over
all n is an infinite extension, and an infinite extension has no adeles.

**Proposition 5.2 (odd levels clear) [Proof sketch].** Suppose X has an L₁-rational divisor class of
degree 1 for some L₁ ∈ 𝓛, with ι = ι₁ defined over L₁, and real points at every real place (Lemma
3.2). For every odd n there is a totally real solvable M_n such that L_n := L₁M_n satisfies
X(𝔸_{L_n})^{n-ab} ≠ ∅.
- Let Y_n := ι^{-1}([n]^{-1}(ι(X))) → X, the untwisted n-covering. It is étale of degree n^{2g} and
  geometrically connected (π₁ of X surjects onto π₁ of J). Riemann–Hurwitz gives
  g(Y_n) = 1 + n^{2g}(g − 1).
- **Real places.** For n odd, multiplication by n is surjective on J(ℝ) ≅ (ℝ/ℤ)^g × (ℤ/2)^k. So every
  real point of X lifts to a real point of Y_n. (For n even this fails on the non-identity
  components; that is the only place where 2 is special.)
- **Finite places.** Apply Lemma 3.1's argument to the curve Y_n. Its bad primes are those of X
  together with the primes dividing n. The Weil threshold is now q_w > 4·g(Y_n)².
- So Y_n is everywhere locally soluble over L_n, and every adelic point of Y_n maps to an adelic
  point of X that lifts to the untwisted Y_n. With a degree-1 class every n-covering is dominated
  by a twist of Y_n (Lemma 5.1(ii)), so this point survives level n. ∎

**Where it stops.** The set of small primes in the proof is S_n ⊇ {p : p ≤ 4g(Y_n)²}, with
g(Y_n) ≈ n^{2g}g. At a prime p with p < 4g(Y_n)² the construction needs residue fields of size
q > 4g(Y_n)², so local degree f ≳ 2·log_p(2g(Y_n)) ≈ 4g·log_p n → ∞ as n → ∞. A single number field
has bounded local degrees at p. So the construction produces, for each level, a field that clears
that level, with local degrees forced to grow with the level. **One L cannot run this construction
for all n.** This is a statement about the construction (Weil-bound local solubility of the
untwisted covering), not a proof that ⋂ U_n is empty: a twisted covering Y_ξ may be locally soluble
over smaller fields, but choosing ξ is exactly the global Selmer problem of §6.

## 6. The two layers

Assume Sha(J/L) finite for the interpretation. (It is only needed to read \hat{Sel} as a closure.)

**Layer 1: the period.** X(𝔸_L)^{f-ab} ≠ ∅ implies that X has an L-rational divisor class of degree 1
[Cited from memory: Stoll 2007]. Equivalently, the torsor V = Pic¹_X has trivial class in H¹(L, J).
- This is cohomological. It is a class of finite period in a Weil–Châtelet group, and it is
  everywhere locally trivial once X is everywhere locally soluble (§3). So it lies in Sha(J/L), and
  base change acts on it by restriction.
- Precedent: in genus 1, X = V and Layer 1 is the whole problem. Ciperiani–Wiles show that a genus 1
  curve over ℚ with points everywhere locally has a point over a solvable extension [Cited from
  memory: M. Ciperiani, A. Wiles, *Solvable points on genus one curves*, Duke Math. J. 142 (2008)],
  by killing the Sha class with solvable base change. Whether the extension can be taken totally
  real, and whether the method extends to the Jacobians here, is [Open].
- Equivalent formulation [Cited from memory: S. Saito (1989), Colliot-Thélène (1999), under
  finiteness of Sha]: Layer 1 is the Hasse principle for 0-cycles of degree 1 on X, which the
  Brauer–Manin obstruction for 0-cycles controls.
- **Layer 1 is the only place in the problem where solvable base change has a known mechanism.**

**Layer 2: the Mordell–Weil sieve.** Given D of degree 1 over L, X(𝔸_L)^{f-ab}_• = ι^{-1}(S(J/L)),
and with Sha finite S(J/L) = \overline{J(L)}. So the condition is

    ∃ x ∈ X(𝔸_L)_•  with  ι(x) ∈ \overline{J(L)} ⊂ ∏_w J(L_w)_•.

- **Not cohomological.** \overline{J(L)} is a closed subgroup. Its quotient Q(J/L) has a large
  torsion-free ℤ_p part at every p. The condition places p-adic analytic points relative to a
  global group, not a class in H¹ of a finite module. Lemma LS fixes the isomorphism type of each
  L_w, and therefore of the local curve X(L_w). It does not touch where ι(X(L_w)) sits relative to
  \overline{J(L)}.
- **Base change does not move it for fixed points.** Proposition B.
- **Dimension count at one p [Heuristic; Cited from memory: S. Siksek, *Explicit Chabauty over number
  fields*, Algebra & Number Theory 7 (2013)].** In ∏_{w|p} J(L_w), of ℚ_p-dimension g·[L:ℚ], the
  closure of J(L) has dimension ≤ r_L := rank J(L), and ι(X(L ⊗ ℚ_p)) has dimension [L:ℚ]. The
  intersection is expected to be finite (rigid) whenever r_L ≤ (g − 1)·[L:ℚ]. In that range the
  f-ab set is expected to be exactly the global points (this is the mechanism behind Stoll's
  conjecture), and nothing forces it to be non-empty.
- **Ranks in solvable towers [Heuristic; model case Cited from memory].** For L/k Galois with group G,
  J(L) ⊗ ℂ = ⊕_ρ ρ^{m_ρ}, with m_ρ the rank of the ρ-twist. Under the minimalist and parity
  heuristics each simple isogeny factor A contributes 0 or [End⁰A : ℚ] per twist, and about half
  the twists are 0. So r_L ≲ (g/2)·Σ_ρ dim ρ ≤ (g/2)·[L:k]. That is below (g − 1)·[L:ℚ] for g ≥ 3,
  and here g ≥ 47881. In the model case, an elliptic curve over ℚ and the cyclotomic ℤ_p-tower
  (totally real, abelian), the rank stays **bounded** [Cited from memory: Kato (2004) with Rohrlich
  (1984)]. So the gap between r_L and the Chabauty dimension grows linearly in [L:ℚ] up the tower.
  Base change makes Layer 2 *more* rigid, not less.

**Summary of the place where base change cannot help.** Stoll's conjecture reduces the target to
Layer 1 + Layer 2 over some L ∈ 𝓛. Layer 1 is a Sha-type class; solvable base change is the known
tool for it (genus 1), and the higher-genus version is [Open]. Layer 2 is the Mordell–Weil sieve.
Its obstruction is the class c(x) ∈ Q(J/L), which (i) base change multiplies by the degree on fixed
points (Proposition B), (ii) can be cleared level by level only with local degree growing in the
level (§5), and (iii) sits in a quotient that grows with [L:ℚ] faster than the Mordell–Weil group
under standard heuristics. Lemma LS controls none of this. So the obstruction cannot be removed by
solvable base change **as a mechanism**: if a good L exists, it is because X_L happens to have a
point, and the obstruction framework gives no way to find it.

## 7. The three sub-questions

**(a) Selmer sets in solvable towers.** Sel^{(n)}(J/L) grows: restriction is injective modulo the
finite kernel H¹(Gal(L′/L), J[n](L′)), and new classes appear. For the *obstruction to a given
adelic point*, growth is irrelevant: Proposition B bounds it by the norm. For *new* adelic points
the relevant growth is that of \overline{J(L)} against g·[L:ℚ] (§6), expected to lose. [Proof for
the fixed-point part; Heuristic for the rest.]

**(b) The 2-part, one prime, and the conic.**
- **The conic contributes nothing [Proof].** The only abelian quotient of S_d (d ≥ 5) is ℤ/2, giving
  X → Ĉ/A_d, the twisted discriminant conic Q. Q has an L-point (P1′ §4.2), so Q ≅ ℙ¹_L. Then
  π₁^{ét}(Q_{L̄}) = 1 and Br(Q) = Br(L). Pulled back to X these give no covers and only constant
  Brauer classes, which pair to 0 with every adelic point (global reciprocity). Moreover X → Q is
  ramified (over λ* and one of 0, ∞), so it is not a descent object in any case. Every abelian
  covering of X comes from J[n]. That module has rank 2g (about 10⁵ at d = 9), and its torsion fields
have Galois group inside GSp_{2g}.
- **One prime ℓ is not easier [Proof sketch].** The ℓ-primary f-ab set is ι^{-1} of the closure of
  S(J/L) in ∏_w J(L_w) ⊗ ℤ_ℓ. At w ∤ ℓ that factor is finite, a finite cohomological condition.
  At w | ℓ it is ℤ_ℓ^{g[L_w:ℚ_ℓ]} × finite, which is the full ℓ-adic Chabauty problem of §6. So
  restricting to one prime keeps the hard part and drops only easy parts.
- **The 2-part is special only at the real places** (Proposition 5.2: odd levels have no real
  condition). That is the "one real place" feature of P1′ reappearing, not a source of leverage.

**(c) Varying the member [Proof sketch; Heuristic].**
- **Structure.** S_d acts on Ĉ over ℚ, and ℚ[S_d] = ∏_ρ M_{dim ρ}(ℚ) (all irreducible characters of
  S_d are rational). So Jac(Ĉ) ~ ∏_ρ B_ρ^{dim ρ} with B_ρ abelian varieties over ℚ that do not
  depend on L or M. The twist by the cocycle c: G_L → S_d of M/L gives
  J = Jac(X) ~ ∏_ρ B_ρ ⊗ ρ_c (tensor twist by the Galois lattice ρ∘c) [Proof sketch: twist
  commutes with the isotypic decomposition; cf. Milne 1972]. Hence
  rank J(L) = Σ_ρ ⟨ρ, B_ρ(N) ⊗ ℚ⟩_{Gal(N/L)}, N the Galois closure of M/L.
- **Pieces that vanish [Proof].** Trivial ρ: Ĉ/S_d = ℙ¹. Sign: Ĉ/A_d is genus 0 (P1′). Standard
  (dim d − 1): its multiplicity is g(Ĉ/S_{d−1}) − g(Ĉ/S_d) = 0 − 0, since Ĉ/S_{d−1} is the source ℙ¹
  of g_{p,q}. So the twist acts only through irreducibles other than 1, sign and the standard
  representation. Which of the rest (V ⊗ sign, (d − 2, 2), …) occur, and with which dim B_ρ, follows
  from Chevalley–Weil with the three branch cycles. That count was not done here [Open, mechanical].
- **Consequence.** All members (all L, M, and the same (p, q)) have Jacobians built from one finite
  list B_ρ over ℚ, twisted by S_d-representations. Under Stoll each member's f-ab set is its point
  set, so the family adds no obstruction-theoretic leverage. It helps only in counting heuristics,
  and those (Poonen 2006) give each member probability 0 of an unexplained surviving adelic point.
  Recorded as structure for P3′ (the refutation stream may use the B_ρ), not as a route.

## 8. Hand-off

- **To the plan.** E-P kill criterion, first half: met in the scoped sense of §0 item 7. If P3′
  finds no refutation mechanism, E-P ends as the plan says: the target is equivalent, conditional
  on Stoll, to the existence of points on an explicit countable family of twisted Belyi curves
  over real solvable fields, and solvable base change acts only on Layer 1.
- **To P5′ (Rumely / Moret-Bailly).** That approach produces points directly, bypassing descent. It
  is the right tool for Layer 2. P2′ does not make P5′ more or less likely to work.
- **To P3′.** Two inputs. (1) The B_ρ decomposition of §7(c): a refutation would have to see the
  twisted Mordell–Weil groups of the B_ρ over solvable fields. (2) Proposition B is unconditional
  and holds for every finite extension, so it cannot by itself separate solvable from non-solvable
  fields. A refutation needs something that does.
- **A correction to carry back to P1′ §5.** Existence of an L-point requires real points at every
  real place of L. Take the lift constant c ∈ ℚ (Lemma 3.2) so that the condition is uniform.
- **Open, minor.** Lemma 5.1(ii) for e > 1. The exact index of X over L (Layer 1's starting point).
  Whether Ciperiani–Wiles-type killing of Layer 1 works over totally real solvable fields for
  these Jacobians.
