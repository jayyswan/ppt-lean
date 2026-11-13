# P5′: Rumely–Moret-Bailly with a shape constraint

Stream P5′ of `PLAN-algebraic.md`, Phase E-P (2026-11-13). Literature reading, then paper
mathematics. No `.lean` edits, no `Defs` changes. Labels: [Proof], [Proof sketch], [Python]
(`scripts/P5prime_checks.py`; no Wolfram tools were attached in this session, so Python is the
plan's labelled fallback), [Cited from memory] (reference not re-opened in this session; verify
before quoting), [Heuristic], [Conditional on …], [Open]. Every obstruction is scoped to the route
it blocks. Nothing here is a negative about `algebraic_Pconstructible`.

Notation as in P1′ and P2′: β real algebraic of degree n ≥ 9, K = ℚ(β); engines tri(N), pp(p, q),
cheb(p, q), five(p, q) with universal cover Z_e → B_e (P1′ §1); for coprime p, q > 0,
g_{p,q} = x^p(1 − x)^q, N = p + q, and Ĉ_{p,q} its Galois closure. X denotes a curve over a number
field k with a smooth real point. An **e-field** over k is a field k(z₀) with z₀ a root of a member
f_{e,λ}, λ ∈ B_e(k) (overshoot allowed: k(z₀) may be a proper factor of the fibre algebra).

## 0. Verdict

**No.** The construction cannot be steered to a prescribed sparse fibre shape, except in cases
that were already solved. The step where control is lost is identified below.

1. **What the method is, for our purposes (§1) [Proof sketch].** Without integrality conditions
   (F has none), Rumely–Moret-Bailly reduces to three steps:
   - (S1) local functions f_v on X over k_v whose zero sets lie in prescribed open sets Ω_v;
   - (S2) **weak approximation** in a Riemann–Roch space, which gives one global f ∈ k(X);
   - (S3) optionally, Hilbert irreducibility in the pencil f − t.

   The output points are the zeros of f. Their residue field is an *output* of the method, and
   the method constrains it only by conditions that are open in ∏_{v∈S} X(k̄_v). Capacity theory
   and Fekete–Szegő patching are needed only for integrality, so they are not the lever here.
2. **Steering over all f is the problem itself (§2, Proposition 2.1) [Proof].** "Some f has a
   fibre over a rational t₀ that is an e-field" is equivalent to "X has a point over an e-field".
   Applied to P1′'s canonical curve X = (Ĉ_{p′,q′})^M, that is (T_β; 𝓛) for the class 𝓛 of
   one-step engine fields (two engine steps in all). RMB's freedom in f is exactly the freedom to
   choose a point, so a shape constraint does not reduce the problem; it restates it.
3. **The precise step: S2/S3, because the shape condition is not local once N ≥ 5 (§3).**
   - **[Proof]** For a degree-N field M, "M is a tri(N)-field" means a k-point on the twist by M
     of a fixed curve of genus 0, 0, 4, 49, 481, 4681, 47881 for N = 4, …, 10. These are the same
     curves as H1's Γ and P1′'s Ĉ ([Python]: the adjunction genus agrees with the Belyi genus for
     every N checked). For pp(p, q) the curve has genus ≥ 4 when N ≥ 5.
   - At N ≤ 4 the shape condition is local (Hasse–Minkowski) and RMB can steer it. But those
     degrees are solvable anyway.
   - At N ≥ 5 it is a point on a curve of genus ≥ 4 over the fibre field. Faltings bounds the
     number of shapes per field, and no S-adic open condition on f decides it.
   - **[Conditional on Bombieri–Lang]** The good t₀ for a given f are infinite only along a curve
     of genus ≤ 1 in the fibre-isomorphism surface. That is precisely an isomorphism
     correspondence between f and the engine, which is the object F2 studies.
4. **Generic shape is a high-codimension closed condition (§3.3) [Proof].** f has engine-shaped
   fibres for all t iff X → ℙ¹_t is (a component of) a pull-back of Z_e along some λ: ℙ¹_t → B_e.
   For pp, the pulled-back covers of degree N form a family of dimension 2m + 1 inside a Hurwitz
   space of dimension 2m(N − 1), so the codimension is 2m(N − 2) − 1 (≥ 11 at N = 5, m = 2).
   S2 picks f from an S-adic open set, so it lands in this locus only if aimed there, and aiming
   there is a purely geometric question about X that RMB does not touch.
5. **Real signature (§3.4) [Proof].** The textbook output (ℚ^{tr} is PRC) is totally real. A
   totally real field of degree ≥ 4 is never a tri- or pp-field, with or without overshoot,
   because those engines have real capacity ≤ 3 (P1′ §5). So for tri and pp one must use
   Moret-Bailly's general local conditions (r ≤ 3 at σ₀), never the PRC statement. Not an
   obstruction, but the PRC form is the wrong tool.
6. **The Chebyshev side (§4).**
   - **[Proof]** On ℙ¹ the archimedean model in Fekete–Szegő is T_N, and the fibre T_N = t₀
     (t₀ ∈ ℚ ∩ (−1, 1)) is a cheb member. So for genus 0 the method's natural output is drawable.
   - **[Proof]** For genus ≥ 1, a Chebyshev-type f = h ∘ φ factors through a rational curve
     (Lüroth). The shape of h governs only the bottom layer; the top layer is the fibre of φ over
     an h-fibre field, which is the same problem over a larger field.
   - The suggestion in the plan does not survive beyond genus 0.
7. **Galois type (§5).**
   - Moret-Bailly can force the group S_N [Cited from memory]. A solvable residue field needs an
     f with solvable monodromy, and Zariski (1926) rules this out for a *general* curve of genus
     > 6 [Cited from memory].
   - The engine analogue is "X is engine-resolvable over k": X is the top of a tower of pull-backs
     of engines. It is geometric and would imply β ∈ F.
   - **[Proof]** The untwisted Ĉ is resolvable by its own Galois-closure tower. That tower does
     not descend to the M-twist X, because its intermediate quotients are not defined over L.
   - **[Open]** Whether X has any other such tower.

**Deliverable, in the plan's terms.** Shape control is lost at the global step. In S2 the residue
field of the output is fixed only up to an S-adic open set of f. Being an e-field is a local
condition for N ≤ 4 (a conic) but, for N ≥ 5, a point on a curve of genus ≥ 4 over that field.
RMB passes freely from local to global for *points over some field*. It says nothing about
*which* field, and a shape constraint is a constraint on exactly that.

## 1. What Rumely and Moret-Bailly prove, and how

**Statements [Cited from memory].**
- R. Rumely, *Capacity Theory on Algebraic Curves*, LNM 1378 (1989), and *Capacity Theory with
  Local Rationality*, AMS Math. Surveys and Monographs 193 (2013): the Fekete–Szegő theorem on
  curves. If the adelic set E = ∏E_v ⊂ X has capacity > 1 relative to a k-rational set of poles,
  there are infinitely many points with all conjugates in E (integral at almost all v), and in
  the 2013 version with local rationality conditions at finitely many v.
- L. Moret-Bailly, *Groupes de Picard et problèmes de Skolem I, II*, Ann. Sci. ENS 22 (1989): for
  X/k geometrically irreducible, S finite, and non-empty Gal-stable open Ω_v ⊂ X(k̄_v) (v ∈ S),
  there are a finite L/k and x ∈ X(L) whose every k-embedding into k̄_v lands in Ω_v. Integral
  versions also exist. *Extensions de corps globaux à ramification et groupe de Galois donnés*,
  CRAS 311 (1990): moreover the Galois closure of L/k can be taken with group S_[L:k].
- Corollary (Moret-Bailly; Green–Pop–Roquette, Jber. DMV 97 (1995); Pop, Ann. Math. 144 (1996)):
  ℚ^{tr}, and more generally totally S-adic fields, are PRC/PSC.

**The no-integrality version, which is all F could use [Proof sketch].** Let D be a k-rational
effective divisor of large degree N on X.
- **(S1) Local step.** For v ∈ S choose f_v ∈ H⁰(X_{k_v}, O(D)) with N simple zeros, all in Ω_v.
  This is Moret-Bailly's local lemma: for N ≫ 0 the sums of N points of Ω_v cover an open set of
  Pic^N(k_v) meeting the class of D, possibly after enlarging D. At a real place it is a real
  function with N simple real zeros in the given arcs.
- **(S2) Global step.** H⁰(X, O(D)) is a k-vector space, so it is dense in
  ∏_{v∈S} H⁰(X_{k_v}, O(D)). "N simple zeros in Ω_v" is an open condition, so some global f
  satisfies it at every v ∈ S. Every closed point x of div₀(f) then has k(x) ⊗ k_v split
  according to Ω_v.
- **(S3) Optional step.** Replace f by f − t₀ with t₀ ∈ k close to 0 in every k_v (v ∈ S) and
  outside a thin set. The fibre is then one closed point of degree N whose Galois group is the
  monodromy group of f, generically S_N.

Capacity, Chebyshev/Fekete polynomials and Cantor–Rumely patching all serve to make the zeros
*integral* at the places outside S. F imposes no integrality, so for this programme the
capacity theory is redundant: weak approximation does S2.

## 2. What "steering the fibre shape" can mean

Fix an engine e. Three readings, from strongest to weakest:
- **(A) Generic shape.** k(X)/k(t) (t = f) is generated by a root of f_{e,λ(t)} with
  λ ∈ B_e(k(t)). Then every fibre off finitely many t₀ is an e-field.
- **(B) One fibre.** For some t₀ ∈ k, the fibre f^{-1}(t₀) contains a closed point whose residue
  field embeds in an e-field over k.
- **(C) Any point.** X has a point over an e-field over k.

Containment, not equality, is what drawability needs: a point over L ⊂ F suffices.

**Proposition 2.1 [Proof].** (B) for some f ∈ k(X) ⟺ (C).
- (B) ⇒ (C): the closed point gives a point of X over its residue field, hence over the e-field.
- (C) ⇒ (B): a point of X over an e-field L is a closed point x with k(x) ↪ L. By Riemann–Roch
  there is f ∈ k(X) with a simple zero at x. Take t₀ = 0. ∎

**Consequence.** Take X = (Ĉ_{p′,q′})^M over L₀, P1′'s canonical curve. Then (C) says K lies in
a two-step engine tower over L₀, which is (T_β; 𝓛) with 𝓛 the one-step engine fields over L₀.
That is a legitimate base class (it lies in F), but it is the problem itself one level up. RMB
contributes only the open local data of S1, which P1′ (Lemma U) and P2′ (§3) already showed are
free. So "can RMB be steered" really asks whether a shape constraint can be imposed by the
*local* steps. The answer depends on whether the shape condition is local, which §3 settles.

## 3. Where control is lost

### 3.1 The shape locus of one field [Proof; Python for the table]

For a degree-N étale algebra M over k, let Sh_e(M) be the variety of τ ∈ R_{M/k}𝔸¹ with
M = k(τ) and τ a root of a member of e (P1′ §4, form (I)). It is a twist by M of a variety over ℚ.
- **tri(N).** τ ↦ (power sums) shows that, up to the scaling τ ↦ μτ and translation, Sh_tri(M) is
  the twist by M of the complete intersection {p₂ = … = p_{N−2} = 0} in the trace-zero ℙ^{N−2}. Its
  degrees are 2, 3, …, N − 2, and adjunction gives 2g − 2 = (N − 2)!·(Σ_{i=2}^{N−2} i − N + 1).

  | N | 4 | 5 | 6 | 7 | 8 | 9 | 10 |
  |---|---|---|---|---|---|---|---|
  | genus | 0 | 4 | 49 | 481 | 4681 | 47881 | 524161 |

  This agrees with the genus of the Galois closure of the three-point map x^N/(1 − x)
  (P1′ §4.2, e₀ = N, e_∞ = N − 1) for every N in the table [Python]. So Sh_tri(M) is H1's Γ_M.
- **pp(p, q), coprime, p, q > 0.** Sh_pp(M) is the M-twist of Ĉ_{p,q}, a curve. Its genus is ≥ 4
  for N ≥ 5: 4 for (4,1), 9 for (3,2), 61489 for (5,4) [Python].
- **cheb(p, q).** There is no scaling symmetry, so Sh is a **surface** (codimension N − 2 in
  dimension N).
- **five(p, q).** Sh is a **fourfold** (four projective parameters, codimension N − 4).

### 3.2 Locality

- **N ≤ 4: local [Proof].** For N = 3, Sh_tri is ℙ¹, so there is no condition. For N = 4, Sh_tri(M)
  is the conic Tr(y²) = 0 in the trace-zero plane. Its points are governed by local conditions
  (Hasse–Minkowski), so S1 can impose them at the finitely many places where the conic could fail.
  Compare the capacity: if M is totally real, Tr(y²) is definite, so the conic has no real point
  and there is no trinomial generator. That is the capacity 2 of tri(4) (P1′ §5) seen from the
  shape side. These degrees are solvable, so nothing is gained.
- **N ≥ 5, tri and pp: not local.** The condition is a k-point on a curve of genus ≥ 4.
  - [Proof, given Faltings] For each fibre field M, finitely many λ realise it.
  - [Proof] By Proposition 2.1, deciding it for the fibre fields of f is the original problem.
  - [Heuristic] No S-adic open condition on f determines it, because these twisted curves fail the
    Hasse principle in general. Unconditionally, no member of this family is *known* to fail it.
    That is why this line is labelled heuristic: we have no proven non-e-field with given local
    data.
- **cheb, five: open.** Sh is a surface or a fourfold. If it were unirational over k whenever it
  has a smooth point, every M with the right real data would be a cheb-field directly, with no
  RMB involved. The surface case is Phase F's W-geometry (F1, F2), not P5′.

**The good-t₀ set, under Bombieri–Lang [Conditional].** For f: X → ℙ¹_t of degree N and a 1-parameter
engine (pp), let I_f = (X̂ ×_ℚ Ĉ)/S_N over ℙ¹_t × ℙ¹_λ (X̂ the Galois closure of f, S_N acting
diagonally). Then I_f(ℚ) is the set of pairs (t₀, λ₀) with isomorphic fibres.
- The fibre over t₀ is Sh_pp(f^{-1}(t₀)), of genus ≥ 4. So I_f is a surface fibred in curves of
  genus ≥ 2, presumably of general type.
- Bombieri–Lang puts I_f(ℚ) on finitely many curves of genus ≤ 1 plus a finite set.
- A genus-≤-1 curve Γ ⊂ I_f dominating ℙ¹_t is an **isomorphism correspondence**: maps
  t: Γ → ℙ¹, λ: Γ → ℙ¹ with t*f ≅ λ*g over ℚ̄(Γ). This is F2's object (Prop. 3.1 there), with one
  engine side replaced by f.
- So, conditionally, (B) holds for infinitely many t₀ only through such a correspondence. That
  is reading (A) after a base change along a curve of genus ≤ 1.

### 3.3 Generic shape is a closed condition of high codimension [Proof]

**Lemma 3.3 (pull-back criterion).** Reading (A) holds for f iff X is birational to a component
of W_λ := ℙ¹_t ×_{B_e} Z_e for some λ: ℙ¹_t → B_e. For pp this means X ⊂ {g_{p,q}(z) = λ(t)}.
- *Proof.* If ℚ(X) = ℚ(t)(z) with f_{e,λ(t)}(z) = 0, then (t, z) maps X birationally onto a
  component of W_λ. The converse is the same statement read backwards. ∎

**Count for pp.** Take λ of degree m with branch values away from {0, ∞, λ*}. Then W_λ → ℙ¹_t has
degree N and is branched exactly over the 3m points λ^{-1}{0, ∞, λ*}, with the local monodromy of
g. Riemann–Hurwitz gives
- genus G = (m − 1)(N − 1);
- these covers form a family of dimension ≤ 2m + 1 (the coefficients of λ);
- all simply branched degree-N covers of genus G form a Hurwitz space of dimension
  2G − 2 + 2N = 2m(N − 1);
- so the codimension is ≥ 2m(N − 2) − 1, for example 11 at (N, m) = (5, 2) and 27 at (9, 2)
  [Python].

S2 chooses f in a non-empty S-adic open subset of H⁰(X, O(D)), and ℚ-points are Zariski dense
there. So S2 produces a pulled-back f only if it is aimed at the closed locus. Whether that locus
meets H⁰(X, O(D)) at all is the geometric question in Lemma 3.3, and RMB contributes nothing to it.
For tri the base B is a surface and the count is analogous: codimension roughly k(N − 2) for
λ = (a(t), b(t)) of degree k [Proof sketch].

### 3.4 Real signature [Proof]

Suppose L/k is a real field all of whose real places over σ₀ number r, generated by a root z₀ of a
tri or pp member (overshoot allowed). All conjugates of z₀ over σ₀ that are real are real roots
of the member, and the member has at most 3 real roots (P1′ Proposition 5.2). So r ≤ 3.
- In particular a totally real field of degree ≥ 4 is never a tri- or pp-field.
- RMB in its PRC form outputs totally real fields, so for these engines one must prescribe
  Ω_∞ = {fibres with r ≤ 3 real points}. That is allowed in S1. cheb and five have unbounded
  capacity, so for them the PRC form is consistent.

## 4. The Chebyshev / Engine S side

**Genus 0 [Proof].** On X = ℙ¹ with E_∞ = [−1, 1], the Fekete–Szegő archimedean model is T_N. For
t₀ ∈ ℚ ∩ (−1, 1) the fibre T_N(x) = t₀ is the cheb(N, q) member with a = 0, c = −t₀. Its roots
cos((arccos t₀ + 2πj)/N) are all real and P-constructible (Engine S). So on genus 0 the method's
model output is drawable. Genus-0 curves with a real point have solvable points anyway.

**Lemma 4.1 (Lüroth tower) [Proof].** Let f ∈ k(X) and suppose f = h ∘ φ with φ: X → ℙ¹ and h a
rational function (by Lüroth, every intermediate field ℚ(f) ⊆ F′ ⊆ ℚ(X) of genus 0 is of this
form). For t₀ ∈ k, a point x of f^{-1}(t₀) has residue field containing s₀ := φ(x), a root of
h = t₀, and k(x) is a residue field of φ^{-1}(s₀) over k(s₀).
- So if h is an engine member (T_N − t₀, a trinomial, …), only k(s₀) is controlled. The top step
  k(x)/k(s₀) is a fibre of φ, which is the same problem for X over the larger field k(s₀).
- Shape control is complete only when deg φ = 1, that is, when X is rational. ∎

**Patching destroys sparsity, and is not needed.** Fekete–Szegő and Cantor–Rumely start from a
Chebyshev-like model and then round or patch coefficients to reach integrality. Each step perturbs
every lower-order coefficient [Cited from memory: the Fekete–Szegő 1955 and Robinson
constructions], so even on ℙ¹ the integral output is not sparse. F needs no integrality, and
without it the sparse model T_N − t₀ survives. That is the genus-0 statement above, and Lemma 4.1
says it does not lift.

**Verdict on the plan's hint.** The Chebyshev polynomials in capacity theory belong to the target
ℙ¹ of f. The Galois type of the output is decided by f: X → ℙ¹ itself. Composing with Chebyshev
adds a cheb layer at the bottom; it never replaces the φ layer at the top.

## 5. Galois type, and engine-resolvable curves

- **S_N is the default [Cited from memory].** Moret-Bailly 1990 makes the Galois group S_N with
  prescribed local behaviour. "Uncontrolled" in the plan means generic, and generic means
  non-solvable.
- **Solvable fibres need solvable monodromy [Proof].** By Hilbert irreducibility, for t₀ outside a
  thin set the fibre field of f has Galois closure group equal to the monodromy group of f. So a
  solvable output on a Hilbert set of t₀ needs a solvable-monodromy f. Zariski (*Sull'impossibilità
  di risolvere parametricamente per radicali …*, 1926) [Cited from memory] shows a curve of genus
  > 6 with general moduli has no map to ℙ¹ with solvable monodromy. Our X are not general (they
  have Aut ⊇ S_d), so this does not apply directly [Open].
- **Engine-resolvable.** Call X/k engine-resolvable if there is a tower X = Y_r → ⋯ → Y₀ = ℙ¹ over k
  in which each Y_{i+1} is a component of Y_i ×_{B_e} Z_e for a map ψ_i: Y_i → B_e (overshoot
  allowed), and each step is an engine or a solvable step.
  - **[Proof sketch]** If the twisted canonical X over a real solvable L is engine-resolvable with
    real fibres along the tower at σ₀, then X has points over F-fields, so β ∈ F. RMB is not needed:
    choose t₀ ∈ ℚ in the real window by approximation.
  - This turns P5′'s positive form into a geometric question, a Zariski-type problem for engine
    pull-backs. The dimension count of §3.3 says a general curve of large genus is not resolvable
    in one step [Heuristic for towers].
- **The untwisted Ĉ is resolvable; the twist breaks it [Proof].**
  - Ĉ_{p,q} → ⋯ → Ĉ/S_{d−2} → Ĉ/S_{d−1} = ℙ¹_z → ℙ¹_λ is the Galois-closure tower. Each step
    adjoins one more root of g(w) = λ over the previous field, so it is a component of the
    pull-back of g along λ, with the known roots removed (overshoot).
  - For the M-twist X, the intermediate quotients X/S_{d−j} are defined over L only for normal
    subgroups (P1′ §4.2), and S_{d−j} is not normal. So this tower does not descend.
  - Whether X has another engine tower over L is [Open]. It is the positive form of P5′ and is
    independent of capacity theory.

## 6. Hand-off

- **To the plan.** P5′ is answered "no, with the step located": S2/S3, because for N ≥ 5 the shape
  condition is a point on a twisted curve of genus ≥ 4 and RMB imposes only S-adic open
  conditions (§0 items 2–4).
  - P2′ suggested RMB as "the right tool for Layer 2". This note shows it does produce points
    bypassing descent, but over fields it does not choose. Layer 2 for a *prescribed class* of
    fields is untouched.
  - E-P now stands as: P1′, P2′, P5′ closed in the scoped sense; P3′ and P6′ remaining.
- **To Phase F.** Under Bombieri–Lang, the only way an RMB-chosen f has infinitely many engine-shaped
  fibres is an isomorphism correspondence between f and the engine (§3.2). That is F2's object
  with one side free. Since f is free, this reduces to F2's question for the pair (f, engine).
  - It adds no new family mechanism: the commensurator argument of F2 §3 needs both sides to be
    three-point covers.
- **Open, recorded.**
  1. Is P1′'s twisted canonical curve engine-resolvable over some real solvable L (§5)?
  2. Is Sh_cheb(M) (a surface) unirational over k when it has a smooth point? If so, every M with
     real data in [−1, 1] would be a cheb-field, and the problem would close without RMB. F2's
     general-type expectations make this unlikely [Heuristic].
  3. Prove that some degree-5 field with prescribed local data is not a tri(5)-field, which would
     turn the "not local" line of §3.2 from [Heuristic] into [Proof]. This is a point-free genus-4
     curve, which is within reach of a Chabauty or descent computation.
