# NOTES-offset-B2 — resolvent degree over ℝ, real closedness, and the engine formalism
Task B2 of the offset research programme. Status: **completed** (with precisely labelled gaps).
Evidence tags: **[Lean]**, **[symbolic]** (exact CAS), **[numeric, N digits]**, **[citation]**.

---

## Summary (≤ 12 lines)

1. `K ⊂ ℝ` is closed under `+ − × ÷`, square roots of positives (`sqrt_Pconstructible`), and real
   roots of degree-≤6 polynomials (`root_Pconstructible_le_six_coeffs`).
2. Artin–Schreier ⇒ `K` real closed ⟺ every odd-degree polynomial over `K` has a root in `K`.
3. **Minimal-counterexample reduction [proved here]:** a least odd degree with a rootless
   irreducible must have **primitive** Galois group; hence
   `K` real closed ⟺ every irreducible odd-degree `P/K` with primitive `Gal(P)` has a root.
4. For prime degree "primitive" is automatic (block sizes divide the degree), so degree 7 needs no
   group restriction *beyond* transitivity.
5. The non-totally-real septic is known (`root_Pconstructible_of_nonreal_root`); so the entire
   degree-7 gap is exactly **totally real irreducible septics over `K`**.
6. Totally real is hard because Hermite's trace form is positive definite: a **real** Tschirnhaus
   map can kill at most one power sum. **Verified exactly** for septics [symbolic].
7. The whole resolvent-degree / Hilbert-13 literature is over **ℂ**; there is **no established
   "real resolvent degree"**. The genuine real obstruction is the casus-irreducibilis family
   (Loewy 1922, Isaacs 1985, Cox Thm 8.6.5/8.6.12).
8. Engine formalism: an algebraic family + semialgebraic side conditions + soundness. Closure under
   cofactor, Möbius, inverse degree-≤6 Tschirnhaus, and composition (the imprimitive step).
9. **Obstruction lemma:** no real Tschirnhaus-to-power-law reduction kills `p₁,p₂` of a totally
   real target. This rules out one *method*, not the offset engines.
10. **Sufficiency lemma:** an engine covering a Zariski-dense union of `PGL₂`-orbits, whose covering
    system is solvable in `K`, covers the degree; the rational-segment sign-change argument is where
    `K`-solvability enters. A count that closes is not a proof.
11. The "no" side is **not** settlable by countability/o-minimality (both too weak); only restricted
    classes (real radicals, single Tschirnhaus) have rigorous negatives.
12. Offsets: the decic family is `codim 3` in coefficient space, but its **`PGL₂`-saturation is
    `codim 1`** (exact rank computation, script `B2-03`), so it misses a `PGL₂`-invariant
    hypersurface (norm/discriminant structure) and does **not** cover generic degree 10. Co-factor
    covering of a totally real septic is *not* excluded by the obstruction lemma.

---

## 1. The real-closedness reduction

### 1.1 Black boxes for `K`

`K ⊆ ℝ` is the set of `PConstructible` reals. The facts we use as axioms (all in `Pptc/Basic.lean`
unless noted):

* **(F)** `K` is a subfield of `ℝ` ([Lean] in `Basic`, closure under `+,-,*,/`).
* **(SQ)** `0 < x ∈ K ⇒ √x ∈ K` (`sqrt_Pconstructible`); in fact `K = K² ∪ (−K²)`.
* **(R6)** every real root of a nonzero polynomial over `K` of degree ≤ 6 lies in `K`
  (`root_Pconstructible_le_six_coeffs`).
* **(R8ℚ)** every real algebraic number of degree ≤ 8 over `ℚ` lies in `K`
  (`root_Pconstructible_le_eight`).
* **(R7nr)** every real root of a degree-7 polynomial over `K` **with a non-real root** lies in
  `K` (`root_Pconstructible_of_nonreal_root`, paper `septicpaper_revised.tex`).
* **(PL)** every real root of `y⁷ = c₃y³+c₂y²+c₁y+c₀`, `cᵢ ∈ K`, lies in `K` (power-law engine).
* **(E_dec)** the offset-cross decic engine of `Pptc/Offset.lean`.

`K` is countable but *not* known to be real closed; real closedness is the top-level question.

### 1.2 Artin–Schreier

> **Theorem 1 (Artin–Schreier, 1926). [citation]** For an ordered field `F` the following are
> equivalent:
> (i) `F` is real closed;
> (ii) `F` has no proper algebraic extension of odd degree and `F = F² ∪ (−F²)`;
> (iii) every positive element of `F` is a square **and** every polynomial of odd degree over `F`
> has a root in `F`.
>
> Sources: S. Kuhlmann, *Real Algebraic Geometry* lecture notes, Prop. 1.1 & 1.4
> (https://www.math.uni-konstanz.de/~kuhlmann/Lehre/WS09-10-ReelleAlgGeo/Skripts/Notes05.pdf);
> nLab "real closed field" (https://ncatlab.org/nlab/show/real+closed+field); Lang, *Algebra* IX.2.

Proof of (iii)⇒(i) (sketch, for completeness). Let `F` satisfy (iii) and let `E/F` be finite
separable. Passing to the normal closure we may suppose `E/F` Galois with group `G`.
*No proper odd extension*: if `α ∈ E` has odd degree `d>1` over `F`, its minimal polynomial is
irreducible of odd degree `d`, so (iii) gives a root in `F`, contradicting irreducibility; hence
every element of an odd-degree subextension lies in `F`, so `[E:F]` has no odd part. Formally, a
Sylow-2 subgroup `S ≤ G` has `[G:S]` odd, so `N^S = F`, i.e. `G=S`, and `[E:F]` is a power of 2.
Then `F=F²∪(−F²)` forces the only quadratic extension to be `F(i)`, and the standard closure
argument (every element of `F(i)` is a square, no odd extensions) gives `F(i)` algebraically closed,
i.e. `F` real closed. ∎

> **Corollary 2. [citation + (SQ)]** `K` is real closed ⟺ every polynomial of odd degree over `K`
> has a real root in `K`.

*Proof.* (SQ) supplies the square-root half of Theorem 1(iii); the odd-root half is exactly the
stated condition. ∎

### 1.3 Elimination steps (all [symbolic]/elementary)

> **Lemma 3 (monic).** Real-root membership for `P` is unchanged by dividing by its leading
> coefficient, which lies in `K`. Hence assume `P` monic. ∎

> **Lemma 4 (factor).** If every **irreducible** polynomial over `K` of odd degree `n` has a root in
> `K`, then so does every odd-degree polynomial of degree `n`.

*Proof.* Factor `P = ∏P_i`; an odd-degree product has an irreducible factor `P_j` of odd degree
`≤ n`. If `deg P_j < n` use strong induction, if `= n` use the hypothesis. ∎

### 1.4 The primitive / block reduction (the main structural result)

Let `P` be separable and irreducible over `K`, `deg P = n`, root field `L = K(β)`, splitting field
`N ⊇ L`, and `G = Gal(N/K) ≤ S_n` acting on the `n` roots (transitively). Call `P` (or `G` or
`L/K`) **primitive** if `G` is primitive as a permutation group, equivalently if the point stabilizer
`G_β` is a maximal subgroup of `G`.

> **Lemma 5 (imprimitive ⇒ intermediate field).** If `G` is imprimitive then there is an
> intermediate field `K ⊊ M ⊆ L` with `1 < [M:K] < n`. Conversely any such `M` makes `G`
> imprimitive.

*Proof.* An imprimitive `G` has a block system with `b` blocks of size `k`, `n=bk`, `1<k<n`. Let
`H ≤ G` be the setwise stabilizer of the block `B ∋ β`. Since `G` fixes `β`, `G_β(B)=B`, so
`G_β ≤ H`, and `H < G`. Set `M = N^H`. Then `M ⊆ N^{G_β} = L`, and by Galois
`[M:K] = [G:H] = b` (the action on the `b` blocks is transitive, orbit–stabilizer). Since
`1<k<n`, also `1<b<n`. The converse is the Galois correspondence. ∎

> **Theorem 6 (reduction to primitive groups). [proved]** Assume (SQ) and (R6). Then
> `K` is real closed **iff** for every odd `n`, every irreducible `P ∈ K[x]` of degree `n` with
> **primitive** Galois group has a real root in `K`.

*Proof.* (⇒) In a real closed field every polynomial splits, so trivially every such `P` has all
roots in `K`.
(⇐) By Corollary 2 it suffices to show every odd-degree `P` has a root. Strong induction on the odd
degree `n`. Assume every odd-degree irreducible of degree `< n` has a root in `K`, and let `P` be
irreducible of odd degree `n`. If `G=Gal(P)` were imprimitive, Lemma 5 gives
`K ⊊ M ⊆ L` with `[M:K]=b` odd, `1<b<n`. Pick `γ ∈ M∖K`. Since `K ⊆ K(γ) ⊆ M`, the degree
`d := [K(γ):K] = deg m_γ` divides `b`, is odd, and satisfies `1<d<n`. The minimal polynomial
`m_γ ∈ K[x]` is irreducible of odd degree `d<n`, so the induction hypothesis gives it a root in
`K` — impossible for an irreducible polynomial of degree `d>1`. Contradiction. Hence `G` is
primitive, and the hypothesis gives a root. ∎

> **Corollary 7 (minimal counterexample).** A rootless irreducible over `K` of **least** odd degree
> is primitive. (Same proof, contrapositive.) ∎

> **Remark 8 (prime degree). [standard]** If `n` is prime, every transitive `G ≤ S_n` is primitive
> (block sizes divide `n`). Hence for odd prime `n` the hypothesis of Theorem 6 is just
> "every irreducible degree-`n` polynomial has a root" — no group restriction at all. For `n=7`
> in particular, all seven transitive groups `C₇, D₇, F₂₁, F₄₂, PSL(2,7), A₇, S₇` remain in
> scope. For composite odd `n`, O'Nan–Scott restricts primitive groups to affine / almost-simple /
> diagonal / product types; "affine" contributes the `n=p^d` cases.

### 1.5 Splitting by real-root pattern; the exact degree-7 frontier

> **Corollary 9.** For degree 7 the reduction of Theorem 6 plus (R7nr) gives:
> `K` contains every real root of:
> * every separable degree-7 polynomial over `K` with at least one non-real root: **(R7nr)**;
> * every degree-7 polynomial over `K` with a repeated root (the paper's Proposition 6.1);
> and the **only** remaining degree-7 obstruction is: **totally real separable irreducible septics
> over `K`.**

The non-separable case is fully handled inside the septic paper (gcd with the derivative has degree
≤ 6).

> **Remark 10 (two independent obstructions).** Two distinct difficulties meet here:
> (a) the **group** difficulty (must we solve it inside `K`?), reduced to primitive groups by
> Theorem 6; and (b) the **real** difficulty (totally real targets make every real trace form
> definite), which is the content of §3.2. Degree 7 has no group difficulty beyond transitivity
> (prime degree) but has the full real difficulty.

### 1.6 The smallest justified target statement

> **Reduction Theorem (clean form). [proved, modulo Theorem 1]**
> `K` is real closed ⟺ for every odd `n`, every monic irreducible `P ∈ K[x]` of degree `n` with
> primitive Galois group has a real root in `K`.
>
> Moreover a minimal counterexample is primitive, and it may be taken **totally real** *if* one
> accepts the (R7nr)-type engines for all non-totally-real degrees; unconditionally, both real-root
> patterns remain in scope for `n ≥ 9`.

Sharpest *known* frontier: "for all odd `n`, every irreducible primitive totally real `P/K` of
degree `n` has a root in `K`", with `n=7` already open and the non-totally-real subcase open from
`n=9` on.

---

## 2. Literature: resolvent degree and Hilbert's 13th problem

### 2.1 Definitions and the key fact

`RD(n)` = least `d` such that every root of the general degree-`n` polynomial is obtainable from the
coefficients by `+ − × ÷` and algebraic functions of ≤ `d` variables. Equivalently
`RD(n) = RD(S_n) = RD(A_n)` (Farb–Wolfson). `ed(S_n)` is the analogous essential-dimension number.

**Central honesty point.** Every result in this table is stated and proved over `ℂ` (or an
algebraically closed base of characteristic 0). Sutherland's survey says it explicitly: "we
summarize what is currently known about `ed(G)` and `RD(G)` for finite groups over `ℂ` (i.e. in
characteristic 0)." The theory relies on accessory irrationalities drawn from the algebraic closure,
and the reductions (Bring, Hamilton, Sylvester, Hilbert, Wiman, Chebotarev, Segre, Brauer, Wolfson,
Sutherland, Heberle–Sutherland, Gómez-Gonzáles) are **complex reductions**. Over `ℝ`, and *a
fortiori* over the countable subfield `K`, the accessory irrationalities may be non-real, and the
standard machinery does not apply.

### 2.2 Table

| Result / author, year | Real or complex? | What it needs | URL |
|---|---|---|---|
| Tschirnhaus 1683: kill `x^{n-1}, x^{n-2}` | works formally; accessory roots needed | degree-2 auxiliary, may be complex | https://dl.acm.org/doi/10.1145/990353.990371 |
| Bring 1786: quintic → `x⁵+px+q` | complex | degree-4 Tschirnhaus, auxiliary solvable by radicals (complex) | https://arxiv.org/abs/1711.09253 |
| Hamilton 1836: septic → `x⁷+ax³+bx²+cx+d` | complex | degree-6 Tschirnhaus + auxiliaries of degree ≤ 6; **Hamilton numbers** | https://www.maths.tcd.ie/pub/HistMath/People/Hamilton/Jerrard/ |
| Sylvester–Hammond 1887: obliteration algorithm | complex | polar-cone / elimination; gives Hamilton-number bounds | https://oeis.org/A000905 |
| Hilbert 1927: `RD(9) ≤ 4` | complex | 27 lines on a smooth cubic surface | https://doi.org/10.1007/BF01447867 |
| Wiman 1927 / Chebotarev 1943–54 | complex | resolvent/critical-manifold methods; gaps repaired in [Sut21] | https://arxiv.org/abs/2107.08139 |
| Segre 1945: `RD(A_n) ≤ n−5`, `n≥9` | complex | normal rational varieties / Brill–Noether (ref. in [Sut23]) | https://arxiv.org/abs/2312.04430 |
| Brauer 1975: introduced `RD` | complex | reformulation of Hilbert 13 (ref. in [FW19]) | https://arxiv.org/abs/1803.04063 |
| Farb–Wolfson 2019: `RD(G)` theory; equivalence with geometry | complex | `E`-versality; reduction to primitive groups | https://arxiv.org/abs/1803.04063 |
| Wolfson 2020: best-to-date `RD(n)`, general method | complex | secant/`k`-plane geometry on hypersurfaces | https://arxiv.org/abs/2001.06515 |
| Sutherland 2021: improved large-`n` thresholds, fixes Wiman/Chebotarev | complex | polar cones + algebraic geometry | https://arxiv.org/abs/2107.08139 |
| Heberle–Sutherland 2023: `RD(n) ≤ n−13` for `n≥5 250 199` | complex | Sylvester obliteration algorithm | https://nyjm.albany.edu/j/2023/29-4p.pdf |
| GGSW 2023, Gómez-Gonzáles 2025: sporadic groups, special points | complex | generalized versality; level-`ℓ` points | https://arxiv.org/abs/2510.10272 |
| Sutherland survey 2023 | complex | summary table of bounds | https://arxiv.org/abs/2312.04430 |
| **Loewy 1922 / Isaacs 1985 / Cox** casus irreducibilis | **REAL** | totally real + solvable by **real radicals** forces `2`-power degree | https://en.wikipedia.org/wiki/Casus_irreducibilis ; Cox, *Galois Theory*, Thm 8.6.5 & 8.6.12 |
| Bailey/Polizzi et al. (MO 182178) worked real examples | **REAL** | explicit totally real polys with only some real-radical roots | https://mathoverflow.net/q/182178 |

### 2.3 Known RD values / bounds (all over ℂ)

From Sutherland's survey (https://arxiv.org/abs/2312.04430), `RD(A_n)=RD(S_n)`:

`RD(2..5)=1`, `RD(6) ≤ 2`, `RD(7) ≤ 3`, `RD(8) ≤ 4`, `RD(9) ≤ 4`, `RD(10) ≤ 5`,
`RD(11) ≤ 6`, `RD(12) ≤ 7`, `RD(13) ≤ 8`, `RD(14) ≤ 9`, `RD(15) ≤ 10`, `RD(16) ≤ 11`,
`RD(17) ≤ 12`, `RD(18) ≤ 13`, `RD(19) ≤ 14`, `RD(20) ≤ 15`, `RD(21) ≤ 15`, `RD(22) ≤ 16`.
Hilbert's conjectures (open): `RD(6)=2`, `RD(7)=3`, `RD(8)=4`. Related:
`ed(S₆)=3`, `ed(S₇)=4` (Duncan), `RD(PSL(2,𝔽₇))=1`, `RD(PSL(2,𝔽₁₁)) ≤ 2`.

### 2.4 Is there a "real resolvent degree"?

Searches for "real resolvent degree", "resolvent degree over ℝ", "real Tschirnhaus over real closed
fields", and "signature obstruction resolvent degree" returned **no established theory**: the term
does not appear in the RD literature, and no paper defines a real analogue. What *does* exist is:

* the classical **casus irreducibilis** and its higher-degree generalisations (Loewy 1922,
  Isaacs 1985, Cox Thm 8.6.5/8.6.12);
* the theory of **real radicals**: if a totally real irreducible `f` over a subfield of `ℝ` has a
  root in a real radical extension, then `[splitting field : base]` is a power of 2 and the roots
  are obtained by iterated square roots only;
* Loewy's refinement: for `f` irreducible of degree `2^m·n` (`n` odd), at most `2^m` roots are
  expressible by real radicals. In particular an irreducible **odd-degree** `f` has at most **one**
  root expressible by real radicals.

**Translated to `K`.** `K` contains degree-≤6 roots and the engines; so `K` is *not* a radical
extension of `ℚ` in any naive sense, and the casus-irreducibilis theorems do not directly exclude
membership in `K`. They do show that the whole complex apparatus is unavailable, and they pin down
the flavour of the obstruction: *realness of the accessory irrationalities, not their degree, is
what fails.*

### 2.5 The project's "accessory irrationalities"

In the RD picture, solving `P` proceeds by a chain of covers, each of essential dimension ≤ `d`.
For `K`, the "free parameters" of the construction are elements of `K`, and the allowed accessory
irrationalities are: roots of degree ≤ 6 (R6), iterated engine outputs, and free rational choices.
So the analogue of `RD` for `K` would be a *real, arithmetic* invariant: the least "generation
depth" in a class of real covers, all of whose branching data must be `K`-rational. The literature's
`RD` lower bounds (e.g. `ed(S₇)=4`) bound how many *independent variables* a uniform formula needs;
they do **not** bound whether the *coefficients of the cover* can be chosen in the countable field
`K`. This is the precise sense in which Hilbert-13-type obstructions do **not** settle whether a
particular totally real septic is in `K`.

---

## 3. Engine formalism

### 3.1 Definitions

Fix `K` as in §1. A **(real) engine datum** is a triple `E = (N, S, P)`:

* `N ∈ ℕ` (the degree);
* a semialgebraic set `S ⊆ K^m` (the *parameter locus*, defined by polynomial inequalities with
  coefficients in `K`);
* a monic-in-`t` polynomial `P(s,t) ∈ K[s,t]` of `t`-degree `N`.

Its member at `s` is `P_s(t) := P(s,t)`. `E` is **sound** if for every `s ∈ S`, every real root of
`P_s` lies in `K`. Write `C(E) ⊆ Poly_N(K)` for the set of members of a sound engine (the *covered
set*). The engine has **effective dimension** `e(E)` = the dimension of `S` modulo the redundancy of
the parametrisation, and **moduli dimension** = the dimension of its image in the moduli of
degree-`N` binary forms (i.e. after quotienting by `PGL₂`).

Sound engines in hand (all [Lean] in the package, up to the paper):

* `E6`: `N=6`, `S=K^6`, free coefficients (R6).
* `EPL(n)`: `N=n`, parameters = coefficients of `q` of degree ≤ 6; `P_s(t)=t^n−q_s(t)`, plus sign
  reflection for negative roots. Sound by (PL) and `powerLaw_root_pos_Pconstructible`.
* `Enon(9)`: `N=9`, members `M³+λM²+v²` with `M` monic cubic, `v` cubic; codim 1 in degree-9
  space (`nonicVal_root_Pconstructible`).
* `E7nr`: `N=7`, the Tschirnhaus + power-law septic engine; sound by (R7nr).
* `Edec`: `N=10`, the offset-cross decics
  `u²(u'²+v'²) − D²v'²`, `u` cubic, `v'` quadratic, `D²=d²(A²+B²)`; image dimension 7 inside the
  10-dimensional coefficient space (`offsetCrossPoly_normalForm`, `Offset.lean`).

### 3.2 Closure rules (all proved from the definitions + (R6))

> **Rule C1 (cofactor).** If `P·g ∈ C(E)` with `g ∈ K[x]` monic, then `P ∈ C(E)`.
> *Proof.* Every root of `P` is a root of `P·g`, hence in `K`. (This is how a lower-degree target can
> be extracted from a higher-degree engine.) ∎

> **Rule C2 (Möbius).** If `P ∈ C(E)` and `m(t)=(at+b)/(ct+e)` with `a,b,c,e ∈ K`,
> `ae−bc≠0`, then the unique monic polynomial whose roots are `m(λ)`, `λ` a root of `P`, is in the
> covered set of the engine `m·E`. *Proof.* `m` maps `K ∪ {∞}` into `K ∪ {∞}`; the
> characteristic-polynomial construction is polynomial in the coefficients. ∎

> **Rule C3 (inverse Tschirnhaus).** Let `Q(t) = charpoly(φ(companion(P)))` for `φ ∈ K[x]`,
> `deg φ = d`. If `Q ∈ C(E)` for a sound engine, then `P` is covered **provided `d ≤ 6`**.
> *Proof.* A root `y = φ(β)` of `Q` is in `K`; `β` is a real root of `φ(x) − y`, of degree `≤ d ≤ 6`
> with coefficients in `K`, so `β ∈ K` by (R6). ∎
> If `d>6`, coverage of `Q` gives `β` only after a further degree-`d` engine; this is exactly the
> point at which a new engine is needed.

> **Rule C4 (composition / the imprimitive step).** Let `P` be irreducible of odd degree `n=bk`
> with an imprimitive Galois group and block system of `b` blocks of size `k`. If (i) a primitive
> element `γ` of the block field `M` has a minimal polynomial covered by an engine, and (ii) the
> block polynomial `g_B ∈ M[y]` becomes an engine-covered polynomial after substituting the
> `K`-value of `γ`, then `P` is covered. *Proof.* §1.4 reduction: the induction hypothesis puts
> `γ ∈ K`, so `M=K` and `g_B ∈ K[y]`; then Rule C1/C3 applies. ∎

> **Rule C5 (earlier-engine parameters).** Replacing any parameter of `E` by an output of a sound
> engine preserves soundness. *Proof.* Sound outputs lie in `K`, and `C(E)` is defined for all
> `K`-parameters in `S`. ∎

### 3.3 The obstruction lemma (Hermite type)

> **Lemma 11 (Hermite). [citation; verified symbolically]** Let `P` be separable of degree `n` with
> `r₁` real roots and `r₂` conjugate pairs (`r₁+2r₂=n`). Put `A=K[x]/(P)`,
> `B(f,g)=Tr(fg)`, `Q(f)=B(f,f)`, and `W={f:Tr f=0}`. Then `B` has signature `(r₁+r₂, r₂)` and
> `Q|_W` signature `(r₁+r₂−1, r₂)`.
>
> *Proof.* Chinese remainder decomposes `A` into `r₁` copies of `K` and `r₂` copies of `K(√−1)`.
> On a real factor the form is `f(λ)²`, signature `(1,0)`; on a complex pair the form is
> `2Re(f(z)²)`, signature `(1,1)`. Summing gives `(r₁+r₂, r₂)`. `W=⟨1⟩^⊥` and `Q(1)=n>0`, removing
> one positive direction. (Sylvester's law of inertia.) ∎

**[symbolic]** verification (`B2-02c-trace-form-exact.py`, exact rational principal minors):

| target | `B` signature on `A` | `Q|_W` signature |
|---|---|---|
| totally real septic `x⁷−14x⁵+49x³−36x+1` | `(7,0)` | `(6,0)` positive definite |
| `(x−1)⋯(x−5)(x²+1)` (5 real, 1 pair) | `(6,1)` | `(5,1)` indefinite |
| `(x−1)(x−2)(x−3)(x²+1)(x²+4)` (3 real, 2 pairs) | `(5,2)` | `(4,2)` indefinite |

> **Obstruction Lemma 12 (Tschirnhaus–power-law; proved).** Let `P` be a **totally real** separable
> polynomial over `K` of degree `n ≥ 7`, and let `φ ∈ K[x]` be real with `deg φ ≤ 6`. Then `φ`
> cannot satisfy `p₁(φ)=p₂(φ)=0` unless `φ=0`. Consequently `φ` can kill **at most one** power sum,
> and a single real Tschirnhaus reduction cannot put `P` into the `EPL(n)` normal form
> `y^n = q(y)`, `deg q ≤ 6` (which needs `p₁=…=p_{n−7}=0`, i.e. `n−7 ≥ 2` conditions for `n ≥ 9`;
> and for `n=7`, `p₁=p₂=p₃=0`).

*Proof.* `p₂(φ)=Q(φ)=Σ φ(λᵢ)²`. Totally real ⇒ `Q|_W` is positive definite (Lemma 11), so
`Q(φ)=0` with `φ∈W` forces `φ=0`. Newton's identities convert `p₁=…=p_k=0` into vanishing of the
top `k` elementary symmetric functions, i.e. the top `k` coefficients. For `n≥9`, `n−7≥2`; for
`n=7` the `EPL(7)` normal form `y⁷ + c₃y³+c₂y²+c₁y+c₀` kills `e₁,e₂,e₃` ⇔ `p₁,p₂,p₃=0`. ∎

> **Corollary 12′ (scope and limits).** Lemma 12 excludes the class
> *"{totally real targets} solved by a single real degree-≤6 Tschirnhaus reduction to a power-law
> normal form"*. It does **not** exclude:
> * the direct engine family `EPL(n)` (members are `t^n−q(t)`, not obtained by Tschirnhaus);
> * any engine whose members are used as **factors** of a higher-degree engine (Rule C1) — in
>   particular it does **not** rule out the offset-decic cofactor route to a totally real septic;
> * multi-step / composed engines (Rule C4).
> This is the exact sense in which the septic paper's method is obstructed for totally real
> septics, and why the offset route remains logically open.

### 3.4 The sufficiency lemma

> **Skeleton Lemma 13 (sufficiency). [proved, conditionally on the covering system]** Let `E` be a
> sound engine of degree `N`. Suppose a target `P` (monic, degree `N`, coefficients in `K`) is
> such that there are parameters `s₀, s₁ ∈ S ∩ K^m` and a rational segment `s(t)=s₀+t(s₁−s₀)`
> with:
> (a) `P` is `K`-Möbius-equivalent to `P_{s(0)}` (so `P_{s(0)}` is covered) — or more generally
> `P_{s(0)} ∈ C(E)`;
> (b) a `K`-algebraic *defect function* `Ψ(t)` (built from the coefficients of `P` and `P_{s(t)}`)
> satisfies `Ψ(0)·Ψ(1) < 0`, and the relation `Ψ(t)=0` is the covering system;
> (c) for every `t` in the segment the side conditions of `E` hold, and `Ψ` restricted to the
> segment is a nonzero polynomial of degree ≤ 6 over `K`.
> Then `P ∈ C(E')` for the engine `E'` obtained by adjoining the segment parameter, and every real
> root of `P` lies in `K`.

*Proof.* `Ψ` is continuous with opposite signs at the endpoints, so `Ψ(t*)=0` for some `t*∈(0,1)`
(IVT). By (c), `Ψ` is a nonzero polynomial over `K` of degree ≤ 6, so (R6) gives `t*∈K`. Then
`P_{s(t*)}` has coefficients in `K` (parameters in `K`) and is `K`-Möbius/Tschirnhaus-equivalent to
`P`; Rule C2/C3 and soundness put the roots of `P` in `K`. ∎

**Where solvability enters.** Step (a) — producing `s₀` and the equivalence — and the description of
`Ψ` in step (b) are themselves systems of polynomial equations over `K`. Lemma 13 is a *transfer
principle*: it converts "the covering system has real solutions arranged so that a ≤ 6 degree
polynomial changes sign" into "covered." It does **not** manufacture the solutions. The solutions
must be found by:
* free rational/`K` choices where the condition is open (density of `K` in its real closure is not
  available, but rational points are dense in `ℝ`, and `ℚ ⊆ K`);
* roots of degree ≤ 6 (R6);
* outputs of earlier sound engines (Rule C5).
If the system has auxiliary unknowns of degree `>6` that are not engine outputs, the argument stops
— this is exactly how the direct degree-9 route died (auxiliary unknowns of degree 10,
`archived files/HANDOFF-degree7-s2.md` ~l.860).

> **Corollary 14 (dimension criteria; necessary, not sufficient).** Let `V` be the image of a
> degree-`N` engine in the `N`-dimensional space of monic degree-`N` polynomials.
> (a) If `dim(PGL₂·V) < N`, the engine misses a `PGL₂`-invariant condition and cannot cover general
> degree `N`. Necessarily `e(E) ≥ N−3` for coverage, but `e(E) = N−3` is not enough.
> (b) If `dim(PGL₂·V) = N`, coverage is *possible* modulo `PGL₂`, but still requires the real image
> to meet every real-root-pattern component and the covering system to be `K`-solvable.
> A parameter count alone proves nothing: the degree-10 offset engine has the "right" effective
> count `8` yet `dim(PGL₂·V)=9 < 10` (Corollary to §5.2), and the earlier direct degree-9 route died
> because its auxiliary unknowns had degree 10.

---

## 4. Can the "no" side be settled?

Four candidate routes and their exact limitations.

1. **Countability.** `K` is countable (finitely many construction trees over a countable alphabet,
   each with finitely many outputs; algebraic/transcendental constructors are countably generated).
   So `|K| = ℵ₀ < |ℝ|`. But the real algebraic numbers over `K` are also countable, so countability
   gives **no** separation between `K` and its real closure. It only excludes "almost all" reals,
   not a single specified algebraic number. **Verdict: useless for the target.**

2. **Monodromy / Galois invariants.** A uniform construction gives algebraic functions whose
   monodromy is generated by the moves. Offsets already realise `A₁₀` (`Offset.lean:756-773`), so
   there is no small group obstruction. Could one show the root function of the generic totally real
   septic (monodromy `S₇`) cannot be generated by the allowed covers? This is a genuine invariant,
   but the allowed class is recursive and includes `A₁₀`, so no known theorem forbids it.
   **Verdict: the right invariant, but no complete argument exists.**

3. **O-minimality.** All the constructible sets and functions are definable in the real field, so
   o-minimality gives cell decomposition, finiteness of components, monotonicity — no *undefinability*
   of anything in `K`. It cannot distinguish `K` from `ℝ`. **Verdict: useless for a "no".**

4. **Uniform (parametric) constructions.** This is the only sharp tool. A uniform construction over
   a base `B` produces a (possibly multi-valued) algebraic function `y(b)`; its monodromy
   representation is determined by the tree, and the *coefficients of the covering maps* must be
   `K`-rational. To cover all totally real septics uniformly one needs a cover of the totally-real
   region whose monodromy surjects to the `S₇`-monodromy of the root function, built from degree-≤6
   and engine covers with `K`-rational branch data. Known `RD`/`ed` results give upper bounds on the
   *number of variables*, not on the *field of definition of the cover*, so they do not decide it.

**What can be proved today.**
* For the restricted class of **real-radical** expressions: a totally real irreducible polynomial of
  degree not a power of 2 has **no** root so expressible (Isaacs/Cox). This is a rigorous negative,
  but its class is strictly smaller than `K` (which contains non-radical engine outputs).
* For a **single real Tschirnhaus reduction to power-law form**: Lemma 12 is a rigorous negative on
  totally real targets.
* Nothing rules out a multi-engine or cofactor construction.

**What cannot be proved today.** There is no known argument that any specific real algebraic number
is outside `K`. The barrier is arithmetic (field of definition / `K`-solvability of covering
systems), and the standard topological invariants (`ed`, `RD`, monodromy, o-minimality) are blind
to it.

---

## 5. Where offsets fit

### 5.1 Mechanisms and verdicts

* **Offset of a cubic pair × line (`Edec`, degree 10, image dim 7).** The natural route to a totally
  real septic is **cofactor** (Rule C1): find parameters with `P | P_s`, `P` totally real of degree
  7. For a *fixed* totally real septic `P`, the decics divisible by `P` are `P·g`, `g` monic cubic:
  3 real parameters; the engine family has 7 parameters (codim 3 in 10-space). The intersection is
  expected to be 0-dimensional, so the route is plausible and **not** excluded by Lemma 12 (which is
  about Tschirnhaus, not factors). It requires solving a 3-parameter covering system inside `K`; this
  is the concrete target for task B1.
* **Offset × offset / self-crossings / cusps (`A3`).** These produce new families with more shape
  freedom; whether they reach a Zariski-dense (or moduli-dense) locus is an algebraic-geometry
  question. They are not excluded by Lemma 12.
* **Rational (PH, parabola) offsets (`A2/A4`).** The square root disappears (`O6`), so crossings are
  exact polynomial equations. Rational offset families are *lower* degree; their value is as
  accessory coordinates and as exact sub-engines, not as degree-7/9 coverage by themselves.
* **Chains `offset ∘ affine ∘ offset` (`A4`).** By (O3) iteration adds nothing without a genuine
  non-similarity affine map between offsets; with one, parameter growth (O5, degree `4n−2`) can
  enlarge the family. Not excluded.
* **Ruled out.** Any mechanism whose *only* content is a real Tschirnhaus reduction killing ≥2 power
  sums of a totally real target (Lemma 12). Concretely, "take a totally real septic, apply a real
  degree-≤6 Tschirnhaus map to reach `y⁷ = cubic(y)`" is impossible.

### 5.2 Decisive check: the Möbius saturation of `Edec` is `codim 1` (computed)

`Offset.lean` states the decic image is codimension 3 in the 10-dimensional **coefficient space**.
Coverage modulo `PGL₂` depends instead on the **`PGL₂`-saturation** `PGL₂·image`. We computed it
directly (`B2-03-decic-mobius-rank.py`, exact rational ranks at three generic parameter points):

* `rank dImage = 7` (confirms the codim-3 coefficient-space statement); and
* `rank [dImage | orbit tangents] = 9`,

i.e. the saturation of the decic family is **9-dimensional**, a hypersurface in coefficient space.
Since the saturation is `PGL₂`-invariant, it descends to a **divisor in the 7-dimensional moduli of
decics**; the family therefore fails to cover general degree 10 by (at least) one invariant. (The
likely invariant is structural: `offsetCrossPoly = u²(u'²+v'²) − D²v'²` is the *norm* of
`u√(u'²+v'²) − D v'` from the quadratic extension, so the decic is a norm form; its discriminant is
a square and it carries a `PGL₂`-invariant distinguished divisor. Verifying the exact invariant is a
lead.)

**Consequences.** (i) The negative statement is stronger than a count: no choice of line/cubic pair
repairs the codimension-1 invariant. (ii) For a fixed totally real septic `P` the cofactor route
`P | P_s` is *not* excluded: `{P·g : g monic cubic}` is 3-dimensional, `image` is 7-dimensional, and
the saturation being codim 1 still leaves a codim-0 system of equations to solve; the route is a
genuine open question, not an impossibility.

### 5.3 Ranked list for the synthesis: what an offset construction would have to achieve

1. **[Degree 7, totally real]** Find a sound, `K`-parameterised engine of degree `N ≥ 7` with a
   member having a prescribed totally real septic `P` as a **factor**, and solve its covering system
   in `K`. The decic `Edec` cofactor is the first candidate (3-parameter cubic `g`); verify real
   feasibility and `K`-solvability.
2. **[Invariant, now computed]** The `Edec` saturation is `codim 1` (§5.2), so degree-10 coverage
   fails by one `PGL₂`-invariant. Identify the invariant (norm/discriminant square) and ask whether
   a modified offset mechanism (offset×offset, non-line crossing, double offset) breaks it.
3. **[Moduli dimension]** Compute the moduli (not coefficient) dimension of every new offset family
   in `A1–A4`; report `dim(image)` **and** `dim(PGL₂·image)`.
4. **[Degree 7, non-totally-real]** Already done by `E7nr`; use only as a template for the
   `K`-solvability pattern (rational-segment + (R6)).
5. **[All degrees]** Build engines `E_n` whose moduli image is dense and whose covering systems are
   `K`-solvable for every odd `n`; by Theorem 6 it suffices to handle **primitive** groups, and by
   Corollary 7 a minimal counterexample is primitive.
6. **[Obstruction respected]** Any proposed construction must avoid relying on killing ≥2 power
   sums of a totally real target by a real Tschirnhaus map (Lemma 12); cofactor and composition are
   the escape routes.

---

## Side discoveries

* **[symbolic]** A concrete **totally real irreducible septic with Galois group `S₇`**:
  `f(x) = x⁷ − 14x⁵ + 49x³ − 36x + 1`. All 7 roots are real (numerically
  `−3.00138, −1.99158, −1.02060, 0.02781, 0.97890, 2.00825, 2.99861`). It is irreducible over `ℚ`;
  factorisation cycle types mod primes give `[7]` (p=2,7,11,19), `[6,1]` (p=29,41,47),
  `[5,1,1]` (p=17,37), `[4,3]` (p=3,5,31), `[3,3,1]` (p=13), `[3,2,2]` (p=43),
  `[3,2,1,1]` (p=23). The 5-cycle forces `5 | |G|`, the 7-cycle `7 | |G|`, and the 6-cycle forces
  `2 | |G|` and `3 | |G|`, so `210 = 2·3·5·7` divides `|G|`. The transitive subgroups of `S₇` are
  `C₇, D₇, F₂₁, F₄₂ (order 42), PSL(2,7) (168), A₇ (2520), S₇`; only `A₇` and `S₇` have order
  divisible by `5`, and `[4,3]` is an odd permutation type, so `G ⊄ A₇`; hence `G = S₇`.
  This is the generic-hardest totally real septic and the natural test target for B1.
  Script `B2-01-totally-real-septic.py`.
* **[symbolic]** Exact Hermite-trace-form signatures for the three septic root patterns, confirming
  Lemma 11 (see table in §3.3). Script `B2-02c-trace-form-exact.py`.
* **[symbolic]** The Loewy/casus example works exactly: `x⁶+6x⁴−234x²−54x−3` is irreducible over `ℚ`,
  has 4 real roots, and factors over `ℚ(√3)` into a cubic with 3 real roots (casus irreducibilis, no
  real-radical root) and a cubic with 1 real root (real-radical). Verified.
* **Structural.** `K ⊂ ℝ` contains no non-real roots of unity and no `i`; therefore **all** the
  classical complex reductions (Bring, Hamilton, Klein's icosahedral, Hilbert's 27 lines) are
  unavailable verbatim. This is the conceptual reason the real problem is open where the complex
  one has centuries of upper bounds.
* **Structural.** The imprimitive case is *automatically* excluded in a minimal counterexample
  (Theorem 6), so the entire "reduce to primitive groups" business is a theorem over `K`, not a
  heuristic.
* **Structural (decisive).** The `PGL₂`-saturation of the decic offset family is exactly
  **9-dimensional** (`codim 1`) in the 10-dimensional coefficient space, computed by exact rank at
  three generic rational points (`B2-03-decic-mobius-rank.py`): `rank dImage = 7`,
  `rank [dImage | orbit] = 9`. This upgrades the "codim 3" statement to a genuine `PGL₂`-invariant
  obstruction (a divisor in moduli) and shows the deficiency is one invariant, not three
  independent ones. The natural explanation is the norm structure
  `offsetCrossPoly = (u√(u'²+v'²) − Dv')(u√(u'²+v'²) + Dv')`.

## Leads for other tasks

* **B1 (totally real septic):** attack `P | P_s` for the totally real `S₇` septic above with the
  `Edec` family; solve the cubic `g` and the 7 engine parameters (7+3 = 10 unknowns, 10 coefficient
  equations, codim-3 engine constraint) over `ℝ`, then attempt `K`-solvability of the covering
  system. A negative: show the real intersection is empty for this family.
* **A1/A2/A3/A4 (geometry):** for every new family, report `dim(PGL₂·image)`, not just
  `dim(image)`. For `Edec` this is now known to be 9; identify its defining invariant.
* **A2:** whether a totally real septic can divide an `Edec` member is a resultant/`Groebner`
  computation; cross-check with the synthesis.
* **B3:** the engine formalism should absorb the transcendental engines (`exp_two`, `sine`, arcs)
  as "sound engines over `K`" and re-run Rules C1–C5.
* **B4 (legality):** Rule C3's `d ≤ 6` is exactly `root_Pconstructible_le_six_coeffs`; the formal
  statement of Theorem 6 needs only `sqrt_Pconstructible` and `root_Pconstructible_le_six_coeffs`,
  so it is a good target to formalise in Lean (small Mathlib footprint).
* **Synthesis:** the decic saturation is now known to be codim 1 (`B2-03`); the remaining decisive
  experiment is §5.3(1): the real feasibility and `K`-solvability of the septic-factor covering
  system `P | P_s` for the totally real `S₇` septic of the Side-discoveries section.
