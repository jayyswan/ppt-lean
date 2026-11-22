# Sessions 39–40: full results (frozen archive)

Frozen on Nov 18, 2026 (session 42). This file holds Sections 0p and 0q of the condensed summary as they stood after session 41, unchanged. **Don't write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session here in its Section 0. Labels S39.1 … S40.5 point here.

## 0p. Session 39 (Nov 17, later): results

Topic: plan item 3(b), first steps: the branch structure of Engine O, its monodromy, and which real-root counts it reaches.

**S39.1 (the discriminant of Engine O).** [exact] `engO_disc.py` (about 90 seconds, symbolic in a, b, U).
- **disc_x G(x; U, a, b) = (4a³ + 27b²)¹⁵ · A(U)⁷ · B(U)⁴** exactly (PARI: D/(A⁷B⁴) is a polynomial and `factor` returns only (4a³ + 27b²)¹⁵). Weight check: disc has weight 16·5 + 72 = 152 = 90 + 42 + 20.
- So the branch locus of Engine O in P(1,2,3) is exactly {Δ_h = 0} ∪ {c² = 0} ∪ {c² = ∞} (Δ_h := 4a³ + 27b²; c² = −A/B). Members are separable away from it.
- Over any field, disc(G) ≡ Δ_h · A mod squares. Over P only the sign matters, and the real-root count r of G is constant on each connected component of the complement of {Δ_h · A · B = 0} in the real (U : a : b)-plane.

**S39.2 (fixed h: monodromy S_9, and the curve X_h has genus 23).** [numerical] `xh_disc.py`, `xh_mono.py`, with h = x³ − x + 1.
- For fixed h, X_h = {G(x; U) = 0} → P¹_U has degree 9, branched only over the 6 roots of A and the 5 roots of B (S39.1); disc_x G = const · B⁴A⁷ as a polynomial in U (degree 62).
- Root tracking around each branch point (radius 2·10⁻⁵, needed because a root of A and a root of B lie 1.7·10⁻⁴ apart at U ≈ −47.974): **cycle type (7, 2) at every root of A** (c² = 0), **(2, 2, 2, 2, 1) at every root of B** (c² = ∞: one point at O and 4 pairs, as in S37.1), and **trivial at U = ∞** (the 3 + 3 + 3 sheet). These match the valuations 7 and 4 of the discriminant.
- Riemann–Hurwitz: 2g − 2 = −18 + 6·7 + 5·4 = 44, so **g(X_h) = 23**. The loops generate **S_9** (sympy: order 9!, primitive); the B-loops alone generate A_9.
- Genericity (*unchecked*, short): A and B are squarefree and coprime for generic h (S38.1), so the local types are the same at every simple root for generic (a, b).
- Consequences. (i) The geometric monodromy of Engine O over ℂ(U, a, b) is S_9, so its Galois group over ℚ(U, a, b) and over P(U, a, b) is S_9 as well. **No resolvent of G has a rational factor on the whole family**: plan item 3(b)(i) is closed. (ii) X_h is not rational, so for fixed h Engine O is *not* the fibre family of one rational function of degree 9 (as trinomials are of x⁹ + ax).

**S39.3 (real-root census: r ∈ {1, 3, 5, 9}, never 7).** [numerical] `engO_chambers.py` (grid with Sturm counts), `engO_slices.py` (exhaustive per slice).
- Real points of P(1,2,3) up to λ ∈ ℝ*: charts a = −1, a = +1 (b, U real, (U, b) ~ (−U, −b)) and a = 0, b = 1. For each b, `engO_slices.py` takes the real roots of A and B in U and runs one exact Sturm count (`polsturm`) per interval between them; by S39.1 this lists every chamber met by the slice.
- Runs: a = ±1 with 1601 values of b ∈ [−8, 8]; a = −1 with 3 × 500 values of b ∈ [0.37, 0.40] and 1001 values in [0.3849, 0.38491] (around 2/√27 ≈ 0.38490, where Δ_h changes sign); a = 0.
- **Result: r ∈ {1, 3, 5, 9} only, never r = 7.** a > 0 (h has one real root, Δ_h > 0) and a = 0: only r ∈ {1, 3}. a < 0: r = 5 occurs only for Δ_h > 0 (|b| > 2/√27, h with one real root), in a band of U around [−8, 8] (for a = −1) that persists to |b| = 8; r = 9 only in thin regions next to Δ_h → 0⁺ (the crunode, as S36 predicts).
- Status: numerical census, not a proof. A sign lemma in the style of S32.1 might prove r ≠ 7 (*open*).
- Consequence: by the sign rule sign(disc) = (−1)^{(9−r)/2}, over P: r = 9 → A_9, r = 7 → S_9, r = 5 → A_9, r = 3 → S_9, r = 1 → A_9 (for members with generic group). **Engine O never reaches the open case S_9, r = 7 over P**, but it does reach A_9, r = 5 (S39.4).

**S39.4 (r = 5 members: the D_K route works; an A_9, r = 5 field over P).** [numerical] `engO_q4.py`; [exact] `engO_r5.py`.
- Line z_i(s) = h(x_i)²(1 + s x_i)/F'(x_i) (in K, real at real roots, P-rational; S29.1 up to the constant c). On 40 r = 5 members (a = −1, b ∈ {−2, −1, −½, 1, 2}, U ∈ {−7, −5, …, 7}): p1, p3, p5 vanish to 10⁻¹³ relative, the quartic Q4(z(s)) has real coefficients (imaginary parts 10⁻⁶¹), and **Q4|line has 2 real roots on all 40**.
- Example (a, b, U) = (−1, 1, 1): G ∝ −2909519x⁹ + 9178020x⁸ − 11787897x⁷ + 22297923x⁶ − 28619304x⁵ + 22794606x⁴ − 19194997x³ + 8654076x² + 322383x − 507674, c² = 6268501/2909519 > 0. Irreducible, **5 real roots**, disc > 0 and not a square in ℚ; 26 Frobenius cycle types mod p < 700, including 9, 7 and (7, 2): **Galois group S_9 over ℚ, A_9 over P with r = 5**.
- So (*unchecked* chain: S29.1 line + fact 3 on the quartic Q4|line + the D_K target) these A_9, r = 5 fields over P have P-constructible roots. Fixed 2-parameter family: nothing about a general K.

**S39.5 (consequences for the plan).**
- Item 3(b): the cheap invariant (resolvent factors) is gone (S39.2). What remains of versality is (ii) curves of low gonality in the twisted surface and (iii) heuristic counts. The structural fact to use is now S39.1: the family is branched only over Δ_h · A · B = 0.
- Engine O's role in the open-case table: r = 9 (A_9, S38.3), r = 5 (A_9, S39.4) for specific fields; never r = 7.

## 0q. Session 40 (Nov 18): results

Topic: plan item 3(c), Engine O against known families, by inertia (branch-type) invariants.

**S40.1 (inertia over Δ_h = 0; the complete branch data of Engine O).** [exact] `dh_member.py`; [numerical] `dh_mono.py`.
- At h = (x − 1)²(x + 2) (a = −3, b = 2) and U ∈ {1/3, 2, −5/7}, G factors exactly as (x − 1)⁶ · (irreducible cubic): the member over Δ_h = 0 has a **6-fold root at the node** of h.
- Looping b once around 2 (a = −3; U = 1/3 and U = 2; radius 10⁻³ and 10⁻⁴; no root of A or B in b within 0.5): **cycle type (2, 2, 2, 1, 1, 1)**. The six roots near the node pair up (they sit at distance ~ (b − 2)^{1/2}).
- So Σ(e − 1) = 3 against discriminant valuation 15: the order ℤ[x]/G is not maximal along Δ_h (6 roots at distance ~ Δ_h^{1/2} give C(6,2) = 15).
- **Complete generic branch data of Engine O on P(1,2,3):** Δ_h: (2³,1³); A (c² = 0): (7,2); B (c² = ∞): (2⁴,1); nothing else (S39.1). No branch curve has transposition inertia. A ∩ B ⊂ Δ_h (Res_U(A, B) ∝ Δ_h⁵, S38.1). Every U-line passes through [1:0:0], the cusp of Δ_h, where the monodromy of the U-line is trivial (S39.2).

**S40.2 (inertia lemmas for pullbacks).** *unchecked* (standard). Let S be a normal surface, K_S = C(S)[x]/G an étale nonic algebra with inertia class g_D at a prime divisor D. Suppose K_S ≅ φ*K_T for a family K_T over a base T and a rational map φ: S ⇢ T (φ is defined at the generic point of D).
- (I1) If φ maps D onto a curve Z ⊂ T (T a surface), or onto the generic point of T (T a curve), then g_D is a power of the generic inertia of K_T along Z (trivial if Z is neither branched nor an orbifold curve). In particular a divisor that dominates a curve base is unramified.
- (I2) If T is a curve and D ⊂ φ^{-1}(c) with multiplicity m, then g_D = g_c^m (g_c the local inertia of K_T at c, orbifold points included).
- (I3) (Cluster lemma.) If some generator of K_S over the completion at D has a characteristic polynomial whose reduction mod D (as a binary form, after any scaling) has root multiplicities (m_1, …, m_k), then g_D lies in a conjugate of S_{m_1} × … × S_{m_k} (Hensel over the strict henselisation). After a base change of degree e (needed to rescale a weighted family), apply this to g_D^e.

**S40.3 (Engine O is not a pullback of any trinomial family).** *unchecked* (short) + [exact] (`irr_pencil.py`).
- Trinomials x⁹ + ax^k + b (k = 1, …, 8) form a 1-parameter family over the weighted line P(9 − k, 9): scaling x is a Tschirnhaus map, so the family over A² is pulled back from this line. For k = 3, 6 the monodromy is imprimitive, which already excludes them (Engine O has monodromy S_9). For gcd(k, 9) = 1 the cover of the line has three branch points: a = 0 (x⁹ + b, orbifold μ_9: a 9-cycle), b = 0 (x^k(x^{9−k} + a), orbifold μ_{9−k}: type (k, 9 − k), e.g. (8,1) for k = 1 and (7,2) for k = 7) and the discriminant point (one double root: a transposition).
- By (I1) each of A, B, Δ_h must lie in a fibre of φ, and by (I2) its inertia is a power of one of these three elements. Powers of a 9-cycle, of type (k, 9 − k) and of a transposition give (7,2) only for k ∈ {2, 7} and (2⁴,1) only for k ∈ {1, 8} (as (8,1)⁴). So **no trinomial family x⁹ + ax^k + b pulls back to Engine O under any rational map**; in particular fact 2 is not a source of Engine O. (For k ≠ 7 the cluster lemma (I3) gives the same directly: no trinomial member has a 7-fold root except at b = 0 for k = 7.)
- Side facts [exact]: A and B are irreducible over ℚ and absolutely irreducible (the specialisation of A at (a, b) = (−1, 1/5) has Galois group S_6, and B has S_5 at three points; a splitting over ℚ̄ into k conjugate factors would give a block system, and k = 6 or k = 5 is impossible by weight, since there are no weight-1 forms in a, b). There is no pencil relation A^{5m} = B^{6m} + βΔ_h^{5m}: the coefficient of U^{30m−2} in A^{5m} − B^{6m} is −1386m·a.
- General criterion (*unchecked*): Engine O is a pullback of a 1-parameter family only if that family has three distinct branch points whose inertia has a power of type (7,2), (2⁴,1) and (2³,1³) respectively (no single element of S_9 has powers of two of these types), and φ has A, B and Δ_h each inside a fibre.

**S40.4 (the E-family, i.e. Engine S (9,5) with zero constant term: inertia test inconclusive).** [exact] `efam_disc.py` + *unchecked*.
- The E-family X⁹ + AX⁷ + BX² + C (base P(2,7,9), no orbifold curves) has discriminant equal to one irreducible curve (chart C = 1, exponent 1) plus the line C = 0 (a double root at X = 0); both have transposition inertia. The full trivariate discriminant times out in PARI; the chart suffices.
- By (I1), a rational map φ: P(1,2,3) ⇢ P(2,7,9) that pulls the E-family back to Engine O must be dominant (a non-dominant φ factors through a rational curve, and then the S40.3 criterion applies to the restricted family), must contract A, B and Δ_h to points, and must have even ramification along every curve of φ^{-1}(Disc_E) that dominates a branch curve.
- No contradiction yet: the orbifold point [1:0:0] (member X⁷(X² + 1): a 7-cluster plus ±i, stabiliser μ_2) has local group containing S_7 × S_2 (the 7-cluster deforms as the degree-7 trinomial X⁷ + BX² + C, and x ↦ −x swaps ±i), which contains all three Engine O types. *Open*: a global argument (degree, Euler characteristic) to exclude such a φ.

**S40.5 (consequences for the plan).**
- Item 3(c): Engine O is new relative to fact 2 in every trinomial shape (S40.3). Against the E-family the inertia test only constrains φ (S40.4). The test is cheap; fact 7 (T_9 + aT_q + c, 2 parameters) and fact 4 (x⁹ = cubic, P(6,7,8,9)) are next if item 3(c) is pursued.
- This does not change the open-case table: it only says that Engine O's fields are not obviously reachable through fact 2.
