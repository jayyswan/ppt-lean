# Sessions 37–38: full results (frozen archive)

Frozen on Nov 17, 2026 (session 39). This file holds Sections 0n and 0o of the condensed summary as they stood after session 38, unchanged. **Don't write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session here in its Section 0. Labels S37.1 … S38.4 point here.

## 0n. Session 37 (Nov 17, later): results

Topic: plan item 3(f), the arithmetic structure of the S_ord fibre over a fixed elliptic curve.

Setting. Fix C: y² = h(x) with h a cubic. Let **U_C** be the curve of *unordered* S_ord configurations on C, i.e. of squarefree monic F of degree 9 with F | F'² − c²h⁵ for some constant c (S29.1). U_C = V_C/S_9, where V_C is the curve of ordered 9-tuples in plan item 3(f). The constant c² is a function on U_C (it depends only on F; c ↦ −c is the negation Q ↦ −Q and gives the same F). Test curves: h = (x − d)(x + d)(x + 1) with d = 0.4 + 0.25i (start), D2 := d² = −2 (h = (x + 1)(x² + 2)) and D2 = 3 (h = (x + 1)(x² − 3)).

**S37.1 (the map U_C → c²-line has degree 6, with monodromy S_6).** [numerical] `track.py`, `rand_fib.py`, `mono2.py`, `perm.py`, `branch.py`, `resolv.py`.
- Fix h (d = 0.4 + 0.25i) and c² ≈ 269 (the value reached by `track.py 0.3 0.4+0.25j 200`). Random-start complex Newton in the log form (2 Σ_j log(x_i − x_j) − 5 log h(x_i) = log c², residual mod 2πi; 2 × 6000 starts) finds exactly **5** genuine solutions F, each many times. Monodromy in w = log c² (`mono2.py`, 2 × 60 loops) adds a **6th**, which random starts miss because it is three tight triples, one at each 2-torsion point. The count stays at 6 over 120 further loops.
- Shape of the fibre as c² → ∞ (*unchecked* reading of the samples, consistent with a balance count): 5 sheets are "one point near O (x ≈ c²) plus 4 close pairs" (pair separation ~ (c²)^{−1/2}), i.e. the S32.3 degenerate valley, and 1 sheet is "3 + 3 + 3 at the three 2-torsion points" (scale ~ 1/c², the 3-point local problem of S35.2).
- Monodromy. Local loops around 7 branch points found by a bordered Newton system (φ = 0, J v = 0, a·v = 1; `branch.py`) and random loops give only transpositions; winding once around c² = 0 at |c²| = 269 is the identity. One sheet was never moved by the loops tried, but the exact computation of S37.2 settles it: moved to the rational curve D2 = −2 and c² = 250, the six values of e1 = Σx_i are the roots of an **irreducible sextic over ℚ with Galois group S_6** (PARI `polgalois`). The geometric monodromy group is normal in the arithmetic one and contains a transposition, so it is S_6. **So U_C is irreducible and U_C → P¹_{c²} has degree 6 with monodromy S_6.**

**S37.2 (U_C is a rational curve, with coordinate u = e1(F) − c²).** [numerical, exact recognition] `resolv.py`, `interp.py`, `Rcurve.gp`. **Made explicit for every h and proved as an identity in S38.1–S38.2.**
- Method: move the 6 sheets to h = (x + 1)(x² − D2) with D2 rational and to integer c², polish each at 60 digits, and form R(T, c²) = ∏_k (T − e1(F_k)). Its coefficients come out as **integers** (to 10⁻⁴⁸). Interpolation in c² over 12 values (D2 = −2) and 9 values (D2 = 3) gives polynomials of degree ≤ 5 in c², with 6 and 3 redundant points as checks.
- For D2 = −2, with c := c²:
  R = T⁶ − (5c − 18)T⁵ + (10c² − 75c + 2265)T⁴ − (10c³ − 120c² + 6810c − 96856)T³ + (5c⁴ − 90c³ + 6840c² − 200330c + 762264)T² + (−c⁵ + 30c⁴ − 2310c³ + 110092c² − 965835c + 7727400)T + (−3c⁵ + 15c⁴ − 6618c³ + 203571c² + 200475c + 23692500).
- **Key identity.** Substituting T = c + u makes R *linear in c*: R = A(u) + c·B(u), with
  - D2 = −2: A = u⁶ + 18u⁵ + 2265u⁴ + 96856u³ + 762264u² + 7727400u + 23692500, B = u⁵ + 15u⁴ + 2250u³ + 90238u² + 558693u + 7927875;
  - D2 = 3: A = u⁶ + 18u⁵ − 4125u⁴ − 147404u³ − 1063341u² + 12283650u + 135320625, B = u⁵ + 15u⁴ − 4230u³ − 135122u² − 388107u + 19105875.
  So **U_C is birational to P¹ with coordinate u = e1(F) − c², and c² = −A(u)/B(u)**. This is consistent with S37.1: c² has degree max(6, 5) = 6; disc_T R has degree 10 in c² with simple roots (10 simple branch points; Riemann–Hurwitz 2g − 2 = −12 + 10 gives g = 0); c² → ∞ at the 5 roots of B and at u = ∞ (6 unramified places, matching the trivial monodromy at |c²| large).
- Status: exact for the two curves tested. (S38: general h done.)
- **Consequence (*unchecked*, short).** For any cubic h over P and any u ∈ P (with B(u) ≠ 0 and the resulting F squarefree), the unique point of U_C over u is Galois-invariant, so it gives **F_{h,u} ∈ P[x]**. A P-rational S_ord line for K gives h, c² and F = (characteristic polynomial of x) over P, hence u ∈ P. So: **S_ord has a P-point for K ⇔ K ≅ P[x]/(F_{h,u}) for some cubic h ∈ P[x] and u ∈ P.** (The line itself is z_i(s) = (1 + s x_i)F'(x_i)/h(x_i)³ up to scale, so it is P-rational even when c ∉ P.) (S38.2 gives F_{h,u} in closed form, so the first sentence is now an identity.)

**S37.3 (an explicit S_ord nonic over ℚ).** [numerical + exact check] `example.py`. Take D2 = −2 and u = −25, so c² = −A(−25)/B(−25) = 93825/4184. The sheet with e1 − c² = −25, polished at 90 digits and recognised, is
  4184·F = 4184x⁹ + 10775x⁸ − 21954x⁷ − 255050x⁶ − 730124x⁵ − 1093620x⁴ − 944440x³ − 446680x² − 81360x + 4320,
and PARI confirms **F'² − (93825/4184)·((x + 1)(x² + 2))⁵ ≡ 0 mod F exactly**. F is irreducible with 3 real roots; Frobenius cycle types mod primes < 2000 include 9, (1,8), (2,7), (1,1,7), so its Galois group is S_9. The six u-values over this c² are −25, −31.217 and two complex pairs, as R predicts.

**S37.4 (consequences for the plan).**
- **S_ord is the Tschirnhaus variety of an explicit rational 2-parameter family of nonics**, F_{h,u}: the cubic h up to affine maps (j, plus a sign twist, since P is Euclidean) and u ∈ P¹. This puts S_ord in the same position as E (S28.1, Engine S (9,5)) and the S29.5 remark: S_ord is an engine. By the session 28 method lesson it is **not a new mechanism for a general K**. A P-point for K exists iff K is a P-specialisation of the S_9-family F_{h,u}, i.e. a versality question for one explicit rational 2-parameter family. (Heuristic, not a proof: ed(S_9), ed(A_9) ≥ 4 over generic fields, so a 2-parameter family can't be versal there; this says nothing about P-points over P itself. Same caveat as S28.2.)
- **New engine (*unchecked* chain).** Every totally real F_{h,u} with h, u over P (Galois group A_9, S_9 or PSL(2,8) over P) has a P-line in L_135 off the pairing spaces, so its roots are P-constructible by T2 (p7 + odd engine), or by the D_K route where Q4|line has a real root. This is a genuinely new 2-parameter family of P-constructible nonics ("Engine O"), not in T0–T7. It does not cover a general K.
- Plan item 3(f) is answered in a stronger form than asked: the trace map V_C → C is not needed. Over P̄ the curve V_C is a 9!-fold cover of U_C ≅ P¹, so maps from the twisted V_C^K to P¹ defined over P (which must be invariant under the Galois action of K) have degree ≥ 9!/|G|·deg ≫ 8, and Theorem G cannot apply to V_C^K. The arithmetic content is entirely in S37.2.
- The line frontier is now: **is K a P-specialisation of Engine S (9,5) (the E component) or of F_{h,u} (the S_ord component)?** Both are explicit rational 2-parameter families. The conic frontier (C_b^gen) should be tested the same way next: is C_b^gen/S_9 also a rational (or low-degree) cover of a 2-dimensional rational base? If so, every curve route through L_135 reduces to versality of explicit families, and the project's real question is (PRC₈)-type versality, not a cleverer curve.

## 0o. Session 38 (Nov 17, later): results

Topic: plan item 3(a), Engine O made explicit for every cubic h, plus a totally real example.

Setting. Every cubic over P has a root in P (fact 3), and P ∋ 1/3, so h can be depressed over P: **h = x³ + a x + b**, with a, b ∈ P. Put **U = e1(F) − c²** in these coordinates (U = u + 3 for the S37.2 normalisation h = (x + 1)(x² − D2), since x ↦ x − 1/3 shifts e1 by −3 and leaves c² alone). Scaling x ↦ λx gives weights x, U, c², e1: 1; a: 2; b: 3; e_k: k. The S_ord condition F | F'² − c²h⁵ is weighted homogeneous.

**S38.1 (A and B in closed form).** [exact fit, then exact identity in S38.2] `engO_AB.py`.
- By weights, A (weight 6, monic in U) and B (weight 5, monic) have only 7 and 4 unknown constants, and the U⁵ term of A and the U⁴ term of B must vanish. Depressing the two S37.2 curves confirms the vanishing and determines every constant (10 equations for 7 unknowns in A, 8 for 4 in B, all consistent):
  - **A(U) = U⁶ + 1278a U⁴ + 50274b U³ + 3321a² U² + 2357586ab U − 1822500a³ + 6751269b²**
  - **B(U) = U⁵ + 1296a U³ + 50112b U² + 27648a² U + 2985984ab**
  - **c² = −A(U)/B(U)**.
- Res_U(A, B) = const · (4a³ + 27b²)⁵ [exact], so A and B are coprime for every smooth h. disc_U(B) = const · a · (4a³ + 27b²) · (824464a⁶ + 2282977224a³b² + 14952627621b⁴) [exact].
- The constant term of A (fitted from 2 equations in 2 unknowns) was then confirmed independently on 57 new exact points (S38.2).

**S38.2 (Engine O in closed form; an exact identity).** [exact] `engO_F.py`, `engO_F2.py`, `engO_fit.py`, `verify_pts.py`, `engO_proof.py`; the formula is in `scripts/EngineO.gp`.
- Data: Newton continuation (70 digits) from the S37.3 polynomial to 6 curves (a, b) ∈ {(1,1), (−1,1), (2,−1), (1,−2), (3,1), (−2,3)} and U ∈ {−4, …, 5}, rational recognition, then an exact PARI check of F | F'² − c²h⁵, c² = −A/B, e1 = c² + U: 54 of 60 points pass (the 6 failures are all U = 0, a recognition failure only), plus 3 earlier points.
- **Theorem (computer-checked identity).** Let G(x; U, a, b) = B(U)·x⁹ + Σ_{k=1}^{9} (−1)^k E_k x^{9−k}, with the integer polynomials E_k = B·e_k listed in `scripts/EngineO.gp` (weight 5 + k, degree ≤ 5 in U). Then **G'² + A·B·h⁵ ≡ 0 mod G in ℚ(a, b, U)[x]** (pseudo-remainder computed symbolically; a control with A replaced by A + 1 gives a nonzero remainder). Hence for all a, b, U in any field with B(U) ≠ 0: **F_{h,U} := G/B satisfies F | F'² − c²h⁵ with c² = −A/B, and e1(F) = c² + U** (the E1 line is −A + U·B).
- So **Engine O is the family G(x; U, a, b) = 0, weighted homogeneous of weight 14, parametrised by the weighted projective plane P(1, 2, 3) ∋ (U : a : b)**. Every coefficient is a polynomial with integer coefficients; for instance E_1 = 18aU⁴ − 162bU³ + 24327a²U² + 628398abU + 1822500a³ − 6751269b² and E_9 = −b³U⁵ − 6a²b²U⁴ − (45a⁴b + 1242ab³)U³ − (225a⁶ + 5184a³b² + 44037b⁴)U² − (7830a⁵b + 109539a²b³)U + 8100a⁷ + 83835a⁴b² − 571536ab⁴.
- Structure in U [exact]: G = Σ_{i=0}^{5} G_i(x)U^i with **G_5 = h³**, G_4 = const·h²·(3ax² + 9bx − a²), G_3 = h·(a sextic); G_2, G_1, G_0 are not divisible by h. (Matches S37.1: as U → ∞ the configuration is 3 + 3 + 3 at the roots of h.)
- That these F_{h,U} are *all* of S_ord: for each c² the 6 roots U of A + c²B give 6 configurations with distinct e1, which by S37.1 (degree 6, [numerical] for one h, exact S_6 at one rational point) is the whole fibre of U_C. So U_C ≅ P¹_U for every smooth h with the 6 roots distinct (*unchecked* beyond the generic case).
- Row E test (item 3(c), first part) [exact]: on 6 exact members the centred power sums give 25p3p7 − 21p5² ≠ 0, so **Engine O is not contained in row E** (as literal polynomials; Tschirnhaus equivalence not tested). The discriminant class of F_{h,U} over ℚ showed no simple pattern (neither disc nor disc·disc(h) is a square on 6 members); over P this is moot (only the sign matters). (S39.1 gives the discriminant exactly.)

**S38.3 (a totally real Engine O nonic over ℚ, Galois group S_9).** [exact] `engO_scan.py`, `engO_example.py`.
- The real locus of S36 says totally real S_ord lines need j(h) < −6.1·10⁴, i.e. h close to a crunode. Scan: h = (x + 1)(x² + β²) with β = 1/40 (j ≈ −1.02·10⁵), U over [−60, 60] in steps of 1/4 (S37.2 coordinates shifted by 3; the script works in the depressed coordinates). G has 9 real roots for U ∈ [9.5, 11.25] (8 grid values), and fewer elsewhere in the range.
- At U = 10 (depressed coordinates): c² = 2047298983439/53280538624 > 0, and in the original coordinate (h = (x + 1)(x² + 1/1600))
  **F = 349179337926246400000000x⁹ − 15861433983349555200000000x⁸ + 13017889976458149888000000x⁷ + 117860826255769600000000x⁶ − 264501554157059112960000x⁵ − 9636896194613806080000x⁴ + 277031020722445312000x³ + 2545978749366393600x² − 35558478089957760x − 250476491015279.**
- Exact: F | F'² − c²·lc(F)²·h⁵; F irreducible; 9 real roots; h(x_i) > 0 at all of them (so the S_ord line is real); disc(F) not a square; Frobenius cycle types mod p < 5000 include 9, (2,7), (1,1,7) and 25 types in all, so the Galois group is S_9 over ℚ (a 7-cycle in a primitive group gives A_9 or S_9, and (2,7) is odd). Over P it is A_9 (disc > 0 is a square in P).
- So Engine O does reach the open case "A_9 over P, r = 9" for specific fields: by S37.4 (*unchecked* chain) this field's roots are P-constructible via T2. It is a fixed 2-parameter family, so this says nothing about a general K.

**S38.4 (consequences for the plan).**
- Item 3(a) is done: Engine O is an explicit, exactly verified 2-parameter family G(x; U, a, b) over ℤ. The S_ord line route for a given K is exactly the question **"is K ≅ P[x]/G(x; U, a, b) for some (U : a : b) ∈ P(1,2,3)(P)?"**
- Engine O now belongs in the tool list as a proved family (the S_ord ⇔ line equivalence is S29.1, *unchecked* but complete; the P-constructibility of totally real members is the S37.4 chain through T2, *unchecked*).
- Next for S_ord is versality (item 3(b)), and the conic engine test (item 4(a)) is still the main open curve target. With an explicit G, invariant-hunting for 3(b) is now cheap (e.g. compute resolvents or the trace form of G symbolically in (U, a, b)).
