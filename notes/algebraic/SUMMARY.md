# Every real algebraic number is P-constructible: summary

This summarizes `pptc/PLAN-algebraic.md`. First written 2026-11-04 (waves 1–2); §§5–7 added
2026-11-05; **§§8–10 and the status table updated 2026-11-06 (Phase D: Y1, Z1–Z8, A1–A2, B1–B3)**.
The sources are the notes in this folder. Labels follow the notes. Nothing here is a negative about
the target: every obstruction is scoped to the route it blocks.

**Where things stand, in one paragraph.** Every real algebraic number of degree ≤ 8, and every one
with a solvable Galois group, is P-constructible. Degree 9 is done when there is a nonreal root.
In general, every real algebraic number is P-constructible if Taylor's question has a positive
answer (Theorem X), but that is sufficient, not necessary. Every unconditional route now ends at
the same kind of problem: a P-point on a variety of general type, defined over ℚ and twisted by
the target field, with smooth real points (§10). The sharpest instances are one P-line on an
explicit surface (totally real nonics) and one P-line on an explicit 3-fold (totally real decics).

## 1. Status by degree

| degree | case | status |
|---|---|---|
| ≤ 8 | P coefficients | done in Lean |
| any | solvable Galois group | proved via complex radicals (X1, W3); Lean-feasible, not in the repo |
| 9 | ℚ, nonreal root | done in Lean (`Nonic/Nonic`) |
| 9 | P, s ≥ 3 | on paper (THREE-PAIRS); the rational certificate centre is a Lean convenience only, so it is an F-construction (Z8) |
| 9 | ℚ totally real, G ⊇ A₉ or PSL(2,8)/PΓL(2,8) | open. **Reduces to one P-line** in {p₁ = p₃ = p₅ = 0} ⊂ ℙ⁷ off the pairing ℙ³'s (Z8, confirmed A2; Lemma N gap closed B1). PSL(2,8) behaves like A₉ (B1) |
| 9 | P with s ≤ 2 | open |
| 10 | imprimitive, or primitive with G ≠ A₁₀, S₁₀ | towers of degree ≤ 6 steps (H5) [Wolfram chains; group list from memory] |
| 10 | ℚ, nonreal root, G ⊇ A₁₀ | **route found, one ingredient missing** (MI-1, §2); the MI-2 line reduction is vacuous for s = 2, 3 (A2) |
| 10 | ℚ totally real, G ⊇ A₁₀ | open. **Reduces to one P-line** in Y₀ = {p₁ = p₃ = 0, S₆ = 0} via Engine C (B2) |
| 11 | any | open; every transitive group needs a degree-11 engine step; no single-line reduction (B2) |
| ≥ 9 | all | **conditional on (SR) / Taylor's question** (Theorem X, §6) |

## 2. Degree 10: the first case beyond the frontier (H5)

- **Engine:** `power_law 10` against a rational sextic `poly_graph`. It needs a rational τ ∈ K with
  p₁ = p₂ = p₃ = 0, i.e. a ℚ-point of V'_K = {quadric} ∩ {cubic} ⊂ ℙ⁸.
  - V'_K is a smooth complete intersection [Proof].
  - It has dimension 6, degree 6 and −K = O(4), so it is Fano.
- **Recovery:** τ has degree ≤ 8 in x, so the octic theorem (or a gcd) recovers β. This uses
  only Lean-proved degree ≤ 8 results, not the degree-9 case.
- **Worked example [Wolfram, re-checked by the orchestrator].**
  - The decic is q = x¹⁰−10x⁸+35x⁶−50x⁴+25x²−x−3. Its Galois group is S₁₀:
    - a 7-cycle from the (3,7) factorization mod 7 gives primitivity and Jordan's theorem;
    - type (3,3,4) mod 11 is an odd permutation.
  - q has 8 real roots.
  - τ = −4+6x+38x²−30x³−57x⁴+19x⁵+24x⁶−3x⁷−3x⁸ gives
    χ_τ = y¹⁰ − 6557y⁶ + 1501y⁵ + 172900y⁴ + 136838y³ − 710506y² − 358949y + 9839.
  - So **every real root of this S₁₀ decic is P-constructible**, modulo writing it out. The point
    was found by LLL on the trace-zero lattice in the Minkowski metric, then a box search to ±3.
- **Missing ingredient MI-1:** V'_K(ℚ) ≠ ∅ for every decic field K with a nonreal embedding.
  - Real points and good-prime local points are fine; bad primes are open.
  - The known Hasse principles need about 30–37 variables, and we have 9.
  - The search succeeded for s = 1, 3, 5. At s = 4 none was found up to height 4.

## 3. General n: what waves 1–2 established

- **The bookkeeping law** (H1, H2, H3).
  - A drawable family with F free parameters leaves about n + 1 − F conditions on τ [Proof].
  - Every measured family has F ≤ 8–13, independent of n.
  - Offset towers are the one exception: 3 parameters per layer, but degree ~2ʲ (G2).
- **Cheap conditions** (H2, Lemma A [Proof]).
  - Over F_{<n} one can satisfy the conditions defining a variety of degree < n that has a smooth
    real point.
  - So p₁…p_k can be killed when k! < n. That grows like log n / log log n (a real form of Brauer).
- **Realness** (H2, N4, H1 [Proof]).
  - Killing p₁…p_k needs s ≥ ⌊k/2⌋.
  - A totally real K allows only p₁, and needs gap ≤ 2 supports.
  - A family with F coefficients serves totally real fields only for n ≤ 2F − 2.
  - The square lift fixes realness but roughly doubles the number of conditions (H2, H3).
- **Arithmetic** (H3, H5).
  - Rational τ makes rational `poly_graph` engines usable, which is how degree 9, and degree 10
    in §2, work.
  - Theorems on forms in many variables stop at n = 9.
  - From n = 10 on, finding ℚ-points on Fano complete intersections is the crux. Search succeeds
    in practice; a general theorem is missing.
- **Transcendental** (H4).
  - Elliptic division values give only A₅ and PSL(2,p) [Proof mod Dickson].
  - Aₙ for n ≥ 9 needs a transcendental step whose monodromy contains Aₙ. Higher-genus theta
    functions would supply one, but they need an inverse-period operation P lacks.
  - Offset towers with more than 5 free branch points are open.

## 4. Leads for wave 3

1. **MI-1, the arithmetic of V'_K.**
   - Rational points on smooth (2,3) complete intersections in ℙ⁸ that come from trace forms.
   - Exploit structure: the quadric has a ℚ-point by Meyer, it is rational, and it contains
     rational linear spaces of dimension equal to its Witt index. Look for conic or quadric
     fibrations, or cubic sections of low degree.
   - Fallback: a uniform construction for a family of K.
   - Also: does the same shape generalize, i.e. n = 11 with p₁..p₄ (degree 24) or overshoot?
2. **The concrete Lean target** "this S₁₀ decic's roots are P-constructible". It is the first
   degree-10 Galois-generic number, and needs only the degree-8 theorem and the power_law/sextic
   engine.
3. **Engines whose parameters grow with n:** offset towers in overshoot mode. Measure the cost.
4. **H1's two-graph engine** τ = R(P(τ)) (degree 36, about 12 of 14 parameters effective, no
   Descartes limit), and H3's F = 9 and F = 13 families, at n = 10–12.
5. **Transcendental:** inverse periods via offset towers (H4 open item).

## 5. Wave 3 (W1–W3, 2026-11-05)

- **W3, transcendental.** No transcendental route to Aₙ (n ≥ 9) survives. This is scoped to:
  - offset-tower periods, which stay elliptic with ≤ 5 free branch points;
  - period-map inversion, which needs a speed containing K² [Proof mod Kovacic];
  - Ritt and Lattès, which give only cyclic, A₅ and PSL(2,p) factors;
  - crossings with the sine and `exp_two`, by Lindemann–Weierstrass, Gelfond–Schneider and
    Pila–Wilkie.
  - **Positive:**
    - complex radicals are free (cos and sin of P-angles), so every real algebraic number with a
      solvable Galois group is P-constructible [proof sketch; Lean-feasible, not stated in the
      repo];
    - cos(2π/23) shows P ∩ ℝ_alg goes beyond the bounded-degree tower.
- **W1, offset towers.**
  - The rank is 3j+2 against a line and 3j+4 against a circle (new), with no collapse. A depth-2
    tower × circle has M = 10 at n = 10, so there are zero conditions on τ.
  - Realness is trivial [Proof].
  - The cost: from depth 2 the genus is ≥ 1, and each non-conformal layer adds a genus-1 square
    condition. Even one condition gives a locus of degree ≥ 42. No sequential construction was
    found.
  - The n = 10 totally real S₁₀ test did not find τ [Open].
  - Would unlock the route: layers whose square condition is rational.
- **W2, big-F engines.**
  - The families are nested: A = C (degree 36, rank 12–13, versal for n ≤ 12, real capacity 36);
    B is the sideways parabola × sextic, with 2/3/4 conditions and degrees 420/945/945.
  - B-engine fields with Galois group S₁₀, S₁₁ and S₁₂ exist with every real-root pattern, so the
    engine *step* carries Sₙ up to 12.
  - LLL search on arbitrary fields found nothing. A and C have no polynomial form in τ to search
    with.
  - Next: the sextic power-law engine at n = 11, with heuristic exponent +1 (forms of degree 2, 3, 4
    in 10 variables), is the best LLL target for a first at n = 11.

### Bottom line after three waves
- **Degree 10, rational with a nonreal root:** a route exists and works on examples; it hinges on
  MI-1.
- **General n:** the obstacle has moved from *parameter count* (now met by offset towers and the
  A/C family up to n = 12) to *finding points on positive-genus or high-degree incidence varieties*
  over F_{<n}.
- Transcendental side-doors are closed, scoped as above.

## 6. X1: Galois-class induction (Opus, 2026-11-05)

- **The right formulation [Proof].** Use H_ℂ(n): "F(i) is closed under roots of degree ≤ n over
  F(i)", where F = P ∩ ℝ_alg. Real α ∈ P ⇔ α ∈ F(i).
- **Solvable numbers [Proof].** Every real algebraic number with a solvable Galois closure is in P,
  via complex radicals: `sqrt`, `arccos`, `rpow`, `cos`/`sin`. This is Lean-feasible and not yet in
  the repo.
- **The Galois-class base case is open.** Three conjugation configurations are unreachable by real
  towers of degree ≤ 8:
  - the swap T×T. Example: u = 2 Re z with z⁵+z+1+2i = 0 has degree 25 and factors A₅,A₅, and needs
    a real step of degree ≥ 25;
  - A₈ with fixed-point-free conjugation;
  - PGL(2,9) with conjugation outer.

  The missing ingredient is **(BR_n)**: roots of zⁿ+z+c lie in F(i) for complex c ∈ F(i).
- **Inductive-step tests.**
  - W1's square condition concerns K-points, which enlarging L does not change.
  - MI-1: the enlarged field kills p₂ = p₃ = 0 at degree 10 [Proof]. Only the rationality of two
    sextic affine invariants remains (degree 30 each in τ); field enlargement cannot help with
    rationality conditions. *[Too strong, Z8: once a rational shape is fixed the condition is
    algebraic; for MI-1 special orbits cut the fibre degree from ~5400 to ~2016, still > 8.]*
- **Theorem X [Proof, conditional].** Every real algebraic number is P-constructible **if (SR)**:
  - **(SR):** the twisted trinomial variety I_{K'} has a point over ℚ^solv ∩ ℝ for every number
    field K' with ≤ 2 real places.
  - The route:
    1. square lift: K' = ℚ(√(β−c)), with ≤ 2 real places;
    2. trinomial engine: `power_law 1 D` (D a fixed integer; power_law only takes rationals)
       × a line whose slope and intercept are free in P;
    3. gcd recovery.
  - It needs no `poly_graph` and no degree induction.
  - (SR) follows from a positive answer to **Taylor's question** (totally real solvable numbers are
    PSC; Bary-Soroker–Fehm arXiv:1106.1310 §3.2), which is open. The analogue for all totally real
    numbers is known (Moret-Bailly; Green–Pop–Roquette).
  - **Sufficient, not necessary (Z8).** The route needs points over F = P ∩ ℝ_alg, which strictly
    contains ℚ^solv ∩ ℝ. A negative answer to Taylor's question would not block it.
  - **No expert expectation either way.** Taylor, posing it (Question 5.5, "Galois
    representations", Ann. Fac. Sci. Toulouse 13 (2004) p. 73–119): "it would have extremely
    important consequences if the following question had an affirmative answer. I do not know if
    it is reasonable to expect one." Bary-Soroker–Fehm call even the weaker "is ℚ^solv PAC" a
    "long-standing open question".

## 7. X2: Wooley-type recasting (Opus, 2026-11-05)

- **Real Wooley, Theorem RW [Proof, relying on Wooley Cor 4.5].** Let L ⊂ ℝ be a number field and X/L
  smooth with a smooth real point and dim X ≥ exp(2^{D+2}(log D)²). Then X has a point over a real
  quadratic extension of L, hence over ℚ^solv ∩ ℝ ⊆ P.
  - Diagonal forms over E = ℚ^solv ∩ ℝ have a zero iff they have a real zero, so E is a Birch field
    (Lampert–Snowden).
- **No existing engine lies in RW's range [Proof]:**
  - none of the rewritings (auxiliary variables, cofactors, cones, Weil restriction) raises the
    dimension usefully;
  - the degree is ≥ c+1, so even one condition needs n ≥ 2184 under RW;
  - MI-1 has dimension 6, against bounds of 16 to 2180;
  - Theorem X's trinomial surface faces a bound of ~10^(10^1517).
- **(BD)**, which would close every n via RW: a drawable family with unboundedly many P-parameters
  whose crossing conditions have *bounded degree* in them. Whether one exists is open; offset towers
  have the parameters, but their degree grows.
- **Theorem O [Proof, conditional on one rational point].** For n = 9…13 there are exact
  rational-`poly_graph` engines that also work for **totally real** q:
  - odd n: χ_τ = t·Q(t²) − c;
  - even n: χ_τ = Q(t²) + c·t (new);
  - both are `poly_graph` Q crossed with `power_law` c·x^(∓1/2).

  The only missing piece is a nonzero rational point on the odd complete intersection O_m. Points
  are heuristically rare, with count exponent −7 to −23. *[Superseded, Z8/A2: no rational τ is
  needed. The P-valued freedom of a rational degree-d `poly_graph` leaves d − 4 rationality
  conditions (1 at n = 10, 11; 2 at n = 12, 13), plus an F-point on O_m. The height heuristic
  concerns ℚ-points only. See §9.]*
- **Lemma N [Proof].** If Gal ⊇ Aₙ, every nonzero trace-zero τ has distinct conjugates and no
  τᵢ = −τⱼ.

## 8. What PowerPoint can and cannot add (Y1, Z1–Z7, 2026-11-05)

- **Minkowski reformulation (Y1a, Prop T) [Proof + Wolfram].** An offset/affine tower is
  base ⊕ Σ d_j·ellipse_j: x(s) = G(s) + Σ d_j ε_j B_j u/√Q_j, with B_j = M_j M_jᵀ for the affine maps
  drawn after layer j. Offsetting is Minkowski sum with a circle; later affine maps make the circles
  ellipses, whose support functions are square roots. Each new parameter brings a new square root.
- **Theorem R (Y1a) [Proof].** n − 1 non-homothetic positive-definite binary forms Q_j with Q_j(τ)
  a square in K_L give β ∈ P, totally real included. The needed variety V_τ is a complete
  intersection of n − 3 diagonal quadrics: K3 at n = 6, general type for n ≥ 7.
- **No square-root-free addition exists (Z4) [Proof sketch].** Every curve constructor is unary
  with numeric parameters, so curves depend on each other only through P-numbers. Offsets add only
  ellipses. Scale by 0 gives a root-free summand, but it is ±p, constant on each branch, i.e. a
  translation. A useful summand would need a non-constant offset.
- **The UI has no two-curve operation (Y1c, Z1, Z6).** Strokes are disk pens; chart smoothing is
  local Catmull-Rom; trendlines stop at order 6; Morph blends (1−w)A + wB but w is a clock value
  and no frame is readable; text-warp guides are presets; equation glyphs are discrete; picture
  tools are raster or preset clips; ink is freehand. Unmeasured: inserting a 3-D model via the
  ribbon.
- **Other engines (Z2, Z3).** Shape C costs more than the odd route. Bézier × y = a·x⁻² has 2
  conditions. The offset cusp is legally readable (restrict + box) with an S₁₂ polynomial, but as an
  engine it is dominated (n − 5 conditions, ≤ 8 real cusps). By-product: box readouts of offset
  cusps give the centre of curvature where the curvature takes a prescribed value.
- **Rational curves on V_τ (Z5) [Proof sketch].** For n ≥ 9 and Gal ⊇ A_n, an L-curve C ≠ ℓ_τ on
  V_τ of genus g and degree e satisfies (n − 8)e ≤ 4g − 4. No genus 0 or 1, for any τ.
- **Multi-crossing readout (Z7) [Proof].** Reading α from several crossings is never cheaper than
  from one: any scheme needs a root orbit of size n (the factor case), 2n or ≥ C(n,2) for n ≥ 9
  (A1 confirmed; exceptions only for n ≤ 8), and the condition variety maps onto the factor-case
  one, so it is never geometrically easier.

## 9. F-points instead of ℚ-points (Z8, A1, A2, B1–B3, 2026-11-05/06)

- **The key fact.** P is closed under real roots of degree ≤ 8 polynomials with P-coefficients,
  hence under real towers of such steps, and contains all solvable real numbers.
- **Over-constraints found (Z8).** Theorem O needs no rational τ (d − 4 rationality conditions;
  confirmed A2). Z5's "genus ≥ 2 ⇒ Faltings" does not apply over F. The THREE-PAIRS centre is a
  Lean convenience. Theorem X needs F-points, not solvable ones.
- **Theorem G (A1) [Proof].** A curve over a subfield of P with a real point has P-points dense in
  its real points if a chain of maps to ℙ¹ (or a conic), each step of degree ≤ 8 or solvable, is
  defined over a subfield of P. Unconditional for genus 0 and 2–5, hyperelliptic, trigonal, degree
  ≤ 8 curves and general genus 6; any genus ≤ 8 with one P-point. Brill–Noether pencils are only
  geometric, so "genus ≤ 13 suffices" is false.
- **Lemma N over F (B2, B1) [Proof].** For totally real nonics the group over F∩Ω is trivial
  (β ∈ P), A₉, or PSL(2,8) acting sharply 3-transitively; Lemma N holds in each case. The mod-2 heart
  is irreducible for A₉ and PSL(2,8), so Z5 also covers PSL(2,8)/PΓL(2,8).
- **Two one-line reductions [Proof of reduction].**
  - Totally real S₉/A₉ nonics ⇐ one P-line in {p₁ = p₃ = p₅ = 0} ⊂ ℙ⁷ off the pairing ℙ³'s
    (Z8; the last step is a septic, so a real root exists and lies in P). Real good lines exist.
  - Totally real S₁₀/A₁₀ decics ⇐ one P-line in Y₀ = {p₁ = p₃ = 0, S₆ = 0}, via **Engine C** (B2):
    the affine image of a rational quintic graph × an axis-aligned P-conic, crossings = roots of
    H² + q; Theorem O at n = 10 is its case σ = τ². Real non-degenerate lines exist.
  - The analogous decic MI-2 reduction is vacuous for s = 2, 3 (A2, numerical). n = 11 admits no
    single-line reduction (B2).
- **Why these don't close yet.**
  - V_τ: expected dimension of {(τ, C)} is g + 5 − 3e ≤ −16 for every curve type Theorem G could
    use (B1). Such curves exist over F̄ for special τ, so the obstruction is F-rationality.
  - The line families S (nonics) and T (decics) are defined over ℚ, of general type
    (K_S = O(13), K_T = O(18)), deg S ≥ 25; their natural F-pencils have degree ≥ 12 (B3).
    The failure, and any success, is uniform in K.

## 10. The frontier (2026-11-06)

**The clean question.** Let E be the real field generated from ℚ by real roots of polynomials of
degree ≤ 8 (iterated) together with all solvable real numbers, so E ⊆ F. Every route in §§6–9 would
close if:

> **(PRC₈)** Every smooth variety over ℚ (here: twisted by a number field) with a smooth real point
> has a point over E, or at least over F.

This is a "pseudo-real-closed" property for bounded-degree real towers. Taylor's question is its
solvable analogue; Moret-Bailly / Green–Pop–Roquette prove it for the field of all totally real
numbers. We know of no result for bounded-degree towers.

**Concrete open targets, in order of promise.**
1. One P-line on the nonic surface S, or on the decic 3-fold T (§9). The intrinsic curves
   Γ₇, Γ_{2,4}, Γ_pl on S have unknown F-gonality (B3 open); the irregularity and any fibration of
   S are unknown; real counts on T timed out.
2. MI-1: ℚ-points on the (2,3) complete intersection V'_K (degree 10, nonreal root).
3. A two-curve or non-constant-offset operation in PowerPoint (none found; would need a Defs
   change, the user's decision).
4. Z9: hyperelliptic / theta route (Umemura), pending external results on hyperelliptic
   functions in P.

**Literature check on (PRC₈) (L1, 2026-11-06; search snippets only).** Not found anywhere: no work
on PAC/PRC/ample properties of fields closed under bounded-degree roots, nor of origami, neusis or
Pierpont fields. "Is ℚ^solv PAC" remains open (Fried–Jarden Problem 10.16(a); Bary-Soroker–Fehm).
Northcott is no obstruction: a Galois PAC field with Northcott exists (Fehm, arXiv:1708.06599), and
our field contains all roots of unity, so it isn't Northcott anyway. Nearest results: Pál 2006
(curves of genus 0, 2, 3, 4 have solvable points; local failures from genus 40), Çiperiani–Wiles
(genus 1), Rawson arXiv:2211.10367 (conditional on Bombieri–Lang, non-density for genus ≥ 5 quotients).
So (PRC₈) appears genuinely open and unstudied.

**P1 (2026-11-06): (PRC₈) for Fano complete intersections.** Local solubility is free over E
(Lemma LS, Grunwald–Wang), so any smooth X with a real point satisfying the Hasse principle and
weak approximation over number fields has dense E-points (Theorem H): hypersurfaces with
N ≥ (d−1)2^d, any X with dim ≥ (D−1)2^D − 1. E is Euclidean, which settles many low-dimensional
quadric-containing CIs (Theorem W). Rational connectedness alone gives nothing unconditional. None
of it reaches the general-type varieties the routes need. Proof sketches; see P1.md.

**WARP (2026-11-10): text-warp engines.** The new `PConstructibleCurve.text` constructor
puts warped glyph outlines in the class; the algebraic ones are rational quartics (egg,
piriform, Gerono). A single warp adds no new numbers (line/conic intersections are degree
≤ 8 with P coefficients). The useful content is as an engine component: egg × quintic graph
is a degree-10 engine with F = 9 (one more than the MI-1 sextic engine), and egg × sextic
graph is a degree-12 engine with F = 10 (still below H5's F ≥ 11 for totally real decics).
No goal is closed; the F-point problem is unchanged. See `WARP.md`.
