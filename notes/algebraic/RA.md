# RA: the "Real Algebraics" side project (sessions 1–24), imported and cross-referenced

Imported 2026-11-17 from the side project's condensed summary ("Condensed summary: plan and
progress (through session 24)"). That project ran separately from this repo and, by its own ground
rules, did not read the repo. Its precise statements and proofs are in its own findings log, which is
not copied here; labels such as S22.1 or Theorem J point into that log. Its confidence labels are
kept as given ("Proved, high", "sketch", "*unchecked*" = its own argument, not checked against a
source). Nothing here has been re-proved in this repo unless marked **[checked here]**.

Notation follows RA: `L` = real numbers in ℚ^solv, `P` = real algebraic P-constructible numbers
(this repo's F), `r` = number of real roots, `s` = number of nonreal pairs (r + 2s = n).

## 0. What RA was doing, in one paragraph

RA treats P as a black box given by seven facts (§1) and works entirely **over P**: a degree-9
element over P whose Galois group over P is A₉, S₉ or PSL(2,8). It looks for one P-point on one of
three twisted varieties in the trace-zero ℙ⁷ of a nonic field K (§3). It proved strong *uniform*
obstructions (no construction rational in the conjugates plus radicands lands on its targets) and
found that every target is of general type. Its newest positive tool (session 24) is genus-one:
P-points on genus-one curves with a real point and period 2^a·3^b, or with CM Jacobian.
**No nonic case was closed in RA.**

## 1. RA's seven facts, mapped to this repo

| RA fact | statement | in this repo | backing |
|---|---|---|---|
| 1 | P is a field containing L | `PConstructible` field constructors; `root_Pconstructible_of_solvable_gal` (`Solvable/Main.lean`) | **Lean** (for ℚ-polynomials; the over-P form, RA's Lemma C.1, is paper only) |
| 2 | real roots of x^D + ax + b, a, b ∈ P | special case of fact 4 | **Lean** (`powerLaw_cubic_root_Pconstructible`, `Basic.lean`) |
| 3 | real roots of degree ≤ 8 over P | `root_Pconstructible_deg8_coeffs` (`Octic/Main.lean`) | **Lean** |
| 4 | x^D = c₃x³ + c₂x² + c₁x + c₀, D > 3, cᵢ ∈ P | `powerLaw_cubic_root_Pconstructible` | **Lean** |
| 5 | U³ + λU² + V² = 0, U monic cubic, V cubic (degree 9, 8 params) | Bézier × Bézier, D0 row **M1** (one Bézier implicitised as a singular cubic) | constructors (`cubic_bezier`); no root lemma |
| 6 | (Ac + Be − C)²(c′² + e′²) = d²(Bc′ − Ae′)², c, e cubics (degree 10) | offset Bézier × line | constructors (`offset`, `cubic_bezier`); **not in D0's census** |
| 7 | T_p(x) + a·T_q(x) + c = 0, roots in [−1, 1] | Engine S of `C1.md` | constructor (`sine`); paper |

RA's target D_K (real roots of C(t)³ + A(t), C, A cubics) is D0 row **N** (Bézier × y = x³,
c_τ = 2) **[checked here]**.

## 2. What RA was not using that this repo has

### 2.1 Results that change RA's case list

1. **Lean: rational nonics with a nonreal root are done** (`root_Pconstructible_of_rat_nonic_nonreal`,
   `Nonic/Nonic.lean`). RA's frame is "Galois group over P", which is more general than RA's stated
   goal needs. For K defined over ℚ, the Lean theorem settles RA's cases PSL(2,8) r = 1,
   A₉ r ∈ {1, 5} and S₉ r ∈ {3, 7}. For the goal "every real algebraic number" in degree 9 (T9Q in
   `PLAN-degree9.md`) only **A₉ and PSL(2,8) with r = 9** remain. Over P, S₉ occurs only with odd s
   and PΓL(2,8) drops to PSL(2,8), matching B1.
2. **Paper: THREE-PAIRS (s ≥ 3) over P** (`N1a.md`; Z8 item 5: the certificate centre need not be
   rational). This covers RA's over-P cases with r ≤ 3: PSL(2,8) r = 1, A₉ r = 1, S₉ r = 3. The
   status is a chain of degree ≤ 6 steps with the realness certificate still missing, not in Lean.
   Over P the cases with no recorded route are then **A₉ r ∈ {5, 9}, S₉ r = 7, PSL(2,8) r = 9**.

### 2.2 Lean-backed tools outside RA's fact list

RA's rule "the list is closed" excluded these. All are existing constructors; several are Lean lemmas.

1. **Lemma Q is in Lean: every monic P-quartic graph is a curve** (`quarticGraph_PConstructibleCurve`,
   `TotallyReal/Engines.lean`). Consequences:
   - fact 4 extends from a P-cubic to a **P-quartic** right-hand side (5 parameters instead of 4),
     by the same crossing (not stated as a Lean theorem);
   - **Bézier × P-quartic graph** (D0 row **G**): degree 12, all dials in P, real capacity 12
     attained, **one condition on the generator** (c_τ = 1). This is a one-condition all-P target
     alongside RA's Z_K, and RA never measured it;
   - P-quartic × rotated P-quartic (row J, c_τ = 1; D4: the condition has degree ≥ 36).
2. **Rational exponents in `power_law`.** Lean has the odd and even engines
   β·R(β²) = c and Q(β²) = c·β (`negHalf_cubic_root_Pconstructible`,
   `half_quartic_root_Pconstructible`; Lemmas E7/E8). The n = 9 odd engine β·Q(β²) = c with Q a
   P-quartic uses the same two pieces (Lemma Q and `power_law (−1/2)`). This is Z8's reduction:
   one P-line in {p₁ = p₃ = p₅ = 0} off the pairing ℙ³'s gives totally real nonics by a septic step.
3. **P-lines on the cubic {p₁ = p₃ = 0} are produced in Lean** (`TotallyReal/Certificate.lean`,
   the odd Tschirnhaus chain for n = 7, 8). Steps: S₃ on a line (degree 3), the second fundamental
   conic (degree 2), S₃ along the conic's pencil (degree 6, cleared), then S₅ on the resulting line
   (degree 5). Realness comes from an open set around a certified centre plus sign changes. The
   algebra is dimension-free; n = 9 would need its own centre. RA's Lemma N.1 says every point
   source it tried needs a full symmetric-group step. This chain is a source of P-lines on a cubic
   that does not.
4. **Text-warp eggs** (`text`). D0 row **M2**, Bézier × egg: all dials in P, **c_τ = 0** with a
   finite fibre, at most 8 real crossings found. That serves P-nonics with s ≥ 1, which includes RA's
   A₉ r = 5 and S₉ r = 7 over P. The fibre degree is unmeasured; a P-point needs that fibre (or a
   chain through it) to have degree ≤ 8.
5. **Rational-shape families with P-affine images** (`poly_graph` plus translate, scale and rotate).
   RA put these out of scope. For K defined over ℚ (T9Q) they are natural, and the Lean nonic
   theorem uses one. Z8's rule: a degree-d rational graph under P-affine maps leaves max(0, d − 4)
   rational invariants. Best T9Q row: **E** (Bézier (t², cubic) × ℚ-sextic): one condition
   `s_{4321}(τ) = 0` of degree 10 (centred: 25p₃p₇ = 21p₅²), containing {p₁ = p₃ = p₅ = 0}. RA's Z_K
   has degree 108.
6. **Five-term sine family** (`C1.md` §1): A cos pθ + B sin pθ + C cos qθ + D sin qθ + E = 0 with
   A…E ∈ P (4 effective parameters). RA's fact 7 is the case B = D = 0 (2 parameters).
7. **Hasse–Minkowski over ℚ is formalised** (`Pptc/HasseMinkowski/`, used as Meyer in the nonic
   proof). It is relevant whenever a ℚ-quadric point is needed.

### 2.3 Paper results here that overlap RA's

| RA | this repo | comparison |
|---|---|---|
| curves of genus 2–4 over L have dense L-points (sketch, medium) | A1 Theorem G | the repo's is stronger and over P: genus 0, 2–5, hyperelliptic, trigonal, degree ≤ 8 plane models, general genus 6, any genus ≤ 8 with one P-point |
| over P only the real place obstructs the Hasse principle (S17.3) | P1 Lemma LS / Theorem H | the same statement |
| Lemma G1: genus-one curve with real point, period 2^a·3^b, has a P-point | Z8 "genus-1 with a real point has dense F-points" | Z8's line argument needs a plane-cubic model, i.e. an F-rational divisor of degree ≤ 8 (degree-d pencil, d ≤ 8). **Correction to Z8: add that hypothesis.** G1 is genuinely needed only from degree 9 up, e.g. RA's "degree-9 divisor" consequence |
| lines on D_K: 2-parameter family B of general type (S20.1, *unchecked*) | B3: line surfaces S (nonic), T (decic) of general type | parallel results on different varieties |
| Theorem J: uniform obstruction, (ℤ/2)³ | Y1b (arithmetic closure carries S_n); C1 resolvent-degree remark | same moral: uniform constructions cannot work, field-specific arithmetic is required |
| normal form H.1: every nonic is g(U) + V² | E normal form σ(t)E(t²) + r(t) | different normal forms for different engines |

## 3. RA results that are new to this repo

Status labels are RA's.

- **(SR) is false** in its original form: a totally real S₅ quintic, since a trinomial has ≤ 3 real
  roots. The corrected form is (SR-3): y with ≤ 3 real conjugates. *Proved, high.* This does not
  affect Theorem X (`X1.md`): its square lift already gives K′ with ≤ 2 real places **[checked here]**.
- Theorem A (D = 5, r = 1, real Bring–Jerrard over L), *proved, high*. Theorem B (D = 5, r = 3,
  projection from a real line through a conjugate pair of non-real solvable points), *medium-high,
  unchecked*.
- Br(L) = ℤ/2. *Proved, high.*
- Lemma C.1: P(i) has no proper solvable extension; polynomials of degree ≤ 7 over P split over P(i).
  *Proved.*
- **Theorem C (GAP-checked; the method extends to degree 22).** Open over P:
  - degree 9: PSL(2,8) r ∈ {1, 9}; A₉ r ∈ {1, 5, 9}; S₉ r ∈ {3, 7};
  - degree 10: A₁₀ r ∈ {2, 6, 10}; S₁₀ r ∈ {4, 8};
  - degree 11: PSL(2,11), M₁₁, A₁₁, S₁₁.

  This **replaces H5's degree-10 group list "from memory"** (SUMMARY §1).
- **Targets.** Coordinates are the nine conjugates of a trace-zero τ ∈ K, in ℙ⁷.
  - Z_K (fact 5): hypersurface of degree 108, contains X_K = quartic ∩ octic.
  - D_K = Q₄ ∩ Q₅, degree 20, any r. Q₄ = 6p₄ − p₂², Q₅ = 18p₅ − 5p₂p₃; Q₄(z) = R(z²) with
    R(w) = 6Tr(w²) − Tr(w)²; Q₅ is the derivative of Q₄ along z ↦ z² − Tr(z²)/9. A P-line on Q₄
    gives a D-point by a quintic step.
  - Y_K (fact 6, decics with one root in P): fivefold of degree ≥ 252. Parked.
  - Fact 5 restated as "Spec K = two singular plane cubics over P with a common flex tangent"
    (S24.1, *unchecked*).
- **Uniform obstructions** (sessions 6–16): Theorem J; radicand towers that remove the abelian
  obstructions (Props O.3, P, P′, Q; sketches, monomial valuations only); exact sign facts
  g₆ ≥ 0 (L.2) and 7/60 ≤ p₄/p₂² ≤ 19/24 on real vectors (L.3); Lemma N.1.
- **Theorem F: for r = 9 there is no P-line on Q₄** (Lemma F.2: no real plane on Q₄).
- **Geometry** (sessions 17–22): F(Q₄), Σ and D are of general type (S18.1, *unchecked*);
  Sing(Q₄) = 280 lines of (3,3,3) points, none P-rational (S18.3, exact), and D ⊃ Sing(Q₄);
  lines on Q₄ via the m-parametrisation need a step of degree ≥ 2648 (S17.2); enlarging the root
  field adds no moduli (S21.1).
- **Genus-one tools** (session 24, *unchecked*): Lemma G1 (period 2^a·3^b, injectivity of
  H¹(P,E)[n] → H¹(ℝ,E)[n]); Lemma G2 (every period, CM Jacobian). No curve of genus 0 or 1 is
  invariant under PSL(2,8), A₉ or S₉.
- **Test fields:** PSL(2,8) r = 1, LMFDB 9.1.79082438656.1,
  x⁹ − 3x⁸ + 12x⁶ − 14x⁵ − 2x⁴ + 12x² + x + 1. PSL(2,8) r = 9, LMFDB 9.9.163…809.1 (polynomial in
  RA's summary). These complement D0's q₃ (S₉, totally real). D0 item 4's caution applies: fields of
  the form ∏(x − aᵢ) + c are degenerate for conditions that see only top coefficients.

## 4. Lines RA closed (do not redo)

All are scoped to RA's targets.

- enlarging the root field, K ⊂ P(τ) (S21.1);
- projection from the singular lines of Q₄, and lines meeting them (S22.1);
- lines on Q₅;
- fact-6 decics with a root in P (S23.4);
- Hasse-class stages on B, and Hasse-class fibrations of F(Q₄), Σ or D_K (S18.1, session 20);
- the A₉/S₉ fixed-line scan;
- small-height search on D_K (expected count about 10⁻²⁰);
- the m-parametrisation of lines on Q₄ (S17.2);
- cones from Sing(Q₄) points (S18.3);
- special D-line configurations (session 19);
- **P-lines on Q₄ when r = 9** (Theorem F).

RA parked: non-monomial valuations; the vertex-tuple/LP scan; mixed eigenbases; smaller radicand
sets; non-rationality of B via B/A₉; certifying the 12 two-flex-tangent lines of a cubic pencil.

## 5. New ideas, from RA and from the cross-reference

Each item is **[Open]** unless marked.

1. **RA's priority 1: a genus-one fibration with a 2^a·3^b multisection or CM fibres.** The fibration
   must come from a subvariety or correspondence whose fibres move with the base, because no genus
   0 or 1 curve is group-invariant. First leads in RA: the rational elliptic surface of S24.1 after
   cyclic triple base change at two singular fibres (a fact-5 line becomes a P-section); surfaces
   swept by lines or conics in Q₄ or D; nonics with j(E) = 0 or 1728. Add from this repo: genus-one
   fibres carrying a P-divisor of degree ≤ 8 need neither G1 nor G2 (§2.3).
2. **D_K meets the old frontier [Proof, checked here].** Q₅ = 18p₅ − 5p₂p₃ vanishes on
   {p₃ = p₅ = 0}. So D_K ⊇ {p₁ = p₃ = p₅ = 0, Q₄ = 0}, and on X₃ = {p₁ = p₃ = 0},
   D_K ∩ X₃ = {p₅ = 0, Q₄ = 0}.
   - A P-line in X₃ ∩ X₅ (Z8's target) gives a D-point if the binary quartic Q₄|ℓ has a real root.
     The odd engine gets a septic step instead, which always has one.
   - A P-line ℓ in X₃, which the Lean chain of §2.2 item 3 produces, gives a D-point when p₅|ℓ and
     Q₄|ℓ have a common real root: one condition on an 8-dimensional family of lines (Fano count
     2·6 − 4 = 8 for a cubic sixfold).
   - D0 row E's condition also contains {p₁ = p₃ = p₅ = 0}. So X₃ ∩ X₅ lies in the E locus, and its
     sublocus {Q₄ = 0} lies in D_K.
3. **Measure the all-P one-condition rows that RA did not have.** These are G (Bézier × P-quartic)
   and D1 over F; compute their hypersurface degrees for comparison with Z_K's 108. M2's finite-fibre
   degree also matters for the s ≥ 1 cases over P.
4. **Add RA's fact 6 (offset Bézier × line, degree 10) to the D0 census** as a degree-10 carrier
   for nonics with one P-root.
5. **RA's PSL(2,8), r = 1 fallback** (a uniform line on Q₄ over F‴′ = F‴(√r₉, √d₆, √g₈)) is moot
   for ℚ-defined K (Lean nonic theorem) and covered on paper over P by THREE-PAIRS. Over P, RA's
   effort is better spent on r ≥ 5.
6. **RA's low-priority literature items** overlap L1: "L is PRC" ≈ (PRC₈) for solvable towers;
   Pál; Dèbes; Beckmann–Black.
