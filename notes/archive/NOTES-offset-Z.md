# NOTES-offset-Z — synthesis of the offset research programme (wave 2)

Task Z. Repo root `C:\dev\Powerpoint\lean`, package root `pptc/`. Log: `HANDOFF-offset-Z.md`.
Scripts: `archived files/offset-scripts/Z-*.py`. Lean: `pptc/Pptc/Scratch/OffsetZ.lean` (private).
Tags: **[Lean]**, **[symbolic]**, **[numeric, N digits]**, **[not re-verified]** = read from a
wave-1 file but not independently recomputed here.

---

## 1. Plain-language summary (≤20 lines)

1. The `offset` constructor adds many high-degree real algebraic numbers to `K`, but still **no
   whole degree** and it does **not** solve the totally real septic.
2. Three extraction mechanisms work and raise the explicit record from degree 10 to degree 92.
3. **Graph route (A1, confirmed):** offset `y=p(x)` (`deg n`) and cross with a line; the crossing
   *coordinate* has degree `4n−2` (14, 18, 22 for `n=4,5,6`), directly via `crossing_Pconstructible`.
4. **Second-curve route (A2, confirmed):** offset a cubic pair and cross a degree-`m` curve; degree
   `2m(2n−1)` = 20 (ellipse), 30 (nodal cubic), with a quintic recovery.
5. **Offset×offset route (A3, confirmed):** two cubic-pair offsets meet with elimination degree
   `96 = q₁·f₉₂`; `f₉₂` is irreducible of degree 92.
6. **Chain route (A4, confirmed):** `off∘affine∘off` gives degree 28 (irreducible, `⊇ A₂₈`), then
   72; degree grows like `2ⁿ` while dimension grows linearly, so chains never become dominant.
7. Because `crossing_Pconstructible` returns *both coordinates*, high-degree numbers are reached
   without inverting the recovery equation at all — this undercuts the old "degree-10 ceiling".
8. Every new family is a low-dimensional (high-codimension) subvariety of the coefficient space.
9. A1's `n=4` instance (`X₀≈−1.59488…`) and A2's degree-20/30 and A3's degree-92 numbers are
   genuinely new: degree `>8`, not nonic, not septic-with-nonreal-root, not the decic family.
10. Galois evidence (Chebotarev cycle types) puts A1's degree-14 number outside every degree-≤6
    tower (`S₁₄`), A2's outside `A₂₀`/`A₃₀`, and A3's degree-92 number outside `A₉₂` (`S₉₂`).
11. **Largest degree fully covered: none.** Degree ≤ 6 over `K` (`root_Pconstructible_le_six_coeffs`)
    and degree ≤ 8 over `ℚ` remain the only unconditional whole-degree results; no offset family
    is proved to cover any additional whole degree.
12. Coverage claims are **dimensional only**; no covering system was solved in `K`.
13. B2 proves (and Z-06 independently confirms) the decic offset family's `PGL₂`-saturation is
    codimension 1, so it cannot cover general degree 10; a `PGL₂`-invariant is the obstruction.
14. **Totally real septic: UNSOLVED.** B1 gives strong evidence (real solutions with `Δ>0` for 26+
    septics; `deg(Δ)≤5`, `deg(a)≤6`) but no proof and no Lean theorem. Evidence, not theorem.
15. Hermite positivity (B2) forbids a *real* degree-≤6 Tschirnhaus map from killing two power sums
    of a totally real target; it does not forbid cofactor/composition routes, so the offset route
    stays logically open.
16. Cusps/evolute are **not extractable** (A3): the evolute is rational but not a legal curve, and
    no constructor is forced through a generic cusp.
17. B3: offsets enrich constructible *curves/functions* but add **no new named transcendental
    constant**; `x=cos x/√(1+cos²x)` is a candidate, unresolved.
18. B4: legality is rarely the bottleneck; `crossing_PConstructible_of_isolated` is a proved,
    strictly cheaper crossing interface; the one real gap is that `offset` is not syntactically
    closed (`C¹` in, but a second offset needs `C²`).
19. The honest programme statement: offsets give a large supply of *individual* high-degree
    constructible numbers; they do not (yet) change which *degrees* are covered.
20. Recommendation: bank the confirmed results in Lean (A1 degree-14, A2 degree-20/30, B4 lemmas),
    and attack B1's square covering system by dedicated elimination as the single frontier.

---

## 2. Wave-1 task status

| task | status | deliverable | unproved / sorry items | blocks a headline? |
|---|---|---|---|---|
| A1 | COMPLETE | `NOTES-offset-A1.md` | `offsetPolyGraphArc_PConstructibleCurve` is `sorry` (legality statement only) | No — the `4n−2` degree claim is [symbolic]/[numeric]; only its Lean packaging is unproved |
| A2 | COMPLETE | `NOTES-offset-A2.md` | none as `sorry`; **covering-system `K`-solvability and real feasibility by root pattern left open** | No for degree-20/30 numbers; yes for any "whole degree covered" claim |
| A3 | COMPLETE (1 sorry) | `NOTES-offset-A3.md` | `offsetOffsetE1_eq_zero_of_cross` **`sorry`/UNPROVED**; `offsetOffset_cross_root_PConstructible` is proved (instantiation) | No for degree 92 (algebra verified independently here); the rationalization step is unproved in Lean |
| A4 | COMPLETE | `NOTES-offset-A4.md` | none as `sorry`; 3 identities [Lean] | No |
| B1 | **REDUCED, NOT SOLVED** | `NOTES-offset-B1.md` | no Lean theorem; P0/P1/P2 open | **YES** — the headline (totally real septic) is unsolved; evidence only |
| B2 | COMPLETE | `NOTES-offset-B2.md` | none as `sorry` in scratch (proved sum-of-squares) | No |
| B3 | COMPLETE | `NOTES-offset-B3.md` | candidates marked unresolved | No |
| B4 | COMPLETE (infrastructure) | `NOTES-offset-B4.md` | `normalEq_rat_eq_zero`, `proper_rational_recovery_degree`, `finite_zeros_of_analyticOnNhd`, `analytic_arcs_finite_meet`, H1 `offsetConic_cross_root_PConstructible`, H3 `degreeTenFamily_covered` are **`sorry`/UNTESTED** | No — they are formalisation infrastructure, but they are not part of the library |

**Bottom line.** No wave-1 task was aborted mid-deliverable; B1 is the only task whose *research
headline* is unresolved (reduced to a square covering system). A3 and B4 contain genuinely
unproved `sorry` statements, each reported above.

---

## 3. Independent verification table

`own script/tool` = the independent recomputation performed for this synthesis.

| # | claim (wave-1) | independent check | verdict |
|---|---|---|---|
| 1 | A1: graph offset×line gives degree `4n−2`; `n=4,5,6` → 14,18,22 | `Z-01` (sympy): `P=p²(1+p'²)−1` degrees 14/18/22, all irreducible | **confirmed** |
| 2 | A1: `X=t+p p'` has irreducible min-poly of degree 14/18/22 | `Z-01`: resultant degrees 14/18/22, all irreducible | **confirmed** |
| 3 | A1: printed degree-14 polynomial (with `4096·` prefix) | `Z-01`: matches up to the wrong prefix; **primitive integer polynomial has leading coefficient `65536`**, not `4096·65536` | **confirmed with corrections** |
| 4 | A1: `n=4` two real crossings both genuine for `d=−1` | `Z-01`: `p√(1+p'²)−1 ≈ −1e−16, 0` | **confirmed** |
| 5 | A1: `n=5` roots are genuine crossings | `Z-01`: roots give `p√(1+p'²)−1 = −2.0` (i.e. `=+1` for `d=+1`) and `0`; both legal via (O4), but **not both for `d=−1`** | **confirmed with corrections** |
| 6 | A1: degree-14 `X₀` lies outside every degree-≤6 tower | `Z-01` cycle types: 14-,13-,12-,11-cycles present; 14-cycle is **odd** ⇒ `G=S₁₄` (stronger than "⊇ A₁₄"); Jordan with 11 ≤ 11 | **confirmed (strengthened)** |
| 7 | A2: F2 offset×ellipse crossing poly degree 20, irreducible | `Z-02` (sympy minimal rationalization): degree 20, irreducible, **matches printed Q2 exactly** | **confirmed** |
| 8 | A2: Q2 real roots `−1.125390657519400400563…`, `0.554181486000122751158…` | `Z-02` + mpmath 80 dps: match NOTES to 40+ digits (initial sympy `nroots` 16-digit disagreement was **sympy error**, not a NOTES error) | **confirmed** |
| 9 | A2: F3 offset×nodal-cubic crossing poly degree 30, irreducible | `Z-02`: `Raw = (45t⁴−24t³+10t²+1)·(−printed Q3)`; the degree-30 factor matches the printed Q3 exactly and is irreducible | **confirmed with clarification** |
| 10 | A2: Q3 real roots (4 values) | `Z-02` + mpmath 80 dps: match NOTES to 40+ digits | **confirmed** |
| 11 | A2: genuine crossing for one sign of `d` | `Z-02`: `F(Γ)=0` to ~1e−14 (d=−2) at Q2 roots, ~1e−16 at Q3 roots | **confirmed** |
| 12 | A2: Galois ⊇ `A₂₀` / ⊇ `A₃₀` | `Z-02`: Q2 mod 3000017 has an 11-cycle; Q3 mod 4000037 has a 13-cycle; both ≤ n−3 with primitivity | **confirmed** |
| 13 | A3: explicit offset×offset crossing (t₁,t₂,P) | `Z-03` (mpmath 60 dps): `|O₁−O₂|≈7.8e−44`, distances `=1` to 1e−61, perp 1e−60 | **confirmed** |
| 14 | A3: crossing transverse, Jacobian det 267.857637… | `Z-03`: det `=267.857637657` | **confirmed** |
| 15 | A3: self-crossing `f₃₂` degree 32, irreducible | `Z-03`: degree 32, irreducible over ℚ; printed `(t,s)` give offset points equal to 1e−46 and centre distances exactly 2 | **confirmed** |
| 16 | A3: offset×offset honest elimination degree `96 = q₁(4)·f₉₂(92)` | `Z-03b` + Wolfram Gröbner (`Modulus→101`, `1000003`): a single degree-96 univariate element; `q₁` divides it | **confirmed** |
| 17 | A3: `f₉₂` irreducible of degree 92 over ℚ | Wolfram `FactorList[Resultant[G,H,t₂]]` over ℚ: `(deg4)²·(deg16)⁴·(deg20)²·(deg92)¹` (FactorList is irreducible) | **confirmed** |
| 18 | A3: `Gal(f₉₂/ℚ)=S₉₂` (large prime cycle + odd) | Wolfram: `f₉₂` factored mod 74 primes; factor degrees include **53** (prime, `q=41`), 63 (`q=109`), 90; odd permutations at `q=41` (3 factors), `q=227` (7), `q=241` (5). 53>46 ⇒ primitive; 53≤89 + Jordan ⇒ `A₉₂⊆G`; odd ⇒ `G=S₉₂` | **confirmed** |
| 19 | A3: self-crossing centre degree 16, `f₃₂` imprimitive | wave-1 only (`A3-05`) | **not re-verified** |
| 20 | A4: length-2 chain line-crossing poly degree 28, irreducible, 6 real roots, `⊇ A₂₈` | `Z-05` (sympy + mpmath): degree 28, irreducible, leading `311233107240000`, constant `5459729809`, 6 real roots (`−1.62965613544226…` matches); cycle types `{23,3,1,1}`@103, `{22,6}`@131, odd type `{13,6,4,3,2}`@101 | **confirmed** |
| 21 | A4: parabola-offset×cubic-Bézier degree 18, irreducible | `Z-05`: implicit degree 6, crossing poly degree 18, irreducible, 4 real roots | **confirmed** |
| 22 | A4: chains never dominant (`dim−degree→−∞`) | wave-1 only | **not re-verified** |
| 23 | B1: every tested totally real rational septic has a real solution with `Δ>0` | wave-1 only (`B1-09`) | **not re-verified** |
| 24 | B1: `deg(Δ)≤5`, `deg(a)≤6` (PSLQ, 200 digits) | wave-1 only (`B1-04`) | **not re-verified** |
| 25 | B1: decic image rank 7 (codim 3) | wave-1 only (`B1-10`) | **not re-verified** |
| 26 | B2: `Edec` coefficient rank 7, `PGL₂`-saturation rank 9 (codim 1) | `Z-06` (exact rational ranks at 4 random points): `rank dImage = 7`, `rank[dImage|orbit] = 9` in all four | **confirmed** |
| 27 | B2: minimal counterexample primitive; Hermite positivity | wave-1 only, but the sum-of-squares core is a short elementary fact | **not re-verified** |
| 28 | B3: `speed(offset)=σ‖1−dκ‖`, offset length `L−dΔθ`, no new transcendental constant | wave-1 only | **not re-verified** |
| 29 | B4: `rationalize`, `rationalize_mul`, `crossing_PConstructible_of_isolated`, `rational_param_recovery`, `chain_recovery`, `offsetParam_parabola` | read only; not re-run through `lean_diagnostic_messages` | **not re-verified** |
| 30 | Z: independent [Lean] certificates of the offset normal form, the norm/rationalize identity, the recovery (normal) equation, the offset×offset `E₁` reduction, and the PH unit identity | `pptc/Pptc/Scratch/OffsetZ.lean` (7 theorems, targeted imports, no `Pptc.*`); `lake_check` single-file `lake env lean`: **OK, no errors or warnings, no `sorry`** | **confirmed [Lean]** |

**§3.addendum (S₉₂).** Independently re-confirmed. `f₉₂` (the degree-92 irreducible factor of
`Resultant[G,H,t₂]`) was factored modulo 74 primes; the observed factor-degree multisets include
a **53-cycle** (`q=41`, type `{1,38,53}`), a 63-cycle (`q=109`), and a 90-cycle, and odd
permutation types (`q=41` with 3 factors, `q=227` with 7, `q=241` with 5). Since `f₉₂` is
irreducible over ℚ the group is transitive; `53 > 92/2` makes it primitive; `53 ≤ 92−3` with
Jordan's theorem gives `A₉₂ ⊆ G`; the odd element forces `G = S₉₂`. This matches wave-1's claim
(its 47-/89-cycles are among the same phenomenon).

**§3.addendum 2 (A4, B2).** A4 was independently re-confirmed (`Z-05`): the degree-28 chain
polynomial (leading `311233107240000`, constant `5459729809`, irreducible, 6 real roots, cycle
types including `{23,3,1,1}` ⇒ `⊇ A₂₈` and an odd type ⇒ `S₂₈`) and the degree-18
parabola-offset×Bézier polynomial. B2's decisive negative was re-confirmed (`Z-06`): the decic
family has coefficient rank 7 and `PGL₂`-saturation rank 9 (codim 1) at four random rational
points. B1's septics and B3's transcendental analysis remain **not re-verified** here.

### "Degree n is covered" claims

| claim | independent check | verdict |
|---|---|---|
| A2: F1 covers `n≤7`, F2 `n≤10`, F3(legal) `n≤11`, F4(graph6) `n≤13`, F5 `n≤9` *dimensionally* | none run here | **not re-verified** |
| A2/overview §4: the covering system must be solved in `K`; it was not | read; A2-10 scan called inconclusive in wave-1 | **open (not re-verified)** |
| B2: `Edec` `PGL₂`-saturation is codim 1 ⇒ misses general degree 10 | `Z-06`: rank 7 → 9 at 4 random points | **confirmed** |
| Library: every real root of degree ≤ 6 over `K`, ≤ 8 over `ℚ` | pre-existing library result, unchanged by this programme | **standing (not offset-derived)** |
| No offset family covers a whole degree beyond the above | follows from the unproved covering systems and the codim-1 decic obstruction | **no contradicted claim; nothing upgraded** |

---

## 4. Reconciled master tables

### 4.1 New number mechanisms (all "genuinely new" relative to degree ≤8 / nonic / septic-nr / decic)

| task | mechanism | crossing degree | extracted number degree | Galois evidence | Z verdict |
|---|---|---|---|---|---|
| A1 | quartic graph `t⁴+t+1`, `offset d=−1`, × x-axis | 14 | 14 (coordinate `X`, and parameter via septic engine) | `S₁₄` (14-cycle odd + Jordan 11) | **confirmed** |
| A1 | quintic graph `t⁵+t+1` | 18 | 18 (coordinate) | wave-1 (not re-verified) | deg confirmed |
| A1 | sextic graph `t⁶+t+1` | 22 | 22 (coordinate) | wave-1: 22-,19-,17-cycles | deg confirmed |
| A2 | cubic pair × ellipse (`4X²+9Y²=36`), `d=2` | 20 | 20 | ⊇ `A₂₀` (11-cycle) | **confirmed** |
| A2 | cubic pair × nodal cubic (`Y²=X³−X²`) | 30 | 30 | ⊇ `A₃₀` (13-cycle) | **confirmed** |
| A3 | offset × offset, two cubic pairs, `d₁=d₂=1` | 96 (=4+92) | 92 | `S₉₂` (53-cycle + odd) | **confirmed** (deg, irred, Galois) |
| A3 | self-crossing (bitangent circle), `d=2` | 32 (param), 16 (centre) | 32 / 16 | imprimitive (blocks of 2) | deg 32 **confirmed**; imprimitivity/centre not re-verified |
| A4 | `off∘L∘off` chain × line | 28 | 28 | ⊇ `A₂₈` (23-cycle) | **confirmed** |
| A4 | parabola-offset × cubic Bézier | 18 | 18 | wave-1 | **confirmed** (deg/irred) |
| B3 | min-distance to `y=x⁷` | — | 12 / 13 | `S₁₂`/`S₁₃` | candidate, **not reachable** (not re-verified) |

### 4.2 Degree laws (reconciled)

| base | second curve | degree | source | Z verdict |
|---|---|---|---|---|
| polynomial graph, deg `n` | line, `m=1` | `4n−2` | A1/A2 | **confirmed for `n=4,5,6`** |
| polynomial base, deg `n` | implicit deg `m` | `2m(2n−1)` | A2 | **confirmed `n=3, m=1,2,3` (10,20,30)** |
| rational base (ellipse), deg `n` | implicit deg `m` | `8m` (`=(4n)m`) | A2 | not re-verified |
| chain length `n` | line | `10, 28, 72` | A4 | `n=1,2` **confirmed**; `n=3` not re-verified |

### 4.3 Coverage / obstruction (reconciled)

| family | image dim `D` (coeff) | `PGL₂`-saturated dim | degrees dimensionally covered | proof of coverage |
|---|---|---|---|---|
| line (F1) | 7 (codim 3) | 8 / codim 1 (mod-`PGL₂` codim 2) | 7 | none (system not solved) |
| conic (F2) | 10 | 11 | 7–10 | none |
| cubic Bézier (F3 legal) | 11 | 12 | 7–11 | none |
| graph6 (F4) | 13 | 14 | 7–13 | none |
| decic `Edec` (line, formalised) | 7 | **9 = codim 1** | **does not cover degree 10** | obstruction confirmed (`Z-06`) |
| library `root_Pconstructible_le_six_coeffs` | — | — | **all `n ≤ 6` over `K`** | proved (library) |
| library `root_Pconstructible_le_eight` | — | — | **all `n ≤ 8` over `ℚ`** | proved (library) |

---

## 5. Programme answer: how offsets probe higher-degree algebraic numbers

**Mechanisms.**
1. **Graph × line (`4n−2`).** `γ(t)=(t,p(t))` is injective with `speed=√(1+p'²)≥1`, so its
   `offset` is legal on every window. Crossing with the `x`-axis gives
   `P(t)=p(t)²(1+p'(t)²)−d²` of degree `4n−2`; `crossing_Pconstructible` returns the
   **coordinate** `X=t+p(t)p'(t)`, whose minimal polynomial has the same degree. No recovery
   inversion is needed.
2. **Cubic pair × implicit curve (`2m(2n−1)`).** Clearing `w=√(x'²+y'²)` gives `Q=A²−B²q`;
   `d↦−d` freedom (O4) makes every real root with `w≠0` a genuine crossing. The parameter is
   recovered by the degree-5 normal equation. This is the mechanism that reaches degree 20/30.
3. **Offset × offset (degree 92).** Two offsets meeting is a 4-equation system; the honest
   elimination degree is 96 with a `w=0` cusp factor `q₁` and a genuine irreducible `f₉₂`.
4. **Chains (degree 28 → 72).** `off∘affine∘off` doubles the degree each step; the unit normal is
   preserved by the affine map, so the two square roots are independent (tower degree ≤4). This
   gives degree without moduli.
5. **Rational (PH/parabola) offsets.** The square root disappears, so crossings are exact
   polynomial systems of comparatively low degree (5–30); their value is exactness and cheap
   degree-1 recovery, not raw degree.

**Largest degree for which ALL of degree `n` is covered.**
- **Unconditionally: `n = 6` over `K` and `n = 8` over `ℚ`** (pre-existing library results). No
  offset-derived family increases this.
- **Conditionally / dimensionally only:** A2's F4 (degree-6 graph) has image dimension 13, so it
  *could* cover `n ≤ 13` if its covering system were solvable in `K` and real-feasible for every
  root pattern — but that was **not achieved**, and B2 shows the line family fails a `PGL₂`
  invariant. So there is **no proved offset coverage of any degree `n ≥ 7`**.

**Totally real septic.** **UNSOLVED.** Status: reduced to a square covering system
(`q | W`, i.e. `u²(u'²+v'²) = Δv'² mod q`, 7 equations in 7 unknowns). B1's evidence: every tested
totally real rational septic has a real solution, always with `Δ>0`; PSLQ at 200 digits gives
`deg(Δ)≤5`, `deg(a)≤6` across all tested septics. This is **evidence, not proof**; uniformity in
the data and the real branch were not established, and the exact elimination stalled on every
available CAS. Do **not** upgrade.

**Obstruction picture.**
- **Hermite positivity (B2 Lemma 12):** for a totally real target, a single *real* degree-≤6
  Tschirnhaus map can kill at most one power sum, so `y⁷=cubic(y)` normal forms are unreachable by
  Tschirnhaus. This excludes one *method*, not the offset engines (cofactor/composition escape).
- **Codimension of families:** every offset family is a proper subvariety; the decic `Edec`
  `PGL₂`-saturation is codimension 1 (norm/discriminant invariant), so it misses general degree 10.
- **Counts are not proofs:** the degree-10 offset family looked dimensionally slack and was
  degenerate; every coverage claim here rests on an unsolved `K`-solvable covering system.
- **No unconditional negative** is known for any specific real algebraic number (countability,
  o-minimality, and complex resolvent-degree all fail to separate `K` from `ℝ`); the sharp
  negatives are only for real-radical expressions and single-Tschirnhaus reductions.
- **Cusps/evolute:** not extractable — rational evolute but not a legal curve; the degree-12
  curvature equation is unusable and no engine covers degree 12.

---

## 6. Follow-up PLAN files

Written at the repo root (one deliverable each), in the `PLAN-jacobi-L*` style (all eight on disk):

**Lean formalisation (`PLAN-offset-L*.md`), using B4's statement drafts / lemma DAG:**

1. `PLAN-offset-L1-polygraph-offset.md` — formalise
   `offsetPolyGraphArc_PConstructibleCurve` (A1 legality, currently `sorry`) and the explicit
   degree-14 instance `p=t⁴+t+1`, `d=−1`.
2. `PLAN-offset-L2-isolation-crossing-library.md` — move B4's proved
   `rationalize`, `rationalize_mul`, `crossing_PConstructible_of_isolated`, `rational_param_recovery`,
   `chain_recovery` out of scratch into the library (one deliverable: the isolation crossing lemma
   with its axioms checked).
3. `PLAN-offset-L3-offset-conic-engine.md` — formalise H1 `offsetConic_cross_root_PConstructible`
   and the degree-20 F2 instance, reusing `rationalize` and `offsetCross_finite_roots`.
4. `PLAN-offset-L4-rational-recovery.md` — formalise `normalEq_rat_eq_zero`,
   `proper_rational_recovery_degree`, and the parabola window bijection of `offsetParam_parabola`.

**Research (`PLAN-offset-C*.md`):**

5. `PLAN-offset-C1-totally-real-septic-elimination.md` — attack B1's square system with a
   dedicated CAS/monodromy (P0: elimination degree ≤6 uniformly; P1: uniform real branch).
6. `PLAN-offset-C2-offsetoffset-galois-coverage.md` — settle `S₉₂`, sample cycle types, and test
   whether the offset×offset family can cover any whole degree.
7. `PLAN-offset-C3-covering-system-ksolvability.md` — apply B2's sufficiency Lemma 13 to the best
   measured family (A2 F4 graph6, `D=13`): find free rational choices + IVT for a prescribed septic.
8. `PLAN-offset-C4-rational-offset-exact-engines.md` — exploit PH/parabola rational offsets (A4)
   for exact high-degree crossing systems and degree-1 recovery.

---

## Side discoveries

- **The degree-10 ceiling was an artefact of offsetting only cubics.** Offsetting a degree-`n`
  polynomial graph and crossing a line reaches degree `4n−2` (up to 22 here) with no new axiom.
  `[symbolic]`, Z-confirmed for `n=4,5,6`.
- **Coordinate extraction is free.** `crossing_Pconstructible` returns both coordinates, so the
  high-degree number is obtained without inverting the recovery equation. The project's prior focus
  on the recovery quintic understated the constructor. `[Lean for extraction]`.
- **A1's printed degree-14 polynomial carries a spurious `4096·` prefix**; the true primitive
  integer polynomial has leading coefficient `65536`. Z-found correction. `[symbolic]`.
- **The `n=5` graph instance needs both signs of `d`** to realize both real crossings; this is
  harmless by (O4) but the NOTES' single-sign phrasing was imprecise. Z-found correction.
- **A1's degree-14 Galois group is `S₁₄`, not merely `⊇ A₁₄`**, because a 14-cycle is odd. Z-found.
- **The genuine cubic-pair×nodal-cubic crossing polynomial is the degree-30 factor of a larger
  degree-34 expression**, the extra factor being `q = 45t⁴−24t³+10t²+1` (the speed²). Any future
  rationalized crossing with a cubic second curve should divide out `q`. `[symbolic]`, Z-found.
- **The offset×offset elimination splits as `q₁ · f₉₂`**, and the same `q₁` (base-curve speed²)
  appears as the spurious cusp factor of every rationalized offset system. `[symbolic]`.
- **The chain tower is not nested** (A4): an affine map preserves the tangent direction, so each
  offset's normal depends only on the once-mapped velocity; the function field is a multiquadratic
  (degree ≤ `2ⁿ`) extension, not a tower of quadratics. `[symbolic, not re-verified]`.
- **B2's `PGL₂`-saturation accounting**: the line family has a 2-dimensional affine stabiliser, so
  its mod-`PGL₂` codimension drops by 2, not 3. `[symbolic, not re-verified]`.
- **The offset normal form is now [Lean]-certified from its geometric inputs** (Z): the passage
  from `u·w + d·v' = 0` and `(A²+B²)(x'²+y'²) = u'²+v'²` to `u²(u'²+v'²) − D²v'² = 0` is a short
  `calc` block, and the norm step `E + w·O = 0 ⇒ E² − S·O² = 0` needs neither `Polynomial` nor
  `Analysis` — so the wave-1 "normal form" claims have an import-light Lean witness
  (`Pptc/Scratch/OffsetZ.lean`).

## Leads for other tasks

- **Library/Lean.** The single highest-value formalisation is A1's `offsetPolyGraphArc_…` plus the
  `n=4` degree-14 instance; it banks a new constructible number and generalises
  `offsetCubicPairArc_PConstructibleCurve`. See `PLAN-offset-L1`.
- **B1 (septic).** The decisive object is `Elim_{a,b,c,p,q,r}(Δ)` for the square system
  `u²(u'²+v'²)=Δv'² mod q`; proving its `.natDegree ≤ 6` uniformly would settle the totally real
  septic. See `PLAN-offset-C1`.
- **A2/A4.** Solve the covering system `Q=P·g` in `K` for F4 (graph6, `D=13`); the positive-
  dimensional fibre is the natural home of a `phi-B`-style sign-change argument. Combine with A4's
  exact rational-offset crossings (`PLAN-offset-C3`, `PLAN-offset-C4`).
- **A3.** Independently settle whether `Gal(f₉₂)=S₉₂` (multi-prime cycle sampling) and whether
  offset×offset can be made totally real for high real-root counts. See `PLAN-offset-C2`.
- **B3.** `x=cos x/√(1+cos²x)` (offset-sine ⋔ vertical line) remains an unresolved candidate;
  decide whether it is a new closure point of `K`.
- **B4 / `Defs.lean`.** `offset` is not syntactically closed: it accepts `C¹` but a second offset
  needs `C²`, and it stores no tracing. Consider adding a `ContDiffOn ℝ 2` hypothesis or storing the
  generating stroke — a modelling fix with consequences beyond this programme.
- **Z → next wave.** If a new constructor "offset by a rational function of the parameter" were
  added, the evolute (already rational) and its cusps would become legal, opening a genuinely new
  degree source (see A3 §5).
