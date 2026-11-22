#!/usr/bin/env python3
"""Session 59 end-of-session edits: condensed summary and Start here (reads /mnt/project mirror)."""
import re

S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
n0S, n0H = len(S), len(H)


def rep(text, old, new, count=1):
    assert text.count(old) == count, (old[:80], text.count(old))
    return text.replace(old, new)


# ---------------- summary ----------------
S = rep(S, '(through session 58, Nov 20;', '(through session 59, Nov 20;')

sec0_line = ("- S59 (Section 0aj): **row G and the P-dense loci for r = 9.** Mechanism tested: a variety with dense P-points "
             "inside Z_G (row G is the only all-P row reaching r = 9). **L_135 and V_odd are not in Z_G** (S59.1, numerical, "
             "planted controls 10⁻¹⁶ against stable minima ≥ 10⁻⁷). Row E's hypersurface H_E contains L_135 and is smooth at its "
             "general points, but the genuine E-points on L_135 are exactly V_odd (S59.2); a tangent line at a P-point of L_135 "
             "gives a degree-8 residual on H_E, but forces a P-sextic graph, out of scope (S59.3). New formulation of row E with a "
             "fixed ℚ-sextic and P-valued Bézier and affine dials (S59.4).\n")
anchor = "- Nov 19 (between sessions 55 and 56): **second repo input**"
S = rep(S, anchor, sec0_line + anchor)

sec0aj = r"""## 0aj. Session 59 (Nov 20): results

Topic: the near-term target (totally real nonics over ℚ, i.e. A_9 and PSL(2,8) with r = 9 over P). Only three toolkit rows reach r = 9 with P dials or rational dials: row G (Z_G, degree 180, all dials in P), fact 5 (Z_K, degree 108) and row E (H_E, degree 10, ℚ-sextic). **Mechanism named: a variety Λ with dense P-points contained in the row's hypersurface.** For r = 9 the known P-dense loci are L_135 = {p1 = p3 = p5 = 0} (T3 chain, S25.1) and the P-lines of X = {p1 = p3 = 0}. If Λ ⊂ Z_G with genuine constructions at its general points, every P-point of Λ is a good generator and the case closes; if Λ ⊂ H with H smooth along Λ but the constructions degenerate on Λ, a tangent line at a P-point of Λ gives a residual of degree deg H − 2 (a step when ≤ 8). The endpoint is a crossing of a Bézier with a P-quartic graph (row G) or a ℚ-sextic graph (row E), a T5-type engine, so no charpoly-shape check applies. **Tests that could fail:** (a) is L_135 (or V_odd) inside Z_G; (b) is L_135 inside H_E with genuine points. **Result:** (a) fails; (b) L_135 ⊂ H_E, smooth, but genuine only on V_odd; the tangent-residual step exists (degree 8) but forces a P-sextic.

**S59.1 (Z_G contains neither L_135 nor V_odd).** [numerical] (`zg59.py`: for a point τ, solve M(a, b)c = 0, the 5 × 3 matrix of t⁴…t⁸ coefficients of X^k mod χ_τ (k = 2, 3, 4, X = t³ + at² + bt; G1a.1), as 5 complex equations in (a, b, c up to a random normalisation) by Gauss–Newton from 60–250 starts; smallest relative residual |Mc|/(|M||c|)).
- Controls: planted points (9 of the 12 crossings of a random Bézier × quartic) give 2.6·10⁻¹⁶, 2.0·10⁻¹⁵, 2.8·10⁻¹⁶; random complex τ give 1.2–1.6·10⁻⁴.
- L_135, complex points: 1.4·10⁻⁷, 6.5·10⁻⁴, 1.2·10⁻⁴, 2.0·10⁻⁵ (the 1.4·10⁻⁷ point is a stable positive minimum: the same value with 250 starts and with 600 iterations, at |a|, |b| = 2.5, 10.4). Totally real points of L_135 (r = 9): 3.5·10⁻⁵, 7.7·10⁻⁶, 7.8·10⁻⁶, 1.0·10⁻⁵. V_odd = L_135 ∩ {p7 = 0}: 5.6·10⁻⁶.
- So **L_135 ⊄ Z_G and V_odd ⊄ Z_G**; X ⊄ Z_G because both are irreducible of different degrees (3 and 180). The known P-dense sources for r = 9 meet Z_G only in 0-dimensional schemes of degree ≥ 180 (a P-line of X) or in a 4-fold of L_135 with no P-point mechanism. **Mechanism ruled out** for row G.

**S59.2 (row E along L_135).** *unchecked* (short algebra with Newton's identities; the coefficient form below was not rechecked against 25p3p7 = 21p5²).
- E nonics are f = σ(t)E(t²) + r(t) (T6). Centred (c1 = 0, so σ = t³ + bt + c), the coefficients of t^{9−k} are c2 = b + e2, c3 = c, c4 = be2 + e1, c5 = ce2, c6 = be1 + e0, c7 = ce1, with E = u³ + e2u² + e1u + e0; for c3 ≠ 0 this gives the single condition c3²c4 = c2c3c5 − c5² + c3c7 (the hypersurface H_E).
- On L_135: c3 = −e3 = 0, c5 = −e5 = 0 and c7 = −e7 = −p7/7 (7e7 = p7 there). A genuine decomposition needs c7 = c·e1 = 0, so **the genuine E-points on L_135 are exactly V_odd**; on L_135 ∖ V_odd, H_E contains only degenerate (closure) points. (On V_odd, f = t·F(t²) + c9 with F quartic, and σ = t³ + bt needs −b a root of F: a quartic step; this is the odd route T2.)
- H_E is smooth at general points of L_135: its gradient there is 25p7·dp3 ≠ 0. (H_E ∩ X = L_135 counted twice, as recorded in Section 6.)

**S59.3 (tangent residual on H_E, out of scope).** *unchecked* (degree count).
- At a P-point τ0 of L_135 with p7(τ0) ≠ 0 (dense in the real locus for r = 9, S25.1), a P-line τ0 + sv with dp3(τ0)·v = 0 meets H_E at s = 0 with multiplicity ≥ 2 and in a residual of degree 8 over P. Any real residual root is a P-point of H_E off L_135, generically with c3 ≠ 0, hence a genuine E-point. **But its forced sextic graph has P coefficients**, and the toolkit has only ℚ-sextic graphs (T6) and quartic graphs over P (Arya, Nov 19). Over ℚ the residual roots are not rational. So the step is out of scope; the real-root count of the residual octic was not run. It becomes the first test if Arya allows P-valued sextic coefficients in some restricted form (D0 §3.4, \"c_τ ≥ 3\").

**S59.4 (row E with a fixed ℚ-sextic and P-valued dials).** *unchecked* (short algebra; dimension count not checked).
- Let the sextic graph y = S(x), S ∈ ℚ[x], be fixed, and let the Bézier (q(t), Y(t)) (q quadratic, Y cubic) and the affine maps have P-valued dials. With u = q(τ) = α w² + β (w = τ + shift), W4(τ) = span(1, u, w, wu), so **u ∈ K is good iff (u − β)/α = w² is a square in K and S(u) − A − Bu = w(C + Du) for some A, B, C, D ∈ P, i.e. χ_u | (S(u) − A − Bu)² − (u − β)(C + Du)²/α**: the crossing of the graph with the singular cubic (y − A − Bu)² = (u − β)(C + Du)²/α (the implicit form of a Bézier whose x-coordinate is quadratic in t). For each rational S this is a family of dimension about 4 per field K (after the affine maps of the graph), all over P, reaching up to 12 real crossings.
- So row E with rational S but P dials is not a ℚ-versality question: it asks for a P-point on one member V_S of a family of P-varieties indexed by ℚ-points S. Not yet tested: the real test for r = 9 on V_S for simple S (u⁶, T_6, u³(u − 1)³), and a forcing mechanism (the square condition (u − β)/α = w² is the circle-type condition of M2, S57.4(i)).
- **Question for Arya:** in row E (Bézier × ℚ-sextic graph), may the Bézier's control points and the affine maps applied to the sextic graph (translation, scaling, shear) have P-constructible parameters, with only the sextic's own coefficients rational? If yes, S59.4 is in scope and is the next main line for r = 9.

**S59.5 (decision).**
- Ruled out: P-dense loci inside Z_G (L_135, V_odd, X). Row E: L_135 ⊂ H_E with degenerate points off V_odd; the tangent-residual step (degree 8) needs a P-sextic, out of scope.
- **Next:** (1) r = 9 (the near-term target): row E in the form of S59.4 once Arya confirms the dial rules: the real test for r = 9 on V_S for a few rational S, then a named mechanism (look first for P-dense loci inside V_S where it is smooth, as in S59.2–S59.3); (2) r = 7: M2 with a chosen generator (S58.4), or Z_G / R5; (3) A_9 r = 5: the S54 candidates; (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic.

"""
S = rep(S, "## 1. The goal, the facts and the repo tools", sec0aj + "## 1. The goal, the facts and the repo tools")

rows = ("| S59.1: row G's hypersurface Z_G contains neither L_135 nor V_odd (nor X); the P-dense loci known for r = 9 give no P-point of Z_G | [numerical] (`zg59.py`; planted controls 10⁻¹⁶, L_135 minima 10⁻⁷ to 10⁻⁴) |\n"
        "| S59.2: L_135 ⊂ H_E (row E) and H_E is smooth at its general points (gradient 25p7·dp3), but the genuine E-points on L_135 are exactly V_odd (c7 = −p7/7 must vanish) | *unchecked* (short algebra) |\n"
        "| S59.3: a P-line tangent to H_E at a P-point of L_135 has a degree-8 residual over P whose real points are genuine E-points, but the forced sextic graph has P coefficients (out of scope) | *unchecked* |\n"
        "| S59.4: row E with a fixed ℚ-sextic S and P-valued Bézier and affine dials: u good ⇔ (u − β)/α = w² in K and χ_u \\| (S(u) − A − Bu)² − (u − β)(C + Du)²/α; a family of P-varieties V_S indexed by rational S | *unchecked* (dial rules to be confirmed by Arya) |\n")
anchor = "| S58.5: genus of Σ:"
i = S.index(anchor); j = S.index("\n", i) + 1
S = S[:j] + rows + S[j:]

old = "- **Z_G (Nov 19, Section 1a):**"
i = S.index(old); j = S.index("\n", i)
S = S[:j] + " **S59.1: Z_G contains neither L_135 nor V_odd**, so the T3 points of L_135 do not help." + S[j:]
old = "- **Row E (rational only):** 25p3p7 = 21p5², degree 10."
S = rep(S, old, old + " S59.2: it contains L_135 (degenerate points off V_odd); S59.4: with a fixed ℚ-sextic and P-valued Bézier and affine dials it becomes a P-point problem on a family V_S (dial rules to be confirmed).")

anchor = "- **Session 58:** S58.1–S58.6 (archive 57–58)."
S = rep(S, anchor, "- **Session 59:** S59.1–S59.5 (Section 0aj). Z_G contains neither L_135 nor V_odd; row E contains L_135 with degenerate points off V_odd, its tangent-residual step needs a P-sextic; row E with a fixed ℚ-sextic and P dials reformulated (S59.4).\n" + anchor)
anchor = "- **Method lesson (S58):**"
S = rep(S, anchor, "- **Method lesson (S59):** (1) **Before measuring a hypersurface row, test whether it contains a variety with dense P-points** (for r = 9: L_135 and the P-lines of X; for r ≤ 5: V_3, V_{124}): a containment with genuine points closes the case at once, and a smooth containment with degenerate points gives a tangent-line residual of degree deg − 2. The test is cheap: an overdetermined Gauss–Newton solve per point, with planted points as the positive control (10⁻¹⁶ against ≥ 10⁻⁷). (2) For a row with a rational-only curve, separate the rational dials from the P dials before calling it a ℚ-versality question: with the curve fixed, the remaining dials may make it a P-point problem (S59.4).\n" + anchor)

anchor = "**Session 58 decision (M2 count and monodromy).**"
S = rep(S, anchor, "**Session 59 decision (P-dense loci in the r = 9 rows).** S59.1: Z_G contains neither L_135 nor V_odd; S59.2–S59.3: H_E contains L_135 (degenerate off V_odd) and its tangent-residual step needs a P-sextic; S59.4: row E with a fixed ℚ-sextic and P dials is a P-point problem on V_S. **Order now:** (1) r = 9: row E as in S59.4 once Arya confirms which dials may be P-valued (question in Section 0aj); then the real test for r = 9 on V_S and a named mechanism (P-dense loci inside V_S first); (2) r = 7: M2 with a chosen generator (S58.4), or Z_G / R5; (3) A_9 r = 5: the S54 candidates (Γ_H, span fibration); (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic.\n\n" + anchor)

anchor = "- Session 58: intermediate covers of the M2"
S = rep(S, anchor, "- Session 59: P-dense loci (L_135, V_odd, X) inside Z_G (S59.1); the tangent-residual step on H_E at P-points of L_135 with a P-sextic (out of scope, S59.3; reopen only if Arya allows P-sextic coefficients).\n" + anchor)

anchor = "Session 58 (one directory; numpy; the pickles are large, a few MB):"
i = S.index(anchor)
j = S.index("\n- `m2blocks.py", i); j = S.index("\n", j + 1) + 1
S = S[:j] + ("Session 59 (self-contained; numpy only; nothing is written to disk):\n"
             "- `zg59.py <mode> <npoints> <starts> <seed>` (about 25 seconds per point at 60 starts, 100 seconds at 250; `ITER=<n>` in the environment sets the Gauss–Newton iterations, default 80): membership in row G's Z_G by solving M(a, b)c = 0 (5 equations, 4 unknowns) from random starts; prints the smallest relative residual, singular-value ratios and |a|, |b|. Modes: `plant` (control: 9 of the 12 crossings of a random Bézier × quartic), `rand`, `l135c`, `l135r` (totally real), `x3`, `vodd`. Runs used: `plant 3 60 1`, `rand 3 60 2`, `l135c 4 60 3`, `l135r 4 60 4`, `l135c 2 250 3`, `ITER=600 … l135c 1 120 3`, `vodd 2 250 5`.\n") + S[j:]

# ---------------- Start here ----------------
H = rep(H, "Updated Nov 20, 2026 (after session 58; repo inputs at commit 2536d12 are filed in the summary's Section 1a; next session is 59).",
        "Updated Nov 20, 2026 (after session 59; repo inputs at commit 2536d12 are filed in the summary's Section 1a; next session is 60, which also archives Sections 0aj and 0ak).")
H = rep(H, "## Next step (priority order, after session 58)", "## Next step (priority order, after session 59)")

i = H.index("**Session 58** (row M2: full count"); j = H.index("\n", i)
H = H[:i] + ("**Session 59** (r = 9 rows and P-dense loci; full text in the summary, Section 0aj). **Mechanism tested:** a variety with dense P-points inside a row hypersurface that reaches r = 9. **Results:** (S59.1, `zg59.py`) **Z_G (row G) contains neither L_135 nor V_odd** (planted controls 10⁻¹⁶, L_135 minima 10⁻⁷ to 10⁻⁴), so row G gets nothing from the T3 points; (S59.2) row E's H_E contains L_135 and is smooth there, but its genuine points on L_135 are exactly V_odd; (S59.3) a tangent P-line at a P-point of L_135 has a degree-8 residual on H_E, but forces a P-sextic graph (out of scope); (S59.4) row E with a fixed ℚ-sextic and P-valued Bézier and affine dials: u good ⇔ (u − β)/α = w² in K and χ_u | (S(u) − A − Bu)² − (u − β)(C + Du)²/α, a P-point problem on a family V_S. **Question for Arya (S59.4):** in row E, may the Bézier's control points and the affine maps applied to the ℚ-sextic graph have P-constructible parameters? (Session 58: M2 for a fixed generator, N ≥ 2638, Klein symmetry, primitive monodromy; archive 57–58.)") + H[j:]

lines = H.split("\n")
def find(prefix):
    k = [n for n, l in enumerate(lines) if l.startswith(prefix)]
    assert len(k) == 1, prefix
    return k[0]
i1, i2, i3 = find("1. **A_9 r = 5"), find("2. **r ∈ {7, 9}"), find("3. **Rational nonics, r = 9: row E**")
assert i2 == i1 + 1 and i3 == i2 + 1
newE = ("1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target): row E with a fixed ℚ-sextic and P-valued Bézier and affine dials (S59.4)**, once Arya confirms the dial rules. Then: the real test for r = 9 on V_S for a few rational S (u⁶, T_6, u³(u − 1)³), and a named mechanism, looking first for P-dense loci inside V_S where it is smooth (as L_135 ⊂ H_E, S59.2–S59.3). If Arya says no, row E stays a ℚ-family (25p3p7 = 21p5², degree 10; genuine points on L_135 only on V_odd). Row G: Z_G contains no known P-dense locus (S59.1).")
lines[i1:i3 + 1] = [newE, lines[i2], "3." + lines[i1][2:]]
H = "\n".join(lines)

anchor = "Session 58 added: intermediate covers of the M2 fixed-generator scheme"
H = rep(H, anchor, "Session 59 added: P-dense loci (L_135, V_odd, X) inside Z_G; the tangent-residual step on H_E with a P-sextic (out of scope unless Arya allows it). " + anchor)

anchor = "- Session 58 (one directory; numpy): `m2mono.py"
i = H.index(anchor); j = H.index("\n", i) + 1
H = H[:j] + "- Session 59 (self-contained; numpy): `zg59.py <plant|rand|l135c|l135r|x3|vodd> <npoints> <starts> <seed>` (about 25 seconds per point at 60 starts; `ITER=<n>` sets the Gauss–Newton iterations): membership in Z_G by an overdetermined solve; planted points give 10⁻¹⁶, others 10⁻⁷ to 10⁻⁴.\n" + H[j:]

open('/home/claude/summary59.md', 'w').write(S)
open('/home/claude/start59.md', 'w').write(H)
print(n0S, len(S), n0H, len(H))
for t in (S, H):
    print([l[:40] for l in t.split("\n") if l.startswith("## ")])
