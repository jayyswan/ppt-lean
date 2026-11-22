# Session 61: edit the condensed summary and Start here.md (string replacements on copies of the /mnt/project mirror).
# Usage: python3 edit61.py "<degree result text>"
import sys
DEG = sys.argv[1]
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
n0S, n0H = len(S), len(H)

def rep(txt, old, new, count=1):
    assert txt.count(old) == count, (old[:80], txt.count(old))
    return txt.replace(old, new)

sec = open('sec0al.md').read().replace('DEGRESULT', DEG)

# ---- summary ----
S = rep(S, '# Condensed summary: plan and progress (through session 60, Nov 20;', '# Condensed summary: plan and progress (through session 61, Nov 20;')
S = rep(S, '## 0. Sessions 25–60 in brief (full text in the frozen archives)', '## 0. Sessions 25–61 in brief (full text in the frozen archives; session 61 in Section 0al)')
line61 = ('- S61 (this file, Section 0al): **row E with P dials in coefficient form** (S61.1, exact): the row-E nonics are quo(V(w²), c(w)) + t; '
          'the good locus is linear in a7 (centred: H_E), the T_6 fibre is E6 (linear in a6) and E8 (linear in a8), so J⁻¹(T_6) is the Tschirnhaus variety of an explicit '
          'rational 6-parameter family. **J has degree 840 on the tangent-residual surfaces of H_E, as on generic 3-spaces** (S61.2, exact mod p): ruled out. '
          '**Row E3** (general cubic Bézier × fixed ℚ-sextic graph, all dials P): a hypersurface G3_S with no rationality gap (S61.3); real test passes for T_6; '
          'H_E and L_135 are not inside it (exact mod p, Chebyshev control); closure ⊃ D_K at inflection points of S (*unchecked*); scope question for Arya.\n')
S = rep(S, '- Nov 19 (between sessions 55 and 56): **second repo input**', line61 + '- Nov 19 (between sessions 55 and 56): **second repo input**')
S = rep(S, '\n## 1. The goal, the facts and the repo tools', '\n' + sec + '\n## 1. The goal, the facts and the repo tools')

# Section 3 rows
anchor = '| S60.4: row E with P dials closes r = 9 for K iff J = (I3, I4): H_E ⇢ A² takes a rational value at a P-point of H_E (a two-condition rationality gap on a P-dense hypersurface) | *unchecked* |\n'
rows = ('| S61.1: row E with P dials ⇔ nonics quo(V(w²), c(w)) + t; good locus Gn linear in a7 with coefficient D = a1a2 − a3 (centred: H_E); T_6 fibre E6 (linear in a6) and E8 (linear in a8): J⁻¹(T_6) is the Tschirnhaus variety of an explicit rational 6-parameter family over ℚ | [exact] (`e61sym.py`) + [numerical] planted check |\n'
        '| S61.2: the T_6 fibre of J on 3-space slices of H_E has degree 840, for generic slices and for slices tangent to H_E at points of L_135; linear-section J-families ruled out | [exact mod p] (`e61slice.py`) |\n'
        '| S61.3: row E3 (general cubic Bézier × fixed ℚ-sextic graph, all dials P): u good ⇔ S(X(u)) ∈ span(1, u, u², u³) for a cubic X, a hypersurface G3_S with no shape invariants; real test passes for T_6; F_p-points of H_E and L_135 are not on G3_{T6} (Chebyshev control vdim 2); closure(G3_S) ⊃ D_K (inflection-point degeneration); degree: ' + DEG.split('.')[0] + ' | *unchecked* (scope, degeneration) + [exact mod p] (`e3exact.py`, `e3deg.py`) + [numerical] (`e3num.py real`) |\n')
S = rep(S, anchor, anchor + rows)

# Section 4
S = rep(S, 'and the remaining condition is that the forced sextic\'s two shape invariants (I3, I4) are rational (S60.4).**',
        'and the remaining condition is that the forced sextic\'s two shape invariants (I3, I4) are rational (S60.4).** **S61: in coefficient form the T_6 fibre is triangular (S61.1); J has degree 840 on every linear-section P-family of H_E, tangent-residual surfaces included (S61.2).**\n'
        '- **G3_S (row E3, S61.3; scope to confirm with Arya):** general cubic Bézier × the graph of a fixed rational sextic S, all dials P. A hypersurface in K, affine-invariant, containing H_S, with no rationality gap; real points for r = 9 (S = T_6). H_E and L_135 are not inside it; its closure contains D_K (constant X at an inflection point of S). A P-point closes the case. The free choice of S is the lever to test next.')

# Section 5
S = rep(S, '- **Session 58:** S58.1–S58.6 (archive 57–58).',
        '- **Session 61:** S61.1–S61.4 (Section 0al). Row E with P dials in coefficient form (nonics quo(V(w²), c) + t; triangular T_6 fibre); J has degree 840 on tangent-residual surfaces of H_E (ruled out); row E3 (general cubic Bézier) turns the rationality gap into one hypersurface G3_S, real-feasible, containing neither H_E nor L_135.\n- **Session 58:** S58.1–S58.6 (archive 57–58).')
lesson = ('- **Method lesson (S61):** (1) **Before measuring a fibre of a map on a P-dense hypersurface, write the conditions in the coefficients of χ_u**: here each condition is linear in its top coefficient (a7, a6, a8), which shows at once that the fibre is the Tschirnhaus variety of an explicit rational family, and that linear slices see its full degree (840) wherever they are placed. '
          '(2) **When a fixed rational curve enters a row with P dials, check whether a more general partner curve absorbs the curve\'s affine invariants**: a cubic x(t) instead of a quadratic one turns the two-invariant gap of row E into a single hypersurface (row E3). '
          '(3) Random-start Gauss–Newton membership tests can converge to a degeneration that makes every point look like a member (here constant X at an inflection point of S); use the exact mod-p test with a saturation that removes the degenerate component, and a planted control over F_p (p ≡ 1 mod 36 makes T_18 = c split, giving 9 F_p-crossings with X = T_3). msolve does not parse parentheses: expand through Singular first (`e3deg.py`).\n')
S = rep(S, '- **Method lesson (S60):**', lesson + '- **Method lesson (S60):**')

# Section 6
dec = ('**Session 61 decision (linear-section J-families ruled out; row E3 proposed).** S61.1: the T_6 fibre of J is triangular in the coefficients of χ_u (a6, a7, a8 rational in a1, …, a5). S61.2: J has degree 840 on the tangent-residual surfaces of H_E, as on generic 3-spaces. S61.3: a general cubic Bézier removes the rationality gap; the good locus is a hypersurface G3_S, real-feasible for T_6, containing neither H_E nor L_135, with D_K in its closure. '
       '**Order now:** (1) r = 9: ask Arya whether row E3 (general cubic Bézier × ℚ-sextic graph) is in scope; then a mechanism for P-points on G3_S using the free choice of S (degenerations of S that put a P-dense locus into closure(G3_S) with genuine nearby points; tangent residuals at singular loci; the degree of G3_S); for row E proper only a P-family inside a J-fibre or a non-linear P-family with low I4-degree; (2) r = 7: M2 with a chosen generator (S58.4), or Z_G / R5; (3) A_9 r = 5: the S54 candidates; (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic.\n\n')
S = rep(S, '**Session 60 decision (row E with P dials reduced to two rational invariants).**', dec + '**Session 60 decision (row E with P dials reduced to two rational invariants).**')
S = rep(S, '- Session 60: linear slices of the row E good-generator locus H_S',
        '- Session 61: linear-section families of H_E (generic, or tangent at P-points of L_135) as J-families (T_6 fibre of degree 840, S61.2); random-start numerical membership tests for row E3 (they converge to the D_K degeneration; use `e3exact.py`); H_E and L_135 as P-dense sources inside G3_{T6} (not contained, S61.3).\n- Session 60: linear slices of the row E good-generator locus H_S')

# Section 7
s7 = ('\nSession 61 (one directory; sympy, numpy, cypari; Singular and msolve via `apt-get update && apt-get install -y singular msolve`):\n'
      '- `e61sym.py` (about a minute; sympy): the identity quo(V(w²), c) + t, the good locus Gn and the T_6 fibre equations E6, E8 in a1, …, a9, planted and random checks; writes `e61_formulas.pkl` (read by `e61slice.py`).\n'
      '- `e61slice.py <seed> <tan|gen|curve> [p]` (5–20 seconds; reads `e61_formulas.pkl`): an F_p-point of L_135 (mode `tan`), a tangent or generic centred 3-space, the system Gn, E6, E8, y·a3 = 1 in x1, x2, x3, y, written to `e61_<seed>_<mode>.ms` and solved by msolve. Runs `1 gen`, `1 tan`, `2 tan`: 840 each.\n'
      '- `e3num.py <plant|rand|G|l135|real> <npoints> <starts> <seed>` (numpy): `real 400 0 1` is the row-E3 real test; the membership modes converge to the D_K degeneration (`SPREAD=` in the environment filters nearly constant X) and are superseded by `e3exact.py`.\n'
      '- `e3exact.py <cheb|rand|HE|L135|HT6> <seed> [p]` (seconds; Singular; use p = 30097 ≡ 1 mod 36 for `cheb`): exact membership in G3_{T6} of an F_p-point; prints dim and vdim (dim −1: no solution; the trailing Singular error message after it is harmless). Runs `cheb 1`, `cheb 2` (dim 0, vdim 2), `rand 1–3`, `HE 1–3`, `L135 1–2` (no solution). `HT6` (a row-E point with 9 F_p-roots) needs too many trials; not used.\n'
      '- `e3deg.py <seed> [p]`: degree of G3_{T6} on a random line (7 variables: k, x0, …, x3 and two saturations; polynomials expanded through Singular, written to `e3deg_<seed>.ms`, solved by msolve; run it in the background). ' + DEG + '\n'
      '- `edit61.py` (the edit script for this file and `Start here.md`; reads `sec0al.md`).\n')
anchor7 = 'and the shape invariants (I3, I4) of the real residual points (runs `1 20 20`, `2 30 20`).\n'
S = rep(S, anchor7, anchor7 + s7)
S = rep(S, 'items decided in sessions 41–60)', 'items decided in sessions 41–61)')
S = rep(S, 'Add a Section 0al (session 61; then 0am, …) here', 'Add a Section 0am (session 62; then 0an, …) here')

# ---- Start here ----
H = rep(H, 'Updated Nov 20, 2026 (after session 60;', 'Updated Nov 20, 2026 (after session 61;')
H = rep(H, 'next session is 61, Section 0al; session 62 archives Sections 0al and 0am)', 'next session is 62, Section 0am; session 62 archives Sections 0al and 0am)')
H = rep(H, '## Next step (priority order, after session 60)', '## Next step (priority order, after session 61)')
i1 = H.index('1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target)')
i2 = H.index('\n2. **r ∈ {7, 9}')
new1 = ('1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 61:** (a) row E with P dials: the T_6 fibre of J is triangular in the coefficients of χ_u (S61.1), and **J has degree 840 on the tangent-residual surfaces of H_E**, as on generic 3-spaces (S61.2): linear-section families are dead; only a P-family inside a J-fibre or a non-linear P-family with low I4-degree could help. '
        '(b) **Row E3** (S61.3): with a general cubic Bézier (X(t), Y(t)) crossed with the graph of the fixed rational sextic S, u is good iff S(X(u)) ∈ span(1, u, u², u³) for some cubic X over P: a hypersurface G3_S in K with **no rationality gap** (S used as is, all dials P), real-feasible for T_6 (≥ 10 real crossings on 395 of 400 members), containing H_S, but **not** H_E or L_135 (exact mod p); its closure contains D_K (constant X at an inflection point of S, *unchecked*). '
        '**Next:** ask Arya whether a general cubic Bézier may be crossed with a ℚ-sextic graph (row E3); then a mechanism for P-points on G3_S using the free choice of S (degenerations of S that put a P-dense locus into closure(G3_S) with genuine nearby points: inflection points give D_K, flatter points give Bézier × y = x^k; tangent residuals at singular loci), with its degree (' + DEG.split('.')[0] + ').')
H = H[:i1] + new1 + H[i2:]
j1 = H.index('**Session 60** (row E with P dials, S = T_6;')
j2 = H.index('\n\n', j1)
p61 = ('**Session 61** (row E with P dials in coefficient form; row E3; full text in the summary, Section 0al). **Mechanism tested:** a P-family in H_E with a low-degree J-fibre (the tangent-residual surfaces of S60.4). **Results:** (S61.1, [exact], `e61sym.py`) the row-E nonics are quo(V(w²), c(w)) + t; the good locus is linear in a7 (centred: H_E) and the T_6 fibre is E6 (linear in a6), E8 (linear in a8), so J⁻¹(T_6) is the Tschirnhaus variety of an explicit rational 6-parameter family; '
       '(S61.2, [exact mod p], `e61slice.py`) **840** on generic 3-spaces and on 3-spaces tangent at L_135: ruled out; (S61.3, `e3exact.py`, `e3num.py`, `e3deg.py`) **row E3**: a general cubic Bézier × the fixed ℚ-sextic graph gives a hypersurface G3_S with no shape invariants, real-feasible for T_6, not containing H_E or L_135 (Chebyshev control vdim 2), closure ⊃ D_K; scope to confirm with Arya. '
       '(Session 60: row E with P dials reduced to J ∈ ℚ² at a P-point of H_E; H_E has dense P-points for r = 9; full text in `claude/Sessions 59-60 results (frozen).md`.)')
H = H[:j1] + p61 + H[j2:]
H = rep(H, 'exclude spurious components over special base points**.',
        'exclude spurious components over special base points**, **S61 write fibre conditions in the coefficients of χ_u (each linear in its top coefficient here); check whether a more general partner curve absorbs a fixed curve\'s affine invariants (row E3); exact mod-p membership with a saturation instead of random-start Gauss–Newton when degenerations attract**.')
H = rep(H, 'Session 60 added: linear slices of row E\'s H_S',
        'Session 61 added: linear-section families of H_E as J-families (840, also tangent at L_135); random-start membership tests for row E3 (they find the D_K degeneration); H_E and L_135 as P-dense sources inside G3_{T6} (not contained). Session 60 added: linear slices of row E\'s H_S')
k1 = H.index('- Session 60 (one directory; Singular and msolve via apt;')
k2 = H.index('\n', k1)
w61 = ('\n- Session 61 (one directory; Singular and msolve via apt; sympy, numpy, cypari): `e61sym.py` (about a minute; formulas Gn, E6, E8 in the coefficients of χ_u, planted checks; writes `e61_formulas.pkl`), `e61slice.py <seed> <tan|gen> [p]` (seconds; reads the pickle; T_6 fibre on a tangent or generic 3-space of H_E by msolve: 840), '
       '`e3num.py real 400 0 1` (row-E3 real test; its membership modes are unreliable), `e3exact.py <cheb|rand|HE|L135> <seed> 30097` (seconds; exact membership in G3_{T6} by Singular; dim −1 = no solution), `e3deg.py <seed>` (background; degree of G3_{T6} on a random line by msolve after expanding through Singular, since msolve does not parse parentheses). `edit61.py` is the edit script (reads `sec0al.md`).')
H = H[:k2] + w61 + H[k2:]
H = rep(H, '**After session 60 the summary is about 170k characters** and this file about 75k.', '**After session 61 the summary is about 185k characters** and this file about 85k.')
H = rep(H, '(S60.3, S60.4).\n- For r = 9 there is no P-rational line on Q4',
        '(S60.3, S60.4). **Session 61:** that rationality gap has no linear structure (840 on every linear-section family, S61.2); a general cubic Bézier removes it (row E3, a hypersurface G3_S with S fixed, S61.3), at the price of a hypersurface with no known P-dense locus inside, like row G.\n- For r = 9 there is no P-rational line on Q4')

open('summary61.md', 'w').write(S); open('start61.md', 'w').write(H)
print('summary', n0S, '->', len(S), '  start', n0H, '->', len(H))
import re
print([m for m in re.findall(r'^## [^\n]*', S, re.M)][:8], '...', len(re.findall(r'^## ', S, re.M)), 'level-2 headings')
