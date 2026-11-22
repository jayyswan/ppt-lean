# edit62.py -- session 62 checklist: archive Sections 0al (session 61) and 0am (session 62) into
# claude/Sessions 61-62 results (frozen).md, update the condensed summary and Start here.md.
# Reads the /mnt/project mirror and sec0am.md; writes summary62.md, archive6162.md, start62.md.
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
am = open('sec0am.md').read().rstrip('\n') + '\n'
n0S, n0H = len(S), len(H)
def rep(txt, old, new, cnt=1):
    assert txt.count(old) == cnt, (old[:70], txt.count(old)); return txt.replace(old, new)

# ---------------- archive ----------------
i0 = S.index('## 0al.'); i1 = S.index('## 1. The goal')
al = S[i0:i1].rstrip('\n') + '\n'
arch = ('# Sessions 61–62: full results (frozen archive)\n\nFrozen on Nov 20, 2026 (end of session 62). This file holds Section 0al (session 61) exactly as it stood in the condensed summary after session 61, and Section 0am (session 62) as written in session 62. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S61.1 … S62.4. Labels S61.1 … S62.4 point here.\n\n'
        + al + '\n' + am)
S = S[:i0] + S[i1:]

# ---------------- summary: header, archive list, Section 0 ----------------
S = rep(S, '(through session 61, Nov 20;', '(through session 62, Nov 20;')
S = rep(S, 'Fourteen frozen archives hold', 'Fifteen frozen archives hold')
S = rep(S, 'moved out of this file at the end of session 60.\n', 'moved out of this file at the end of session 60.\n- `claude/Sessions 61-62 results (frozen).md` (this project): the full Sections 0al and 0am for sessions 61–62 (labels S61.1 … S62.4), moved out of this file at the end of session 62.\n')
S = rep(S, 'Sessions from 61 on exist only in this file (Section 0al for session 61, 0am for session 62, and so on).', 'Sessions from 63 on exist only in this file (Section 0an for session 63, 0ao for session 64, and so on).')
S = rep(S, '## 0. Sessions 25–61 in brief (full text in the frozen archives; session 61 in Section 0al)', '## 0. Sessions 25–62 in brief (full text in the frozen archives)')
S = rep(S, '- S61 (this file, Section 0al):', '- S61 (archive 61–62):')
line62 = ('- S62 (archive 61–62): **row B5: Bézier (t², cubic) × P-affine image of a ℚ-quintic graph** (ℚ-graphs of degree ≤ 6 are allowed; *our reading, to confirm with Arya*). Crossing polynomial of degree 10 = 9 + 1; τ good iff (τ + s, ζ) ∈ L_135^{(10)}(K × P) and the forced quintic\'s one affine invariant I = B2²/B3³ is rational, with B3 = (p2² − 10p4)/40, B2 = −(p2³ − 15p2p4 + 50p6)/300 (S62.1, exact). **On L_135 itself (ζ = 0) every point is genuine** (unlike row E), so **r = 9 closes (over ℚ and over P) if I takes a rational value at a P-point of L_135**: one condition on a P-dense variety; planted end-to-end check with y = x⁵ − x³. Real test r = 9: B3 < 0 always, I fills (−2/5, 0], Ω_0 = L_135 ∩ {B2 = 0} has real points (S62.2). Exact mod p: degree 15 on lines (H5), 90 / 180 on planes (I0 = 0 / random), Galois group ⊇ A_90 (73-cycle): linear and planar families ruled out (S62.3). msolve misreads integer coefficients ≥ 2³¹: reduce mod p first.\n')
S = rep(S, '- Nov 19 (between sessions 55 and 56): **second repo input**', line62 + '- Nov 19 (between sessions 55 and 56): **second repo input**')

# ---------------- Section 3 rows ----------------
k = S.index('| S61.3: row E3'); ke = S.index('\n', k) + 1
rows = ('| S62.1: row B5 (Bézier (t², cubic) × P-affine image of a ℚ-quintic graph, all dials P): τ good ⇔ (τ + s, ζ) ∈ L_135^{(10)}(K × P) and I = B2²/B3³ ∈ ℚ (B3 = (p2² − 10p4)/40, B2 = −(p2³ − 15p2p4 + 50p6)/300, 10-point power sums); on the slice ζ = s = 0 (L_135 itself) every point with distinct nonzero conjugates is genuine; so r = 9 closes for K (over ℚ and over P) if I takes a rational value at a P-point of L_135 | [exact] (`b5sym.py`) + [numerical] planted (`b5plant.py`) + *unchecked* (reduction; scope reading of the degree-6 rule) |\n'
        '| S62.2: real test: on real L_135 (r = 9) B3 < 0, I ∈ (−2/5, 0] (bound observed), B2 changes sign (Ω_0 = L_135 ∩ {B2 = 0} has real points); same for the padded n = 10, r = 10; L_135 has real points with I of both signs for r = 5, 7 | [numerical] (`b5real.py`) |\n'
        '| S62.3: H5 (I free) has degree 15 on lines; B5_{I0} has degree 90 (I0 = 0) and 180 (random I0) on planes; on an integer plane the degree-90 scheme is irreducible over ℚ with a 73-cycle, so its Galois group contains A_90 | [exact mod p] (`b5deg.py`, `b5frob.py`, Singular cross-check `b5sing.py`) |\n'
        '| S62.4: linear and planar P-families of row B5 ruled out; the r = 9 gap is one rational value of I on L_135(P) | *unchecked* |\n')
S = S[:ke] + rows + S[ke:]

# ---------------- Section 4 ----------------
k = S.index('- **G3_S (row E3, S61.3;'); ke = S.index('\n', k) + 1
b5 = ('- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}, I0 ∈ ℚ ∩ (−2/5, 0] (row B5, S62; ℚ-quintic graph, all dials P):** a P-point on any one of them closes r = 9 for K, over ℚ and over P. I0 = 0 is the sextic hypersurface 50p6 − 15p2p4 + p2³ = 0 of L_135 (real points exist, S62.2). Same type as W (a hypersurface of the P-dense L_135), but a countable family whose union is dense in L_135(ℝ). Equivalently, I: L_135 ⇢ A¹ takes a rational value at a P-point. Slices of K: degrees 15, 90, 180, Galois group ⊇ A_90 (S62.3).\n')
S = S[:ke] + b5 + S[ke:]

# ---------------- Section 5 ----------------
S = rep(S, '- **Session 61:** S61.1–S61.4 (Section 0al).', '- **Session 62:** S62.1–S62.4 (archive 61–62). Row B5 (ℚ-quintic graph): L_135 is genuine for it, so r = 9 reduces to one rational value of I = B2²/B3³ at a P-point of L_135; real test passes; slices of K have degrees 15, 90, 180 with Galois group ⊇ A_90.\n- **Session 61:** S61.1–S61.4 (archive 61–62).')
lesson = ('- **Method lesson (S62):** (1) **List every graph degree the rules allow before designing a row**: the degree-≤ 6 rule for ℚ-graphs includes quintics, and a lower-degree graph with the same Bézier has fewer auxiliary crossings (one instead of three), which made L_135 genuine where row E needed V_odd. (2) **Count the invariants of the fixed curve under all allowed affine maps** (quintics: one, I = B2²/B3³; sextics: two): that is the size of the rationality gap. (3) **msolve misreads integer coefficients of about 2³¹ and above**; always reduce coefficients mod p in Python before writing the input (a wrong cycle type [1, 2, 87] became [17, 73] after reduction; Singular agreed). (4) For a degree-N scheme a Frobenius type with a prime cycle q, N/2 < q ≤ N − 3, coprime to the other cycle lengths, together with subset sums {0, N}, proves the Galois group contains A_N (Jordan); this is cheap evidence against decomposition mechanisms.\n')
S = rep(S, '- **Method lesson (S61):**', lesson + '- **Method lesson (S61):**')

# ---------------- Section 6 ----------------
dec = ('**Session 62 decision (row B5: one rational condition on L_135).** S62.1: a ℚ-quintic graph with the row-E Bézier gives a row whose good locus contains all of L_135 with genuine constructions; what is left is the quintic\'s one affine invariant I = B2²/B3³, which must be rational. S62.2: the real test passes for r = 9 (I ∈ (−2/5, 0], B2 changes sign). S62.3: linear and planar slices of K have degrees 15, 90, 180 with full monodromy. **Order now:** (0) ask Arya to confirm that ℚ-quintic graphs (rational coefficients) are allowed under the degree-≤ 6 rule; (1) r = 9: a mechanism controlling I on L_135(P): a P-rational non-line curve in L_135 with deg I ≤ 8 or decomposable monodromy; the T3 chain with a free P-dial before the quintic cut (measure the degree of I = I0 along it); row B5 with a general cubic Bézier (a hypersurface for fixed I0; degree, containment of L_135); the extremal configurations of the observed bound I ≥ −2/5; the ζ ≠ 0 branch s² = p2/240 over X; then G3_S (row E3) as before; (2) r = 7: M2 with a chosen generator (S58.4), or Z_G / R5, and row B5 if L_135 has P-points for r = 7; (3) A_9 r = 5: the S54 candidates, and row B5 likewise; (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic.\n\n')
S = rep(S, '**Session 61 decision (linear-section J-families ruled out;', dec + '**Session 61 decision (linear-section J-families ruled out;')
S = rep(S, '- Session 61: linear-section families of H_E', '- Session 62: linear and planar slices of K for row B5 (H5 degree 15; B5_{I0} degree 90 / 180, Galois group ⊇ A_90, S62.3); P-lines in L_135 as a source for Ω_{I0} (they already close r = 9 through T2, so they add nothing); msolve inputs with unreduced integer coefficients.\n- Session 61: linear-section families of H_E')
S = rep(S, 'items decided in sessions 41–61)', 'items decided in sessions 41–62)')

# ---------------- Section 7 ----------------
s7 = ('\nSession 62 (one directory; sympy, numpy, cypari; Singular and msolve via `apt-get update && apt-get install -y singular msolve`):\n'
      '- `b5sym.py` (seconds; sympy): Newton\'s identities with odd power sums zero, B3 = (p2² − 10p4)/40, B2 = −(p2³ − 15p2p4 + 50p6)/300, depressing check, and a numerical 10-point identity χ_v(w)(w − ζ) = Π(w − y_i).\n'
      '- `b5real.py <r> <n> <N> <seed>` (about 10 seconds per 1500 points; numpy): real points of {p1 = p3 = p5 = 0} in ℝ^r × ℂ^s by minimum-norm Newton; ranges of b2 = (p2³ − 15p2p4 + 50p6)/p2³, b3 = (p2² − 10p4)/p2² and I. Runs `9 9 1500 1`, `10 10 1500 1`, `7 9 1500 1`, `5 9 1500 1`, `8 10 1500 1`. (n − r must be even.)\n'
      '- `b5plant.py <seed>` (seconds; numpy): a real point of Ω_0 by Newton, E, R, the affine image of y = x⁵ − x³ and the 10 crossings of the Bézier (t², −R(t)) (runs 1, 2).\n'
      '- `b5deg.py <line|plane|plane0|l135plane> <seed> [p]` (seconds; sympy over GF(p), msolve): H5 on a random line (15), B5_{I0} on a random plane (`plane0` 90, `plane` 180), control `l135plane` (90); writes `b5_<mode>_<seed>.ms(.out)`.\n'
      '- `fdeg.py <file.ms.out>` (seconds; cypari): factor degrees mod p of msolve\'s eliminant.\n'
      '- `b5frob.py <seed> <nprimes>` (about 40 seconds per prime; msolve): the `plane0` system on one integer plane (entries in [−9, 9]) reduced mod each of the first primes above 40000; cycle types and common subset sums (run `3 10`: {0, 90}, [17, 73] at 40013). **Reduces coefficients mod p before writing (msolve misreads large integers).**\n'
      '- `b5sing.py` (about a minute; Singular): the same system mod 40013 by `std` + `fglm` + `factorize` (cross-check: 17 + 73).\n'
      '- `edit62.py` (the edit and archive script for this file, `Start here.md` and the 61–62 archive; reads `sec0am.md`).\n')
anchor7 = '- `edit61.py` (the edit script for this file and `Start here.md`; reads `sec0al.md`).\n'
S = rep(S, anchor7, anchor7 + s7)

# ---------------- Section 8 ----------------
S = rep(S, 'Add a Section 0am (session 62; then 0an, …) here', 'Add a Section 0an (session 63; then 0ao, …) here')
S = rep(S, '**At the end of session 62, move Sections 0al and 0am into a new frozen archive `claude/Sessions 61-62 results (frozen).md`.**', '**At the end of session 64, move Sections 0an and 0ao into a new frozen archive `claude/Sessions 63-64 results (frozen).md`.**')
S = rep(S, '`Sessions 57-58 results (frozen).md`, `Sessions 59-60 results (frozen).md`), and don', '`Sessions 57-58 results (frozen).md`, `Sessions 59-60 results (frozen).md`, `Sessions 61-62 results (frozen).md`), and don')

# ---------------- Start here ----------------
H = rep(H, 'Updated Nov 20, 2026 (after session 61;', 'Updated Nov 20, 2026 (after session 62;')
H = rep(H, 'next session is 62, Section 0am; session 62 archives Sections 0al and 0am)', 'next session is 63, Section 0an; session 64 archives Sections 0an and 0ao)')
H = rep(H, 'sessions 59–60 (S59.1 … S60.4) in `claude/Sessions 59-60 results (frozen).md`.', 'sessions 59–60 (S59.1 … S60.4) in `claude/Sessions 59-60 results (frozen).md`; sessions 61–62 (S61.1 … S62.4) in `claude/Sessions 61-62 results (frozen).md`.')
H = rep(H, 'session 61 is Section 0al, session 62 Section 0am; session 62 also moves 0al and 0am to a 61–62 archive', 'session 63 is Section 0an, session 64 Section 0ao; session 64 also moves 0an and 0ao to a 63–64 archive')
H = rep(H, '`claude/Sessions 57-58 results (frozen).md` or `claude/Sessions 59-60 results (frozen).md`', '`claude/Sessions 57-58 results (frozen).md`, `claude/Sessions 59-60 results (frozen).md` or `claude/Sessions 61-62 results (frozen).md`')
H = rep(H, '`claude/Sessions 59-60 results (frozen).md` (S59.1 … S60.4).', '`claude/Sessions 59-60 results (frozen).md` (S59.1 … S60.4), `claude/Sessions 61-62 results (frozen).md` (S61.1 … S62.4).')
H = rep(H, '**After session 61 the summary is about 185k characters** and this file about 85k.', '**After session 62 the summary is about 180k characters** and this file about 90k.')
H = rep(H, 'At the end of session 62, move Sections 0al and 0am (sessions 61–62) into a new frozen archive `claude/Sessions 61-62 results (frozen).md` the same way', 'At the end of session 64, move Sections 0an and 0ao (sessions 63–64) into a new frozen archive `claude/Sessions 63-64 results (frozen).md` the same way (session 62 did this for sessions 61–62 with `edit62.py`)')
H = rep(H, '## Next step (priority order, after session 61)', '## Next step (priority order, after session 62)')
i1 = H.index('1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target)')
i2 = H.index('\n2. **r ∈ {7, 9}')
new1 = ('1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 62: row B5** (Bézier (t², cubic) × P-affine image of a **ℚ-quintic** graph; ℚ-graphs of degree ≤ 6 are allowed by Arya\'s Nov 20 rule, *our reading: confirm with Arya first*). The crossing polynomial has degree 10 = 9 + 1, and τ is good iff (τ + s, ζ) ∈ L_135^{(10)}(K × P) and the forced quintic\'s single affine invariant **I = B2²/B3³** is rational, with B3 = (p2² − 10p4)/40 and B2 = −(p2³ − 15p2p4 + 50p6)/300 (S62.1). **On L_135 itself (ζ = s = 0) every point is genuine**, so **r = 9 closes for K, over ℚ and over P, as soon as I takes a rational value at a P-point of L_135** (I0 = 0: the sextic hypersurface 50p6 − 15p2p4 + p2³ = 0 of L_135). The real test passes: I ∈ (−2/5, 0] and B2 changes sign (S62.2). Slices of K have degrees 15 (lines), 90 and 180 (planes), with Galois group ⊇ A_90 (S62.3): linear families are dead. '
        '**Next:** a mechanism that controls I on L_135(P). Candidates: (a) a P-rational non-line curve in L_135 with deg I ≤ 8 or decomposable monodromy (P-lines in L_135 already close r = 9 through T2); (b) the T3 chain with a free P-dial before the quintic cut (q0 on the conic Q_P), measuring the degree of I = I0 along the resulting curve of L_135-points; (c) row B5 with a general cubic Bézier (a hypersurface for fixed I0): degree and containment of L_135; (d) the extremal configurations of the observed bound I ≥ −2/5; (e) the ζ ≠ 0 branch s² = p2/240 over X (S62.1). '
        '(Row E3 / G3_S from session 61 stays open behind these: a mechanism for P-points on G3_S using the free choice of S, and its degree, which msolve did not finish in 7 minutes.) **Toolkit rules (Arya, Nov 20):** any linear map with P entries plus P translations on any curve; ℚ-graphs strictly ≤ degree 6; any two toolkit curves may be crossed; Béziers ≤ degree 3; P closed under trig, exp, log (summary Section 1a).')
H = H[:i1] + new1 + H[i2:]
j1 = H.index('**Session 61** (row E with P dials in coefficient form;')
j2 = H.index('\n\n', j1)
p62 = ('**Session 62** (row B5: Bézier × ℚ-quintic graph; full text in `claude/Sessions 61-62 results (frozen).md`, Section 0am). **Mechanism tested:** the P-dense L_135 inside row B5\'s good locus with genuine constructions, leaving one rational invariant. **Results:** (S62.1, [exact] `b5sym.py`, planted `b5plant.py`) τ good ⇔ (τ + s, ζ) ∈ L_135^{(10)} and I = B2²/B3³ ∈ ℚ; L_135 (ζ = 0) is genuine everywhere, so r = 9 reduces to a rational value of I at a P-point of L_135; '
       '(S62.2, `b5real.py`) real test passes for r = 9 (I ∈ (−2/5, 0], B2 changes sign); (S62.3, `b5deg.py`, `b5frob.py`, [exact mod p]) degrees 15 / 90 / 180 on lines and planes, Galois group ⊇ A_90: slices ruled out. msolve misreads integer coefficients ≥ 2³¹ (reduce mod p first). '
       '(Session 61: row E with P dials in coefficient form, 840 on tangent-residual surfaces; row E3 G3_S; same archive, Section 0al.)')
H = H[:j1] + p62 + H[j2:]
H = rep(H, 'exact mod-p membership with a saturation instead of random-start Gauss–Newton when degenerations attract**.',
        'exact mod-p membership with a saturation instead of random-start Gauss–Newton when degenerations attract**, **S62 list every graph degree the rules allow (a ℚ-quintic has one auxiliary crossing with the row-E Bézier, which makes L_135 genuine); count the fixed curve\'s affine invariants (the size of the rationality gap); reduce msolve coefficients mod p; a prime cycle q with N/2 < q ≤ N − 3 plus subset sums {0, N} proves ⊇ A_N**.')
H = rep(H, 'Session 61 added: linear-section families', 'Session 62 added: linear and planar slices of K for row B5 (15, 90, 180, ⊇ A_90); P-lines in L_135 as a source for Ω_{I0} (they already close r = 9 through T2); msolve inputs with unreduced integer coefficients. Session 61 added: linear-section families')
k1 = H.index('- Session 61 (one directory; Singular and msolve via apt;'); k2 = H.index('\n', k1)
w62 = ('\n- Session 62 (one directory; sympy, numpy, cypari; Singular and msolve via apt): `b5sym.py` (seconds; B2, B3 in power sums), `b5real.py <r> <n> <N> <seed>` (real test; n − r even), `b5plant.py <seed>` (end-to-end planted crossing with y = x⁵ − x³), '
       '`b5deg.py <line|plane|plane0|l135plane> <seed>` (msolve counts 15, 180, 90, 90), `fdeg.py <out>` (factor degrees of msolve\'s eliminant), `b5frob.py <seed> <nprimes>` (integer plane, cycle types over many primes; about 40 seconds per prime), `b5sing.py` (Singular cross-check). **Reduce coefficients mod p before writing msolve input.** `edit62.py` is the edit and archive script (reads `sec0am.md`).')
H = H[:k2] + w62 + H[k2:]
H = rep(H, 'a hypersurface with no known P-dense locus inside, like row G.\n',
        'a hypersurface with no known P-dense locus inside, like row G. **Session 62:** a ℚ-quintic graph with the row-E Bézier (row B5) is genuine on all of L_135, so the r = 9 gap is one rational value of I = B2²/B3³ at a P-point of L_135 (S62.1–S62.2); slices of K have full monodromy (S62.3).\n')

H = rep(H, 'one line per session 25–60 (Section 0), the full results of sessions from 61 on (Section 0al onward)', 'one line per session 25–62 (Section 0), the full results of sessions from 63 on (Section 0an onward)')
open('summary62.md', 'w').write(S); open('archive6162.md', 'w').write(arch); open('start62.md', 'w').write(H)
import re
print('summary', n0S, '->', len(S), ' archive', len(arch), ' start', n0H, '->', len(H))
print([l[:40] for l in S.split('\n') if l.startswith('## ')])
print([l[:40] for l in arch.split('\n') if l.startswith('## ')])
