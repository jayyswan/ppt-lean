# edit66.py -- session 66 checklist: archive Sections 0ap (session 65) and 0aq (session 66) into
# claude/Sessions 65-66 results (frozen).md, update the condensed summary and Start here.md.
# Reads the /mnt/project mirror and sec0aq.md; writes summary66.md, archive6566.md, start66.md.
import re
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
aq = open('sec0aq.md').read().rstrip('\n') + '\n'
n0S, n0H = len(S), len(H)
def rep(txt, old, new, cnt=1):
    assert txt.count(old) == cnt, (old[:80], txt.count(old)); return txt.replace(old, new)

# ---------------- archive ----------------
i0 = S.index('## 0ap.'); i1 = S.index('## 1. The goal')
ap = S[i0:i1].rstrip('\n') + '\n'
arch = ('# Sessions 65–66: full results (frozen archive)\n\nFrozen on Nov 21, 2026 (end of session 66). This file holds Section 0ap (session 65) exactly as it stood in the condensed summary after session 65, and Section 0aq (session 66) as written in session 66. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S65.1 … S66.5. Labels S65.1 … S66.5 point here.\n\n'
        + ap + '\n' + aq)
S = S[:i0] + S[i1:]

# ---------------- header, archive list, Section 0 ----------------
S = rep(S, '(through session 65, Nov 21;', '(through session 66, Nov 21;')
S = rep(S, 'Sixteen frozen archives hold', 'Seventeen frozen archives hold')
b = '- `claude/Sessions 63-64 results (frozen).md` (this project): the full Sections 0an and 0ao for sessions 63–64 (labels S63.1 … S64.6), moved out of this file at the end of session 64.\n'
S = rep(S, b, b + '- `claude/Sessions 65-66 results (frozen).md` (this project): the full Sections 0ap and 0aq for sessions 65–66 (labels S65.1 … S66.5), moved out of this file at the end of session 66.\n')
S = rep(S, 'Sessions from 65 on exist only in this file (Section 0ap for session 65, 0aq for session 66, and so on).', 'Sessions from 67 on exist only in this file (Section 0ar for session 67, 0as for session 68, and so on).')
S = rep(S, '## 0. Sessions 25–65 in brief (full text in the frozen archives; session 65 in Section 0ap below)', '## 0. Sessions 25–66 in brief (full text in the frozen archives)')
S = rep(S, '- S65 (Section 0ap):', '- S65 (archive 65–66):')
i = S.index('- S65 (archive 65–66):'); j = S.index('\n', i)
line66 = ('\n- S66 (archive 65–66): **what a global mechanism for V_A must contain, and the wild local primes.** '
          '(S66.1) By Brassil–Reichstein\'s criterion (n = 10 = 9 + 1: 9y1 + y2 = 9y1³ + y2³ = 0 has only the trivial solution) there is a 3-field F ⊇ ℚ and a degree-10 algebra E with X_E(F) = V_E(F) = ∅; so E(w²) + R(w) is not generic for S_10, and **every field-independent construction and every quadric / conic / Châtelet fibration over a rational base is dead**; a global mechanism needs cubic-type ℚ-arithmetic. '
          '(S66.2) Over ℚ, Tr a³ (10 variables, nonsingular) has a zero for every A by Heath-Brown; the 126-nodal nonary X_A is not covered by results found. '
          '(S66.3) Exact p-adic plane sections (squarefree degree-15 resultant + polrootspadic) certify smooth ℚ_p-points on ramified algebras. '
          '(S66.4) **No local obstruction in 1427 wild or uncovered algebras at p = 2, 3, 5, 7** (977 at p = 3, including Eisenstein nonics and (e, f) = (3, 3) fields).')
S = S[:j] + line66 + S[j:]

# ---------------- Section 3 rows ----------------
i = S.index('| S65.5:'); j = S.index('\n', i)
rows = '''
| S66.1: (Brassil–Reichstein, n = 10 = 3² + 3⁰) there are a 3-field F ⊇ ℚ and a degree-10 étale F-algebra E with no nonzero a, tr a = tr a³ = 0 (even tr a³ = 0 alone fails); hence V_E(F) = ∅, E(w²) + R(w) is not a generic polynomial for S_10 over ℚ, and no construction of points of V_A valid over all fields of characteristic 0 using linear steps, rational varieties, quadrics, conics or roots of degree prime to 3 exists; no fibration of a variety built from A over a ℚ-rational base with quadric, conic or Châtelet fibres exists | [source] (BR Thm 1.2, 1.3, Rem. 9.3, via a summary of the paper) + *unchecked* (consequences) |
| S66.2: over ℚ, tr_A(a³) is a nonsingular cubic form in 10 variables, so (Heath-Brown 1983) every degree-10 A has a ∉ ℚ with Tr a³ = 0; the Hermite–Joubert cubic X_A = {Tr a = Tr a³ = 0} (9 variables, 126 geometric nodes) is not covered by Hooley 1988 (nonsingular) or Browning–Heath-Brown (n ≥ 11 + σ) | [source] + *unchecked* (Hooley II, III not checked) |
| S66.3: exact certificate for smooth ℚ_p-points of V_A on any étale algebra: a ℚ-plane in {Tr = 0} with nonzero constant leading coefficients, deg Res = 15 and Res squarefree; every simple ℚ_p-root of Res is a smooth ℚ_p-point; use factor-adapted coordinates for product algebras | [exact] (`loc66.py`, `prod66.py`) |
| S66.4: no local obstruction in 1427 sampled wild or S64-uncovered local algebras: p = 3 (977: Eisenstein nonics, (3,3) fields, three wild cubics, wild cubic × sextic, …), p = 5 (240: E5 × E5, E10, E5 × U3 × ℚ_5², …), p = 7 (60), p = 2 (150); every one has a certified smooth ℚ_p-point | [exact] (random sample, not a classification) |
| S66.5: any unconditional global mechanism for V_A must contain a step that fails over some 3-field (cubic-type ℚ-arithmetic, e.g. nonsingular cubic forms in ≥ 10 variables); local side unchanged (no obstruction found) | decision |'''
S = S[:j] + rows + S[j:]

# ---------------- Section 4 ----------------
S = rep(S, '- (conditional, S65.4) under Colliot-Thélène\'s conjecture:', '- (conditional, S65.4; S66.4: no local obstruction in 1427 wild local algebras) under Colliot-Thélène\'s conjecture:')

# ---------------- Section 5 ----------------
S = rep(S, '- **Session 65:** S65.1–S65.5 (Section 0ap).', '- **Session 66:** S66.1–S66.5 (archive 65–66). The 3-field test of global mechanisms (Brassil–Reichstein): V_A has no points over some 3-field, so every field-independent or quadric-fibration mechanism is dead and cubic-type ℚ-arithmetic is required; Heath-Brown gives Tr a³ = 0 over ℚ; exact p-adic plane sections find no local obstruction in 1427 wild algebras.\n- **Session 65:** S65.1–S65.5 (archive 65–66).')
lesson = ('- **Method lesson (S66):** (1) **Before designing a global ℚ-point mechanism, test the variety over p-closed fields** (Brassil–Reichstein criterion for trace conditions): if it has no points over some p-field, every mechanism built from steps solvable over all p-fields (linear, rational, quadrics, conics, roots of degree prime to p) is impossible, and the essential arithmetic input (here cubic forms, p = 3) and the first prime to test locally are identified. '
          '(2) **Certify local points by exact plane sections**: squarefree resultant of full Bézout degree plus polrootspadic gives smooth ℚ_p-points on wild algebras without smooth points mod p. '
          '(3) **Use factor-adapted coordinates for product algebras** (the power basis of a root of the product polynomial is p-adically ill-conditioned: 0 of 300 planes against 34 of 150).\n')
S = rep(S, '- **Method lesson (S65):**', lesson + '- **Method lesson (S65):**')

# ---------------- Section 6 ----------------
dec = ('**Session 66 decision (the global mechanism must be cubic-arithmetic; no local obstruction).** S66.1: by Brassil–Reichstein, V_A has no points over some 3-field for some A, so field-independent constructions and quadric / conic / Châtelet fibrations over rational bases are dead. S66.2: Tr a³ = 0 has ℚ-solutions by Heath-Brown; the nodal nonary X_A is uncovered. S66.4: no local obstruction in 1427 wild local algebras. '
       '**Order now:** (1) rational nonics and decics: a cubic-arithmetic mechanism for V_A(ℚ) (a variety Y → V_A built from A, fibred over a base with dense ℚ-points, with nonsingular cubic fibres in ≥ 10 variables; or the Hasse principle for the 126-nodal nonary X_A (check Hooley II, III) plus a step for the quintic); the local classification at 2, 3, 5, 7 or a lemma for wild factors (S66.4 sampled only), and the six unramified W_K types; (2) over P (r = 9): the S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic.\n\n')
S = rep(S, '**Session 65 decision (no', dec + '**Session 65 decision (no')
S = rep(S, '- Session 65: searching for a Brauer', '- Session 66: field-independent constructions of points of V_A or X_A (generic Tschirnhaus, E(w²) + R(w) as a generic polynomial) and fibrations of varieties built from A over rational bases with quadric, conic or Châtelet fibres (all impossible, S66.1); random-entry plane sections in the power basis of a product polynomial (use factor-adapted coordinates, S66.3).\n- Session 65: searching for a Brauer')
S = rep(S, 'items decided in sessions 41–65)', 'items decided in sessions 41–66)')

# ---------------- Section 7 ----------------
s7 = ('Session 66 (one directory; cypari; all certificates exact):\n'
      '- `loc66.py "<f>" <p> <planes> <seed> [B] [nonic]` (about 0.1–1 s per 30 planes): certified p-adic plane sections of V_A for A = ℚ_p[x]/(f) × ℚ_p (nonic mode, deg f = 9) or A = ℚ_p[x]/(f) (mode `decic`, deg f = 10, planes moved into {Tr = 0} by `tz`); also the module for the next scripts (exec\'d up to `__main__`).\n'
      '- `sweep66.py <eis9|e3f3|c333|c36|c3u6|c3e3u3> <count> <planes> <seed> [p] [M]` (1–3 minutes per 100 algebras): random nonic local algebras at p (Eisenstein coefficients p·[0, M)); prints hits per algebra and ZERO lines. Runs: `eis9 60 20 1 3 9`, `eis9 300 15 2 3 27`, `e3f3 120 15 4 3 9`, `c333 150 15 3 3 9`, `c36 150 15 5 3 9`, `c3u6 100 15 6 3 9`, `c3e3u3 100 15 7 3 9`.\n'
      '- `recheck66.py <log> <planes> <B> [max]` (nonic, p = 3): reruns the ZERO algebras of a log with entries uniform in [−B, B] (B = 364).\n'
      '- `sweep5.py <kind> <count> <planes> <seed> <p> [M]` (degree-10 algebras; kind = comma list of E<d> Eisenstein, U<d> unramified, K<e> x^e − p·u, Q linear): runs `E5,E5`, `E5,U3,Q,Q`, `E5,K3,Q,Q`, `E10`, `E5,U5`, `E5,E3,Q,Q` (40 each, p = 5, M = 25), `E7,U2,Q`, `E7,Q,Q,Q` (30 each, p = 7, M = 49), `E5,U3,Q,Q`, `E5,E3,Q,Q`, `E3,E3,E3,Q`, `E7,U3`, `E5,E5` (30 each, p = 2, M = 8). `recheck5.py <log> <planes> <B> <p> [seed]` reruns ZERO lines (B = 312 for 5⁴).\n'
      '- `prod66.py "<g1>;<g2>;…" <p> <planes> <seed> <B> <wmax>` (seconds per 100 planes): the same certificate in factor-adapted coordinates with valuation-weighted entries; use it for product algebras.\n'
      '- `edit66.py` (this edit and archive script; reads `sec0aq.md`).\n\n')
S = rep(S, '## 8. Ground rules (revised Nov 17)', s7 + '## 8. Ground rules (revised Nov 17)')

# ---------------- Section 8 ----------------
S = rep(S, 'Add a Section 0aq (session 66) here', 'Add a Section 0ar (session 67; then 0as, …) here')
S = rep(S, '**At the end of session 66, move Sections 0ap and 0aq into a new frozen archive `claude/Sessions 65-66 results (frozen).md`.**', '**At the end of session 68, move Sections 0ar and 0as into a new frozen archive `claude/Sessions 67-68 results (frozen).md`.**')
S = rep(S, '`Sessions 63-64 results (frozen).md`), and don', '`Sessions 63-64 results (frozen).md`, `Sessions 65-66 results (frozen).md`), and don')

# ---------------- Start here ----------------
H = rep(H, 'Updated Nov 21, 2026 (after session 65;', 'Updated Nov 21, 2026 (after session 66;')
H = rep(H, 'next session is 66, Section 0aq; session 66 archives Sections 0ap and 0aq into `claude/Sessions 65-66 results (frozen).md`)', 'next session is 67, Section 0ar; session 68 archives Sections 0ar and 0as into `claude/Sessions 67-68 results (frozen).md`)')
H = rep(H, 'sessions 63–64 (S63.1 … S64.6) in `claude/Sessions 63-64 results (frozen).md`.', 'sessions 63–64 (S63.1 … S64.6) in `claude/Sessions 63-64 results (frozen).md`; sessions 65–66 (S65.1 … S66.5) in `claude/Sessions 65-66 results (frozen).md`.')
H = rep(H, 'session 65 is Section 0ap, session 66 Section 0aq; session 66 also moves 0ap and 0aq to a 65–66 archive', 'session 67 is Section 0ar, session 68 Section 0as; session 68 also moves 0ar and 0as to a 67–68 archive')
H = rep(H, '`claude/Sessions 61-62 results (frozen).md` or `claude/Sessions 63-64 results (frozen).md`', '`claude/Sessions 61-62 results (frozen).md`, `claude/Sessions 63-64 results (frozen).md` or `claude/Sessions 65-66 results (frozen).md`')
H = rep(H, 'At the end of session 66, move Sections 0ap and 0aq (sessions 65–66) into a new frozen archive `claude/Sessions 65-66 results (frozen).md` the same way (session 64 did this for sessions 63–64 with `edit64.py`;',
        'At the end of session 68, move Sections 0ar and 0as (sessions 67–68) into a new frozen archive `claude/Sessions 67-68 results (frozen).md` the same way (session 66 did this for sessions 65–66 with `edit66.py`; session 64 did this for sessions 63–64 with `edit64.py`;')
H = rep(H, '`claude/Sessions 63-64 results (frozen).md` (S63.1 … S64.6).', '`claude/Sessions 63-64 results (frozen).md` (S63.1 … S64.6), `claude/Sessions 65-66 results (frozen).md` (S65.1 … S66.5).')
H = rep(H, 'one line per session 25–64 (Section 0), the full results of sessions from 65 on (Section 0ap onward)', 'one line per session 25–66 (Section 0), the full results of sessions from 67 on (Section 0ar onward)')
H = rep(H, '## Next step (priority order, after session 65)', '## Next step (priority order, after session 66)')
i = H.index('**Session 65** (the global step'); j = H.index('\n', i)
p66 = ('**Session 66** (what a global mechanism for V_A must contain; wild local primes; full text in `claude/Sessions 65-66 results (frozen).md`, Section 0aq). **Mechanisms tested:** field-independent constructions (versality of E(w²) + R(w)) and fibrations with quadric / conic / Châtelet fibres over a rational base. **Test:** points over 3-fields. **Result: dead.** '
       '(S66.1) By Brassil–Reichstein (n = 10 = 9 + 1: 9y1 + y2 = 9y1³ + y2³ = 0 only trivially) some degree-10 algebra over a 3-field F ⊇ ℚ has no a ≠ 0 with tr a = tr a³ = 0, so V_E(F) = ∅, while quadrics, conics, roots of degree prime to 3 and rational varieties all have F-points; **any global mechanism must contain a cubic-type arithmetic step** (fails over some 3-field). '
       '(S66.2) Over ℚ, Tr a³ is a nonsingular 10-variable cubic, so Heath-Brown gives Tr a³ = 0 for every A; the 126-nodal nonary X_A = {Tr a = Tr a³ = 0} is not covered by results found. '
       '(S66.3) Exact p-adic plane sections (squarefree degree-15 resultant + polrootspadic) certify smooth ℚ_p-points on wild algebras. (S66.4) **No local obstruction in 1427 sampled wild or uncovered algebras at p = 2, 3, 5, 7.** (Session 65: no Brauer–Manin obstruction, conditional closure under Colliot-Thélène; same archive, Section 0ap.)')
H = H[:i] + p66 + H[j:]
H = rep(H, '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** ',
        '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 66: a global mechanism must be cubic-arithmetic (S66.1: V_A can fail over 3-fields, so field-independent and quadric/conic-fibration mechanisms are dead); no local obstruction in 1427 wild algebras (S66.4).** **Next: a variety built from A, fibred over a base with dense ℚ-points, whose fibres are nonsingular cubic hypersurfaces in ≥ 10 variables (Heath-Brown), or the Hasse principle for the 126-nodal nonary X_A (check Hooley II, III) plus a quintic step; then the local classification at 2, 3, 5, 7.** ')
H = rep(H, '**S65 before a Brauer–Manin', '**S66 test a global mechanism over p-closed fields first (Brassil–Reichstein): if the variety can lack points there, steps solvable over all p-fields cannot suffice; certify local points by exact plane sections (squarefree resultant + polrootspadic) in factor-adapted coordinates**, **S65 before a Brauer–Manin')
H = rep(H, 'Session 65 added: searching for a Brauer', 'Session 66 added: field-independent constructions for V_A / X_A and quadric, conic or Châtelet fibrations over rational bases (S66.1); plane sections in the power basis of a product polynomial. Session 65 added: searching for a Brauer')
H = rep(H, '**Session 65:** no Brauer–Manin obstruction on any twist V_A', '**Session 66:** every global mechanism needs cubic-type ℚ-arithmetic (S66.1, 3-fields); no local obstruction in 1427 wild local algebras (S66.4). **Session 65:** no Brauer–Manin obstruction on any twist V_A')
i = H.index('- Session 65 (one directory; numpy; Singular'); j = H.index('\n', i)
ws = ('\n- Session 66 (one directory; cypari; exact): `loc66.py "<f>" <p> <planes> <seed> [B] [nonic|decic]` (module and single test), `sweep66.py <kind> <count> <planes> <seed> [p] [M]` (nonic local algebras at p), `recheck66.py <log> <planes> <B>`, `sweep5.py <E5,U3,Q,Q-style kind> <count> <planes> <seed> <p> [M]` (degree-10 algebras), `recheck5.py`, `prod66.py "<g1>;<g2>" <p> <planes> <seed> <B> <wmax>` (factor-adapted coordinates; use for products), `edit66.py` (edit and archive script; reads `sec0aq.md`). Runs and timings: summary Section 7.')
H = H[:j] + ws + H[j:]
H = re.sub(r'\*\*After session 65 the summary is about \d+k characters\*\* and this file about \d+k\.',
           '**After session 66 the summary is about %dk characters** and this file about %dk.' % (round(len(S) / 1000), round(len(H) / 1000) + 1), H)
assert 'After session 66 the summary' in H
H = rep(H, '4. **Frozen archives:** don\'t update', '4. **Frozen archives:** don\'t update `claude/Sessions 65-66 results (frozen).md`,')

open('summary66.md', 'w').write(S); open('archive6566.md', 'w').write(arch); open('start66.md', 'w').write(H)
print('summary', n0S, '->', len(S), ' start', n0H, '->', len(H), ' archive', len(arch))
print(re.findall(r'^## [^\n]*', S, re.M))
