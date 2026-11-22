# edit64.py -- session 64 checklist: archive Sections 0an (session 63) and 0ao (session 64) into
# claude/Sessions 63-64 results (frozen).md, update the condensed summary and Start here.md.
# Reads the /mnt/project mirror and sec0ao.md; writes summary64.md, archive6364.md, start64.md.
import re
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
ao = open('sec0ao.md').read().rstrip('\n') + '\n'
n0S, n0H = len(S), len(H)
def rep(txt, old, new, cnt=1):
    assert txt.count(old) == cnt, (old[:80], txt.count(old)); return txt.replace(old, new)

# ---------------- archive ----------------
i0 = S.index('## 0an.'); i1 = S.index('## 1. The goal')
an = S[i0:i1].rstrip('\n') + '\n'
arch = ('# Sessions 63–64: full results (frozen archive)\n\nFrozen on Nov 20, 2026 (end of session 64). This file holds Section 0an (session 63) exactly as it stood in the condensed summary after session 63, and Section 0ao (session 64) as written in session 64. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S63.1 … S64.6. Labels S63.1 … S64.6 point here.\n\n'
        + an + '\n' + ao)
S = S[:i0] + S[i1:]

# ---------------- header, archive list, Section 0 ----------------
S = rep(S, '(through session 63, Nov 20;', '(through session 64, Nov 20;')
S = rep(S, 'Fifteen frozen archives hold', 'Sixteen frozen archives hold')
b6162 = '- `claude/Sessions 61-62 results (frozen).md` (this project): the full Sections 0al and 0am for sessions 61–62 (labels S61.1 … S62.4), moved out of this file at the end of session 62.\n'
S = rep(S, b6162, b6162 + '- `claude/Sessions 63-64 results (frozen).md` (this project): the full Sections 0an and 0ao for sessions 63–64 (labels S63.1 … S64.6), moved out of this file at the end of session 64.\n')
S = rep(S, 'Sessions from 63 on exist only in this file (Section 0an for session 63, 0ao for session 64, and so on).', 'Sessions from 65 on exist only in this file (Section 0ap for session 65, 0aq for session 66, and so on).')
S = rep(S, '## 0. Sessions 25–63 in brief (full text in the frozen archives; session 63 in Section 0an below)', '## 0. Sessions 25–64 in brief (full text in the frozen archives)')
S = rep(S, '- S63 (Section 0an):', '- S63 (archive 63–64):')
i = S.index('- S63 (archive 63–64):'); j = S.index('\n', i)
line64 = ('\n- S64 (archive 63–64): **local solubility of V_K, uniformly in K** (test of the Hasse-principle route; one obstructed local algebra would kill it for a positive-density set of fields). '
          '**Involution lemma** (S64.1): m(K_v) ≥ 2 disjoint Frobenius-stable ± pairs give an explicit smooth point (all real places; 26 of 30 unramified types). '
          '**Theorem (S64.2): V_K has a smooth ℚ_p-point at every prime p unramified in K, for every K**: Chevalley–Warning (3 + 5 < 9) gives #V(F_p) ≡ 1 mod p, and #Sing(F_p) = 0, 1, 3, 2 for the types (9), (7,2), (7,1,1), (5,3,1) (p ≥ 11; 0, 2, 10, 5 at p = 7); '
          '(7,2) by a tangent-cone lemma at its single pairing point (S64.3) plus Chevalley–Warning on a 7-variable cubic; p = 2, 3, 5, 7 by Hensel certificates; plane sections confirm all p ≤ 10⁵. '
          'Ramified factors: Kummer points for exponents ∉ {1, 3, 5}, graded Fermat-cubic points for tame e = 3 factors with total residue degree ≥ 3 (S64.4). '
          'Random p-adic search fails on ramified algebras even where points exist (S64.5; L5 × L3 × ℚ_p: residues forced to pairing configurations for p = 11, 13, 17, 19, 23, 31, points by S64.3(b)). '
          'No local obstruction anywhere; the scope (i) gap is the global step.')
S = S[:j] + line64 + S[j:]

# ---------------- Section 3 rows ----------------
i = S.index('| S63.6: for scope (i) the r = 9'); j = S.index('\n', i)
rows = '''
| S64.1: involution lemma: if K_v has m ≥ 2 disjoint stable ± pairs (two swapped isomorphic factors or factors with an index-2 subfield), u = anti-invariant element on them, 0 elsewhere, is a smooth point of V_K; covers every real place and 26 of the 30 unramified types; the types with m ≤ 1 are (9), (7,2), (7,1,1), (5,3,1) | *unchecked* (short proof) + enumeration (`sing64.py`) |
| S64.2: for every nonic field K and every prime p unramified in K, V_K has a smooth ℚ_p-point (Chevalley–Warning: #V(F_p) ≡ 1 mod p; #Sing(F_p) = 0, 1, 3, 2 for (9), (7,2), (7,1,1), (5,3,1), p ≥ 11, and 0, 2, 10, 5 at p = 7; (7,2) for p ≥ 11 via S64.3(a) and Chevalley–Warning on the 7-variable cubic of U7; p ≤ 7 by Hensel certificates) | *unchecked* (write-up) + [exact mod p] (`sing64.py`) + Hensel (`hens64.py`) + [numerical] (`plane64.py`: all four types, every prime 7 ≤ p ≤ 10⁵) |
| S64.3: tangent-cone lemma: (a) K_v = (pair) × A, deg A = 7, and a smooth ℚ_v-zero w0 of Tr_A(w³) − (Tr_A w)³ with w0² non-scalar give smooth ℚ_v-points of V_K; (b) K_v = ℚ_v × A′, deg A′ = 8, and a smooth ℚ_v-point of {Tr w′ = Tr w′³ = 0} with w′² non-scalar likewise (the ℚ_v factor pairs with ζ) | *unchecked* (p-adic implicit function theorem) |
| S64.4: (a) a factor L = M(π), π^e ∈ M, [L : M] = e ∉ {1, 3, 5} gives the point (π, 0, …, 0) (smooth for e ≥ 4, or e = 2 with [M : ℚ_v] ≥ 2); (b) tame e = 3 factors with Σ f_j ≥ 3 give graded points (a_j π_j) with Σ Tr(ζ_j a_j³) = 0 (Fermat cubic over F_p) | *unchecked* (short) |
| S64.5: random p-adic search finds certificates for some ramified algebras (L3 × U5 × ℚ_11, (3,2) × U3 at 13, two ramified cubics × U2 × ℚ_13) but none in 60000 samples for the (3,3) fields at 11, 13, three ramified cubics at 13, L5 × L3 × ℚ_11, all of which have points (S64.4b, S64.3b); for L5 × L3 × ℚ_p the residues are forced onto the pairing configurations (0,0,1,−1), (1,−1,−1,−1) for p = 11, 13, 17, 19, 23, 31 | [numerical] (`hensram64.py`) + [exact mod p] (`resid64.py`) + *unchecked* (valuation lemma) |
| S64.6: no local obstruction for V_K found; local solubility reduces for each K to its ramified primes outside S64.1–S64.4 (odd distinct unramified factors and tame e ∈ {3, 5} factors with F₃ ≤ 2 and no pair; wild algebras at 2, 3, 5, 7); the scope (i) gap is the global step (Hasse principle for V_K or a construction) | decision |'''
S = S[:j] + rows + S[j:]
S = rep(S, 'and V_K is everywhere locally soluble for the test field (S63.5) | **open** |',
        'and V_K is everywhere locally soluble for the test field (S63.5); for every K, V_K has smooth points at all real places and unramified primes (S64.2) | **open** |')

# ---------------- Section 4 ----------------
S = rep(S, 'V_K is everywhere locally soluble for both test fields (S63.5). Singular along the pairing curves.',
        'V_K is everywhere locally soluble for both test fields (S63.5). **For every K, V_K has smooth points at every real place and every unramified prime (S64.1, S64.2), and at most ramified local algebras (S64.3, S64.4);** local solubility is a finite check per K. Singular along the pairing curves.')

# ---------------- Section 5 ----------------
S = rep(S, '- **Session 63:** S63.1–S63.6 (Section 0an).',
        '- **Session 64:** S64.1–S64.6 (archive 63–64). Local solubility of V_K uniformly in K: every real place and every unramified prime for every K (involution lemma, Chevalley–Warning with exact singular counts, a tangent-cone lemma, Hensel certificates at p ≤ 7); ramified algebras by Kummer and graded-cubic constructions; no obstruction found.\n- **Session 63:** S63.1–S63.6 (archive 63–64).')
lesson = ('- **Method lesson (S64):** (1) **Chevalley–Warning plus an exact count of the singular F_p-points**: for a complete intersection with Σ deg < n, #V(F_p) ≡ 1 mod p, so smooth points exist as soon as #Sing(F_p) ≢ 1 mod p; the singular points are the symmetric (pairing) configurations, and counting them by Frobenius type is a finite combinatorial problem. '
          '(2) **When exactly one singular point blocks the count, expand at it**: the tangent cone at a pairing point is a lower-degree variety on the complementary algebra (here a cubic in 7 or 8 variables), whose smooth points give smooth points nearby by the p-adic implicit function theorem. '
          '(3) **Random p-adic search is unreliable for ramified algebras**: near the natural points (Kummer or graded elements) all 2 × 2 minors have high valuation; construct points instead, and use residue systems (valuation of the leading terms) for necessary conditions before suspecting an obstruction.\n')
S = rep(S, '- **Method lesson (S63):**', lesson + '- **Method lesson (S63):**')

# ---------------- Section 6 ----------------
dec = ('**Session 64 decision (local solubility of V_K is uniform; the gap is global).** S64.1–S64.2: every real place and every unramified prime, for every K. S64.3–S64.5: most ramified local algebras by construction; random search is not evidence there. **Order now:** (1) rational nonics and decics (the near-term target): the global step for V_K / W_K: Hasse principle or a construction (Brauer group of a desingularisation of the twisted V̄, which is singular exactly along the pairing locus; fibration or descent mechanisms; conics on V_K through a point; a variant of the odd-Tschirnhaus chain whose last step is linear); finish the local classification (the shapes left in S64.6 for p ≥ 11, wild algebras at 2, 3, 5, 7); W_K: the unramified count for S_10 types and a totally real primitive decic test field; (2) over P (r = 9): the S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic.\n\n')
S = rep(S, '**Session 63 decision (row B5 over ℚ: a Fano target for the rational degree bound).**', dec + '**Session 63 decision (row B5 over ℚ: a Fano target for the rational degree bound).**')
S = rep(S, '- Session 63: the extremal configurations of I', '- Session 64: random p-adic search as evidence of local insolubility for ramified algebras (it misses points near Kummer and graded elements, S64.5); Lang–Weil / plane-section sweeps for unramified primes (Chevalley–Warning settles them, S64.2).\n- Session 63: the extremal configurations of I')
S = rep(S, 'items decided in sessions 41–63)', 'items decided in sessions 41–64)')

# ---------------- Section 7 ----------------
s7 = ('Session 64 (one directory; cypari, sympy, numpy; `ffalg.py` is imported by the others, keep them together):\n'
      '- `ffalg.py` (module): unramified or arbitrary étale algebras ∏ Z[x]/(g_j) mod M (p or p^N), multiplication, traces by Newton power sums, F3, F5 and their gradients; `irred_mod_p`.\n'
      '- `sing64.py <p list>` (seconds): the 30 Frobenius types of degree 9 with pair numbers m; for the m ≤ 1 types (9), (7,2), (7,1,1), (5,3,1), exact counts of Sing(F_p) in the constant-orbit family, and the singular points of the 7-variable cubic of U7 (run `7 11 13 17`).\n'
      '- `plane64.py <type> <pmin> <pmax> [seed] [maxplanes]` (about 150 primes per second): smooth F_p-points of V for the unramified type by random plane sections (exact multinomial restriction, PARI resultant, gradient rank). Runs `9`, `7,2`, `7,1,1`, `5,3,1` with `7 100000` (in the background): no failures, at most 12 planes.\n'
      '- `hens64.py <type> <p> [samples] [N] [seed]` (seconds to a minute): Hensel certificate (minor of valuation m, v(F3), v(F5) ≥ 2m + 1) for an unramified type at small p (runs: the four m ≤ 1 types at p = 2, 3, 5, 7 with `30000 12 1`).\n'
      '- `hensram64.py <p> "<g1>;<g2>;…" [samples] [N] [seed]` (about a minute per 60000 samples): the same for an arbitrary étale algebra given by monic integer polynomials (power basis). Unreliable for ramified algebras (S64.5); `ramcases.sh` holds the seven test algebras.\n'
      '- `resid64.py <e-list> <pmax>` (seconds): residue system for totally ramified factors of degrees e_j (plus ζ), primes without a nonzero solution (run `5,3,1 200`: none); the inline variant in S64.5 lists the solutions with smoothness.\n'
      '- `edit64.py` (this edit and archive script; reads `sec0ao.md`).\n\n')
S = rep(S, '## 8. Ground rules (revised Nov 17)', s7 + '## 8. Ground rules (revised Nov 17)')

# ---------------- Section 8 ----------------
S = rep(S, 'Add a Section 0ao (session 64; then 0ap, …) here', 'Add a Section 0ap (session 65; then 0aq, …) here')
S = rep(S, '**At the end of session 64, move Sections 0an and 0ao into a new frozen archive `claude/Sessions 63-64 results (frozen).md`.**', '**At the end of session 66, move Sections 0ap and 0aq into a new frozen archive `claude/Sessions 65-66 results (frozen).md`.**')
S = rep(S, '`Sessions 61-62 results (frozen).md`), and don', '`Sessions 61-62 results (frozen).md`, `Sessions 63-64 results (frozen).md`), and don')

# ---------------- Start here ----------------
H = rep(H, 'Updated Nov 20, 2026 (after session 63;', 'Updated Nov 20, 2026 (after session 64;')
H = rep(H, 'next session is 64, Section 0ao; session 64 archives Sections 0an and 0ao into `claude/Sessions 63-64 results (frozen).md`)', 'next session is 65, Section 0ap; session 66 archives Sections 0ap and 0aq into `claude/Sessions 65-66 results (frozen).md`)')
H = rep(H, 'sessions 61–62 (S61.1 … S62.4) in `claude/Sessions 61-62 results (frozen).md`.', 'sessions 61–62 (S61.1 … S62.4) in `claude/Sessions 61-62 results (frozen).md`; sessions 63–64 (S63.1 … S64.6) in `claude/Sessions 63-64 results (frozen).md`.')
H = rep(H, 'session 64 is Section 0ao; session 64 also moves 0an and 0ao to a 63–64 archive', 'session 65 is Section 0ap, session 66 Section 0aq; session 66 also moves 0ap and 0aq to a 65–66 archive')
H = rep(H, '`claude/Sessions 59-60 results (frozen).md` or `claude/Sessions 61-62 results (frozen).md`', '`claude/Sessions 59-60 results (frozen).md`, `claude/Sessions 61-62 results (frozen).md` or `claude/Sessions 63-64 results (frozen).md`')
H = rep(H, 'At the end of session 64, move Sections 0an and 0ao (sessions 63–64) into a new frozen archive `claude/Sessions 63-64 results (frozen).md` the same way (session 62 did this for sessions 61–62 with `edit62.py`)',
        'At the end of session 66, move Sections 0ap and 0aq (sessions 65–66) into a new frozen archive `claude/Sessions 65-66 results (frozen).md` the same way (session 64 did this for sessions 63–64 with `edit64.py`; session 62 did this for sessions 61–62 with `edit62.py`)')
H = rep(H, '`claude/Sessions 61-62 results (frozen).md` (S61.1 … S62.4).', '`claude/Sessions 61-62 results (frozen).md` (S61.1 … S62.4), `claude/Sessions 63-64 results (frozen).md` (S63.1 … S64.6).')
H = rep(H, 'one line per session 25–62 (Section 0), the full results of sessions from 63 on (Section 0an onward)', 'one line per session 25–64 (Section 0), the full results of sessions from 65 on (Section 0ap onward)')
H = rep(H, '## Next step (priority order, after session 63)', '## Next step (priority order, after session 64)')
i = H.index('**Session 63** (row B5 over ℚ; full text in the summary, Section 0an)'); j = H.index('\n', i)
p64 = ('**Session 64** (local solubility of V_K uniformly in K; full text in `claude/Sessions 63-64 results (frozen).md`, Section 0ao). **Mechanism tested:** the Hasse principle for V_K, local half, uniformly in K (one obstructed local algebra would kill the route for a positive-density set of fields). '
       '**Results:** (S64.1) involution lemma: m ≥ 2 stable ± pairs give an explicit smooth point (every real place, 26 of 30 unramified types); (S64.2, `sing64.py`, `hens64.py`, `plane64.py`) **for every nonic K, V_K has a smooth ℚ_p-point at every unramified p**: Chevalley–Warning (#V(F_p) ≡ 1 mod p) with #Sing(F_p) = 0, 1, 3, 2 for (9), (7,2), (7,1,1), (5,3,1), the tangent-cone lemma for (7,2), Hensel certificates at p ≤ 7, plane sections for all p ≤ 10⁵; '
       '(S64.3) tangent-cone lemma at a pairing point (reduces to a cubic on the complementary algebra); (S64.4) Kummer points (exponent ∉ {1, 3, 5}) and graded Fermat-cubic points (tame e = 3, Σf ≥ 3) for ramified factors; (S64.5, `hensram64.py`, `resid64.py`) random p-adic search fails on ramified algebras that do have points; no obstruction anywhere. '
       'The scope (i) gap is now the global step. (Session 63: row B5 over ℚ, V_K Fano of index 1, ELS for the test fields; same archive, Section 0an.)')
H = H[:i] + p64 + H[j:]
H = rep(H, '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** ',
        '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 64: local solubility of V_K is uniform** (every real place and every unramified prime for every K, S64.1–S64.2; most ramified algebras by Kummer / graded / tangent-cone constructions, S64.3–S64.4; random p-adic search is not evidence for ramified algebras, S64.5). **Next for scope (i): the global step** (Brauer group of a desingularisation of the twisted V̄, singular exactly along the pairing locus; fibration or descent; conics through a point; a linear last step), then the remaining local shapes (S64.6: odd distinct unramified factors with tame e ∈ {3, 5} factors, F₃ ≤ 2, no pair; wild algebras at 2, 3, 5, 7) and the W_K count for S_10 types. ')
H = rep(H, '**S63 before fighting', '**S64 Chevalley–Warning plus an exact count of singular F_p-points (smooth points exist when #Sing ≢ 1 mod p); expand at a lone singular point (tangent cone on the complementary algebra); don\'t trust random p-adic search on ramified algebras**, **S63 before fighting')
H = rep(H, 'Session 63 added: the extremal', 'Session 64 added: random p-adic search as evidence of local insolubility for ramified algebras; Lang–Weil or plane-section sweeps for unramified primes (Chevalley–Warning settles them). Session 63 added: the extremal')
H = rep(H, 'the rational degree bound is now conditional only on producing such ℚ-points (Hasse principle, conjectural, or a construction).',
        'the rational degree bound is now conditional only on producing such ℚ-points (Hasse principle, conjectural, or a construction). **Session 64:** the local half is uniform: V_K has smooth points at every real place and every unramified prime for every K, and at most ramified local algebras by explicit constructions; no local obstruction found.')
i = H.index('- Session 63 (one directory; sympy, numpy, scipy, cypari)'); j = H.index('\n', i)
ws = ('\n- Session 64 (one directory; cypari, sympy, numpy; `ffalg.py` is the shared module): `sing64.py 7 11 13 17` (types, pair numbers, exact singular counts; seconds), `plane64.py <type> 7 100000 <seed> 40` (smooth F_p-points by plane sections, about 150 primes per second; run the four types in the background, two at a time), '
      '`hens64.py <type> <p> 30000 12 1` (Hensel certificates for unramified types at p ≤ 7), `hensram64.py <p> "<g1>;…" 60000 16 1` (arbitrary étale algebras; unreliable for ramified ones), `resid64.py 5,3,1 200` (residue systems), `edit64.py` (edit and archive script; reads `sec0ao.md`).')
H = H[:j] + ws + H[j:]

open('summary64.md', 'w').write(S); open('archive6364.md', 'w').write(arch)
H = rep(H, '**After session 62 the summary is about 180k characters** and this file about 90k.', '**After session 64 the summary is about %dk characters** and this file about %dk.' % (round(len(S) / 1000), round(len(H) / 1000) + 0))
open('start64.md', 'w').write(H)
print('summary', n0S, '->', len(S), ' start', n0H, '->', len(H), ' archive', len(arch))
print(re.findall(r'^## [^\n]*', S, re.M))
print(re.findall(r'^## [^\n]*', arch, re.M))
