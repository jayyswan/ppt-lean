# S58 end-of-session edit: summary, archive 57-58, Start here. Reads s58_sum_old.md, s58_start_old.md, sec0ai_final.md
import re
def rep(s, old, new, cnt=1):
    assert s.count(old) == cnt, ("count", s.count(old), old[:100])
    return s.replace(old, new)
V = dict(l.split('=', 1) for l in open('vals.txt').read().strip().split('\n'))
s = open('s58_sum_old.md').read()
sec = open('sec0ai_final.md').read().rstrip() + "\n"
# --- archive 57-58
a = s.index('## 0ah.'); b = s.index('## 1. The goal')
sec0ah = s[a:b].rstrip() + "\n\n"
arch = ("# Sessions 57–58: full results (frozen archive)\n\nFrozen on Nov 20, 2026 (end of session 58). This file holds Section 0ah (session 57) exactly as it stood in the condensed summary after session 57 (including Arya's Nov 20 answer on nodal eggs), and Section 0ai (session 58) as written in session 58. **Don't write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S57.1 … S58.5. Labels S57.1 … S58.6 point here. (S58.2 supersedes the lower bound of S57.2: N = " + V['N'] + " solutions, " + V['NC'] + " orbits of the Klein group of S58.1.)\n\n" + sec0ah + sec)
open('arch5758.md', 'w').write(arch)
s = s[:a] + s[b:]
# --- header, archive list
s = rep(s, '(through session 57, Nov 20;', '(through session 58, Nov 20;')
s = rep(s, 'Twelve frozen archives hold older detail', 'Thirteen frozen archives hold older detail')
s = rep(s, "moved out of this file at the end of session 56.\n",
        "moved out of this file at the end of session 56.\n- `claude/Sessions 57-58 results (frozen).md` (this project): the full Sections 0ah and 0ai for sessions 57–58 (labels S57.1 … S58.6), moved out of this file at the end of session 58.\n")
s = rep(s, 'Sessions from 57 on exist only in this file (Section 0ah for session 57, 0ai for session 58, and so on).',
        'Sessions from 59 on exist only in this file (Section 0aj for session 59, 0ak for session 60, and so on).')
s = rep(s, '## 0. Sessions 25–57 in brief (full text in the frozen archives; session 57 in Section 0ah below)',
        '## 0. Sessions 25–58 in brief (full text in the frozen archives)')
s = rep(s, '- S57 (Section 0ah):', '- S57 (archive 57–58):')
i = s.index('- S57 (archive 57–58):'); j = s.index('\n', i) + 1
s = s[:j] + ('- S58 (archive 57–58): **row M2, full count and monodromy for a fixed generator.** A second symmetry, the egg\'s horizontal reflection ι: (R, Z, e) ↦ (1 − R, Z/(1 + e), −e/(1 + e)), generates with θ ↦ −θ a Klein group V acting freely (S58.1); monodromy solving gives N = ' + V['N'] + ' solutions, ' + V['NC'] + ' V-orbits (S58.2); ' + V['SHORTMONO'] + ' (S58.3), so no intermediate cover beyond two quadratic steps; M2 is a 7-parameter family of nonics, dominant over C, and the open choice is the generator y (S58.4); the genus of Σ by Gröbner bases failed a second time (S58.5).\n') + s[j:]
s = s.replace('(Section 0ah)', '(archive 57–58)')
# --- Section 1a row M2
s = rep(s, "**Measured in session 57 (S57.1–S57.3).**", "**Measured in session 57 (S57.1–S57.3); full count and monodromy in session 58: N = " + V['N'] + ", Klein symmetry, " + V['SHORTMONO'] + " (S58.1–S58.3).**")
# --- Section 3 rows
k = s.index('| S57.3: real M2 solutions'); k2 = s.index('\n', k) + 1
s = s[:k2] + (
 '| S58.1: ι: (R, Z, e) ↦ (1 − R, Z/(1 + e), −e/(1 + e)) (horizontal reflection of the egg) preserves the M2 condition and allowed eggs; with Z ↦ −Z a Klein group V acting freely on X_τ | [exact] (short algebra); [numerical] check (`m2mono.py`) |\n'
 '| S58.2: the M2 fixed-generator scheme X_τ has degree N = ' + V['N'] + ' (' + V['NC'] + ' V-orbits); supersedes the lower bound of S57.2 | [numerical] (`m2mono.py`, monodromy solving, saturated) |\n'
 '| S58.3: ' + V['ROW3'] + ' | [numerical] (`m2blocks.py`) |\n'
 '| S58.4: the M2 incidence W_K is a degree-N cover of the affine 9-space K; M2 is a 7-parameter nonic family over a P-rational base, dominant over C | *unchecked* (dimension count) |\n'
 '| S58.5: genus of Σ: `red56.py 1 ramw` (determinant of degree 74) did not finish in 24 minutes (second attempt) | — |\n') + s[k2:]
s = rep(s, "but its fixed-generator scheme has ≥ 181 points (S57.2)**",
        "but its fixed-generator scheme has " + V['N'] + " points, " + V['NC'] + " up to a Klein symmetry, " + V['SHORTMONO'] + " (S58.1–S58.3)**")
s = rep(s, "≥ 181 solutions modulo θ ↦ −θ (S57.2); real r = 7 solutions with genuine eggs exist (S57.3). A P-point needs a mechanism (two-stage form: a square condition for θ, then linear algebra).",
        "N = " + V['N'] + " solutions, " + V['NC'] + " orbits of a Klein group V (S58.1, S58.2; S57.2 had ≥ 181 pairs); " + V['SHORTMONO'] + " (S58.3); real r = 7 solutions with genuine eggs exist (S57.3). A P-point needs a mechanism that chooses the generator y (S58.4): a y ∈ K where the fibre splits.")
# --- Section 5
s = rep(s, '- **Session 57:** S57.1–S57.4 (archive 57–58).', '- **Session 58:** S58.1–S58.6 (archive 57–58). Row M2: Klein symmetry, N = ' + V['N'] + ', ' + V['SHORTMONO'] + '; genus of Σ not reached.\n- **Session 57:** S57.1–S57.4 (archive 57–58).')
s = rep(s, '- **Method lesson (S57):**',
 '- **Method lesson (S58):** (1) **Before counting, list the symmetries of the curve family** (here the egg\'s reflection x ↦ 1 − x, which had been missed): they give free group actions on every fibre and hence blocks; quotienting by them first shows what the count really is. (2) **Monodromy solving beats random starts by an order of magnitude** (S57: 181 pairs from 12,000 starts; S58: ' + V['N'] + ' solutions from about 25 loops); seed it by choosing the parameters as roots of a random member. (3) Path jumps show up as non-injective loops and as violations of known blocks; use both as filters, and keep steps ≤ 0.02. (4) Union–find minimal blocks from partial permutations are lower bounds, so they can prove primitivity but not imprimitivity.\n- **Method lesson (S57):**')
# --- Section 6
s = rep(s, 'items decided in sessions 41–57)', 'items decided in sessions 41–58)')
s = rep(s, '\n**Session 57 decision (row M2 measured).**',
 '\n**Session 58 decision (M2 count and monodromy).** S58.1: Klein symmetry V (θ ↦ −θ and the egg\'s reflection); S58.2: N = ' + V['N'] + ' (' + V['NC'] + ' V-orbits); S58.3: ' + V['SHORTMONO'] + '; S58.5: the genus of Σ by Gröbner bases failed again. **Order now:** (1) r = 7 (S_9): a mechanism that chooses the generator y for M2 (a y ∈ K whose fibre splits: tangency or P-rational crossings imposed by construction, the branch locus of W_K → K), or Z_G / R5 for r = 7; (2) A_9 r = 5: the S54 candidates (Γ_H, the span fibration), named first; the genus of Σ only numerically (branch points of Σ → ℓ1 by tracking the 65 sheets); (3) row E; (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic; (6) parked leads as before.\n'
 + '\n**Session 57 decision (row M2 measured).**')
s = rep(s, '- Session 57: M2 for a fixed generator as a finite step',
 '- Session 58: intermediate covers of the M2 fixed-generator scheme (only the Klein group V, two quadratic steps); the genus of Σ by Singular on the reduced model (`red56.py ramw`, two attempts, > 15 and > 24 minutes).\n- Session 57: M2 for a fixed generator as a finite step')
# --- Section 7
s = rep(s, '\n## 8. Ground rules (revised Nov 17)',
 'Session 58 (one directory; numpy; the pickles are large, a few MB):\n'
 '- `m2mono.py <seed> <loops> [out.pkl] [resume.pkl]` (monodromy solving for the M2 fixed-generator scheme: seeds a solution by taking τ as 9 of the 12 roots of a random member, then triangle loops in the space of the nine roots; RK4 predictor, Newton corrector, step ≤ `HMAX` from the environment (use `HMAX=0.02`); colliding endpoints are dropped; pickles (τ0, solutions, partial permutations) after every loop). Loose runs `1 80` (to 1890), resumed (to 2496), then `HMAX=0.02 … 1 40 m2mono_1c.pkl r2.pkl` and `HMAX=0.02 … 2 40 m2mono_2c.pkl r3.pkl` in parallel (about 230 seconds per loop at 2500 solutions; resume with a different seed, or the loops repeat). Resuming discards the old loops.\n'
 '- `m2blocks.py <pkl> [<pkl> …]` (merges runs from the same base by coordinates; Klein classes under Z ↦ −Z and ι, class-level maps by unanimous vote, orbit of 0, minimal blocks containing {0, i} for every class i by union–find; about a minute per few loops).\n'
 '\n## 8. Ground rules (revised Nov 17)')
s = rep(s, 'Add a Section 0ai (session 58; then 0aj, …) here', 'Add a Section 0aj (session 59; then 0ak, …) here')
s = rep(s, '**At the end of session 58, move Sections 0ah and 0ai into a new frozen archive `claude/Sessions 57-58 results (frozen).md`.**', '**At the end of session 60, move Sections 0aj and 0ak into a new frozen archive `claude/Sessions 59-60 results (frozen).md`.**')
s = rep(s, '`Sessions 55-56 results (frozen).md`), and don', '`Sessions 55-56 results (frozen).md`, `Sessions 57-58 results (frozen).md`), and don')
open('s58_sum_new.md', 'w').write(s)

# ---------------- Start here
t = open('s58_start_old.md').read()
t = rep(t, 'Updated Nov 20, 2026 (after session 57;', 'Updated Nov 20, 2026 (after session 58;')
t = rep(t, 'next session is 58).', 'next session is 59).')
t = rep(t, 'session 57 (S57.1 … S57.4) only in the summary, Section 0ah.', 'sessions 57–58 (S57.1 … S58.6) in `claude/Sessions 57-58 results (frozen).md`.')
t = rep(t, 'session 57 is Section 0ah, session 58 Section 0ai; session 58 also moves 0ah and 0ai to the 57–58 archive)', 'session 59 is Section 0aj, session 60 Section 0ak; session 60 also moves 0aj and 0ak to a 59–60 archive)')
t = rep(t, '`claude/Sessions 53-54 results (frozen).md` or `claude/Sessions 55-56 results (frozen).md`.', '`claude/Sessions 53-54 results (frozen).md`, `claude/Sessions 55-56 results (frozen).md` or `claude/Sessions 57-58 results (frozen).md`.')
t = rep(t, 'At the end of session 58, move Sections 0ah and 0ai (sessions 57–58) into a new frozen archive `claude/Sessions 57-58 results (frozen).md` the same way, leaving their one-line entries in Section 0, and add that file to the frozen lists here and in the summary (session 56 did this',
        'At the end of session 60, move Sections 0aj and 0ak (sessions 59–60) into a new frozen archive `claude/Sessions 59-60 results (frozen).md` the same way, leaving their one-line entries in Section 0, and add that file to the frozen lists here and in the summary (session 58 did this for sessions 57–58 with `edit58.py`; session 56 did this')
t = rep(t, 'one line per session 25–56 (Section 0), the full results of sessions from 57 on (Section 0ah onward)', 'one line per session 25–58 (Section 0), the full results of sessions from 59 on (Section 0aj onward)')
t = rep(t, '`claude/Sessions 55-56 results (frozen).md` (S55.1 … S56.4).\n', '`claude/Sessions 55-56 results (frozen).md` (S55.1 … S56.4), `claude/Sessions 57-58 results (frozen).md` (S57.1 … S58.6).\n')
t = rep(t, '## Next step (priority order, after session 57)', '## Next step (priority order, after session 58)')
t = rep(t, '**Sessions 25–57 in one line each:**', '**Sessions 25–58 in one line each:**')
a = t.index('**Session 57** (row M2'); b = t.index('\n', a)
t = t[:a] + ('**Session 58** (row M2: full count and monodromy for a fixed generator; full text in `claude/Sessions 57-58 results (frozen).md`, Section 0ai). **Mechanism tested:** an intermediate cover of the M2 scheme X_τ (a block system with a small or 2-power quotient). **Results:** (S58.1) a second symmetry, the egg\'s horizontal reflection ι: (R, Z, e) ↦ (1 − R, Z/(1 + e), −e/(1 + e)), which keeps eggs allowed; with θ ↦ −θ a Klein group V acting freely; (S58.2, `m2mono.py`, monodromy solving) **N = ' + V['N'] + ', so ' + V['NC'] + ' V-orbits** (S57.2\'s 181 pairs were a small part); (S58.3, `m2blocks.py`) **' + V['SHORTMONO'] + '**: no intermediate cover beyond two quadratic steps; (S58.4) M2 is a 7-parameter nonic family over a P-rational base, dominant over C, so the open choice is the generator y (a y ∈ K whose fibre X_y splits); (S58.5) genus of Σ: `red56.py 1 ramw` did not finish in 24 minutes (second attempt). (Session 57: M2 measured with Arya\'s egg; nodal eggs not allowed, so M2 serves r = 7 only.)') + t[b:]
t = rep(t, '**Session 57: row M2 measured (egg from Arya): real r = 7 solutions with genuine eggs exist, but ≥ 181 solutions per generator; next a P-mechanism for it (two-stage form: θ ∈ K with 1/(1 + θ²) ∈ W4, a square condition, then linear algebra), and its exact count/monodromy as a background run (`m2ms.py`); nodal eggs are not allowed (Arya, Nov 20), so M2 is for r = 7 only.',
        '**Session 58: M2 for a fixed generator has N = ' + V['N'] + ' solutions (' + V['NC'] + ' up to a Klein symmetry) and ' + V['SHORTMONO'] + ' (S58.1–S58.3); next a mechanism that chooses the generator y (S58.4: a y ∈ K whose fibre splits, e.g. tangency or P-rational crossings imposed by construction, or the branch locus of W_K → K), or Z_G / R5 for r = 7. Session 57: real r = 7 solutions with genuine eggs exist; nodal eggs are not allowed (Arya, Nov 20), so M2 is for r = 7 only.')
t = rep(t, '(S56.2 unfinished: start `red56.py 1 ramw` in the background at the beginning of a session; only a small genus would make a map of degree ≤ 8 plausible)',
        '(S56.2, S58.5: `red56.py 1 ramw` did not finish in 15 or 24 minutes; Gröbner bases are out; if the genus is wanted, count branch points of Σ → ℓ1 numerically by tracking the 65 sheets; only a small genus would make a map of degree ≤ 8 plausible)')
t = rep(t, 'S57 turn crossings into a divisibility', 'S58 list the symmetries of a curve family before counting, and count by monodromy solving, not random starts**, **S57 turn crossings into a divisibility')
t = rep(t, 'Session 57 added: M2 for a fixed generator as a finite step (≥ 181).', 'Session 58 added: intermediate covers of the M2 fixed-generator scheme (only the Klein group, two quadratic steps); the genus of Σ by Singular (`red56.py ramw`, twice). Session 57 added: M2 for a fixed generator as a finite step (≥ 181).')
t = rep(t, '**Session 57:** row M2 (Bézier × egg) has real r = 7 solutions with genuine eggs, the first toolkit row besides fact 7 and row G shown to reach S_9 r = 7 on the real side, but ≥ 181 solutions per generator.',
        '**Session 57:** row M2 (Bézier × egg) has real r = 7 solutions with genuine eggs, the first toolkit row besides fact 7 and row G shown to reach S_9 r = 7 on the real side, but ≥ 181 solutions per generator. **Session 58:** exactly what the M2 scheme is for a fixed generator: N = ' + V['N'] + ', a Klein symmetry, ' + V['SHORTMONO'] + '; the open choice is the generator.')
t = rep(t, '\n- Sympy is too slow for the Weierstrass resolvent,',
 '\n- Session 58 (one directory; numpy): `m2mono.py <seed> <loops> [out.pkl] [resume.pkl]` (monodromy solving for M2, `HMAX=0.02` in the environment; about 230 seconds per loop at 2500 solutions; resume a run with another seed or the loops repeat; two processes in parallel), `m2blocks.py <pkl> …` (Klein classes, orbit, minimal blocks; merges runs by coordinates).'
 + '\n- Sympy is too slow for the Weierstrass resolvent,')
open('s58_start_new.md', 'w').write(t)
for f in ('s58_sum_new.md', 's58_start_new.md', 'arch5758.md'):
    x = open(f).read(); print(f, len(x), re.findall(r'^## 0a[a-z]\.[^\n]*', x, re.M), x.count('<<'))
