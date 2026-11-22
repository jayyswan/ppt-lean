# edit72.py (session 72, Nov 21): adds Section 0aw, moves Sections 0av and 0aw (sessions 71-72) into a new frozen archive,
# updates Sections 0, 3-8 of the condensed summary and the session-specific parts of Start here.
# Reads the read-only mirror under /mnt/project and sec0aw.md; writes summary72.md, start72.md, archive7172.md.
import re
s = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
t = open('/mnt/project/claude_Start_here.md').read()
sec = open('sec0aw.md').read().rstrip('\n') + '\n'

def rep(x, a, b):
    assert x.count(a) == 1, (a[:80], x.count(a))
    return x.replace(a, b)

# ---------- archive ----------
i = s.index('## 0av.'); j = s.index('## 1. The goal')
sec0av = s[i:j].rstrip('\n') + '\n'
arch = ('# Sessions 71–72: full results (frozen archive)\n\n'
        'Frozen on Nov 21, 2026 (end of session 72). This file holds Section 0av (session 71) exactly as it stood in the condensed summary after session 71, '
        'and Section 0aw (session 72) as written in session 72. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, '
        'which keeps one line per session in its Section 0 and the Section 3 rows S71.1 … S72.6. Labels S71.1 … S72.6 point here. '
        '**Note (S72.1): S71.5 states the Witt index of Tr u² on K_0 as \"≥ min(s, 3)\"; session 72 proved it is exactly s for s ≤ 3, and 3 or 4 for s ∈ {4, 5} depending on a local condition.**\n\n'
        + sec0av + '\n' + sec)
open('archive7172.md', 'w').write(arch)
s = s[:i] + s[j:]

# ---------- summary: header and archive lists ----------
s = rep(s, '# Condensed summary: plan and progress (through session 71,', '# Condensed summary: plan and progress (through session 72,')
s = rep(s, 'Eighteen frozen archives hold older detail', 'Nineteen frozen archives hold older detail')
k = s.index('- `claude/Sessions 69-70 results (frozen).md` (this project)'); ke = s.index('\n', k) + 1
s = s[:ke] + '- `claude/Sessions 71-72 results (frozen).md` (this project): the full Sections 0av and 0aw for sessions 71–72 (labels S71.1 … S72.6), moved out of this file at the end of session 72.\n' + s[ke:]
s = rep(s, 'Sessions from 71 on exist only in this file (Section 0av for session 71, 0aw for session 72, and so on).',
        'Sessions from 73 on exist only in this file (Section 0ax for session 73, 0ay for session 74, and so on).')

# ---------- Section 0 ----------
s = rep(s, '## 0. Sessions 25–71 in brief (full text in the frozen archives; session 71 in Section 0av)', '## 0. Sessions 25–72 in brief (full text in the frozen archives)')
s = rep(s, '- S71 (Section 0av):', '- S71 (archive 71–72):')
k = s.index('- S71 (archive 71–72):'); ke = s.index('\n', k) + 1
line72 = ('- S72 (archive 71–72): decics over ℚ via V_3 = {Tr u = Tr u² = Tr u³ = 0}. **Witt index** of Tr u² on K_0 over ℚ is exactly s for s ≤ 3 and 3 or 4 for s ∈ {4, 5} (local condition; both dense S_10 test fields with s ≥ 4 have index 3, obstructions at 367 and 17 [exact]) (S72.1); '
          'V_3 is smooth and locally soluble at every unramified p ≥ 11 (S72.2); **Hilbert\'s 3-plane cubic surfaces S_Λ have full W(E6) line monodromy** (F_p point counts at p = 31, 37 match the W(E6) trace distribution), so Galois-stable skew sets need a thin set of Λ (S72.3); '
          'secant/tangent/quadratic-point descents are equivalent to V_3(ℚ) ≠ ∅ and Heath-Brown cannot enter through linear maps (S72.4); with P-dials the decic gap is two invariants of degrees 30 and 20 on the P-dense V_3 (S72.5).\n')
s = s[:ke] + line72 + s[ke:]

# ---------- Section 3 rows ----------
k = s.index('| S71.5:'); ke = s.index('\n', k) + 1
rows = ('| S72.1: the Witt index of Tr u² on K_0 (decic K, signature (r + s − 1, s)) over ℚ is exactly s for s ≤ 3; for s ∈ {4, 5} it is 4 iff a ternary residual form is isotropic at every prime, else 3; dense S_10 examples with (r, s) = (2, 4) and (0, 5) have index 3 (anisotropic at 367, at 17), x^10 + x³ − 2x + 1 has 4 | *unchecked* (short, complete) + [exact] (`witt72.py`) |\n'
        '| S72.2: V̄_3 is smooth (Jacobian rank < 3 iff ≤ 2 coordinate values); smooth reduction at unramified p ≥ 11; Chevalley–Warning + Hensel give V_3(ℚ_p) ≠ ∅ for every unramified p ≥ 11; bad: p = 2, 3 (degenerate model), 5 ((1 : … : 1) singular), 7 (Frobenius-stable 7-sets), ramified p | *unchecked* (short, complete) |\n'
        '| S72.3: for maximal isotropic Λ ⊂ Q the cubic surfaces S_Λ = Λ ∩ {Tr u³ = 0} have line monodromy W(E6) (F_p point counts, 2500 surfaces at p = 31 and 1500 at p = 37, match the W(E6) trace distribution, all smooth); Galois-stable skew sets of lines occur only for a thin set of Λ | [numerical] (`we6_72.py`) |\n'
        '| S72.4: V_3(ℚ) ≠ ∅ ⇔ a quadratic point x ∈ V_3 with B(x, x̄) = 0 ⇔ a ℚ-line of Q on which Tr u³ has a rational root (also via tangency); linear spaces in Q have dimension ≤ 3 and polynomial families inside Q through linear maps are isotropic spaces, so nonsingular cubic forms in ≥ 10 variables (Heath-Brown) cannot map linearly to V_3 | *unchecked* (short) |\n'
        '| S72.5: x^10 × P-affine ℚ-sextic graph: u ∈ V_3(P) is good iff J1 = N3²/N4³ and J2 = N2/N4² (degrees 30, 20; depressed sextic part of the charpoly) are rational; shears into x give degree 60; over P Artin–Schreier reduces decics to odd degrees only via index 45 | *unchecked* (short) |\n'
        '| S72.6: mechanisms (a) Hilbert 3-plane with skew-line descent, (b) secant descent, (c) linear Heath-Brown inputs ruled out for V_3; next: ℚ-linear spaces in X_A on which Tr u² is a conic, quadric surface or indefinite form in ≥ 5 variables (Hasse–Minkowski, Meyer), the families of planes and lines in V_3 | decision |\n')
s = s[:ke] + rows + s[ke:]

# ---------- Section 4 ----------
s = rep(s, 'a ℚ-point u ∉ ℚ closes the field with one crossing. No field-independent transfer from X_A(ℚ) (it fails over the ',
        'a ℚ-point u ∉ ℚ closes the field with one crossing. **S72: V_3 is smooth and locally soluble at unramified p ≥ 11 (S72.2); ℚ-linear spaces in Q have dimension min(s, 3) or 4 (S72.1); Hilbert\'s cubic surfaces S_Λ have W(E6) line monodromy (S72.3); secant/quadratic-point descents are equivalent to the problem and Heath-Brown cannot enter linearly (S72.4); with P-dials: two rational invariants of degrees 30, 20 at a P-point (S72.5).** No field-independent transfer from X_A(ℚ) (it fails over the ')

# ---------- Section 5 ----------
s = rep(s, '- **Session 71:** S71.1–S71.5 (Section 0av).',
        '- **Session 72:** S72.1–S72.6 (archive 71–72). Decics over ℚ via V_3: Witt index exactly s (s ≤ 3) or 3/4 (s ≥ 4, local condition); V_3 smooth, locally soluble at unramified p ≥ 11; Hilbert\'s cubic surfaces have full W(E6) monodromy; secant descent and linear cubic-form inputs are equivalent or inapplicable; with P-dials the gap is two invariants.\n'
        '- **Session 71:** S71.1–S71.5 (archive 71–72).')
s = rep(s, '- **Method lesson (S71):**',
        '- **Method lesson (S72):** (1) **Before building a mechanism on linear subspaces of a quadric over ℚ, compute the Witt index exactly** (iterated `qfsolve`): it is s for s ≤ 3 and depends on a local Hasse-invariant condition beyond that; dense test fields fail it. (2) **Measure the monodromy of a family of cubic surfaces by F_p point counts**: #S(F_p) = p² + (1 + tr w)p + 1, compared with the W(E6) trace distribution (BFS on six reflections, seconds); a match kills uniform line-orbit mechanisms. (3) **A descent that produces a point from conjugate points (secants, tangents, points of degree prime to 3) is a mechanism only if the conjugate points come from somewhere else**; for V_3 each such reformulation is equivalent to V_3(ℚ) ≠ ∅ (check by writing x = a + √δ·b). (4) Test fields for Tschirnhaus targets must be dense: a sparse polynomial like x^10 + x³ − 2x + 1 already lies in V_6.\n'
        '- **Method lesson (S71):**')

# ---------- Section 6 ----------
s = rep(s, '**Session 71 decision (offsets closed; power curves read in c; V_3 for decics).**',
        '**Session 72 decision (V_3 over ℚ: linear and secant mechanisms ruled out).** S72.1: Witt index of Tr u² on K_0 is s (s ≤ 3) or 3/4 (s ≥ 4, local). S72.3: Hilbert\'s cubic surfaces have W(E6) line monodromy, so skew-line descent needs a thin set of Λ. S72.4: secant, tangent and quadratic-point descents are equivalent to V_3(ℚ) ≠ ∅; Heath-Brown cannot enter linearly. S72.5: with P-dials the decic gap is two invariants. '
        '**Order now:** (1) decics over ℚ: ℚ-linear spaces in the Hermite–Joubert cubic X_A (planes, P³\'s; Hooley gives points of X_A, and planes through a general point form a 3-dimensional family) on which Tr u² restricts to a conic, a quadric surface or an indefinite form in ≥ 5 variables (Hasse–Minkowski, Meyer); the surface of planes and the 7-fold of lines in V_3 (Kodaira dimension, ℚ-points); special Λ only with a construction; (2) over P: power-curve rows with p1, p2 free and extra conditions of degree ≤ 8 (eggs, P-quartic graphs, depth-2 offsets, cusp contact), with the S59 test; (3) S_9 r = 7: a P-point source for the y³ = x⁴ rows; (4) paused as before.\n\n'
        '**Session 71 decision (offsets closed; power curves read in c; V_3 for decics).**')
s = rep(s, '- Session 71: offsets of P-affine',
        '- Session 72: Galois-stable skew sets of lines on Hilbert\'s cubic surfaces S_Λ as a uniform mechanism (W(E6) monodromy, S72.3); secant, tangent and quadratic-point descents for V_3 (equivalent to the problem, S72.4); nonsingular cubic forms in ≥ 10 variables mapped linearly to V_3 (S72.4); small-height searches on V_3 for dense decic fields (S72.1); the Witt-index claim \"≥ min(s, 3)\" as a source of ℚ-P³\'s (index 4 needs s ≥ 4 and a local condition).\n'
        '- Session 71: offsets of P-affine')

# ---------- Section 7 ----------
sc7 = ('Session 72 (one directory; cypari, numpy; nothing is written to disk except small pickles and the outputs of `edit72.py`):\n'
       '- `pick72.py <seed>` (seconds; cypari): random dense monic decics with coefficients in [−4, 4], one per s ∈ {2, 3, 4, 5}, certified S_10 by a Frobenius 7-cycle (no imprimitive group of degree 10 has order divisible by 7) and an odd Frobenius class; seed 1 gives the four S72.1 fields.\n'
       '- `witt72.py "<decic>"` (seconds; cypari): trace form on K_0 (integral basis via `matkerint`), signature, determinant, iterated `qfsolve` Witt decomposition; prints the number of mutually orthogonal isotropic vectors and the prime where the residual form is anisotropic; writes `witt_<poly>.pkl`.\n'
       '- `surf72.py <witt pickle>` (seconds): saturates and LLL-reduces (w.r.t. T2) the isotropic subspace, checks Tr = Tr u² = 0 on it and prints the cubic tensor Tr(L_a L_b L_c) (the cubic surface or plane cubic); writes `surf.pkl`.\n'
       '- `we6_72.py <p> <N> <seed>` (about 40 seconds for `31 2500 2`, 60 for `37 1500 3`; numpy): W(E6) trace distribution (BFS, 51840 elements) and F_p point counts of N cubic surfaces S_Λ in the split model of V_3.\n'
       '- `edit72.py` (this edit and archive script; reads `sec0aw.md` and the mirror under /mnt/project; writes `summary72.md`, `start72.md`, `archive7172.md`).\n\n')
s = rep(s, '\n## 8. Ground rules (revised Nov 17)', '\n' + sc7 + '## 8. Ground rules (revised Nov 17)')

# ---------- Section 8 ----------
s = rep(s, 'Add a Section 0aw (session 72; then 0ax, …) here', 'Add a Section 0ax (session 73; then 0ay, …) here')
s = rep(s, '**At the end of session 72, move Sections 0av and 0aw into a new frozen archive `claude/Sessions 71-72 results (frozen).md`.**',
        '**At the end of session 74, move Sections 0ax and 0ay into a new frozen archive `claude/Sessions 73-74 results (frozen).md`.**')
s = rep(s, '`Sessions 69-70 results (frozen).md`), and don\'t leave', '`Sessions 69-70 results (frozen).md`, `Sessions 71-72 results (frozen).md`), and don\'t leave')
open('summary72.md', 'w').write(s)

# ================= Start here =================
t = rep(t, "Updated Nov 21, 2026 (after session 71; repo inputs at commit 2536d12 are filed in the summary's Section 1a; session 71 is the summary's Section 0av; next session is 72, Section 0aw; session 72 archives Sections 0av and 0aw into `claude/Sessions 71-72 results (frozen).md`)",
        "Updated Nov 21, 2026 (after session 72; repo inputs at commit 2536d12 are filed in the summary's Section 1a; sessions 71–72 are in `claude/Sessions 71-72 results (frozen).md`; next session is 73, Section 0ax; session 74 archives Sections 0ax and 0ay into `claude/Sessions 73-74 results (frozen).md`)")
t = rep(t, 'sessions 69–70 (S69.1 … S70.4) in `claude/Sessions 69-70 results (frozen).md`.',
        'sessions 69–70 (S69.1 … S70.4) in `claude/Sessions 69-70 results (frozen).md`; sessions 71–72 (S71.1 … S72.6) in `claude/Sessions 71-72 results (frozen).md`.')
t = rep(t, 'session 71 is Section 0av, session 72 Section 0aw; session 72 also moves 0av and 0aw to a 71–72 archive',
        'session 73 is Section 0ax, session 74 Section 0ay; session 74 also moves 0ax and 0ay to a 73–74 archive')
t = rep(t, '`claude/Sessions 67-68 results (frozen).md` or `claude/Sessions 69-70 results (frozen).md`.\n5.',
        '`claude/Sessions 67-68 results (frozen).md`, `claude/Sessions 69-70 results (frozen).md` or `claude/Sessions 71-72 results (frozen).md`.\n5.')
t = rep(t, 'At the end of session 72, move Sections 0av and 0aw (sessions 71–72) into a new frozen archive `claude/Sessions 71-72 results (frozen).md` the same way (session 70 did this',
        'At the end of session 74, move Sections 0ax and 0ay (sessions 73–74) into a new frozen archive `claude/Sessions 73-74 results (frozen).md` the same way (session 72 did this for sessions 71–72 with `edit72.py`, slicing at `## 0av.` and `## 1.`; session 70 did this')
t = rep(t, 'one line per session 25–70 (Section 0), the full results of sessions from 71 on (Section 0av onward)',
        'one line per session 25–72 (Section 0), the full results of sessions from 73 on (Section 0ax onward)')
t = rep(t, '`claude/Sessions 69-70 results (frozen).md` (S69.1 … S70.4).', '`claude/Sessions 69-70 results (frozen).md` (S69.1 … S70.4), `claude/Sessions 71-72 results (frozen).md` (S71.1 … S72.6).')
t = rep(t, '## Next step (priority order, after session 71)', '## Next step (priority order, after session 72)')
t = rep(t, '1. **Session 71 (summary Section 0av): item (1) closed negatively:',
        '1. **Session 72 (71–72 archive, Section 0aw): decics over ℚ via V_3: Witt index of Tr u² on K_0 is exactly s for s ≤ 3, and 3 or 4 for s ≥ 4 by a local condition (both dense S_10 test fields with s ≥ 4 have 3) (S72.1); V_3 smooth and locally soluble at unramified p ≥ 11 (S72.2); Hilbert\'s cubic surfaces S_Λ have full W(E6) line monodromy, so skew-line descent needs a thin set of Λ (S72.3); secant/tangent/quadratic-point descents are equivalent to V_3(ℚ) ≠ ∅ and Heath-Brown cannot enter linearly (S72.4); with P-dials the decic gap is two invariants of degrees 30, 20 (S72.5). Order now: (1) decics over ℚ: ℚ-linear spaces (planes, P³\'s) in the Hermite–Joubert cubic X_A on which Tr u² is a conic, a quadric surface or an indefinite form in ≥ 5 variables (Hasse–Minkowski, Meyer); the families of planes and lines in V_3; (2) over P: power-curve rows with p1, p2 free; (3) S_9 r = 7: a P-point source for the y³ = x⁴ rows.** '
        '**Session 71 (71–72 archive, Section 0av): item (1) closed negatively:')
i = t.index('**Session 71** (summary Section 0av).'); j = t.index('(Session 70: RHJ_10 is false, 69–70 archive.)', i) + len('(Session 70: RHJ_10 is false, 69–70 archive.)')
p72 = ('**Session 72** (71–72 archive, Section 0aw). **Mechanisms named:** Hilbert\'s 3-plane (a ℚ-P³ Λ in Q = {Tr u² = 0} and the cubic surface S_Λ = Λ ∩ {Tr u³ = 0}, with points forced by a Galois-stable skew set of lines); secant descent from points of degree prime to 3 on plane sections; cubic forms in ≥ 10 variables (Heath-Brown). '
       '(S72.1) The Witt index of Tr u² on K_0 over ℚ is exactly s for s ≤ 3 and 3 or 4 for s ∈ {4, 5} (local condition); both dense S_10 test fields with s ≥ 4 have index 3 (anisotropic at 367, at 17) [exact, `witt72.py`]. '
       '(S72.2) V_3 is smooth, locally soluble at every unramified p ≥ 11 (Chevalley–Warning + Hensel). '
       '(S72.3) The 27 lines of S_Λ have monodromy W(E6) (F_p point counts of 4000 surfaces match the W(E6) trace distribution, `we6_72.py`), so skew-line descent needs a thin set of Λ. '
       '(S72.4) Secant, tangent and quadratic-point descents are equivalent to V_3(ℚ) ≠ ∅; linear spaces in Q have dimension ≤ 3, so Heath-Brown cannot enter linearly. '
       '(S72.5) With P-dials (x^10 × P-affine ℚ-sextic) the decic gap is two rational invariants of degrees 30 and 20 on the P-dense V_3. (Session 71: offsets do not free I; power curves are lacunary in c; V_3 is the decic target; 71–72 archive.)')
t = t[:i] + p72 + t[j:]
t = rep(t, 'Session 71 added: offsets as a P-dial',
        'Session 72 added: uniform skew-line mechanisms on Hilbert\'s cubic surfaces S_Λ (W(E6) monodromy, S72.3); secant, tangent and quadratic-point descents for V_3 (equivalent to the problem, S72.4); cubic forms in ≥ 10 variables mapped linearly to V_3 (S72.4); height searches on V_3 for dense decic fields. Session 71 added: offsets as a P-dial')
t = rep(t, '- Session 71 (one directory; cypari, numpy):',
        '- Session 72 (one directory; cypari, numpy): `pick72.py 1` (seconds; dense S_10 decic test fields per signature), `witt72.py "<decic>"` (seconds; Witt decomposition of Tr u² on K_0 by iterated `qfsolve`), `surf72.py <witt pickle>` (seconds; LLL-reduced isotropic subspace and its cubic tensor), `we6_72.py <p> <N> <seed>` (under a minute for `31 2500 2`, `37 1500 3`; W(E6) trace distribution vs F_p point counts of Hilbert\'s cubic surfaces), `edit72.py` (edit and archive script; reads `sec0aw.md` and the mirror under /mnt/project). Runs in the summary, Section 7.\n'
        '- Session 71 (one directory; cypari, numpy):')
t = rep(t, '**Session 71:** offsets of the B5 quintic do not free I',
        '**Session 72:** for decics over ℚ via V_3, linear and secant mechanisms are ruled out: ℚ-P³\'s in Q need s ≥ 4 and a local condition (S72.1), Hilbert\'s cubic surfaces have W(E6) monodromy (S72.3), secant descents are equivalent to the problem and Heath-Brown cannot enter linearly (S72.4); V_3 is smooth and locally soluble at unramified p ≥ 11. **Session 71:** offsets of the B5 quintic do not free I')
t = rep(t, '**S71 read power-curve rows',
        '**S72 compute the Witt index exactly before using linear spaces of a quadric; test cubic-surface monodromy by F_p point counts against the W(E6) trace distribution; a descent from conjugate points is a mechanism only if those points come from elsewhere; use dense test fields**, **S71 read power-curve rows')
open('start72.md', 'w').write(t)
print('summary', len(s), 'start', len(t), 'archive', len(arch))
for h in re.findall(r'^## .*', s, re.M): print(h[:80])
