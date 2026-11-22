# edit68.py -- session 68 edit and archive script.
# Reads the mirrored project docs and sec0as.md; writes summary_new.md, start_new.md, archive6768.md.
import re
M = '/mnt/project/'
S = open(M + 'claude_Condensed_summary_-_plan_and_progress.md').read()
T = open(M + 'claude_Start_here.md').read()
sec = open('sec0as.md').read().rstrip('\n') + '\n'

def rep(s, old, new, cnt=1):
    n = s.count(old)
    assert n == cnt, (n, old[:80])
    return s.replace(old, new)

# ---------- summary ----------
i0 = S.index('## 0ar. Session 67 (Nov 21): results'); i1 = S.index('## 1. The goal, the facts and the repo tools')
sec0ar = S[i0:i1].rstrip('\n') + '\n'
S = S[:i0] + S[i1:]
S = rep(S, '(through session 67, Nov 21;', '(through session 68, Nov 21;')
m = re.search(r"\n- `claude/Sessions 65-66 results \(frozen\)\.md` \(this project\)[^\n]*\n", S)
S = S[:m.end()] + "- `claude/Sessions 67-68 results (frozen).md` (this project): the full Sections 0ar and 0as for sessions 67–68 (labels S67.1 … S68.5), moved out of this file at the end of session 68.\n" + S[m.end():]
S = rep(S, 'Sessions from 67 on exist only in this file (Section 0ar for session 67, 0as for session 68, and so on).',
        'Sessions from 69 on exist only in this file (Section 0at for session 69, 0au for session 70, and so on).')
S = rep(S, '## 0. Sessions 25–67 in brief (full text in the frozen archives; session 67 in Section 0ar)',
        '## 0. Sessions 25–68 in brief (full text in the frozen archives)')
line68 = ("- S68 (archive 67–68): **the quintic step as a field-independent problem.** (S68.1) Node-line residuals over any field: if ν ∈ A has ν² = d ∈ F^×, Tr ν = 0, then y = Tr(v⁵)ν − 5Tr(νv⁴)v ∈ V_A for every v ∈ Y_ν = {Tr v = Tr(νv²) = Tr v³ = 0} (a (2,3) 5-fold): a rational node removes the quintic [numerical 10⁻¹⁴]; no use over ℚ for primitive A. "
          "(S68.2) Decic fields over ℚ_p are imprimitive: a quintic subfield gives pairing points, a quadratic subfield a node; 17 of the 42 factor-degree types have no split node. "
          "(S68.3) **Given Hooley IV, the scope (i) gap is the relative Hermite–Joubert problem RHJ_10** (can the generic decic with e1 = e3 = 0 be Tschirnhaus-transformed over its coefficient field to e5 = 0 as well?) plus the ramified local conditions for X_A: a covariant a = g(θ)/f'(θ) (dual basis, Tr a = 0 automatic; ansatz of arXiv 2609.15786, Hermite–Joubert in degree 7) applied to a Hooley point of X_A. "
          "(S68.4) p-field test of RHJ_10: passes for every p ≠ 3 and every 3-field type except E′ = L1 × L2 × L3 × F′ (three distinct cyclic cubics), where the leading-term system forces the singular point (1, −1, 0, 0) (other branch: roots of 3x³ − 3x² − 15x + 7, group S3); that type is the open test.\n")
S = rep(S, '\n- S67 (Section 0ar): **the cubic half', '\n- S67 (archive 67–68): **the cubic half')
j = S.index('- S67 (archive 67–68): **the cubic half'); j = S.index('\n', j) + 1
S = S[:j] + line68 + S[j:]
# Section 3 rows
j = S.index('| S67.5: the cubic (3-primary) half'); j = S.index('\n', j) + 1
rows = ("| S68.1: node-line residuals: for ν ∈ A with ν² ∈ F^×, Tr ν = 0 (a rational node, split or not) and v ∈ Y_ν = {Tr v = Tr(νv²) = Tr v³ = 0}, Tr(ν + κv)⁵ = 5κ⁴Tr(νv⁴) + κ⁵Tr v⁵, so y = Tr(v⁵)ν − 5Tr(νv⁴)v ∈ V_A(F), smooth and generating for general v; over any field of characteristic 0 | [numerical] (`node68.py`) + *unchecked* (short algebra) |\n"
        "| S68.2: decic fields over ℚ_p are imprimitive (solvable primitive groups have prime-power degree): a quintic subfield gives smooth pairing points; a quadratic subfield only gives a node, reducing V to Y_ν(ℚ_p) (Hermite element of L/ℚ_p(√d) with Tr_{L/Q}(v0²) ∈ ℚ_p^×Q^{×2}, not proved in general); 17 of 42 factor-degree types of degree 10 have no split node (nonic types: [9,1], [8,1,1], [7,2,1], [7,1,1,1], [6,3,1], [6,2,1,1], [6,1⁴], [3,3,3,1]) | *unchecked* + exact enumeration (`parts68.py`) |\n"
        "| S68.3: RHJ_10 (generic decic with e1 = e3 = 0 over F = ℚ(e2, e4, e5, …, e10) has a generator with Tr a = Tr a³ = Tr a⁵ = 0) implies, with Hooley IV, V_A(ℚ) ∋ generators for every A whose ramified completions carry smooth points of X_A; so the scope (i) gap = RHJ_10 + X-local conditions | *unchecked* (short; unirationality of the nodal X_A from a smooth ℚ-point unchecked) |\n"
        "| S68.4: p-field test of RHJ_10: passes for p = 2 (odd degree 15), p = 5 (split nodes, S68.1), p = 7 (Kummer), p ≥ 11 (split), and p = 3 except type [3,3,3,1] with pairwise non-isomorphic cubics; there X has smooth points and the leading-term system of V has only the singular solution (1, −1, 0, 0) (other branch needs a root of 3x³ − 3x² − 15x + 7, Galois group S3) | exact (`parts68.py`) + *unchecked* (arguments; BR valuation not redone) |\n"
        "| S68.5: the scope (i) gap is RHJ_10 plus local conditions; the [3,3,3,1] 3-field test decides whether a field-independent transfer can exist | decision |\n")
S = S[:j] + rows + S[j:]
# Section 4
S = rep(S, 'the quintic section is the whole remaining gap (S67.3: five transfers fail).**',
        'the quintic section is the whole remaining gap (S67.3: five transfers fail).** **S68: given Hooley IV the gap is the field-independent relative Hermite–Joubert problem RHJ_10 (the generic decic with e1 = e3 = 0 Tschirnhaus-transformed over its coefficient field to e5 = 0) plus the ramified local conditions for X_A; RHJ_10 passes every p-field test except the 3-field type [3,3,3,1] with distinct cubics (S68.3–S68.4); a rational node removes the quintic (S68.1).**')
j = S.index('- (S67.1–S67.2, given Hooley IV) ℚ-points of the Hermite–Joubert cubic'); j = S.index('\n', j) + 1
S = S[:j] + '- (S68.1, any field) node-line residuals: when A has a node ν (ν² scalar, Tr ν = 0) over the base field, every point v of the (2,3) 5-fold Y_ν with Tr v⁵ ≠ 0 gives y = Tr(v⁵)ν − 5Tr(νv⁴)v ∈ V_A;\n' + S[j:]
# Section 5
S = rep(S, '- **Session 67:** S67.1–S67.5 (Section 0ar).', '- **Session 67:** S67.1–S67.5 (archive 67–68).')
j = S.index('- **Session 67:** S67.1–S67.5 (archive 67–68).'); j = S.index('\n', j) + 1
S = S[:j] + '- **Session 68:** S68.1–S68.5 (archive 67–68). Node-line residuals remove the quintic whenever a rational node exists; given Hooley IV the scope (i) gap is the field-independent relative Hermite–Joubert problem RHJ_10 plus X-local conditions; its p-field test passes except one 3-field type ([3,3,3,1], distinct cubics).\n' + S[j:]
j = S.index('- **Method lesson (S67):**'); j = S.index('\n', j) + 1
S = S[:j] + ('- **Method lesson (S68):** (1) **When a theorem gives points on a containing variety (Hooley on X_A) and the target is a section of it, ask for a field-independent transfer (a covariant) and test it over p-fields first**: a transfer that exists must produce points over every p-field over which the containing variety has generators; list the p-field algebra types by factor degrees (p-powers) and dispose of them by split nodes (a sub-multiset of degrees summing to n/2), involutions (isomorphic factors) and Kummer factors. '
             '(2) **The dual basis θ^j/f\'(θ) (Euler: Tr = 0 for j ≤ n − 2) makes the linear trace condition automatic**; this is how the 2026 degree-7 Hermite–Joubert proof is set up. '
             '(3) **A node ν with ν² scalar turns lines through it into lines whose quintic restriction is κ⁴(5Tr(νv⁴) + κTr v⁵)**: look for points of the variety whose powers are scalars before projecting.\n') + S[j:]
# Section 6
S = rep(S, 'items decided in sessions 41–67)', 'items decided in sessions 41–68)')
S = rep(S, '\n**Session 67 decision (the cubic half is done;',
        '\n**Session 68 decision (the quintic step is a field-independent problem).** S68.1: node-line residuals remove the quintic when a rational node exists (any field; not for primitive A over ℚ). S68.3: given Hooley IV, the scope (i) gap is RHJ_10 (the generic e1 = e3 = 0 decic Tschirnhaus-transformed over its coefficient field to e5 = 0) plus the ramified local conditions for X_A. S68.4: RHJ_10 passes the p-field test except for the 3-field type [3,3,3,1] with distinct cyclic cubics (undecided). **Order now:** (1) rational nonics and decics: decide the [3,3,3,1] test by Brassil–Reichstein\'s valuation method (with k = 1, 3, 5 and generating points); if it passes, a covariant search for RHJ_10 (a = g(θ)/f\'(θ), g of low weight, the two trace identities in PARI modulo f over ℚ(e)); the local leftovers via S68.1–S68.2; (2) over P (r = 9): the S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic.\n\n**Session 67 decision (the cubic half is done;')
S = rep(S, '\n- Session 67: fibrations of V_A with cubic fibres via linear maps',
        '\n- Session 68: node-line residuals as a ℚ-mechanism for primitive A (no rational nodes, S65.1); the 5-field digit point of S67.3(e) as evidence (it is the singular node; superseded by S68.4).\n- Session 67: fibrations of V_A with cubic fibres via linear maps')
# Section 7
j = S.index('\n## 8. Ground rules')
S = S[:j].rstrip('\n') + ('\n\nSession 68 (one directory; numpy, sympy, cypari; nothing is written to disk):\n'
     '- `node68.py [trials] [seed]` (seconds): node-line residual identity (S68.1) on random split and non-split nodes over ℂ: Newton for v on Y_ν, the identity in κ, the traces of y, Jacobian rank and distinct y_i² (run `40 1`: max residual 1.6·10⁻¹⁴, rank 3, 10 distinct).\n'
     '- `parts68.py` (seconds): factor-degree types of degree 10 with and without a split node, the p-field types, and the [3,3,3,1] leading-term system (the cubic 3x³ − 3x² − 15x + 7: irreducible, disc 2⁸·3³·7, S3).\n'
     '- `edit68.py` (this edit and archive script; reads `sec0as.md` and the mirrored docs under /mnt/project).\n') + '\n' + S[j:]
# Section 8
S = rep(S, 'Add a Section 0as (session 68; then 0at, …) here, update Sections 3–7 and the header, save scripts to `scripts/`, and update `Start here.md`. **At the end of session 68, move Sections 0ar and 0as into a new frozen archive `claude/Sessions 67-68 results (frozen).md`.**',
        'Add a Section 0at (session 69; then 0au, …) here, update Sections 3–7 and the header, save scripts to `scripts/`, and update `Start here.md`. **At the end of session 70, move Sections 0at and 0au into a new frozen archive `claude/Sessions 69-70 results (frozen).md`.**')
S = rep(S, '`Sessions 63-64 results (frozen).md`, `Sessions 65-66 results (frozen).md`), and don\'t leave',
        '`Sessions 63-64 results (frozen).md`, `Sessions 65-66 results (frozen).md`, `Sessions 67-68 results (frozen).md`), and don\'t leave')
left = [m.start() for m in re.finditer('Section 0ar', S)]
print('remaining "Section 0ar" mentions in summary:', len(left))
for p in left: print('   ', S[max(0, p-80):p+40].replace('\n', ' '))
S = S.replace('(Section 0ar)', '(archive 67–68)')

# ---------- archive ----------
A = ('# Sessions 67–68: full results (frozen archive)\n\n'
     'Frozen on Nov 21, 2026 (end of session 68). This file holds Section 0ar (session 67) exactly as it stood in the condensed summary after session 67, and Section 0as (session 68) as written in session 68. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S67.1 … S68.5. Labels S67.1 … S68.5 point here.\n\n'
     + sec0ar + '\n' + sec)

# ---------- start here ----------
T = rep(T, 'Updated Nov 21, 2026 (after session 67; repo inputs at commit 2536d12 are filed in the summary\'s Section 1a; next session is 68, Section 0as; session 68 archives Sections 0ar and 0as into `claude/Sessions 67-68 results (frozen).md`).',
        'Updated Nov 21, 2026 (after session 68; repo inputs at commit 2536d12 are filed in the summary\'s Section 1a; next session is 69, Section 0at; session 70 archives Sections 0at and 0au into `claude/Sessions 69-70 results (frozen).md`).')
T = rep(T, 'sessions 65–66 (S65.1 … S66.5) in `claude/Sessions 65-66 results (frozen).md`. ',
        'sessions 65–66 (S65.1 … S66.5) in `claude/Sessions 65-66 results (frozen).md`; sessions 67–68 (S67.1 … S68.5) in `claude/Sessions 67-68 results (frozen).md`. ')
T = rep(T, 'session 67 is Section 0ar, session 68 Section 0as; session 68 also moves 0ar and 0as to a 67–68 archive',
        'session 69 is Section 0at, session 70 Section 0au; session 70 also moves 0at and 0au to a 69–70 archive')
T = rep(T, 'or `claude/Sessions 65-66 results (frozen).md`.', '`claude/Sessions 65-66 results (frozen).md` or `claude/Sessions 67-68 results (frozen).md`.')
T = rep(T, '**After session 67 the summary is about 233k characters** and this file about 95k. At the end of session 68, move Sections 0ar and 0as (sessions 67–68) into a new frozen archive `claude/Sessions 67-68 results (frozen).md` the same way (',
        '**After session 68 the summary is about SUMK characters** and this file about STARTK. At the end of session 70, move Sections 0at and 0au (sessions 69–70) into a new frozen archive `claude/Sessions 69-70 results (frozen).md` the same way (session 68 did this for sessions 67–68 with `edit68.py`, slicing at `## 0ar.` and `## 1.` in the mirror `/mnt/project/claude_Condensed_summary_-_plan_and_progress.md` (underscores, no spaces); ')
T = rep(T, '`claude/Sessions 65-66 results (frozen).md` (S65.1 … S66.5).', '`claude/Sessions 65-66 results (frozen).md` (S65.1 … S66.5), `claude/Sessions 67-68 results (frozen).md` (S67.1 … S68.5).')
T = rep(T, 'one line per session 25–66 (Section 0), the full results of sessions from 67 on (Section 0ar onward)',
        'one line per session 25–68 (Section 0), the full results of sessions from 69 on (Section 0at onward)')
T = rep(T, '(priority order, after session 67)', '(priority order, after session 68)')
T = rep(T, '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 67:',
        '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 68: given Hooley IV, the gap is the field-independent relative Hermite–Joubert problem RHJ_10 (can the generic decic with e1 = e3 = 0 be Tschirnhaus-transformed over its own coefficient field to e5 = 0 too? a covariant a = g(θ)/f\'(θ) applied to a Hooley point, S68.3) plus the ramified local conditions for X_A; node-line residuals remove the quintic when a rational node exists (S68.1); RHJ_10 passes every p-field test except the 3-field type [3,3,3,1] with three distinct cyclic cubics (S68.4).** **Next: decide [3,3,3,1] by Brassil–Reichstein\'s valuation method (read BR\'s proof; conditions k = 1, 3, 5; generating points); if it passes, search for the covariant (low weight, PARI modulo f over ℚ(e), coefficients solved on specialisations first); then the local leftovers via S68.1–S68.2.** **Session 67:')
i = T.index('**Session 67** (the cubic half of the global step; full text in the summary, Section 0ar).')
k = T.index('(Session 66: 3-field test, Brassil–Reichstein; archive 65–66.)') + len('(Session 66: 3-field test, Brassil–Reichstein; archive 65–66.)')
T = T[:i] + ('**Session 68** (the quintic step as a field-independent problem; full text in the 67–68 archive, Section 0as). **Mechanism named:** a field-independent transfer X_A ⇢ V_A (a covariant a = g(θ)/f\'(θ) in the dual basis, where Tr a = 0 is automatic; the ansatz of the 2026 degree-7 Hermite–Joubert proof, arXiv 2609.15786) fed by Hooley\'s ℚ-points of X_A, and node-line residuals. **Result:** (S68.1) if A has a rational node ν (ν² scalar, Tr ν = 0), y = Tr(v⁵)ν − 5Tr(νv⁴)v ∈ V_A for every v on the (2,3) 5-fold Y_ν: the quintic disappears [numerical 10⁻¹⁴; any field; useless over ℚ for primitive A]. (S68.2) Decic fields over ℚ_p are imprimitive, so they have pairing points (quintic subfield) or a node (quadratic subfield); 17 of 42 factor-degree types lack a split node. (S68.3) **Given Hooley IV the scope (i) gap is RHJ_10** (the generic e1 = e3 = 0 decic Tschirnhaus-transformed over its coefficient field to e5 = 0) **plus the ramified local conditions for X_A.** (S68.4) The p-field test of RHJ_10 passes at p = 2, 5, 7, ≥ 11 and at p = 3 except for E′ = L1 × L2 × L3 × F′ with three distinct cyclic cubics, where the leading terms are forced to the singular point (1, −1, 0, 0) (the other branch needs a root of 3x³ − 3x² − 15x + 7, group S3): undecided, and it decides whether a field-independent transfer can exist. (Session 67: Hooley IV for X_A; archive 67–68.)') + T[k:]
T = rep(T, 'Session 67 added:', 'Session 68 added: node-line residuals as a ℚ-mechanism for primitive A (no rational nodes); the 5-field digit point of S67.3(e) as evidence (it is the singular node; superseded by S68.4). Session 67 added:')
T = rep(T, '**S67 check Hooley IV', '**S68 test a field-independent transfer over p-fields first (factor degrees as p-powers; split nodes, involutions, Kummer factors); the dual basis θ^j/f\'(θ) makes the linear trace automatic; a node with ν² scalar turns the quintic on lines into κ⁴(5Tr(νv⁴) + κTr v⁵)**, **S67 check Hooley IV')
T = rep(T, 'the quintic section of X_A is the remaining gap. **Session 65',
        'the quintic section of X_A is the remaining gap. **Session 68:** given Hooley IV that gap is a field-independent algebraic statement, RHJ_10 (the generic e1 = e3 = 0 decic Tschirnhaus-transformed over its coefficient field to e5 = 0), plus X-local conditions; RHJ_10 passes every p-field test except one 3-field type. **Session 65')
j = T.index('- Session 67 (one directory; Singular via apt;'); j = T.index('\n', j) + 1
T = T[:j] + '- Session 68 (one directory; numpy, sympy, cypari): `node68.py 40 1` (seconds; node-line residual identity, S68.1), `parts68.py` (seconds; factor-degree types, p-field types, the [3,3,3,1] leading-term cubic), `edit68.py` (edit and archive script; reads `sec0as.md` and the mirror under /mnt/project). Runs and timings: summary Section 7.\n' + T[j:]
T = T.replace('SUMK', '%dk' % round(len(S)/1000)).replace('STARTK', '%dk' % round((len(T))/1000))
open('summary_new.md', 'w').write(S); open('start_new.md', 'w').write(T); open('archive6768.md', 'w').write(A)
for name, x in (('summary', S), ('start', T), ('archive', A)):
    print(name, len(x), [h for h in re.findall(r'^## [^\n]*', x, re.M)][:30] if name != 'start' else len(re.findall(r'^## ', x, re.M)))
