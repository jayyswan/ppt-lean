# edit65.py -- session 65 checklist: add Section 0ap to the condensed summary and update
# Sections 0, 3-8 and Start here.md. Reads the /mnt/project mirror and sec0ap.md;
# writes summary65.md and start65.md (no archive this session; session 66 archives 0ap, 0aq).
import re
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
H = open('/mnt/project/claude_Start_here.md').read()
ap = open('sec0ap.md').read().rstrip('\n') + '\n\n'
n0S, n0H = len(S), len(H)
def rep(txt, old, new, cnt=1):
    assert txt.count(old) == cnt, (old[:80], txt.count(old)); return txt.replace(old, new)

# ---------------- header, Section 0, new section ----------------
S = rep(S, '(through session 64, Nov 20;', '(through session 65, Nov 21;')
S = rep(S, '## 0. Sessions 25–64 in brief (full text in the frozen archives)', '## 0. Sessions 25–65 in brief (full text in the frozen archives; session 65 in Section 0ap below)')
i = S.index('- S64 (archive 63–64):'); j = S.index('\n', i)
line65 = ('\n- S65 (Section 0ap): **the global step for V_K / W_K, Brauer–Manin side.** Both are twists of V̄ = {p1 = p3 = p5 = 0} ⊂ P⁹ by a degree-10 étale algebra A. '
          '**Sing V̄ = 7875 lines** ⟨e_A, e_B⟩ (pairing configurations with two values) (S65.1); the singularities are terminal (transversal ODP of rank 6 along the lines; cone over a 125-nodal (2,3) 5-fold at the 126 points (±1)^5; a quadric-plus-nodal-cubic weighted form at the points with zeros), so V̄ is a terminal Fano 6-fold and every resolution is rationally connected (S65.2). '
          '**Theorem S65.3: for every A, Br(X̃) = Br(ℚ) for any smooth projective model** (Pic X̃̄ = ℤH ⊕ permutation module of exceptional divisors, by local factoriality and Grothendieck–Lefschetz; Br(X̃̄) = 0 by Lefschetz for lci: H³ = 0). '
          'So no Brauer–Manin obstruction; **under Colliot-Thélène\'s conjecture every nonic field (and every primitive decic field) with V_A everywhere locally soluble closes over ℚ with one crossing**, including both test fields (S65.4). Unconditional global step still open.')
S = S[:j] + line65 + S[j:]
i1 = S.index('## 1. The goal')
S = S[:i1] + ap + S[i1:]

# ---------------- Section 3 rows ----------------
i = S.index('| S64.6: no local obstruction'); j = S.index('\n', i)
rows = '''
| S65.1: Sing(V̄) (V̄ = {p1 = p3 = p5 = 0} ⊂ P⁹) is the union of the 7875 lines ⟨e_A, e_B⟩ (two-valued pairing configurations); points of three kinds: general (type 1), with zeros (type 2, z ∈ {2, 4, 6, 8}), the 126 points (±1)^5 on 125 lines each (type 3); none defined over ℚ for primitive A | *unchecked* (short proof) |
| S65.2: V̄ has terminal Gorenstein singularities (type 1: transversal ODP, Hessian rank 6 on the 8-dim tangent space; type 3: tangent cone = cone over a (2,3) CI 5-fold Y ⊂ P⁷ with exactly 125 nodes, discrepancy 2; type 2: weighted leading form −5Q(x) + (5/3)C(u), C = {Σu = Σu³ = 0} with 3, 10, 35 nodes for z = 4, 6, 8, discrepancy ≥ 7); hence V̄ (Fano, K = O(−1)) and every resolution of every twist are rationally connected (Zhang 2006) | [numerical] (`sing65.py hess 12 1`) + [exact] (`sing65.py type3`, `type2 4/6/8`, Singular over ℚ) + *unchecked* (type-2 leading form, assembly) |
| S65.3: for every étale ℚ-algebra A of degree 10 and every smooth projective model X̃ of V_A: Br(X̃) = Br(ℚ) (Pic X̃̄ = ℤπ*H ⊕ ⊕ℤE_i permutation, by SGA2 XI 3.14 (factorial, Sing in codim 5), SGA2 XII 3.7 (Pic = ℤ) and the negativity lemma; Br(X̃̄) = 0 by Lefschetz for lci (H² = ℤ, H³ = 0) and Br(V̄_sm) = 0) | *unchecked* (proof; citations not rechecked) |
| S65.4: under Colliot-Thélène's conjecture (rational points dense in the Brauer–Manin set for smooth projective geometrically rationally connected varieties), V_A(ℚ) is Zariski dense whenever V_A has smooth ℚ_v-points at every place; so every nonic field over ℚ with its ramified local algebras covered (S64), including the PSL(2,8) r = 9 test field and the S_9 control, and every primitive decic field with W_K everywhere locally soluble, closes over ℚ by row B5 with one crossing | *unchecked* (conditional, short) |
| S65.5: the scope (i) gap is now exactly the unconditional global step (a construction or a fibration with Hasse-principle fibres; V_A → P(2,4,6,8,10,7,9) is finite, so V_A(ℚ) ≠ ∅ ⇔ the family E(w²) + R(w) is versal for A) plus the S64.6 local leftovers and, for W_K, the unramified types (9,1), (7,3), (7,2,1), (7,1,1,1), (5,3,2), (5,3,1,1) | decision |'''
S = S[:j] + rows + S[j:]
S = rep(S, '| PSL(2,8), r = 9 | **open**; S63', '| PSL(2,8), r = 9 | **open**; closed under Colliot-Thélène\'s conjecture (S65.4: no Brauer–Manin obstruction on V_K for any K, S65.3; the test field is everywhere locally soluble); S63')
S = rep(S, '| A_9, r = 9 | **open**; S63', '| A_9, r = 9 | **open**; closed under Colliot-Thélène\'s conjecture when V_K is everywhere locally soluble (S65.4; ELS for the S_9 control); S63')
S = rep(S, '**Decics (S49.1, S51.1, S63.4).**', '**Decics (S49.1, S51.1, S63.4, S65.4).** Over ℚ, under Colliot-Thélène\'s conjecture, every primitive decic field with W_K everywhere locally soluble closes (S65.3: no Brauer–Manin obstruction; S65.2: rationally connected).')

# ---------------- Section 4 ----------------
S = rep(S, 'local solubility is a finite check per K. Singular along the pairing curves.',
        'local solubility is a finite check per K. Singular along the pairing curves (**S65.1: exactly 7875 lines; S65.2: terminal singularities, rationally connected; S65.3: Br(X̃) = Br(ℚ) for every K, so no Brauer–Manin obstruction; S65.4: under Colliot-Thélène\'s conjecture, everywhere local solubility suffices**).')
S = rep(S, '- Hasse-principle varieties (S17.3;', '- (conditional, S65.4) under Colliot-Thélène\'s conjecture: every twist V_A of V̄ = {p1 = p3 = p5 = 0} with smooth local points everywhere (Br trivial, rationally connected, S65.2–S65.3);\n- Hasse-principle varieties (S17.3;')

# ---------------- Section 5 ----------------
S = rep(S, '- **Session 64:** S64.1–S64.6', '- **Session 65:** S65.1–S65.5 (Section 0ap). The global step for V_K / W_K on the Brauer–Manin side: the singular locus is 7875 lines with terminal singularities, every resolution is rationally connected, and Br(X̃) = Br(ℚ) for every twist; so under Colliot-Thélène\'s conjecture local solubility suffices, and the rational degree bound reaches 10 conditionally.\n- **Session 64:** S64.1–S64.6')
lesson = ('- **Method lesson (S65):** (1) **Before looking for a Brauer–Manin obstruction on a singular complete intersection, check factoriality and Lefschetz first**: an lci singular in codimension ≥ 4 is locally factorial (SGA2 XI 3.14) and has Pic = ℤ (SGA2 XII 3.7) in dimension ≥ 3, so the Picard lattice of any resolution is ℤH plus a permutation module of exceptional divisors and H¹(k, Pic) = 0 for every twist; Lefschetz (H³ = 0) kills the transcendental part. '
          '(2) **For rational connectedness of a singular Fano, classify the singular strata and check each tangent cone exactly** (Singular over ℚ: dimension and degree of the singular locus of the projectivised cone; a reduced 0-dimensional singular locus means nodes); terminal or klt Fano ⇒ rationally connected (Zhang). '
          '(3) **Write twisted forms for all degrees at once**: V_K (nonics, K × ℚ) and W_K (decics) are twists of one variety, so every geometric statement is proved once.\n')
S = rep(S, '- **Method lesson (S64):**', lesson + '- **Method lesson (S64):**')

# ---------------- Section 6 ----------------
dec = ('**Session 65 decision (no Brauer–Manin obstruction; the gap is the unconditional global step).** S65.1–S65.3: Sing V̄ is 7875 lines with terminal singularities, resolutions are rationally connected, Br(X̃) = Br(ℚ) for every twist. S65.4: under Colliot-Thélène\'s conjecture every nonic field (and every primitive decic field) with V_A everywhere locally soluble closes over ℚ. '
       '**Order now:** (1) rational nonics and decics: an unconditional ℚ-point mechanism for V_A (a fibration of V_A or of a variety dominating it, with fibres where the Hasse principle is a theorem: quadrics, Châtelet surfaces, cubic hypersurfaces in ≥ 10 variables; the P⁴\'s of pairing configurations and the type-3 tangent cones as structure to exploit; versality of E(w²) + R(w)); the local leftovers (S64.6 shapes for p ≥ 11, wild algebras at 2, 3, 5, 7; the six unramified W_K types with m ≤ 1); (2) over P (r = 9): the S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic.\n\n')
S = rep(S, '**Session 64 decision (local', dec + '**Session 64 decision (local')
S = rep(S, '- Session 64: random p-adic search', '- Session 65: searching for a Brauer–Manin obstruction on V_K or W_K, algebraic or transcendental (none exists for any twist, S65.3); resolving V̄ explicitly for the Picard lattice (factoriality makes it unnecessary); circle-method or Lang–Weil-type global arguments for the (3,5) system in 9 variables (far out of range).\n- Session 64: random p-adic search')
S = rep(S, 'items decided in sessions 41–64)', 'items decided in sessions 41–65)')

# ---------------- Section 7 ----------------
s7 = ('Session 65 (one directory; numpy; Singular via `apt-get update && apt-get install -y singular`):\n'
      '- `sing65.py hess <trials> <seed>` (seconds): rank of the transversal Hessian at random type-1 points of the singular lines (run `hess 12 1`: rank 6 on all, radical ⟨e_A, e_B⟩).\n'
      '- `sing65.py type3` (about a minute; Singular over ℚ with primdec.lib): the tangent cone at e = (1⁵, (−1)⁵), Y = {Σz = 0, z0 = 0, Σe_i z_i² = 0, Σz_i³ = 0}: affine dimension 6, degree 6, singular locus of affine dimension 1 and degree 125, radical of degree 125 (125 nodes).\n'
      '- `sing65.py type2 <z>` (seconds): the cubic {Σu = 0, Σu³ = 0} in z variables; singular locus of affine dimension 1 and degree 3, 10, 35 for z = 4, 6, 8 (Jacobian multiplicity 1: nodes). (The radical lines need primdec.lib, added by the session; rerun if the radical degree is wanted.)\n'
      '- `sing65.py vbar <seed>` (Sing(V̄) on a hyperplane section mod p by 4 × 4 minors): did not finish in 10 minutes; not needed (S65.1 is a proof).\n'
      '- `edit65.py` (this edit script; reads `sec0ap.md`).\n\n')
S = rep(S, '## 8. Ground rules (revised Nov 17)', s7 + '## 8. Ground rules (revised Nov 17)')

# ---------------- Section 8 ----------------
S = rep(S, 'Add a Section 0ap (session 65; then 0aq, …) here', 'Add a Section 0aq (session 66) here')

# ---------------- Start here ----------------
H = rep(H, 'Updated Nov 20, 2026 (after session 64;', 'Updated Nov 21, 2026 (after session 65;')
H = rep(H, 'next session is 65, Section 0ap; session 66 archives', 'next session is 66, Section 0aq; session 66 archives')
H = rep(H, '## Next step (priority order, after session 64)', '## Next step (priority order, after session 65)')
i = H.index('**Session 64** (local solubility'); j = H.index('\n', i)
p65 = ('**Session 65** (the global step for V_K / W_K, Brauer–Manin side; full text in the summary, Section 0ap). **Mechanism tested:** the Hasse principle through the Brauer–Manin obstruction (Colliot-Thélène\'s conjecture). Tests that could fail: a nonzero H¹(ℚ, Pic) on a resolution, a transcendental Brauer class (Artin–Mumford type), non-klt singularities. **None occurs.** '
       '(S65.1) Sing V̄ is the union of 7875 lines ⟨e_A, e_B⟩ (V_K and W_K are twists of V̄ = {p1 = p3 = p5 = 0} ⊂ P⁹); (S65.2, `sing65.py`) the singularities are terminal: transversal ODP of rank 6 along the lines, cone over a (2,3) 5-fold with exactly 125 nodes at the 126 points (±1)^5, quadric plus nodal cubic (3, 10, 35 nodes) at the points with zeros; so every resolution is rationally connected; '
       '(S65.3) **Br(X̃) = Br(ℚ) for every twist** (Pic = ℤH ⊕ permutation module by local factoriality and Grothendieck–Lefschetz; Br(X̃̄) = 0 by Lefschetz for lci); (S65.4) **under Colliot-Thélène\'s conjecture every nonic field over ℚ with V_K everywhere locally soluble, including both test fields, and every primitive decic field with W_K everywhere locally soluble, closes with one crossing.** '
       'The unconditional global step is the remaining gap for scope (i). (Session 64: local solubility uniform in K; archive 63–64, Section 0ao.)')
H = H[:i] + p65 + H[j:]
H = rep(H, '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** ',
        '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 65: no Brauer–Manin obstruction on V_A for any degree-10 étale algebra A (S65.3), resolutions rationally connected (S65.2), so under Colliot-Thélène\'s conjecture local solubility suffices (S65.4).** **Next: an unconditional ℚ-point mechanism** (a fibration of V_A, or of a variety dominating it, with fibres where the Hasse principle is a theorem: quadrics, Châtelet surfaces, cubic hypersurfaces in ≥ 10 variables; use the P⁴\'s of pairing configurations and the type-3 tangent cones; equivalently versality of E(w²) + R(w) for A), then the local leftovers (S64.6; for W_K the unramified types (9,1), (7,3), (7,2,1), (7,1,1,1), (5,3,2), (5,3,1,1)). ')
H = rep(H, '**S64 Chevalley–Warning', '**S65 before a Brauer–Manin computation on a singular complete intersection check local factoriality (SGA2 XI 3.14) and Lefschetz (Pic = ℤ, H³ = 0): then H¹(Pic) = 0 and Br(X̄) = 0 for every twist; classify singular strata and check tangent cones exactly for klt (⇒ rationally connected)**, **S64 Chevalley–Warning')
H = rep(H, 'Session 64 added: random', 'Session 65 added: searching for a Brauer–Manin obstruction on V_K / W_K (none, S65.3); explicit resolutions for the Picard lattice; circle-method arguments for the (3,5) system in 9 variables. Session 64 added: random')
H = rep(H, '**Session 64:** the local half is uniform', '**Session 65:** no Brauer–Manin obstruction on any twist V_A (S65.3) and rationally connected resolutions (S65.2), so the rational degree bound reaches 10 under Colliot-Thélène\'s conjecture plus finitely many local checks per field (S65.4); the unconditional global step is the gap. **Session 64:** the local half is uniform')
i = H.index('- Session 64 (one directory; cypari'); j = H.index('\n', i)
ws = ('\n- Session 65 (one directory; numpy; Singular via `apt-get update && apt-get install -y singular`): `sing65.py hess 12 1` (seconds; transversal Hessian rank at type-1 points: 6), `sing65.py type3` (about a minute; tangent cone at (±1)^5: degree 6, 125 nodes), `sing65.py type2 <4|6|8>` (seconds; 3, 10, 35 nodes), `sing65.py vbar <seed>` (too slow, not used), `edit65.py` (edit script; reads `sec0ap.md`).')
H = H[:j] + ws + H[j:]
H = rep(H, '**After session 64 the summary is about 203k characters** and this file about 90k.', '**After session 65 the summary is about %dk characters** and this file about %dk.' % (round(len(S) / 1000), round(len(H) / 1000) + 1))

open('summary65.md', 'w').write(S); open('start65.md', 'w').write(H)
print('summary', n0S, '->', len(S), ' start', n0H, '->', len(H))
print(re.findall(r'^## [^\n]*', S, re.M))
