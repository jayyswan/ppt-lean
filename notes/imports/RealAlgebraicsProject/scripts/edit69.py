# edit69.py (session 69): edits the condensed summary and Start here from the /mnt/project mirror.
import re
S = '/mnt/project/claude_Condensed_summary_-_plan_and_progress.md'
T = '/mnt/project/claude_Start_here.md'
s = open(S).read(); t = open(T).read()
sec = open('sec0at.md').read().rstrip('\n') + '\n\n'

def rep(text, a, b, count=1):
    assert text.count(a) == count, (a[:60], text.count(a))
    return text.replace(a, b)

# ---------- summary ----------
s = rep(s, '# Condensed summary: plan and progress (through session 68', '# Condensed summary: plan and progress (through session 69')
s = rep(s, '## 0. Sessions 25–68 in brief (full text in the frozen archives)', '## 0. Sessions 25–69 in brief (full text in the frozen archives; session 69 in Section 0at)')
s = rep(s, '- Nov 19 (between sessions 55 and 56)',
 '- S69 (Section 0at): **the [3,3,3,1] 3-field test passes.** (S69.1) Over a 3-field, an F′-point of V of multiplicity prime to 3 gives smooth generators (a generic plane through it has a residual scheme of degree 15 − m ≢ 0 mod 3). (S69.2) P = (1, −1, 0, 0) has multiplicity 2 on V whenever two factors have equal degree d ∈ {2, 3, 4} (Hessian 10·diag(P) on T_P X; d = 1 gives 3) [numerical: order 2, 13 residual generators]; so [3,3,3,1] passes for any cubics. (S69.3) Audit: S68.4 left [9,1] with X having generators untreated; V has no rational singular points there, contains the plane cubic {Tr_M(mβ³) = 0} (K9 = M(ρ), ρ³ = m); **[9,1] with X-generators is the single open p-field test of RHJ_10.**\n- Nov 19 (between sessions 55 and 56)')
s = rep(s, '## 1. The goal', sec + '## 1. The goal')
# Section 3 rows
rows = ('| S69.1: over a 3-field F′ (every finite extension of 3-power degree), an F′-point of V_{E′} of multiplicity m with 3 ∤ m gives smooth generators of E′ in V_{E′}(F′) (generic plane through it: residual of degree 15 − m ≢ 0 mod 3, avoiding Sing V and the non-generator locus) | *unchecked* (short, complete) + [numerical] (`mult69.py`) |\n'
 '| S69.2: if E′ has two factors of equal degree d, P = (1, −1, 0, …) ∈ V_{E′}(F′) has multiplicity 2 for d ∈ {2, 3, 4} (Hessian 10·diag(P) nonzero on T_P X), ≥ 3 for d = 1, 6 for d = 5; so the [3,3,3,1] p-field test of RHJ_10 passes for any cubic factors | *unchecked* (short) + [numerical] (`mult69.py`: order 2 and 13 residual generators for d = 2, 3; order 3 for d = 1) |\n'
 '| S69.3: S68.4 did not treat [9,1] with X(F′) ∋ generators; there V has no F′-rational singular point, contains the plane cubic {Tr_{M/F′}(mβ³) = 0} ⊂ P(Mρ) (K9 = M(ρ), ρ³ = m), and the tangent-line pullback of Tr y⁵ has order 5 along the lines of X through θ (index 3, nothing forced); [9,1] with X-generators is the single open p-field test | *unchecked* (short) |\n'
 '| S69.4: RHJ_10 survives every p-field test except possibly [9,1] with X-generators | decision |\n')
s = rep(s, '\n**Open cases (after S51.1).**', '\n' + rows.rstrip('\n') + '\n\n**Open cases (after S51.1).**') if False else s
# insert rows after the S68.5 row
i = s.index('| S68.5:'); j = s.index('\n', i) + 1
s = s[:j] + rows + s[j:]
# Section 4 V_K target
s = rep(s, 'RHJ_10 passes every p-field test except the 3-field type [3,3,3,1] with distinct cubics (S68.3–S68.4); a rational node removes the quintic (S68.1).**',
 'RHJ_10 passes every p-field test except the 3-field type [3,3,3,1] with distinct cubics (S68.3–S68.4); a rational node removes the quintic (S68.1).** **S69: [3,3,3,1] passes (a rational point of V of multiplicity 2 plus a residual plane section of degree 13, S69.1–S69.2); the single open p-field test is [9,1] with X-generators (S69.3).**')
# Section 5
s = rep(s, '- **Session 68:** S68.1',
 '- **Session 69:** S69.1–S69.4 (Section 0at). Over a 3-field a rational point of V of multiplicity prime to 3 gives generators by a residual plane section; P = (1, −1, 0, 0) has multiplicity 2, so [3,3,3,1] passes; [9,1] with X-generators (missed by S68.4) is the remaining p-field test.\n- **Session 68:** S68.1')
s = rep(s, '- **Method lesson (S68):**',
 '- **Method lesson (S69):** (1) **Over a p-field, a rational point of multiplicity prime to p on a variety of degree divisible by p is an input, not an obstruction**: a generic plane through it leaves a residual 0-cycle of degree prime to p, hence a rational point, away from any given proper closed set. A valuation (leading-term) argument that forces solutions to a singular rational configuration proves nothing until the multiplicity there is computed. (2) Compute multiplicities on a complete intersection by the Hessian of the right combination (here Tr y⁵ − (5/3)Tr y³, whose differential vanishes at P) restricted to the tangent space of the smooth part, and confirm with the order of a resultant along random planes. (3) When a session lists cases \"handled\", check each against the exact statement of the test (S68.4 had listed [9,1] for the wrong reason).\n- **Method lesson (S68):**')
# Section 6
s = rep(s, '**Session 68 decision',
 '**Session 69 decision ([3,3,3,1] passes; [9,1] is the open test).** S69.1–S69.2: over every 3-field, a rational point of V of multiplicity 2 (two factors of equal degree 2, 3 or 4) gives smooth generators, so [3,3,3,1] passes. S69.3: [9,1] with X-generators was not treated in S68.4 and is the single open p-field test. **Order now:** (1) rational nonics and decics: the [9,1] test (BR-type valuation analysis of y = (α + βρ + γρ², c) on K9 = M(ρ) over an iterated Laurent 3-field with X-generators, or a proof from an X-generator); if it passes, the covariant search for RHJ_10; the local leftovers via S68.1–S68.2; (2) over P (r = 9): the S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic.\n\n**Session 68 decision')
s = rep(s, '- Session 68: node-line residuals as a ℚ-mechanism',
 '- Session 69: valuation (leading-term) analyses of 3-field types that have a rational point of V of multiplicity prime to 3 (S69.1 settles them); the plane-section residual argument at points of multiplicity divisible by 3 (d = 1 pairs, type-3 nodes).\n- Session 68: node-line residuals as a ℚ-mechanism')
# Section 7
s = rep(s, '- `edit68.py` (this edit and archive script',
 '- `edit68.py` (this edit and archive script')
k = s.index('## 8. Ground rules')
s = s[:k].rstrip('\n') + ('\n\nSession 69 (one directory; numpy, sympy (`pip install --break-system-packages sympy numpy`); nothing is written to disk):\n'
 '- `mult69.py <pattern> <trials> <seed>` (about a minute per trial; foreground with `timeout 110`): pattern = the 10 split coordinates of a rational point of V (e.g. `1,1,1,-1,-1,-1,0,0,0,0`); random integer planes through it, R = Res_t(Tr y³, Tr y⁵), order of R at the point (its multiplicity on V for a generic plane), and the residual points: count, squarefree, generators (distinct coordinates), smoothness (rank of [1, y², y⁴]). Runs: `1,1,1,-1,-1,-1,0,0,0,0 2 1` (order 2, 13 and 13), `… 1 4` (order 2, 13), `1,1,-1,-1,0,0,0,0,0,0 1 3` (order 2, 13), `1,-1,0,0,0,0,0,0,0,0 1 2` (order 3, 12).\n'
 '- `edit69.py` (this edit script; reads `sec0at.md` and the mirror under /mnt/project).\n\n') + s[k:]
s = rep(s, 'Add a Section 0at (session 69; then 0au, …) here', 'Add a Section 0au (session 70; then 0av, …) here')
open('summary69.md', 'w').write(s)

# ---------- Start here ----------
t = rep(t, 'Updated Nov 21, 2026 (after session 68;', 'Updated Nov 21, 2026 (after session 69;')
t = t.replace('next session is 69, Section 0at; session 70 archives Sections 0at and 0au', 'next session is 70, Section 0au; session 70 archives Sections 0at and 0au')
t = rep(t, '## Next step (priority order, after session 68)', '## Next step (priority order, after session 69)')
i = t.index('**Session 68** (the quintic step'); j = t.index('\n', i)
t = t[:i] + ('**Session 69** (the [3,3,3,1] 3-field test; full text in the summary, Section 0at). **Mechanism named:** a rational point of V of multiplicity prime to 3 plus a residual plane section (deg V = 15). **Result:** (S69.1) over a 3-field, any F′-point of V_{E′} of multiplicity m with 3 ∤ m gives smooth generators (generic plane through it: residual of degree 15 − m ≢ 0 mod 3). (S69.2) P = (1, −1, 0, …) has multiplicity 2 when two factors have equal degree d ∈ {2, 3, 4} (d = 1: 3) [numerical, `mult69.py`: order 2, 13 residual generators], so **[3,3,3,1] passes** for any cubic factors. (S69.3) Audit: S68.4 never treated [9,1] with X-generators; there V has no rational singular point and contains the plane cubic {Tr_M(mβ³) = 0} (K9 = M(ρ), ρ³ = m); **[9,1] with X-generators is the single open p-field test of RHJ_10.** (Session 68: RHJ_10 reduction, node-line residuals; summary Section 0 and the 67–68 archive.)') + t[j:]
t = rep(t, '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 68:',
 '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 69: [3,3,3,1] passes (S69.1–S69.2: a rational point of V of multiplicity 2 and a residual plane section); the single open p-field test of RHJ_10 is [9,1] with X(F′) ∋ generators (S69.3). Next: the [9,1] test (BR-type valuation analysis of y = (α + βρ + γρ², c) on K9 = M(ρ), ρ³ = m, over an iterated Laurent 3-field, with m chosen so that X has generators but Tr_M m ≠ 0 and the cubic Tr_M(mβ³) is anisotropic; or a proof from an X-generator); if it passes, the covariant search for RHJ_10; then the local leftovers.** **Session 68:')
t = rep(t, 'Session 68 added: node-line', 'Session 69 added: valuation analyses of 3-field types having a rational point of V of multiplicity prime to 3 (S69.1 settles them); plane-section residuals at points of multiplicity divisible by 3. Session 68 added: node-line')
t = rep(t, '- Session 68 (one directory; numpy, sympy, cypari)',
 '- Session 69 (one directory; numpy, sympy): `mult69.py <pattern> <trials> <seed>` (about a minute per trial; multiplicity of V at a rational point by resultants on random planes, residual generators and smoothness; runs in the summary, Section 7), `edit69.py` (edit script; reads `sec0at.md` and the mirror under /mnt/project).\n- Session 68 (one directory; numpy, sympy, cypari)')
t = rep(t, '**Session 68:** given Hooley IV', '**Session 69:** over every 3-field, [3,3,3,1] passes (a rational point of V of multiplicity 2, residual plane section of degree 13); the open p-field test of RHJ_10 is [9,1] with X-generators. **Session 68:** given Hooley IV')
t = rep(t, '**S68 test a field-independent transfer', '**S69 over a p-field a rational point of multiplicity prime to p on a variety of degree divisible by p gives rational points by a residual plane section; compute the multiplicity before trusting a leading-term obstruction**, **S68 test a field-independent transfer')
open('start69.md', 'w').write(t)
print(len(s), len(t))
for h in re.findall(r'^## .*', s, re.M): print(h[:70])
