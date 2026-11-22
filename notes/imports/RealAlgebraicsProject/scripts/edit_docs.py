# Session 56 end-of-session edits: archive 0af + 0ag, update summary and Start here.
import sys, re
G = {}  # genus placeholders filled from genus.txt
for line in open('genus.txt'):
    k, v = line.rstrip('\n').split('\t', 1)
    G[k] = v
def fill(t):
    for k, v in G.items():
        t = t.replace(k, v)
    return t
def rep(s, old, new, count=1):
    assert s.count(old) >= 1, ("missing", old[:80])
    if count == 1:
        assert s.count(old) == 1, ("not unique", old[:80], s.count(old))
    return s.replace(old, new)

s = open('summary_old.md').read()
sec0ag = fill(open('sec0ag.md').read())
i = s.index('## 0af.'); j = s.index('## 1. The goal')
sec0af = s[i:j]
# ---------- archive ----------
arch = ("# Sessions 55–56: full results (frozen archive)\n\n"
        "Frozen on Nov 20, 2026 (end of session 56). This file holds Section 0af (session 55) exactly as it stood in the condensed summary after session 55, "
        "and Section 0ag (session 56) as written in session 56. **Don't write to it.** The living record is `claude/Condensed summary - plan and progress.md`, "
        "which keeps one line per session in its Section 0 and the Section 3 rows S55.1 … S56.3. Labels S55.1 … S56.4 point here. "
        "(S56.1 confirms S55.2 exactly: Σ → ℓ1 has degree 65 and is irreducible.)\n\n"
        + sec0af.rstrip() + "\n\n" + sec0ag.rstrip() + "\n")
open('archive_55_56.md', 'w').write(arch)
# ---------- summary ----------
s = s[:i] + s[j:]
s = rep(s, '# Condensed summary: plan and progress (through session 55, Nov 19; repo inputs at commit 2536d12 filed Nov 19, Section 1a)',
        '# Condensed summary: plan and progress (through session 56, Nov 20; repo inputs at commit 2536d12 filed Nov 19, Section 1a)')
s = rep(s, 'Nov 19, 2026. This file combines', 'Nov 20, 2026. This file combines')
s = rep(s, 'Eleven frozen archives hold older detail', 'Twelve frozen archives hold older detail')
s = rep(s, "- `claude/Sessions 53-54 results (frozen).md` (this project): the full Sections 0ad and 0ae for sessions 53–54 (labels S53.1 … S54.4), moved out of this file at the end of session 54.\n",
        "- `claude/Sessions 53-54 results (frozen).md` (this project): the full Sections 0ad and 0ae for sessions 53–54 (labels S53.1 … S54.4), moved out of this file at the end of session 54.\n"
        "- `claude/Sessions 55-56 results (frozen).md` (this project): the full Sections 0af and 0ag for sessions 55–56 (labels S55.1 … S56.4), moved out of this file at the end of session 56.\n")
s = rep(s, 'Sessions from 55 on exist only in this file (Section 0af for session 55, 0ag for session 56, and so on).',
        'Sessions from 57 on exist only in this file (Section 0ah for session 57, 0ai for session 58, and so on).')
s = rep(s, '## 0. Sessions 25–55 in brief (full text in the frozen archives; session 55 in Section 0af below)',
        '## 0. Sessions 25–56 in brief (full text in the frozen archives)')
s = rep(s, '- S55 (Section 0af): **quadrilateral residuals (S55.1)**', '- S55 (archive 55–56): **quadrilateral residuals (S55.1)**')
s = rep(s, '- Nov 19 (between sessions 55 and 56): **second repo input**',
        fill('- S56 (archive 55–56): **exact measurement of the quadrilateral curve Σ (S56.1)** with Singular mod p: Σ → ℓ1 has degree exactly 65 and is irreducible (S55.2 confirmed), Σ → ℓ3 65, Σ → P⁴ of 3-spaces 166, deg Σ = 230; GENUS_ONELINE; Theorem G on Σ through natural maps ruled out. Hygiene (S56.3): Singular `int` overflow in numeric constant products gave a false exact-looking count (82).\n')
        + '- Nov 19 (between sessions 55 and 56): **second repo input**')
# Section 3 rows
row_anchor = '| S55.3: real test for r = 5: 41 real quadrilaterals in 9 trials'
k = s.index(row_anchor); k2 = s.index('\n', k) + 1
rows = fill('| S56.1: Σ → ℓ1 (quadrilateral fourth vertices, S55.1) has degree exactly 65 and is irreducible (common subset sums {0, 65} over 18 fibres, two seeds); Σ → ℓ3: 65; Σ → P⁴ of 3-spaces through ⟨ℓ1, ℓ3⟩, projected: 166; deg Σ ⊂ P⁷: 230; no natural map of degree ≤ 8 | [exact mod p] (`irr56.py`, `red56.py`, `lam56.py`, `wdeg.py`) |\n'
            '| S56.2: genus of Σ: GENUS_ROW |\n'
            '| S56.3: Singular evaluates constant subexpressions of polynomial strings in machine ints (silent overflow); keep parameters as ring variables | hygiene |\n')
s = s[:k2] + rows + s[k2:]
s = rep(s, 'the fourth vertices form a curve Σ whose map to ℓ1 has degree 65 (S55.2). |',
        fill('the fourth vertices form a curve Σ whose map to ℓ1 has degree 65 (S55.2), exactly, irreducible; natural maps 65, 65, 166, 230; GENUS_ONELINE (S56). |'))
# Section 4
s = rep(s, 'but Σ → ℓ1 has degree 65 (S55.2).**', fill('but Σ → ℓ1 has degree 65 (S55.2).** **S56: exact (Singular mod p): Σ → ℓ1 is 65 and irreducible, the other natural maps have degrees 65, 166, 230; GENUS_ONELINE.**'))
# Section 5
s = rep(s, '- **Session 54:** S54.1–S54.4 (archive 53–54).',
        fill('- **Session 56:** S56.1–S56.4 (archive 55–56). The quadrilateral curve Σ measured exactly mod p: 65 over ℓ1 (irreducible), 65 over ℓ3, 166 to the P⁴ of 3-spaces, degree 230; GENUS_ONELINE; Theorem G through natural maps ruled out; a Singular integer-overflow trap found.\n')
        + '- **Session 54:** S54.1–S54.4 (archive 53–54).')
s = rep(s, '- **Method lesson (Nov 19, repo input):**',
        '- **Method lesson (S56):** (1) **Exact fibre counts mod p are cheap (under a second per fibre for Σ), curve-level computations are not**: a ramification count by a kernel vector of the Jacobian over a free base parameter needed 24–25 variables and more than 15 minutes and 5 GB in msolve. Reduce first: write the linear conditions as a kernel basis by Cramer (`red56.py`: Q′ in a 4-dimensional kernel, 4 equations left), then take a symbolic determinant instead of kernel variables. Validate the ramification method on a curve of known genus first (`valid56.py`: C_Q, genus 13, degree 12, R = 48). (2) **Look for spurious components over special base points before any curve-level Gröbner run**: here x1 = Q carries a spurious surface, so the base must exclude it (a ≠ 0), and the excluded fibre needs a separate local count in Riemann–Hurwitz for that map; a generic linear projection avoids this. (3) Singular evaluates constant subexpressions in machine ints: never write unreduced numeric products into a polynomial string (S56.3).\n'
        + '- **Method lesson (Nov 19, repo input):**')
# Section 6
s = rep(s, '## 6. Current plan of work (rebuilt after session 40; reoriented Nov 18; items decided in sessions 41–55)',
        '## 6. Current plan of work (rebuilt after session 40; reoriented Nov 18; items decided in sessions 41–56)')
s = rep(s, '\n1. ~~n = 9 certificate for T3~~: done (S25.1).',
        fill('\n**Session 56 decision (Σ measured exactly; Theorem G through natural maps fails).** S56.1: Σ → ℓ1 has degree exactly 65 and is irreducible; the other natural maps have degrees 65, 166, 230; GENUS_DECISION. **Order now:** (1) A_9 r = 5: GENUS_NEXT the S54 candidates (Γ_H; the span fibration of twisted cubics in V_{124}), each with a named mechanism and measured with Singular mod p (fibre counts, then common subset sums); (2) r ∈ {7, 9}: row M2 once the egg family (T5) is written out (ask Arya for its parametrisation), Z_G or an R5 partner with a named mechanism; (3) row E (rational, r = 9); (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic; (6) parked leads as before.\n')
        + '\n1. ~~n = 9 certificate for T3~~: done (S25.1).')
s = rep(s, '- Nov 19 (repo inputs): row G via lines, tangent lines',
        '- Session 56: the natural maps of Σ (to ℓ1, ℓ3, the P⁴ of 3-spaces, linear projections: degrees 65, 65, 166, 230) as Theorem G inputs; random-start fibre counts for Σ (exact now); the 24-variable kernel formulation of ramification in msolve (too heavy; use `red56.py`).\n'
        + '- Nov 19 (repo inputs): row G via lines, tangent lines')
# Section 7
s = rep(s, '\n## 8. Ground rules (revised Nov 17)',
        fill('\nSession 56 (one directory; Python + Singular + msolve from `apt-get update && apt-get install -y singular msolve`; `sing.py` is the Singular runner, keep all files together):\n'
        '- `setup56.py <seed>` (under a second): a random F_p-point Q of V_3 (p = 32003) and two lines of V_3 through Q from F_p-points of C_Q (random hyperplane slices of C_Q, linear factors of the eliminant). Imported by the others through `sigma56.py`.\n'
        '- `sigma56.py`: module (`mk(seed)` gives Q, v1, v3 and random charts; `system(...)` the 10 equations of Σ in (Q′, σ, a) plus the exclusions σ ≠ 0, Q′ ≠ Q, a ≠ 0; `elim_script`). Keep a as a ring variable (S56.3).\n'
        '- `irr56.py <seed> <n>` (about a second per fibre): n random fibres of Σ → ℓ1, vdim, eliminant degree, F_p-factor degrees, common subset sums. Runs: `1 10`, `2 8` (65; {0, 65}).\n'
        '- `wdeg.py <seed>` (about 6 seconds): number of points of Σ on a generic hyperplane of Q′ (230) and over a fixed σ (65). `lam56.py <seed>` (seconds): points of Σ on a generic hyperplane through ⟨ℓ1, ℓ3⟩ (166). `sfib.py <seed>` (seconds): σ-fibres with and without the a ≠ 0 exclusion (65; without it the dimension is 2, the spurious surface over x1 = Q).\n'
        '- `red56.py <seed> <fib a0|wdeg|ramw|rama>`: the reduced model (Q′ = Σ c_j b_j(a, s), b_j by Cramer from the five linear conditions; 4 equations in c1..c4, s, a). `fib` gives 65 in under a second; `wdeg` takes more than 100 seconds; `ramw` (ramification of a generic linear form by the symbolic 6 × 6 determinant) GENUS_REDRUN.\n'
        '- `ram56.py <seed> <a|s|w>` and `export56.py <seed> <a|w>` (writes `ms_<which>_<seed>.in` for msolve): the kernel-vector formulation (24–25 variables). `msolve -f ms_w_1.in -o ms_w_1.out` GENUS_MSRUN.\n'
        '- `valid56.py` (seconds): validation of the kernel ramification count on C_Q (degree 12, genus 13: R = 48).\n'
        '\n## 8. Ground rules (revised Nov 17)'))
# Section 8
s = rep(s, 'Add a Section 0af (session 55; then 0ag, …) here', 'Add a Section 0ah (session 57; then 0ai, …) here')
s = rep(s, '**At the end of session 56, move Sections 0af and 0ag into a new frozen archive `claude/Sessions 55-56 results (frozen).md`.**',
        '**At the end of session 58, move Sections 0ah and 0ai into a new frozen archive `claude/Sessions 57-58 results (frozen).md`.**')
s = rep(s, '`Sessions 51-52 results (frozen).md`, `Sessions 53-54 results (frozen).md`), and don',
        '`Sessions 51-52 results (frozen).md`, `Sessions 53-54 results (frozen).md`, `Sessions 55-56 results (frozen).md`), and don')
open('summary_new.md', 'w').write(s)

# ---------- Start here ----------
t = open('start_old.md').read()
t = rep(t, 'Updated Nov 19, 2026 (after session 55, plus repo inputs at commit 2536d12 filed in the summary\'s Section 1a; next session is 56).',
        'Updated Nov 20, 2026 (after session 56; repo inputs at commit 2536d12 are filed in the summary\'s Section 1a; next session is 57).')
t = rep(t, 'sessions 53–54 (S53.1 … S54.4) in `claude/Sessions 53-54 results (frozen).md`; session 55 (S55.1 … S55.4) only in the summary, Section 0af.',
        'sessions 53–54 (S53.1 … S54.4) in `claude/Sessions 53-54 results (frozen).md`; sessions 55–56 (S55.1 … S56.4) in `claude/Sessions 55-56 results (frozen).md`.')
t = rep(t, 'session 55 is Section 0af, session 56 Section 0ag)', 'session 57 is Section 0ah, session 58 Section 0ai)')
t = rep(t, '`claude/Sessions 51-52 results (frozen).md` or `claude/Sessions 53-54 results (frozen).md`.',
        '`claude/Sessions 51-52 results (frozen).md`, `claude/Sessions 53-54 results (frozen).md` or `claude/Sessions 55-56 results (frozen).md`.')
t = rep(t, '**After session 54 the summary is about 123k characters** and this file about 70k. At the end of session 56, move Sections 0af and 0ag (sessions 55–56) into a new frozen archive `claude/Sessions 55-56 results (frozen).md` the same way, leaving their one-line entries in Section 0, and add that file to the frozen lists here and in the summary (session 54 did this for sessions 53–54 with one Python script: slice the summary at `## 0ad.` and `## 1.`, write the slice plus the new section to the archive, insert the one-line entry, upload both).',
        '**After session 56 the summary is about 145k characters** and this file about 75k. At the end of session 58, move Sections 0ah and 0ai (sessions 57–58) into a new frozen archive `claude/Sessions 57-58 results (frozen).md` the same way, leaving their one-line entries in Section 0, and add that file to the frozen lists here and in the summary (session 56 did this for sessions 55–56 with one Python script, `edit_docs.py`: slice the summary at `## 0af.` and `## 1.`, write the slice plus the new section to the archive, insert the one-line entry, upload both).')
t = rep(t, 'one line per session 25–54 (Section 0), the full results of sessions from 55 on (Section 0af onward)',
        'one line per session 25–56 (Section 0), the full results of sessions from 57 on (Section 0ah onward)')
t = rep(t, '`claude/Sessions 53-54 results (frozen).md` (S53.1 … S54.4).\n',
        '`claude/Sessions 53-54 results (frozen).md` (S53.1 … S54.4), `claude/Sessions 55-56 results (frozen).md` (S55.1 … S56.4).\n')
t = rep(t, '## Next step (priority order, after session 55 and the Nov 19 repo inputs)', '## Next step (priority order, after session 56)')
t = rep(t, '**Sessions 25–55 in one line each:**', '**Sessions 25–56 in one line each:**')
a = t.index('**Session 55** (quadrilateral residual conics in V_3;'); b = t.index('\n', a)
t = t[:a] + fill(open('start_s56.md').read().strip()) + t[b:]
t = rep(t, '1. **A_9 r = 5: a P-point on one of the families of curves through a P-point Q** (conics in V_3, a 4-fold, now also the curve Σ of quadrilateral fourth vertices for two fixed P-lines through Q, S55;',
        fill('1. **A_9 r = 5: a P-point on one of the families of curves through a P-point Q** (conics in V_3, a 4-fold, now also the curve Σ of quadrilateral fourth vertices for two fixed P-lines through Q, S55; **S56: Σ measured exactly: natural maps 65, 65, 166, 230, irreducible; GENUS_ONELINE; Theorem G through natural maps fails**;'))
t = rep(t, 'Candidates: the genus and gonality of Σ (branch count of Σ → ℓ1, now cheap: eliminate to the ℓ1 coordinate in Singular mod p and take the degree of the discriminant, then Riemann–Hurwitz; other maps of Σ, e.g. to the P⁴ of 3-spaces through ⟨ℓ1, ℓ3⟩);',
        fill('Candidates: GENUS_CAND'))
t = rep(t, '2. **r ∈ {7, 9} (S_9 r = 7; totally real nonics, goal 1): no chain of the S48 type exists (S52.1).** **New first step (Nov 19): measure row M2 (Bézier × egg) for a fixed generator with Singular mod p**',
        '2. **r ∈ {7, 9} (S_9 r = 7; totally real nonics, goal 1): no chain of the S48 type exists (S52.1).** **First step: measure row M2 (Bézier × egg) for a fixed generator with Singular mod p; the egg family (T5, rational quartics) is not written out in this project, so ask Arya for its parametrisation first (session 56)**')
t = rep(t, '**S55 list residual classes of known lines on quadric-surface sections before searching for curves directly**.',
        '**S55 list residual classes of known lines on quadric-surface sections before searching for curves directly**, **S56 exact fibre counts mod p are cheap, curve-level ones are not: reduce by Cramer kernels and validate the ramification count on a known curve; exclude spurious components over special base points**.')
t = rep(t, 'In `v3real.py` with r = 7 some Newton points have two coinciding coordinates (min separation 0.0); filter by separation before using a point as a generator of K.',
        'In `v3real.py` with r = 7 some Newton points have two coinciding coordinates (min separation 0.0); filter by separation before using a point as a generator of K. **Session 56: Singular evaluates constant subexpressions of a polynomial string in machine ints, with silent overflow: `((928+22101*(11889)))*((928+22101*(11889)))*y1` is not the product mod p. This produced an exact-looking wrong count (82 instead of 65). Keep parameters as ring variables and add `a - a0` equations, or reduce every constant mod p in Python. `print(std(...))` output has no `_[i]=` labels (parse lines ending in commas). With msolve and Singular both running, memory (8 GB) is the limit: msolve reached 5 GB on 25 variables.**')
t = rep(t, 'Session 55 added: the map Σ → ℓ1 (degree 65)',
        'Session 56 added: the natural maps of Σ (65, 65, 166, 230) as Theorem G inputs; random-start counts where Singular mod p gives exact ones; the 24-variable kernel formulation of ramification. Session 55 added: the map Σ → ℓ1 (degree 65)')
t = rep(t, 'real-feasible for r = 5 (3 of 41), but Σ → ℓ1 has degree 65 with transitive monodromy. Next:',
        fill('real-feasible for r = 5 (3 of 41), but Σ → ℓ1 has degree 65 with transitive monodromy. **Session 56:** Σ measured exactly mod p (65 over ℓ1, irreducible; 65, 166, 230 for the other natural maps); GENUS_ONELINE. Next:'))
t = rep(t, '\n- Sympy is too slow for the Weierstrass resolvent,',
        fill('\n- Session 56 (one directory; Singular, msolve; `sing.py` runner; keep all together): `setup56.py <seed>` (F_p-point Q of V_3 and two lines through it), `sigma56.py` (module: Σ in (Q′, σ, a) with exclusions σ ≠ 0, Q′ ≠ Q, a ≠ 0), `irr56.py <seed> <n>` (fibres of Σ → ℓ1, about a second each; runs `1 10`, `2 8`: 65, common subset sums {0, 65}), `wdeg.py <seed>` (230 and 65, seconds), `lam56.py <seed>` (166), `sfib.py <seed>`, `red56.py <seed> <fib a0|wdeg|ramw|rama>` (reduced 10-variable model; `fib` under a second; GENUS_REDRUN), `ram56.py`/`export56.py` (kernel formulation, 24–25 variables; msolve GENUS_MSRUN), `valid56.py` (method check on C_Q: R = 48).')
        + '\n- Sympy is too slow for the Weierstrass resolvent,')
open('start_new.md', 'w').write(t)
for f in ('summary_new.md', 'start_new.md', 'archive_55_56.md'):
    x = open(f).read()
    print(f, len(x), [h for h in re.findall(r'^## [^\n]*', x, re.M)][:40])
    assert 'GENUS_' not in x, f
