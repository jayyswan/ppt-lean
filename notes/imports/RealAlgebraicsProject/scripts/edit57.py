import re
def rep(s, old, new):
    assert s.count(old) == 1, ("count", s.count(old), old[:90])
    return s.replace(old, new)
s = open('s57_sum_old.md').read()
sec = open('sec0ah.md').read().rstrip() + "\n\n"
s = rep(s, '(through session 56, Nov 20;', '(through session 57, Nov 20;')
s = rep(s, '## 0. Sessions 25–56 in brief (full text in the frozen archives)', '## 0. Sessions 25–57 in brief (full text in the frozen archives; session 57 in Section 0ah below)')
s = rep(s, '- Nov 19 (between sessions 55 and 56): **second repo input**',
 '- S57 (Section 0ah): **row M2 (Bézier × egg) measured** with Arya\'s egg parametrisation: for a fixed generator the condition is χ_τ | Z² − R(1 − R)(1 + e − eR)² (R, Z cubics, e = d1/d0) (S57.1); ≥ 181 solutions modulo θ ↦ −θ, not a step (S57.2); **real solutions for r = 7 exist, also with genuine eggs** (S57.3); r = 9 only with nodal eggs (D vanishing on the egg; allowed? question for Arya).\n'
 + '- Nov 19 (between sessions 55 and 56): **second repo input**')
k = s.index('## 1. The goal'); s = s[:k] + sec + s[k:]
s = rep(s, "- **Row M2: Bézier × egg** (D0 §2, §4; egg = T5): for a fixed generator, finitely many solutions; all dials in P; up to 8 real crossings found, so **it may reach S_9 r = 7**, where only fact 7 is known. The size of that finite set was never measured; the cap 8 is heuristic (egg convexity).",
 "- **Row M2: Bézier × egg** (D0 §2, §4; egg = T5): for a fixed generator, finitely many solutions; all dials in P; up to 8 real crossings found, so **it may reach S_9 r = 7**, where only fact 7 is known. The size of that finite set was never measured; the cap 8 is heuristic (egg convexity). **Egg (Arya, Nov 20; repo `eggCurve`, Pptc/Warp/Bilinear.lean:172, image of a glyph circle under the height-cell warp):** a²(D(x) − 2y)² = D(x)²·x·(2a − x), D(x) = d0 + d1x, x ≥ 0; a rational quartic of genus 0, quadratic in y (a double cover of the x-line). Five P-parameters (WARP.md:80, :124): shape d0 : d1 (the Triangle handle, the only shape modulus) and placement l (x-position), w (x-scale), y0 (y-position), the height D (y-scale); census form u = (x − l)/w, D = d0 + d1u, E = 4u(1 − u), crossing with y = P(x): N = (D − 2(P − y0))² − D²E. Parametrisation (W4-offset.md:33, a = ½, x ∈ [0, 1]): x = t²/(1 + t²), D(t) = (d0 + (d0 + d1)t²)/(1 + t²), y = D(t)(t − 1)²/(2(1 + t²)); t ≥ 0 lower branch, t ≤ 0 upper (the same formula covers both). **Measured in session 57 (S57.1–S57.3).**")
row_anchor = '| S56.3: Singular evaluates constant subexpressions'
k = s.index(row_anchor); k2 = s.index('\n', k) + 1
s = s[:k2] + ('| S57.1: row M2 (Bézier × egg) for a fixed generator τ ⇔ χ_τ \\| Z² − R(1 − R)(1 + e − eR)² with R, Z cubics, e = d1/d0 (r = 1/(1 + θ²) = R(τ), θ the egg parameter); solutions paired by θ ↦ −θ | *unchecked* (short algebra) |\n'
 '| S57.2: that scheme has ≥ 181 points modulo the pairing (12,000 starts, still growing); not a step | [numerical] (`m2num.py`; lower bound) |\n'
 '| S57.3: real M2 solutions for r = 7 exist, some with D > 0 on the egg (e = 0.450, −0.816, −0.823); for r = 9 only with D vanishing on the egg (nodal); r = 5 found | [numerical] (`m2real.py`) |\n') + s[k2:]
s = rep(s, "Engine O has no r = 7 members (S39.3), so it can never serve this case (S41.1);",
 "Engine O has no r = 7 members (S39.3), so it can never serve this case (S41.1); **row M2 (Bézier × egg) has real r = 7 members with genuine eggs (S57.3), but its fixed-generator scheme has ≥ 181 points (S57.2)**;")
s = rep(s, "- **Row M2 (Bézier × egg, unmeasured, Section 1a):** finitely many solutions for a fixed generator, P dials, up to 8 real crossings, so possibly S_9 r = 7. First step: its count (Singular mod p).",
 "- **Row M2 (Bézier × egg, Section 1a; measured in S57):** for a fixed generator, χ_τ | Z² − R(1 − R)(1 + e − eR)² (S57.1); ≥ 181 solutions modulo θ ↦ −θ (S57.2); real r = 7 solutions with genuine eggs exist (S57.3). A P-point needs a mechanism (two-stage form: a square condition for θ, then linear algebra).")
s = rep(s, '- **Session 56:** S56.1–S56.4 (archive 55–56).',
 '- **Session 57:** S57.1–S57.4 (Section 0ah). Row M2 measured with the egg from the repo: a degree-12 crossing condition with a sign pairing, ≥ 181 solutions for a fixed generator, real r = 7 solutions with genuine eggs.\n- **Session 56:** S56.1–S56.4 (archive 55–56).')
s = rep(s, '- **Method lesson (Nov 19, repo input):**',
 '- **Method lesson (S57):** (1) **Use the curve\'s rational parametrisation to turn a crossing condition into a divisibility χ_τ | (polynomial in a few cubics)**, and look for coefficients that drop out (here Z² has degree 6 < 9, so two equations involve R and e only). (2) Random-start Newton on such systems lands mostly on spurious families (R constant, special e); filter by nondegeneracy and a nonsingular Jacobian before counting. (3) For dense 9 × 9 systems of degree up to 6, neither Singular nor msolve finished in 5–12 minutes; start exact counts in the background at the beginning of a session.\n- **Method lesson (Nov 19, repo input):**')
s = rep(s, 'items decided in sessions 41–56)', 'items decided in sessions 41–57)')
s = rep(s, '\n1. ~~n = 9 certificate for T3~~: done (S25.1).',
 '\n**Session 57 decision (row M2 measured).** S57.1: the M2 condition for a fixed generator is χ_τ | Z² − R(1 − R)(1 + e − eR)²; S57.2: ≥ 181 solutions modulo θ ↦ −θ; S57.3: real r = 7 solutions with genuine eggs. **Order now:** (1) r = 7 (S_9) and r = 9: a P-mechanism for M2 (the two-stage form: θ ∈ K with 1/(1 + θ²) ∈ W4 is a square condition; a P-rational family inside it would leave linear algebra), or for Z_G; the exact M2 count and monodromy mod p as a background run; ask Arya whether nodal eggs (D vanishing on the egg) are allowed; (2) A_9 r = 5: as in the session 56 order (Γ_H, span fibration, genus of Σ in the background); (3) row E; (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic; (6) parked leads as before.\n'
 + '\n1. ~~n = 9 certificate for T3~~: done (S25.1).')
s = rep(s, '- Session 56: the natural maps of Σ',
 '- Session 57: M2 for a fixed generator as a finite step (≥ 181 modulo sign); random-start counts of M2 without the nondegeneracy filter (spurious families dominate).\n- Session 56: the natural maps of Σ')
s = rep(s, '\n## 8. Ground rules (revised Nov 17)',
 '\nSession 57 (one directory with `sing.py`; numpy; Singular and msolve):\n'
 '- `m2num.py <seed> <starts> [maxprint]` (about 0.008 seconds per start; 12,000 starts in about 100 seconds): complex Newton for the M2 system χ_τ | Z² − R(1 − R)(1 + e − eR)² at a generic complex τ; distinct nondegenerate solutions modulo Z ↦ −Z every 2000 starts, then the Jacobian singular values of the first ones. Run `1 12000` (181).\n'
 '- `m2real.py <seed> <starts> <r>` (execs the header of `m2num.py`, keep them together; about 15 seconds per 1000 starts): τ with r real conjugates, real Newton, distinct real nondegenerate solutions and their e. Runs `3 2500 7` (0), `4 6000 7` (30), `5 6000 7` (15), `3 2500 9` (5, all e < −1), `3 2500 5` (2).\n'
 '- `m2red.py <seed> count [p] [n]` (Singular) and `m2ms.py <seed> [p] [timeout]` (msolve): exact count of the same system mod p (10 variables with q1 ≠ 0); neither finished (Singular > 2 minutes, msolve > 12 minutes at 1.9 GB); run in the background. `m2count.py` is the first, 20-variable form (also too slow).\n'
 '\n## 8. Ground rules (revised Nov 17)')
s = rep(s, 'Add a Section 0ah (session 57; then 0ai, …) here', 'Add a Section 0ai (session 58; then 0aj, …) here')
open('s57_sum_new.md', 'w').write(s)

t = open('s57_start_old.md').read()
t = rep(t, 'Updated Nov 20, 2026 (after session 56;', 'Updated Nov 20, 2026 (after session 57;')
t = rep(t, 'next session is 57).', 'next session is 58).')
t = rep(t, 'S56.4) in `claude/Sessions 55-56 results (frozen).md`. **Session 51', 'S56.4) in `claude/Sessions 55-56 results (frozen).md`; session 57 (S57.1 … S57.4) only in the summary, Section 0ah. **Session 51')
t = rep(t, 'session 57 is Section 0ah, session 58 Section 0ai)', 'session 57 is Section 0ah, session 58 Section 0ai; session 58 also moves 0ah and 0ai to the 57–58 archive)')
t = rep(t, '## Next step (priority order, after session 56)', '## Next step (priority order, after session 57)')
t = rep(t, '**Sessions 25–56 in one line each:**', '**Sessions 25–57 in one line each:**')
a = t.index('**Session 56** (exact measurement'); b = t.index('\n', a)
t = t[:a] + ('**Session 57** (row M2, Bézier × egg; full text in the summary, Section 0ah). Arya supplied the egg (repo `eggCurve`: a²(D(x) − 2y)² = D(x)²x(2a − x), D = d0 + d1x; parametrisation x = t²/(1 + t²), y = D(t)(t − 1)²/(2(1 + t²)); filed in the summary, Section 1a, G1a.7). **Mechanism tested:** the Bézier × egg crossing at a generator τ as a finite P-scheme (step if ≤ 8 or split). **Results:** (S57.1) for a fixed generator the condition is **χ_τ | Z² − R(1 − R)(1 + e − eR)²** (R, Z cubics, e = d1/d0, r = 1/(1 + θ²) = R(τ)), solutions paired by θ ↦ −θ; (S57.2, `m2num.py`) **≥ 181 solutions modulo the pairing**, still growing: not a step; (S57.3, `m2real.py`) **real solutions for r = 7 exist, also with genuine eggs (e = 0.450, −0.816, −0.823)**; r = 9 only with nodal eggs (e < −1). Exact counts (Singular, msolve) did not finish. **Question for Arya:** are nodal eggs (D vanishing on the egg) allowed?') + t[b:]
t = rep(t, '2. **r ∈ {7, 9} (S_9 r = 7; totally real nonics, goal 1): no chain of the S48 type exists (S52.1).** **First step: measure row M2 (Bézier × egg) for a fixed generator with Singular mod p; the egg family (T5, rational quartics) is not written out in this project, so ask Arya for its parametrisation first (session 56)**',
 '2. **r ∈ {7, 9} (S_9 r = 7; totally real nonics, goal 1): no chain of the S48 type exists (S52.1).** **Session 57: row M2 measured (egg from Arya): real r = 7 solutions with genuine eggs exist, but ≥ 181 solutions per generator; next a P-mechanism for it (two-stage form: θ ∈ K with 1/(1 + θ²) ∈ W4, a square condition, then linear algebra), and its exact count/monodromy as a background run (`m2ms.py`); ask Arya whether nodal eggs are allowed (r = 9). Earlier first step, now done:** measure row M2 (Bézier × egg) for a fixed generator')
t = rep(t, '**S56 exact fibre counts mod p are cheap,', '**S57 turn crossings into a divisibility χ_τ | (polynomial in a few cubics) via the curve\'s parametrisation, filter spurious families before counting**, **S56 exact fibre counts mod p are cheap,')
t = rep(t, 'Session 56 added: the natural maps of Σ', 'Session 57 added: M2 for a fixed generator as a finite step (≥ 181). Session 56 added: the natural maps of Σ')
t = rep(t, '\n- Sympy is too slow for the Weierstrass resolvent,',
 '\n- Session 57 (one directory with `sing.py`; numpy): `m2num.py <seed> <starts>` (complex Newton for the M2 system, 12,000 starts in about 100 seconds; run `1 12000`: 181), `m2real.py <seed> <starts> <r>` (execs the header of `m2num.py`; real solutions; runs `4 6000 7`: 30, `5 6000 7`: 15, `3 2500 9`: 5), `m2red.py`, `m2ms.py` (exact count mod p by Singular / msolve; did not finish, run in the background), `m2count.py` (20-variable form, too slow).'
 + '\n- Sympy is too slow for the Weierstrass resolvent,')
open('s57_start_new.md', 'w').write(t)
for f in ('s57_sum_new.md', 's57_start_new.md'):
    x = open(f).read(); print(f, len(x), re.findall(r'^## 0a[a-z]\.[^\n]*', x, re.M))
