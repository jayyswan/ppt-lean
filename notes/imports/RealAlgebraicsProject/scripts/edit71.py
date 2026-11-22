# edit71.py (session 71, Nov 21): adds Section 0av and updates Sections 0, 1a, 3-8 of the condensed
# summary and the session-specific parts of Start here. Reads the read-only mirror under /mnt/project
# and sec0av.md; writes summary71.md and start71.md in the current directory.
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
T = open('/mnt/project/claude_Start_here.md').read()
sec = open('sec0av.md').read().rstrip('\n') + '\n\n'

def rep(x, a, b):
    assert x.count(a) == 1, (a[:80], x.count(a))
    return x.replace(a, b)

# ---------------- summary: header ----------------
S = rep(S, '(through session 70, Nov 21;', '(through session 71, Nov 21;')

# ---------------- Section 0 one-liner ----------------
k = S.index('- S70 (archive 69–70): **RHJ_10 is false.**'); ke = S.index('\n', k) + 1
line71 = ('- S71 (Section 0av): **offsets do not free I** (a crossing that generates K needs a degree-9 point on the foot cover s² = q_M(E0′(x)), genus 3, or 1 for a metric matched to a non-real critical value of E0′, never 0 for quintic graphs; the B5 incidence is lost: offset degree 18, 54 crossings with a cubic Bézier [exact]) (S71.1); '
          '**lacunary lemma**: on a power curve (x, y) = (c^q, c^p) the crossings are the roots of F(c^q, c^p), so Tschirnhaus varieties are elementary-symmetric vanishing loci; graph partners give nothing new over P in degrees 9, 10 (only T1 and the reciprocal of T2) (S71.2); '
          'power curve × cubic Bézier census: the y³ = x⁴ rows have codimension 3 and reach r = 7 (never 9 in hill-climbs); pattern A is {p1 = p2 = p5 = 0} ∩ {Δ = 0} in 1/c; no P-point source (S71.3); '
          '**decics over ℚ with a nonreal root ↔ ℚ-points of the (2,3) Fano V_3 = {Tr u = Tr u² = Tr u³ = 0}** (x^10 × ℚ-sextic), which fails over the S70.2 3-field (Z123: one closed point of degree 6 [exact]) (S71.4).\n')
S = S[:ke] + line71 + S[ke:]
S = rep(S, '## 0. Sessions 25–70 in brief (full text in the frozen archives)', '## 0. Sessions 25–71 in brief (full text in the frozen archives; session 71 in Section 0av)')

# ---------------- Section 0av ----------------
S = rep(S, '## 1. The goal, the facts and the repo tools', sec + '## 1. The goal, the facts and the repo tools')

# ---------------- Section 1a: toolkit rules (6), (7) note ----------------
S = rep(S, '(about 4 effective dials, Rolle caps not yet computed).',
        '(about 4 effective dials, Rolle caps not yet computed; **measured in S71.3: codimension 3 in the Bézier parameter, reaches r = 7, never 9 in hill-climbs; S71.2: read in c = y/x every power-curve row is lacunary**).')

# ---------------- Section 3 rows ----------------
k = S.index('| S70.4: covariant search dropped;'); ke = S.index('\n', k) + 1
rows = ('| S71.1: for an offset of a P-affine image of the graph of E0 ∈ ℚ[x] (degree m), a crossing that generates K gives a degree-9 point with residue field K on the foot cover C_M: s² = q_M(E0′(x)); for m = 5 genus(C_M) ≥ 1 for every positive definite P-metric, = 1 iff the metric is matched to a non-real critical value of E0′; the offset has degree 18 and meets a cubic Bézier in 54 points; with the matched metric 2 dials face 3 partner conditions; so offsets do not free the B5 invariant I | *unchecked* (short, complete) + [exact] (`offs71.py`) |\n'
        '| S71.2: lacunary lemma: on y^q = x^p, parametrised (c^q, c^p), the crossings with a partner F are the roots of F(c^q, c^p)/c^m, so Ts_c ⊂ {e_{n−e} = 0 for missing exponents e}, with equality for linear partner systems; Descartes: two consecutive missing exponents ⇒ no totally real members; reciprocals: top coefficients are power sums of 1/c; over P with P-quartic graphs only x⁹ = quartic, c⁹ = Q(c²) (reciprocal of the T2 odd engine) and x^10 = quartic occur in degrees 9, 10; over ℚ with ℚ-graphs ≤ 6, degree 10 gives V_3 = {e1 = e2 = e3 = 0} and five general-type lacunary CIs | *unchecked* (elementary) + [numerical] (`lac71.py`) |\n'
        '| S71.3: census of power curve × cubic Bézier (p ≤ 12) in degrees 9, 10: codimension 2 only for 3/1 (D_K) and 3/2 (⊂ fact 5); codimension 3 for those with dy = 2 and for y³ = x⁴ patterns A ((dx, dy) = (2, 3)) and B (transversal through the cusp); pattern A = {p1 = p2 = p5 = 0} ∩ {Δ = 0} in w = 1/c, so r ≤ 7; A, B, C reach 7 real crossings in hill-climbs, never 9; for r = 7 the quadric {p1 = p2 = 0} is Lorentzian, no P-point source | [numerical] (`census71.py`, `lac71.py`) + *unchecked* (identification) |\n'
        '| S71.4: a decic field over ℚ closes with one crossing (x^10 × ℚ-sextic graph) from a ℚ-point u ∉ ℚ of V_3 = {Tr u = Tr u² = Tr u³ = 0} ⊂ P⁸ ((2,3) CI, Fano index 4); smooth real generators for every r ≤ 8, none for r = 10; over the S70.2 3-field V_3 has no point while X has generators (residue scheme Z123: one closed point of degree 6, p⁶ + 88p³ − 80), so no field-independent transfer X_A → V_3 | *unchecked* (short) + [numerical] (`v3dec71.py`) + [exact] (`z123_71.py`) |\n'
        '| S71.5: item (1) of the Nov 21 order closed negatively; power curves add r = 7 engines without a P-point source; next: decics over ℚ via V_3 (nonreal root) and W_K (totally real) with ℚ-arithmetic beyond X_A, then power-curve rows over P whose c-support leaves p1, p2 free | decision |\n')
S = S[:ke] + rows + S[ke:]

# ---------------- open-case table and decics paragraph ----------------
S = rep(S, 'fact 7 does have r = 7 members (S43.1). (Quintic graphs, which would have closed it (S51.3), are not available.) |',
        'fact 7 does have r = 7 members (S43.1). (Quintic graphs, which would have closed it (S51.3), are not available.) **S71.3: the y³ = x⁴ × cubic Bézier rows reach r = 7 with Tschirnhaus varieties of codimension 3 (pattern A = {p1 = p2 = p5 = 0} ∩ {Δ = 0} in 1/c), but have no P-point source.** |')
S = rep(S, '**All five cases are open** (the S49.4 and S50 closures are retracted, S51.1).',
        '**S71.4: decics over ℚ with a nonreal root close with one crossing (x^10 × ℚ-sextic graph) from a ℚ-point of the (2,3) Fano V_3 = {Tr u = Tr u² = Tr u³ = 0} ⊂ P⁸ (index 4, real points for r ≤ 8); V_3 fails over the S70.2 3-field, so a mechanism needs ℚ-arithmetic beyond X_A.** **All five cases are open** (the S49.4 and S50 closures are retracted, S51.1).')

# ---------------- Section 4 ----------------
S = rep(S, '- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}',
        '- **V_3^{(10)} = {Tr u = Tr u² = Tr u³ = 0} ⊂ P(K_ℚ) for decic fields K with a nonreal root (S71.4; power law x^10 × ℚ-sextic graph, over ℚ):** a (2,3) complete intersection 6-fold in P⁸, Fano of index 4; smooth real points for every r ≤ 8; a ℚ-point u ∉ ℚ closes the field with one crossing. No field-independent transfer from X_A(ℚ) (it fails over the S70.2 3-field). No mechanism yet.\n'
        '- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}')
S = rep(S, 'Slices of K: degrees 15, 90, 180, Galois group ⊇ A_90 (S62.3).',
        'Slices of K: degrees 15, 90, 180, Galois group ⊇ A_90 (S62.3). **S71.1: offsets of the quintic do not free I** (a generating crossing needs a degree-9 point on a foot cover of genus ≥ 1, and the B5 incidence is lost).')

# ---------------- Section 5 ----------------
S = rep(S, '- **Session 70:** S70.1–S70.4 (archive 69–70).',
        '- **Session 71:** S71.1–S71.5 (Section 0av). Offsets of the B5 quintic trade the rationality gap for a degree-9 point on a foot cover of genus ≥ 1 (item (1) closed); power curves read in their own coordinate give lacunary (elementary-symmetric) Tschirnhaus varieties: nothing new over P with graph partners, r = 7 engines with Bézier partners (no mechanism); decics over ℚ with a nonreal root reduce to the (2,3) Fano V_3, which fails over the S70.2 3-field.\n'
        '- **Session 70:** S70.1–S70.4 (archive 69–70).')
S = rep(S, '- **Method lesson (S70):**',
        '- **Method lesson (S71):** (1) **Read a power-curve row in the curve\'s own parameter c**, (x, y) = (c^q, c^p): the crossing polynomial is F(c^q, c^p), its support is visible at once, and the Tschirnhaus variety is a lacunary elementary-symmetric locus plus the partner\'s own conditions; two filters are then immediate: Descartes (two consecutive missing exponents ⇒ no totally real members) and reciprocals (vanishing top coefficients are power sums of 1/c). (2) **An offset row always carries a K-point on the foot double cover s² = q(E0′(x))** (the crossing coordinates generate K only together with the foot and the speed): compute that genus first (≥ 1 for quintic graphs in every metric). (3) **The S70 valued 3-field is reusable** for any relative statement \"X-points ⇒ Y-points\" with Y ⊂ X cut by trace forms: replace the last condition and factor the residue scheme over ℚ (here Z123, one point of degree 6). (4) Random real-root sampling badly underestimates a row\'s reach (1500 samples gave 7 real once; hill-climbs reach 7 on most restarts); measure reach by hill-climbing.\n'
        '- **Method lesson (S70):**')

# ---------------- Section 6 ----------------
S = rep(S, '**Nov 21 scope decision (Arya, after session 70).**',
        '**Session 71 decision (offsets closed; power curves read in c; V_3 for decics).** S71.1: offsets of the B5 quintic do not free I (item (1) closed negatively). S71.2–S71.3: power curves give lacunary Tschirnhaus varieties; with graph partners nothing new over P in degrees 9, 10; with Bézier partners the y³ = x⁴ rows reach r = 7 in codimension 3 without a mechanism. S71.4: decics over ℚ with a nonreal root reduce to the (2,3) Fano V_3, which fails over the S70.2 3-field. '
        '**Order now:** (1) decics over ℚ (item (2)): mechanisms for V_3 (nonreal root) and W_K (totally real) that use ℚ-arithmetic beyond X_A (plane cubics on ℚ-planes of the isotropic quadric Tr u² with a forced singular member; cubic forms in ≥ 10 variables mapping to V_3), then the rest of the ℚ-row census by incidence type (eggs, offsets, Bézier × ℚ-graphs); (2) over P (items (3), (5)): power-curve rows whose c-support leaves p1, p2 free and whose other conditions have degree ≤ 8 (eggs, P-quartic graphs and depth-2 offsets as partners, with cusp contact), with the S59 test for each; (3) S_9 r = 7: a P-point source for the y³ = x⁴ rows (V_{125} ∩ {Δ = 0} in 1/c); (4) paused as before (Hasse principle for V_A, W_K local leftovers, S70.4 items).\n\n'
        '**Nov 21 scope decision (Arya, after session 70).**')
S = rep(S, '- Session 70: the covariant search for RHJ_10',
        '- Session 71: offsets of P-affine images of ℚ-quintic (or ℚ-sextic) graphs as a P-dial on the B5 invariant I (S71.1); power curves with graph partners as new engines over P in degrees 9, 10 (S71.2: only T1 and the reciprocal of T2); field-independent transfers X_A(ℚ) → V_3(ℚ) for decics (S71.4); random real-root sampling as a measure of a row\'s reach (hill-climb instead, S71.3).\n'
        '- Session 70: the covariant search for RHJ_10')

# ---------------- Section 7 ----------------
sc7 = ('Session 71 (one directory; cypari, numpy; nothing is written to disk except `census71.log` by redirection and the outputs of `edit71.py`):\n'
       '- `offs71.py` (under a second; cypari): for E0 = x⁵ + 2x⁴ − x³ + 3x² − x: offset degree on a generic line (18), Res_x of the normal and distance equations with a cubic Bézier (degree 54 in t, squarefree), genus of the foot cover for a random metric (3) and for the metric matched to a non-real critical value of E0′ (1; double roots detected with tolerance 10⁻⁶).\n'
       '- `census71.py [nsamples] [pmax] [seed]` (about 10 minutes for `1500 12 1`; run with `timeout 900` and redirect to `census71.log`): power curve y^q = x^p × cubic Bézier patterns (degrees, cusp passages), stripped degree n ∈ {9, 10}, dials, family rank, rank with translations, codimension of Ts_K, random real-root counts (lower bounds only; use `lac71.py reach` for maxima).\n'
       '- `lac71.py lac [seed]` (seconds): charpoly of c = y/x at the crossings for the y³ = x⁴ patterns A and B (vanishing coefficients; top-cube relations for B; Tr(1/c) = Tr(1/c²) = 0 for A). `lac71.py reach <A|B|C> <restarts> <iters> [seed]` (1–3 minutes for `60 1500 2`): hill-climb on the dials for the number of real crossings (A, B, C: maximum 7).\n'
       '- `v3dec71.py [N] [seed]` (about a minute): smooth real generators of V_3 = {Tr u = Tr u² = Tr u³ = 0} in degree 10 for each signature (all r ≤ 8; none for r = 10).\n'
       '- `z123_71.py [lam]` (seconds; cypari): the residue scheme Z123 for k3 = k(λ^{1/3}); λ = 10 gives p⁶ + 88p³ − 80, irreducible.\n'
       '- `edit71.py` (this edit script; reads `sec0av.md` and the mirror under /mnt/project; writes `summary71.md`, `start71.md`).\n\n')
S = rep(S, '\n## 8. Ground rules (revised Nov 17)', '\n' + sc7 + '## 8. Ground rules (revised Nov 17)')

# ---------------- Section 8 ----------------
S = rep(S, 'Add a Section 0av (session 71; then 0aw, …) here', 'Add a Section 0aw (session 72; then 0ax, …) here')

# ================= Start here =================
T = rep(T, 'Updated Nov 21, 2026 (after session 70; repo inputs at commit 2536d12 are filed in the summary\'s Section 1a; next session is 71, Section 0av;',
        'Updated Nov 21, 2026 (after session 71; repo inputs at commit 2536d12 are filed in the summary\'s Section 1a; session 71 is the summary\'s Section 0av; next session is 72, Section 0aw;')
T = rep(T, '## Next step (priority order, after session 70)', '## Next step (priority order, after session 71)')
T = rep(T, '1. **Nov 21 scope decision (Arya, after session 70): unconditional only',
        '1. **Session 71 (summary Section 0av): item (1) closed negatively: offsets of the B5 quintic need a degree-9 point on a foot cover of genus ≥ 1 and lose the B5 structure (S71.1); power curves read in c = y/x give lacunary Tschirnhaus varieties, nothing new over P with graph partners (S71.2); the y³ = x⁴ × Bézier rows reach r = 7 in codimension 3 with no P-point source (S71.3); decics over ℚ with a nonreal root ↔ ℚ-points of the (2,3) Fano V_3 = {Tr u = Tr u² = Tr u³ = 0} (x^10 × ℚ-sextic), which fails over the S70.2 3-field (S71.4). Order now: (1) decics over ℚ: mechanisms for V_3 and W_K using ℚ-arithmetic beyond X_A (plane cubics on ℚ-planes of the isotropic quadric with a forced singular member; cubic forms in ≥ 10 variables), then the rest of the ℚ-row census; (2) over P: power-curve rows whose c-support leaves p1, p2 free and whose extra conditions have degree ≤ 8 (eggs, P-quartic graphs, depth-2 offsets as partners); (3) S_9 r = 7: a P-point source for the y³ = x⁴ rows.** '
        '**Nov 21 scope decision (Arya, after session 70): unconditional only')
i = T.index('**Session 70** (the [9,1] 3-field test;'); j = T.index('(Session 69: [3,3,3,1] passes by a multiplicity-2 residual; 69–70 archive.)', i)
j = j + len('(Session 69: [3,3,3,1] passes by a multiplicity-2 residual; 69–70 archive.)')
p71 = ('**Session 71** (summary Section 0av). **Mechanisms named:** an offset of the B5 quintic as a P-dial on I; power curves (rules (6)–(7)) as new engines. '
       '(S71.1) Offsets do not free I: a crossing that generates K forces its foot point and speed into K, i.e. a degree-9 point on the foot cover s² = q_M(E0′(x)) (genus 3; genus 1 for a metric matched to a non-real critical value of E0′; never 0 for quintic graphs), and the B5 incidence is lost (offset degree 18, 54 crossings with a cubic Bézier [exact, `offs71.py`]). '
       '(S71.2) Lacunary lemma: in the power curve\'s coordinate c, (x, y) = (c^q, c^p), crossings are the roots of F(c^q, c^p), so Tschirnhaus varieties are elementary-symmetric vanishing loci (plus partner conditions); graph partners give only T1 and the reciprocal of T2 over P in degrees 9, 10; Descartes kills r = n when two consecutive exponents are missing. '
       '(S71.3) Census of power curve × cubic Bézier (`census71.py`): the y³ = x⁴ rows have codimension 3 (Bézier parameter) and reach r = 7 in hill-climbs, never 9; pattern A is {p1 = p2 = p5 = 0} ∩ {Δ = 0} in w = 1/c; no P-point source for r = 7 (Lorentzian quadric). '
       '(S71.4) Decics over ℚ with a nonreal root close with one crossing (x^10 × ℚ-sextic) from a ℚ-point of V_3 = {Tr u = Tr u² = Tr u³ = 0} ⊂ P⁸ ((2,3) CI, Fano index 4, real points for r ≤ 8); over the S70.2 3-field V_3 has no point while X has generators (Z123: one closed point of degree 6 [exact]), so no field-independent transfer from Hooley\'s X_A. (Session 70: RHJ_10 is false, 69–70 archive.)')
T = T[:i] + p71 + T[j:]
T = rep(T, 'Session 70 added: the covariant search for RHJ_10',
        'Session 71 added: offsets as a P-dial on the B5 invariant I (S71.1); power curves with graph partners as new engines over P in degrees 9, 10 (S71.2); field-independent transfers X_A → V_3 (S71.4); random real-root sampling as a measure of reach (hill-climb instead, S71.3). Session 70 added: the covariant search for RHJ_10')
T = rep(T, '- Session 70 (one directory; numpy, sympy):',
        '- Session 71 (one directory; cypari, numpy): `offs71.py` (under a second; offset degree 18, 54 crossings with a cubic Bézier, foot-cover genus 3 or 1), `census71.py 1500 12 1` (about 10 minutes, `timeout 900`, redirect to `census71.log`; power curve × cubic Bézier census in degrees 9, 10), `lac71.py lac 1` (seconds; lacunary charpolys in c) and `lac71.py reach <A|B|C> 60 1500 2` (1–3 minutes; real reach by hill-climbing: 7), `v3dec71.py 40 1` (about a minute; real points of V_3 in degree 10 per signature), `z123_71.py 10` (seconds; residue scheme Z123), `edit71.py` (edit script; reads `sec0av.md` and the mirror under /mnt/project). Runs in the summary, Section 7.\n'
        '- Session 70 (one directory; numpy, sympy):')
T = rep(T, '**Session 70:** RHJ_10 is false: over a valued 3-field',
        '**Session 71:** offsets of the B5 quintic do not free I (a degree-9 point on a foot cover of genus ≥ 1); power curves give lacunary Tschirnhaus varieties and new r = 7 engines (y³ = x⁴ × Bézier, codimension 3) without a mechanism; decics over ℚ with a nonreal root reduce to the (2,3) Fano V_3, which fails over the S70.2 3-field. **Session 70:** RHJ_10 is false: over a valued 3-field')
T = rep(T, '**S70 fixed-point tests are only necessary',
        '**S71 read power-curve rows in the curve\'s parameter c (crossings F(c^q, c^p): lacunary supports, Descartes and reciprocal filters at once); every offset row carries a K-point on the foot double cover (compute its genus first); reuse the S70 valued 3-field for any relative \"X ⇒ Y\" test (factor the residue scheme over ℚ); measure real reach by hill-climbs, not random samples**, **S70 fixed-point tests are only necessary')

open('summary71.md', 'w').write(S); open('start71.md', 'w').write(T)
import re
print('summary', len(S), 'start', len(T))
print([l for l in S.split('\n') if l.startswith('## ')])
