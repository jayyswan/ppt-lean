# Session 63: edit the condensed summary and Start here.md (reads sec0an.md and the /mnt/project mirror).
import re, sys
SUM = '/mnt/project/claude_Condensed_summary_-_plan_and_progress.md'
SH = '/mnt/project/claude_Start_here.md'
s = open(SUM).read(); L0 = len(s)
sec = open('sec0an.md').read().strip() + '\n\n'

def rep(old, new, count=1):
    global s
    assert s.count(old) >= 1, ('missing', old[:80])
    s = s.replace(old, new, count)

rep('(through session 62, Nov 20;', '(through session 63, Nov 20;')
rep('## 0. Sessions 25–62 in brief (full text in the frozen archives)',
    '## 0. Sessions 25–63 in brief (full text in the frozen archives; session 63 in Section 0an below)')
# one-line entry after the S62 line
i = s.index('- S62 (archive 61–62):'); j = s.index('\n', i)
line63 = ('\n- S63 (Section 0an): **I = −(8/45)γ², γ the skewness of the ten y_i²** (S63.1); the bound I ≥ −2/5 is |γ| ≤ 3/2, '
          'attained only at pairing configurations, so candidate (d) is dead (S63.2). **Over ℚ row B5 has no rationality gap:** a ℚ-point of '
          '**V_K = {Tr u³ = (Tr u)³, Tr u⁵ = (Tr u)⁵} ⊂ P(K_ℚ)**, a (3,5) complete intersection in P⁸, **Fano of index 1**, closes the rational nonic '
          'with one crossing (S63.3; planted totally real S_9 member); decics likewise with W_K = {Tr u = Tr u³ = Tr u⁵ = 0} ⊂ P⁹, real points for every '
          'signature (S63.4). **V_K is everywhere locally soluble for the PSL(2,8) r = 9 test field and the S_9 control** (Hensel at 2, 3, 5; '
          'smooth F_p-points for all other p ≤ 10⁶; Lang–Weil above, *unchecked*) (S63.5). Gap for scope (i): the Hasse principle for V_K '
          '(Colliot-Thélène\'s conjecture for smooth CIs; V_K is singular along pairing curves) or an explicit ℚ-point construction.')
s = s[:j] + line63 + s[j:]
# Section 0an before Section 1
rep('## 1. The goal, the facts and the repo tools', sec + '## 1. The goal, the facts and the repo tools')
# Section 3 rows
i = s.index('| S62.4: linear and planar P-families of row B5 ruled out'); j = s.index('\n', i)
rows = '''
| S63.1: B3 = −(5/2)σ², B2 = −(5/3)μ3 for the ten values V_i = y_i², so I = −(8/45)γ² with γ their skewness; I ∈ ℚ ⇔ γ² ∈ ℚ | [exact] (`b5q.py`) |
| S63.2: on real {p1 = p3 = p5 = 0} ⊂ ℝ^10 the maximum of γ² is 9/4 (I = −2/5), attained at the pairing configurations (±a, ±b ×4) only; no nondegenerate local maxima | [numerical] (`skew63.py 150 1`: 148 of 148 converged maxima) |
| S63.3: over ℚ, u ∈ K_ℚ ∖ ℚ on V_K = {Tr u³ = (Tr u)³, Tr u⁵ = (Tr u)⁵} gives (w + Tr u)χ_u = E(w²) + R(w) over ℚ and a one-crossing construction (Bézier (t², −R(t)) × ℚ-quintic graph y = E(x)); V_K is a (3,5) CI in P⁸, dim 6, K = O(−1) (Fano index 1); the B5 family over ℚ contains totally real S_9 nonics (planted g = 6000w⁹ + 18000w⁸ − …) | [exact] + [numerical] (`plant63.py`) + *unchecked* (canonical-class comparison with rows E, G) |
| S63.4: decics over ℚ: a ℚ-point of W_K = {Tr u = Tr u³ = Tr u⁵ = 0} ⊂ P⁹ ((1,3,5) CI, Fano index 1) closes a primitive decic field with one crossing, no auxiliary point; smooth real points with distinct unpaired coordinates for every signature r = 0, …, 10 | *unchecked* (short) + [numerical] (`dec63.py 10 40 1`) |
| S63.5: V_K is everywhere locally soluble for the PSL(2,8) r = 9 test field and the S_9 control: ℚ_2, ℚ_3, ℚ_5 by Hensel (F3 ≡ 0 mod 3, F5 ≡ 0 mod 5 on unramified residue algebras, so smooth points mod 3, 5 never exist), smooth F_p-points for all other p ≤ 10⁶ including every ramified prime, Lang–Weil (Cafure–Matera, δ = 15) for p ≥ 8.5·10⁵ | [exact mod p] + Hensel (`locplane63.py`, `loc63.py`) + *unchecked* (Lang–Weil step, geometric integrality of V̄ mod p for p ≥ 7) |
| S63.6: for scope (i) the r = 9 (and decic) gap is a ℚ-point on a twisted Fano 6-fold, everywhere locally soluble on the test fields; conditional on the Hasse principle for (a desingularisation of) V_K the test fields close; over P the S62 gap is unchanged | decision |'''
s = s[:j] + rows + s[j:]
# open-case table
rep('| PSL(2,8), r = 9 | **open** | **open** |',
    '| PSL(2,8), r = 9 | **open**; S63: a ℚ-point on the Fano 6-fold V_K suffices (one crossing, row B5 over ℚ), and V_K is everywhere locally soluble for the test field (S63.5) | **open** |')
rep('| A_9, r = 9 | **open** | **open**;', '| A_9, r = 9 | **open**; S63: as for PSL(2,8) r = 9 (ℚ-point on V_K; ELS for the S_9 control, which is A_9 over P) | **open**;')
rep('**Decics (S49.1, S51.1).** ', '**Decics (S49.1, S51.1, S63.4).** Over ℚ (S63.4): a ℚ-point on the Fano 6-fold W_K = {Tr u = Tr u³ = Tr u⁵ = 0} closes a primitive decic field with one crossing (Bézier (t², cubic) × ℚ-quintic graph); real points exist for every signature. ')
# Section 4 target
i = s.index('- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}')
tgt = ('- **V_K = {u ∈ P(K_ℚ) : Tr u³ = (Tr u)³, Tr u⁵ = (Tr u)⁵} (S63.3; rational nonics, scope (i)) and W_K = {Tr u = Tr u³ = Tr u⁵ = 0} (S63.4; decics over ℚ):** '
       'twisted (3,5) and (1,3,5) complete intersections, Fano 6-folds of index 1. A **ℚ-point** (u ∉ ℚ) closes the field with one crossing of rational curves, '
       'no rationality gap. V_K is everywhere locally soluble for both test fields (S63.5). Singular along the pairing curves. No unconditional theorem gives ℚ-points '
       '((3,5) in 9 variables); the Hasse principle for these is conjectural (Colliot-Thélène, for smooth CIs of dimension ≥ 3).\n')
s = s[:i] + tgt + s[i:]
rep('- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}, I0 ∈ ℚ ∩ (−2/5, 0] (row B5, S62; ℚ-quintic graph, all dials P):**',
    '- **Ω_{I0} = L_135 ∩ {B2² = I0·B3³}, I0 ∈ ℚ ∩ (−2/5, 0] (row B5, S62; ℚ-quintic graph, all dials P; S63.1: I = −(8/45)γ², γ the skewness of the y_i²):**')
# Section 5
i = s.index('- **Session 62:** S62.1–S62.4');
s = s[:i] + ('- **Session 63:** S63.1–S63.6 (Section 0an). I is a squared skewness; its extremum is degenerate; over ℚ row B5 has no rationality gap and its incidence V_K '
             '(and W_K for decics) is a Fano 6-fold, everywhere locally soluble for the test fields; the open step for scope (i) is a ℚ-point on V_K.\n') + s[i:]
i = s.index('- **Method lesson (S62):**')
s = s[:i] + ('- **Method lesson (S63):** (1) **Before fighting a rationality gap over P, ask whether the target scope is over ℚ**: for rational nonics every '
             'invariant of the forced curve is rational at a ℚ-point, so the gap is replaced by a ℚ-point problem, and what matters is the canonical class of the '
             'over-ℚ incidence (weighted CI count: Σ condition weights against Σ variable weights). Row B5 gives K = O(−1), row E O(1), row G O(9). '
             '(2) **Write affine invariants of the forced curve as moments** of the crossing data (here I = −(8/45)·skewness²): extremal values then come from '
             'two-point distributions, i.e. degenerate configurations. (3) **Local solubility at all p is cheap**: plane sections mod p with a unit Jacobian minor '
             'run at about 100 primes per second up to 10⁶, Lang–Weil (Cafure–Matera) covers the rest; but Tr(a^p) = Tr(a) makes F_p ≡ 0 mod p identically for '
             'p = 3, 5 on unramified residue algebras, so use p-adic Hensel (v(F) ≥ 2m + 1) there.\n') + s[i:]
# Section 6: decision and Dropped
i = s.index('**Session 62 decision (row B5: one rational condition on L_135).**')
dec = ('**Session 63 decision (row B5 over ℚ: a Fano target for the rational degree bound).** S63.1–S63.2: I = −(8/45)γ²; candidate (d) dead. '
       'S63.3–S63.5: for rational nonics the row-B5 condition is a ℚ-point on the twisted Fano (3,5) complete intersection V_K, everywhere locally soluble for both '
       'test fields; decics over ℚ likewise (W_K). **Order now:** (1) rational nonics and decics (the near-term target): a construction of ℚ-points on V_K / W_K '
       '(odd-Tschirnhaus chain over ℚ with Meyer at the quadric step; a variant whose last step is linear; conics on V_K through a point; fibrations with fibres '
       'satisfying the Hasse principle), the Brauer group of a desingularisation of V_K, local solubility uniformly in K, and a primitive totally real decic test '
       'field for W_K; (2) over P (r = 9): the remaining S62.4 items (a), (b), (c), (e) and G3_S; (3) r = 7: M2 with a chosen generator, Z_G / R5; (4) A_9 r = 5: '
       'the S54 candidates; (5) decics over P via V_5 only with a new mechanism; (6) osculation and ℚ-arithmetic (now item (1) for scope (i)).\n\n')
s = s[:i] + dec + s[i:]
i = s.index('- Session 62: linear and planar slices of K for row B5')
s = s[:i] + ('- Session 63: the extremal configurations of I (pairing, S63.2); naive or fibred height searches for ℚ-points on V_K (σ·H with tiny σ, S63.5); '
             'plane-section local checks at p = 3, 5 (F3 ≡ 0 mod 3, F5 ≡ 0 mod 5 identically; use `loc63.py`); imprimitive decics as test fields (they have '
             'subfields; e.g. ∏(x − a) + 1 for A = {−10, −7, −5, −2, 0, 1, 3, 6, 8, 11} has a quintic subfield).\n') + s[i:]
# Section 7 scripts
i = s.index('## 8. Ground rules (revised Nov 17)')
scr = ('Session 63 (one directory; sympy, numpy, scipy, cypari; nothing else installed):\n'
       '- `b5q.py` (seconds; sympy): B3 = −(5/2)σ², B2 = −(5/3)μ3, I = −(8/45)γ²; 10-point check of p3 against the w⁷ coefficient.\n'
       '- `skew63.py <starts> <seed>` (about a minute for 150; scipy SLSQP): maxima of γ² on real {p1 = p3 = p5 = 0} ⊂ ℝ^10, structure of the maximisers (run `150 1`).\n'
       '- `plant63.py <seed> [den]` (seconds; cypari): a rational member of the B5 family from a rounded real point (E, R, ζ rational, E(ζ²) + R(ζ) = 0 exactly), '
       'irreducibility, real roots, Frobenius types, the V_K check (run `1 2000`: the totally real S_9 nonic of S63.3).\n'
       '- `dec63.py <n> <N> <seed>` (seconds): real points of {p1 = p3 = p5 = 0} in ℝ^r × ℂ^s for every r ≡ n mod 2 (run `10 40 1`, `9 20 2`).\n'
       '- `locplane63.py <psl|s9|plant|poly> <pmin> <pmax> [extra primes|-] [dec]` (about 100–200 primes per second; PARI `nfinit([f, listP])`, F3, F5 as '
       'integer forms in an integral basis; random F_p-planes, resultant, unit 2 × 2 Jacobian minor): smooth F_p-points of V_K (or W_K with `dec`); prints FAIL '
       'for primes without one on 12 planes (always 3 and 5, by design). Runs: `psl 2 200 3,37,2977717`, `psl 200 30000 -`, `psl 30000 1000000 -`, '
       '`s9 2 200 5,2897,2192761,4172210359447267,1200747702100008604489847184402079`, `s9 200 30000 -`, `s9 30000 1000000 -` (no failures besides 3, 5). '
       'The `dec` mode with a composite cofactor in the prime list hangs in `nfinit`; factor the discriminant first.\n'
       '- `loc63.py <psl|s9|plant|poly> <pmax> [samples] [non|dec]` (seconds to a minute; numpy mod p^N with N maximal for p^N ≤ 10⁸, structure constants of '
       'the order from PARI): p-adic Hensel search (a 2 × 2 minor of valuation m and v(F3), v(F5) ≥ 2m + 1); use it for p = 2, 3, 5 (runs `psl 5 30000`, '
       '`s9 5 30000`, `plant 30 3000` and `plant 3 30000` for validation).\n'
       '- `edit63.py` (this edit script; reads `sec0an.md`).\n\n')
s = s[:i] + scr + s[i:]
# Section 8: next session section number
rep('Add a Section 0an (session 63; then 0ao, …) here', 'Add a Section 0ao (session 64; then 0ap, …) here')
open('summary63.md', 'w').write(s)
print('summary', L0, '->', len(s))
print([h for h in re.findall(r'^## [^\n]*', s, re.M)])

# ---------------- Start here.md ----------------
t = open(SH).read(); T0 = len(t)
def rept(old, new):
    global t
    assert old in t, ('SH missing', old[:80])
    t = t.replace(old, new, 1)
rept('Updated Nov 20, 2026 (after session 62;', 'Updated Nov 20, 2026 (after session 63;')
rept('next session is 63, Section 0an; session 64 archives Sections 0an and 0ao)', 'next session is 64, Section 0ao; session 64 archives Sections 0an and 0ao into `claude/Sessions 63-64 results (frozen).md`)')
rept('## Next step (priority order, after session 62)', '## Next step (priority order, after session 63)')
# session paragraph: replace the session 62 paragraph by a session 63 one (62 lives in the archive)
i = t.index('**Session 62** (row B5: Bézier × ℚ-quintic graph;'); j = t.index('\n', i)
p63 = ('**Session 63** (row B5 over ℚ; full text in the summary, Section 0an). **Mechanism tested:** for rational nonics take the row-B5 point over ℚ, '
       'where the forced quintic is rational automatically. **Results:** (S63.1, [exact] `b5q.py`) I = −(8/45)γ², γ the skewness of the ten y_i²; '
       '(S63.2, `skew63.py`) the bound I ≥ −2/5 is attained only at pairing configurations: candidate (d) dead; (S63.3, `plant63.py`) **a ℚ-point of '
       'V_K = {Tr u³ = (Tr u)³, Tr u⁵ = (Tr u)⁵} ⊂ P(K_ℚ) closes the rational nonic with one crossing**; V_K is a (3,5) complete intersection in P⁸, '
       '**Fano of index 1**; the family has totally real S_9 members over ℚ; (S63.4, `dec63.py`) decics over ℚ: W_K = {Tr u = Tr u³ = Tr u⁵ = 0}, Fano, '
       'real points for every signature; (S63.5, `locplane63.py`, `loc63.py`) **V_K is everywhere locally soluble for the PSL(2,8) r = 9 test field and the '
       'S_9 control** (Hensel at 2, 3, 5; smooth points mod p for all other p ≤ 10⁶; Lang–Weil above, *unchecked*). The gap for scope (i) is now the Hasse '
       'principle for V_K (conjectural; V_K is singular along pairing curves) or an explicit ℚ-point construction. (Session 62: row B5 over P, the I-gap on '
       'L_135, slices 15 / 90 / 180 with ⊇ A_90; archive 61–62, Section 0am.)')
t = t[:i] + p63 + t[j:]
# priority 1 text: prepend the over-Q item
rept('1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** ',
     '1. **Rational nonics and A_9 / PSL(2,8) r = 9 (the near-term target).** **Session 63: over ℚ row B5 has no rationality gap.** For a nonic field K_ℚ, '
     'a ℚ-point u ∉ ℚ of **V_K = {Tr u³ = (Tr u)³, Tr u⁵ = (Tr u)⁵}** (a (3,5) complete intersection in P⁸, Fano of index 1) gives '
     '(w + Tr u)χ_u = E(w²) + R(w) over ℚ and the roots by one crossing (Bézier (t², −R(t)) × ℚ-quintic graph y = E(x)); decics: '
     'W_K = {Tr u = Tr u³ = Tr u⁵ = 0}. V_K is everywhere locally soluble for both test fields (S63.5). **Next for scope (i):** a construction of ℚ-points '
     'on V_K / W_K (odd-Tschirnhaus chain over ℚ with Meyer at the quadric step, failing only at a (2,3) Fano 4-fold point and a rational quintic root: '
     'look for a variant whose last step is linear; conics on V_K through a point; fibrations with Hasse-principle fibres), the Brauer group of a '
     'desingularisation of V_K, local solubility uniformly in K, a primitive totally real decic test field for W_K. Naive height searches are hopeless '
     '(σ·H with tiny σ). Over P (scope (ii)) the S62 items below stand, with I = −(8/45)γ² and (d) dead. ')
# method lessons list
rept('**S62 list every graph degree the rules allow', '**S63 before fighting a rationality gap over P, check whether the target scope is over ℚ (then compare canonical classes of the over-ℚ incidences); write affine invariants as moments; local solubility by plane sections mod p plus Hensel at 3, 5 (Tr(a^p) = Tr(a))**, **S62 list every graph degree the rules allow')
# Dropped line
rept('Session 62 added: linear and planar slices of K for row B5', 'Session 63 added: the extremal configurations of I (pairing); naive height searches for ℚ-points on V_K; plane-section checks at p = 3, 5 (use `loc63.py`); imprimitive decic test fields. Session 62 added: linear and planar slices of K for row B5')
# where things stand
rept('**Session 62:** a ℚ-quintic graph with the row-E Bézier (row B5) is genuine on all of L_135, so the r = 9 gap is one rational value of I = B2²/B3³ at a P-point of L_135 (S62.1–S62.2); slices of K have full monodromy (S62.3).',
     '**Session 62:** a ℚ-quintic graph with the row-E Bézier (row B5) is genuine on all of L_135, so the r = 9 gap is one rational value of I = B2²/B3³ at a P-point of L_135 (S62.1–S62.2); slices of K have full monodromy (S62.3). **Session 63:** over ℚ that gap vanishes: totally real nonics (and decics) over ℚ reduce to a ℚ-point on a twisted Fano 6-fold V_K (W_K), everywhere locally soluble for both test fields; the rational degree bound is now conditional only on producing such ℚ-points (Hasse principle, conjectural, or a construction).')
# workspace setup line
i = t.index('- Sympy is too slow for the Weierstrass resolvent')
t = t[:i] + ('- Session 63 (one directory; sympy, numpy, scipy, cypari): `b5q.py` (I = −(8/45)γ²), `skew63.py 150 1` (extremal configurations), '
             '`plant63.py 1 2000` (rational totally real S_9 member of row B5), `dec63.py 10 40 1` (decic real test), `locplane63.py <field> <pmin> <pmax> '
             '[primes|-] [dec]` (smooth F_p-points of V_K by plane sections, about 100–200 primes per second; FAIL at 3 and 5 by design), `loc63.py <field> '
             '<pmax> [samples]` (p-adic Hensel search; use for 2, 3, 5). Factor the field discriminant before passing ramified primes (a composite in the list hangs '
             '`nfinit`). `edit63.py` is the edit script (reads `sec0an.md`).\n') + t[i:]
# frozen-archive list unchanged; end-of-session checklist numbering
rept('session 63 is Section 0an, session 64 Section 0ao; session 64 also moves 0an and 0ao to a 63–64 archive', 'session 64 is Section 0ao; session 64 also moves 0an and 0ao to a 63–64 archive')
open('start63.md', 'w').write(t)
print('start', T0, '->', len(t))
