# edit60.py -- session 60 checklist: archive Sections 0aj (session 59) and 0ak (session 60) into
# claude/Sessions 59-60 results (frozen).md and update the condensed summary.  Reads /mnt/project copies
# and sec0ak.md; writes summary60.md and archive5960.md.
S = open('/mnt/project/claude_Condensed_summary_-_plan_and_progress.md').read()
ak = open('sec0ak.md').read().rstrip('\n') + '\n'
def rep(old, new, cnt=1):
    global S
    assert S.count(old) == cnt, (old[:60], S.count(old)); S = S.replace(old, new)
i0 = S.index('## 0aj.'); i1 = S.index('## 1. The goal')
aj = S[i0:i1].rstrip('\n') + '\n'
arch = ('# Sessions 59–60: full results (frozen archive)\n\nFrozen on Nov 20, 2026 (end of session 60). This file holds Section 0aj (session 59) exactly as it stood in the condensed summary after session 59 (including Arya\'s Nov 20 answer on the row E dials and S59.6), and Section 0ak (session 60) as written in session 60. **Don\'t write to it.** The living record is `claude/Condensed summary - plan and progress.md`, which keeps one line per session in its Section 0 and the Section 3 rows S59.1 … S60.4. Labels S59.1 … S60.4 point here.\n\n'
        + aj + '\n' + ak)
S = S[:i0] + S[i1:]
rep('(through session 59, Nov 20;', '(through session 60, Nov 20;')
rep('Thirteen frozen archives hold', 'Fourteen frozen archives hold')
rep("moved out of this file at the end of session 58.\n", "moved out of this file at the end of session 58.\n- `claude/Sessions 59-60 results (frozen).md` (this project): the full Sections 0aj and 0ak for sessions 59–60 (labels S59.1 … S60.4), moved out of this file at the end of session 60.\n")
rep('Sessions from 59 on exist only in this file (Section 0aj for session 59, 0ak for session 60, and so on).', 'Sessions from 61 on exist only in this file (Section 0al for session 61, 0am for session 62, and so on).')
rep('## 0. Sessions 25–59 in brief (full text in the frozen archives; session 59 in Section 0aj)', '## 0. Sessions 25–60 in brief (full text in the frozen archives)')
rep('- S59 (Section 0aj; Arya confirmed', '- S59 (archive 59–60; Arya confirmed')
line60 = ('- S60 (archive 59–60): **row E with a fixed ℚ-sextic and P dials (S = T_6).** Only p1 … p8 of the 12 crossing points and two affine shape invariants (I3, I4) of S matter (S60.1). Exact counts mod p: the shift/extra-crossing data form an irreducible degree-10 scheme per generator; the good-generator locus H_{T_6} has degree 840 (generic S 1680), irreducible on a random plane, so linear slices are no step (S60.2). The shift is P-rational exactly on the old hypersurface H_E = {25p3p7 = 21p5²}, and **H_E has dense P-points for r = 9** (tangent residual octic at P-points of L_135 has a real root on about 98 % of directions, S60.3). **Reduction (S60.4): row E closes r = 9 for K iff the shape map J: H_E ⇢ A² takes a rational value at a P-point of H_E**; J reaches an open region around T_6\'s (0, 3/2) on real points.\n')
i = S.index('- Nov 19 (between sessions 55 and 56)'); S = S[:i] + line60 + S[i:]
# Section 3 rows
row = S.index('| S59.4: row E with a fixed'); e = S.index('\n', row) + 1
rows60 = ('| S60.1: row E with P dials: τ good ⇔ the 12 points {τ + s} ∪ {z} have p_odd = 0 (k ≤ 7) and p_{2m} = 2Σ v_j^m (m ≤ 4), v_j = (x_j − β)/α, x_j roots of S; S enters only through its affine shape invariants (I3, I4); a rational S exists iff (I3, I4) ∈ ℚ² | *unchecked* (short algebra) |\n'
          '| S60.2: odd part: 10 (shift, extra crossings) per generator, shift eliminant irreducible of degree 10 over ℚ; shift = 0 exactly on H_E (25p3p7 = 21p5², centred); H_{T_6} has degree 840 (generic S: 1680), irreducible on a random plane (840-cycle mod p) | [exact mod p] (`e60.py`, `odd60.py`, `e60r.py`, `msparam.py`) |\n'
          '| S60.3: H_E has dense P-points for r = 9: the tangent residual octic at P-points of L_135 has real roots on 395/400 and 591/600 directions, residual points genuine (p3 ≠ 0); the shape invariants of real points fill an open region around T_6\'s (0, 3/2) | *unchecked* (chain: T3 for r = 9, fact 3) + [numerical] (`hres60.py`) |\n'
          '| S60.4: row E with P dials closes r = 9 for K iff J = (I3, I4): H_E ⇢ A² takes a rational value at a P-point of H_E (a two-condition rationality gap on a P-dense hypersurface) | *unchecked* |\n')
S = S[:e] + rows60 + S[e:]
# Section 4 row E line
j = S.index('- **Row E (rational only):** 25p3p7 = 21p5², degree 10.'); je = S.index('\n', j)
S = S[:je] + ' **S60: with P-valued affine dials H_E is the locus where the shift dial is P-rational; H_E has dense P-points for r = 9 (S60.3), and the remaining condition is that the forced sextic\'s two shape invariants (I3, I4) are rational (S60.4).**' + S[je:]
# Section 5 lesson
lesson = ('- **Method lesson (S60):** (1) **Write a crossing row in power sums of the full crossing set (the generator plus the auxiliary crossings) before counting**: here only p1 … p8 enter and the fixed curve enters through two affine invariants, which turned "a P-point on a 5-fold with no known P-points" into "two rational invariants on a hypersurface with dense P-points". (2) **When dials become P-valued, recheck the out-of-scope steps of earlier sessions**: S59.3\'s residual step, dropped for forcing a P-sextic, now gives P-points up to two invariants. (3) msolve on 5 variables with degrees 4–8 gives a 1680-point count in seconds; when its chosen separating variable is not the one you want, compute the charpoly of that coordinate modulo the eliminant in PARI (`msparam.py`; degree 840 took about 6 minutes) and factor it mod p for an exact irreducibility test.\n')
k = S.index('- **Method lesson (S59):**'); S = S[:k] + lesson + S[k:]
# Section 6 decision
dec = ('**Session 60 decision (row E with P dials reduced to two rational invariants).** S60.2: H_{T_6} has degree 840, irreducible, so linear slices are no step; the shift dial is P-rational exactly on H_E. S60.3: H_E has dense P-points for r = 9 (tangent residual octics at L_135). S60.4: row E closes r = 9 iff J = (I3, I4) takes a rational value at a P-point of H_E. **Order now:** (1) r = 9: a P-family in H_E (tangent-residual curves or surfaces through a P-point of L_135) on which J has a low-degree fibre over a rational value (measure the fibre degree over J0 = (0, 3/2) mod p), or a degenerate locus on which J is constant; (2) r = 7: M2 with a chosen generator (S58.4), or Z_G / R5; (3) A_9 r = 5: the S54 candidates (Γ_H, span fibration); (4) decics via V_5 only with a new mechanism; (5) osculation and ℚ-arithmetic.\n\n')
k = S.index('**Session 59 decision (P-dense loci'); S = S[:k] + dec + S[k:]
rep('- Session 59: P-dense loci (L_135, V_odd, X) inside Z_G (S59.1); the tangent-residual step on H_E at P-points of L_135 with a P-sextic (out of scope, S59.3; reopen only if Arya allows P-sextic coefficients).',
    '- Session 60: linear slices of the row E good-generator locus H_S (degree 840 for T_6, 1680 generic, irreducible, S60.2); treating the shift as a free P-dial off H_E (it is a root of an irreducible decic, S60.2).\n- Session 59: P-dense loci (L_135, V_odd, X) inside Z_G (S59.1); the tangent-residual step on H_E at P-points of L_135 with a P-sextic (out of scope under the old rules, S59.3; **reopened in S60.3** under P-valued affine dials, where it gives P-points of H_E up to two rational invariants).')
rep('items decided in sessions 41–58)', 'items decided in sessions 41–60)')
# Section 7 scripts
s7 = ('Session 60 (one directory; Singular and msolve via `apt-get update && apt-get install -y singular msolve`; sympy, cypari, numpy):\n'
      '- `e60.py odd <seed>` (seconds; Singular mod 32003): odd equations p_k(τ + s) + p_k(z) = 0, k = 1, 3, 5, 7 for a random τ: dim 0, vdim 10, the shift eliminant. (Its `plane` mode, 8 variables, did not finish in 3 minutes; use `e60r.py`.)\n'
      '- `odd60.py <seed>` (seconds; Singular over ℚ): the same for an integer τ, factored over ℚ (runs 1, 2: irreducible of degree 10).\n'
      '- `e60r.py <seed> <sing|msolve> [T6|gen|P1,P2,P3,P4] [p]` (msolve: about 7 seconds; Singular: slower, not finished in 3 minutes): plane slice of H_S, unknowns x, y, s, A, b after eliminating e1, e2, e3; environment `EVEN=1` uses the invariant variables (α⁻², β/α) for even S, `ORDER=` sets the msolve variable order; writes `e60r_<seed>.ms` and `.ms.out`. Runs: `1 msolve` (1680), `EVEN=1 … 1 msolve` (840), `2 msolve gen` (1680).\n'
      '- `msparam.py <file.ms> <file.out> <var>` (about 6 minutes for degree 840, run in the background): reads msolve\'s parametrisation (sign convention v = −num/den checked on the equations), the charpoly of a coordinate modulo the eliminant, squarefree degree and factor degrees mod p (`msparam.py e60r_1.ms e60r_1.ms.out x` after the `EVEN=1` run: 840 distinct, one factor).\n'
      '- `hres60.py <seed> <N> <M>` (seconds; numpy): N real points of L_135 (r = 9) × M tangent directions, residual octic of 25p3p7 − 21p5², real-root distribution, genuineness checks, the auxiliary cubic, and the shape invariants (I3, I4) of the real residual points (runs `1 20 20`, `2 30 20`).\n')
k = S.index('## 8. Ground rules'); S = S[:k] + s7 + '\n' + S[k:]
open('summary60.md', 'w').write(S); open('archive5960.md', 'w').write(arch)
import re
print(len(S), len(arch)); print([l for l in S.split('\n') if l.startswith('## ')])
