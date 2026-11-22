# Arya (Nov 20, after session 62): rational quintic graphs (e.g. y = x^5 - x^3) are plainly allowed as Q-graphs of degree <= 6.
S = open('summary62.md').read(); H = open('start62.md').read()
def rep(t, o, n, c=1):
    assert t.count(o) == c, (o[:60], t.count(o)); return t.replace(o, n)
note = 'confirmed by Arya, Nov 20: rational quintic graphs such as y = x⁵ − x³ are ℚ-graphs of degree ≤ 6; the Nov 19 "no" concerned P coefficients only'
S = rep(S, '(ℚ-graphs of degree ≤ 6 are allowed; *our reading, to confirm with Arya*)', '(' + note + ')')
S = rep(S, '*unchecked* (reduction; scope reading of the degree-6 rule)', '*unchecked* (reduction); scope confirmed by Arya (Nov 20)')
S = rep(S, '**Order now:** (0) ask Arya to confirm that ℚ-quintic graphs (rational coefficients) are allowed under the degree-≤ 6 rule; (1)', '**Order now (row B5 confirmed in scope by Arya after the session):** (1)')
S = rep(S, 'S51.3 is moot, and degree ≥ 5 polynomial graphs are not to be assumed.', 'S51.3 is moot, and degree ≥ 5 polynomial graphs **with P coefficients** are not to be assumed. (Clarified Nov 20: ℚ-graphs of degree 5 and 6, rational coefficients, are allowed; see row B5, S62.)')
S = rep(S, '- Session 51 (after Arya\'s answer): any route that needs graphs of polynomials of degree ≥ 5 (', '- Session 51 (after Arya\'s answer): any route that needs graphs of polynomials of degree ≥ 5 **with P coefficients** (rational-coefficient graphs of degree ≤ 6 are allowed, S62; ')
H = rep(H, 'ℚ-graphs of degree ≤ 6 are allowed by Arya\'s Nov 20 rule, *our reading: confirm with Arya first*', note)
H = rep(H, 'quintic graphs are not available as a base curve, so S51.3 is moot and degree ≥ 5 graphs are not to be assumed)', 'quintic graphs with P coefficients are not available as a base curve, so S51.3 is moot; rational-coefficient graphs of degree ≤ 6 are allowed (Arya, Nov 20), which is row B5)')
open('summary62.md','w').write(S); open('start62.md','w').write(H); print('ok', len(S), len(H))
