# Session 40: E-family X^9 + A X^7 + B X^2 + C (weights 2,7,9): discriminant in the chart C = 1 (the full trivariate
# discriminant times out). Result: one irreducible factor, exponent 1 (transposition inertia). The line C = 0 is also
# branched (double root at X = 0, splitting as +-sqrt(-C/B): transposition).
import cypari; P=cypari.pari; P.allocatemem(2*10**9)
P('f=X^9+A*X^7+B*X^2+C'); P('f=subst(f,C,1)')
d=P('poldisc(f,X)')
fa=P('factor')(d)
for i in range(len(fa[0])):
    q=fa[0][i]; print('factor exp',int(fa[1][i]),' degrees (A,B,C):',[int(P('poldegree')(q,P(v))) for v in ('A','B')],' nterms', len(str(q))//20)
