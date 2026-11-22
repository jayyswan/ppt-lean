# exact verification of engO_pts.txt: F | F'^2 - c2 h^5, c2 = -A/B, e1 = c2+u
import cypari,sys; P=cypari.pari
for line in open(sys.argv[1] if len(sys.argv)>1 else 'engO_pts.txt'):
    t=line.split(); a,b,u=t[:3]; c2=t[3]; e=t[4:]
    F=P('x^9'+''.join(f'+(-1)^{k+1}*({e[k]})*x^{8-k}' for k in range(9)))
    G=P(f'deriv({F})^2-({c2})*(x^3+({a})*x+({b}))^5')
    A=P(f'U=({u});a=({a});b=({b}); U^6+1278*a*U^4+50274*b*U^3+3321*a^2*U^2+2357586*a*b*U-1822500*a^3+6751269*b^2')
    B=P(f'U^5+1296*a*U^3+50112*b*U^2+27648*a^2*U+2985984*a*b')
    print(a,b,u,'rem0:',P(f'({G})%({F})')==0,' c2=-A/B:',P(f'({c2})+({A})/({B})')==0,' e1=c2+u:',P(f'({e[0]})-({c2})-({u})')==0, ' B*e_k int:',all(P(f'type({B}*{x})')=='t_INT' for x in e), ' irr:',P(f'polisirreducible({F})'), ' real roots:',P(f'polsturm({F})'))
