# Session 38: depress h, check weighted homogeneity of A,B (S37.2), fit constants.
import cypari; P=cypari.pari
P('Am2=u^6+18*u^5+2265*u^4+96856*u^3+762264*u^2+7727400*u+23692500')
P('Bm2=u^5+15*u^4+2250*u^3+90238*u^2+558693*u+7927875')
P('Ap3=u^6+18*u^5-4125*u^4-147404*u^3-1063341*u^2+12283650*u+135320625')
P('Bp3=u^5+15*u^4-4230*u^3-135122*u^2-388107*u+19105875')
for D2,An,Bn in [(-2,'Am2','Bm2'),(3,'Ap3','Bp3')]:
    h=P(f'subst((x+1)*(x^2-({D2})),x,X-1/3)')
    a=P(f'polcoef({h},1,X)'); b=P(f'polcoef({h},0,X)')
    A=P(f'subst({An},u,U-3)'); B=P(f'subst({Bn},u,U-3)')
    print('D2',D2,'a',a,'b',b); print(' A',A); print(' B',B)
    # fitted guesses
    for k,(mono) in [(4,'a'),(3,'b'),(2,'a^2'),(1,'a*b')]:
        print('  A U^%d / %s ='%(k,mono), P(f'polcoef({A},{k},U)/({mono.replace("a",str(a)).replace("b","("+str(b)+")")})'))
    c0=P(f'polcoef({A},0,U)'); print('  A0',c0,' a^3',P(f'({a})^3'),' b^2',P(f'({b})^2'))
    for k,mono in [(3,'a'),(2,'b'),(1,'a^2'),(0,'a*b')]:
        print('  B U^%d / %s ='%(k,mono), P(f'polcoef({B},{k},U)/({mono.replace("a",str(a)).replace("b","("+str(b)+")")})'))
