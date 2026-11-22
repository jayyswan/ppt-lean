\\ Session 37: e1-resolvent R(T,c) of U_C for h = (x+1)(x^2+2) (D2 = -2), c = c^2 of S29.1.
\\ Run: python3 run_read.py Rcurve.gp   (or paste into cypari line by line)
R = T^6 - (5*c-18)*T^5 + (10*c^2-75*c+2265)*T^4 - (10*c^3-120*c^2+6810*c-96856)*T^3 + (5*c^4-90*c^3+6840*c^2-200330*c+762264)*T^2 + (-c^5+30*c^4-2310*c^3+110092*c^2-965835*c+7727400)*T + (-3*c^5+15*c^4-6618*c^3+203571*c^2+200475*c+23692500);
print(polgalois(subst(R,c,250)));
print(factor(poldisc(R,T)));
S = subst(R,T,c+u); print(vector(7,k,polcoef(S,k-1,u)));
