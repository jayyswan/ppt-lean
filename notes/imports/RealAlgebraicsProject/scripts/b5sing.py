import random, subprocess, sympy as sp
random.seed(3)
C = [[random.randrange(-9, 10) for _ in range(9)] for _ in range(3)]
x, y, s = sp.symbols('x y s')
U = [C[0][i] + C[1][i]*x + C[2][i]*y for i in range(9)]
Z = [u + s for u in U]; zeta = -sum(U) - 9*s
q = lambda k: sp.expand(sum(z**k for z in Z) + zeta**k)
q2, q3, q4, q5, q6 = map(q, (2, 3, 4, 5, 6))
N2 = sp.expand(q2**3 - 15*q2*q4 + 50*q6)
E = [str(e).replace('**', '^') for e in (q3, q5, N2)]
scr = f"""ring r=40013,(x,y,s),dp; ideal I={E[0]},{E[1]},{E[2]};
option(redSB); ideal G=std(I); print(dim(G)); print(vdim(G));
ring r2=40013,(x,y,s),lp; ideal G2=fglm(r,G); poly f=G2[1]; print(deg(f));
list L=factorize(f); int i; for(i=1;i<=size(L[1]);i++){{ print(string(deg(L[1][i]))+\"^\"+string(L[2][i])); if(deg(L[1][i])==1){{print(L[1][i]);}} }}
quit;"""
open('b5sing.sing', 'w').write(scr)
out = subprocess.run(['Singular', '-q', 'b5sing.sing'], capture_output=True, text=True, timeout=300)
print(out.stdout[-1500:], out.stderr[-500:])
