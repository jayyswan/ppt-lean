# Session 38: fit B(u)*e_k as weighted-homogeneous polynomials in (u,a,b), weights (1,2,3), weight 5+k.
import cypari,sys; P=cypari.pari
P.allocatemem(10**9)
rows=[l.split() for l in open(sys.argv[1])]
P('Bf(U,a,b)=U^5+1296*a*U^3+50112*b*U^2+27648*a^2*U+2985984*a*b')
res={}
for k in range(1,10):
    w=5+k; mons=[(i,j,l) for l in range(w//3+1) for j in range((w-3*l)//2+1) for i in [w-3*l-2*j]]
    M=[];V=[]
    for r in rows:
        a,b,u=r[:3]; ek=r[3+k]
        M.append([f'({u})^{i}*({a})^{j}*({b})^{l}' for (i,j,l) in mons]); V.append(f'Bf({u},{a},{b})*({ek})')
    Ms='['+';'.join(','.join(x) for x in M)+']'; Vs='['+','.join(V)+']~'
    sol=P(f'matinverseimage({Ms},{Vs})')
    ok = len(sol)>0 and P(f'{Ms}*{sol}=={Vs}')
    terms=[(mons[n],sol[n]) for n in range(len(mons))] if len(sol)>0 else []
    maxdeg=max([m[0] for m,c in terms if c!=0],default=None)
    poly=P('+'.join(f'({c})*U^{m[0]}*a^{m[1]}*b^{m[2]}' for m,c in terms)) if terms else None
    res[k]=poly
    print(f'k={k} weight {w}: {len(mons)} monomials, exact fit on {len(rows)} pts: {bool(ok)}, max u-degree {maxdeg}')
    print('   B*e_%d ='%k, poly)
open('engO_poly.gp','w').write('\n'.join(f'E{k}={res[k]};' for k in res)+'\n')
