from tb_refine import *
mp.mp.dps=60
S,sol=refine(-0.5,0,1,(1,1),[4.80809,0.19608,-0.779941,-0.207165,0.104362])
d1,d2,tT,xs,ys=sol
P=S.P2s(d1,d2,tT,1,1); mx=sum(p[0] for p in P)/9; my=sum(p[1] for p in P)/9
Pc=[(p[0]-mx,p[1]-my) for p in P]
c,Sv=cubic_through(Pc)
print('9x10 singular values (last two):',mp.nstr(Sv[7],4),mp.nstr(Sv[8],4))
F=lambda x,y: Feval(c,x,y)
# lines through node: F(S0+s(1,m)) = s^2 (a(m) s + b(m))
def ab(m):
    # fit by sampling s
    vals=[F(xs+s,ys+m*s) for s in (mp.mpf(1),mp.mpf(2))]
    # v1 = a+b , v2 = 4(2a+b)
    a=(vals[1]/4-vals[0]); b=vals[0]-a; return a,b
a3=[c[6],c[7],c[8],c[9]]          # a(m)= c30 + c21 m + c12 m^2 + c03 m^3
print("cubic part:",[mp.nstr(x,8) for x in a3])
m0=-3*c[6]/c[7]; print("m0",mp.nstr(m0,15), " check a(m0)=",mp.nstr(sum(a3[e]*m0**e for e in range(4)),3))
def B(tau):
    m=m0+1/tau; a,b=ab(m); s=-b/a; return (xs+s, ys+m*s)
# polynomial check: sample and fit degree-3 in tau
taus=[mp.mpf(k)/7+mp.mpf(1)/3 for k in range(1,9)]
pts=[B(t) for t in taus]
for comp in (0,1):
    V=mp.matrix([[t**e for e in range(4)] for t in taus[:4]]); co=mp.lu_solve(V,mp.matrix([p[comp] for p in pts[:4]]))
    err=max(abs(sum(co[e]*t**e for e in range(4))-p[comp]) for t,p in zip(taus,pts))
    print('coordinate',comp,'cubic in tau:',[mp.nstr(x,10) for x in co],' fit err on other samples',mp.nstr(err,3))
    if comp==0: cx=co
    else: cy=co
# parameters of the 9 points
for (px,py) in Pc:
    m=(py-ys)/(px-xs); tau=1/(m-m0)
    bx=sum(cx[e]*tau**e for e in range(4)); by=sum(cy[e]*tau**e for e in range(4))
    print(' tau=%s  |B(tau)-P2|=%s'%(mp.nstr(tau,12),mp.nstr(mp.sqrt((bx-px)**2+(by-py)**2),3)))
