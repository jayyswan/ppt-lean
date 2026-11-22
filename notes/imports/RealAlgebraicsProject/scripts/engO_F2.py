# Session 38: Engine O, exact values of F_{h,u} (h = x^3+a x+b) on a grid.
# Moves (a,b) at large complex u (no poles there), then walks u along the real integers
# with complex bumps around the roots of B. usage: python3 engO_F2.py "<a1>,<b1>;<a2>,<b2>;..." <ulist> <out>
import sys, mpmath as mp, cypari
P=cypari.pari
exec(open('engO_F.py').read().split("# start:")[0])   # Af,Bf,rem,pmul,resid,newton
exec(open('engO_F.py').read().split("def go(")[1].split("def rat(")[0].join(["def go(",""]))
Fx=P('(4184*x^9+10775*x^8-21954*x^7-255050*x^6-730124*x^5-1093620*x^4-944440*x^3-446680*x^2-81360*x+4320)/4184')
FX=P(f'subst({Fx},x,X-1/3)')
co=[P(f'polcoef({FX},{9-k},X)') for k in range(10)]
e=[mp.mpf(int(P(f"numerator({c})")))/int(P(f"denominator({c})"))*(-1)**k for k,c in enumerate(co)]
a0,b0,u0=mp.mpf(5)/3,mp.mpf(38)/27,mp.mpf(-22)
v=[mp.mpc(x) for x in e[2:]]+[mp.mpc(mp.mpf(93825)/4184)]; v,nr=newton(v,a0,b0,u0)
def rat(z): return P(f'bestappr({mp.nstr(mp.re(z),66)},10^28)')
def Broots(a,b): return mp.polyroots([1,0,1296*a,50112*b,27648*a**2,2985984*a*b],maxsteps=200,extraprec=200)
def upath(a,b,u0,u1):
    # waypoints from u0 to u1 avoiding roots of B by distance >= 0.4|root|+1
    rts=Broots(a,b); pts=[u0,u1]
    for _ in range(6):
        bad=False; new=[pts[0]]
        for i in range(len(pts)-1):
            p,q=pts[i],pts[i+1]
            for r in rts:
                d=q-p; t=max(0,min(1,mp.re((r-p)*mp.conj(d))/abs(d)**2)); m=p+t*d
                if abs(m-r)<0.3+0.05*abs(r):
                    w=m+(1j if mp.im(m-r)>=0 else -1j)*(0.6+0.1*abs(r)); new.append(w); bad=True; break
            new.append(q)
        pts=new
        if not bad: break
    return pts
def walk(v,a,b,us):
    for i in range(len(us)-1):
        v=go(v,[a,b,us[i]],[a,b,us[i+1]],10)
        if v is None: return None
    return v
U_FAR=mp.mpc(-22,5)
cur=walk(v,a0,b0,[u0]+upath(a0,b0,u0,U_FAR)[1:])
print('at far u', cur is not None, flush=True)
pa,pb=a0,b0
out=open(sys.argv[3],'w')
ulist=[int(s) for s in sys.argv[2].split(',')]
for ab in sys.argv[1].split(';'):
    a,b=[mp.mpf(P(s).__float__()) if '/' not in s else mp.mpf(int(s.split('/')[0]))/int(s.split('/')[1]) for s in ab.split(',')]
    mid=[(pa+a)/2+0.37j,(pb+b)/2-0.23j]
    w=go(cur,[pa,pb,U_FAR],[mid[0],mid[1],U_FAR],20); w=go(w,[mid[0],mid[1],U_FAR],[a,b,U_FAR],20) if w else None
    if w is None: print('ab fail',ab,flush=True); continue
    cur=w; pa,pb=a,b
    x=cur; prevu=U_FAR
    for u in ulist:
        pre=[prevu]
        x=walk(x,a,b,pre[:-1]+upath(a,b,pre[-1],mp.mpf(u)))
        if x is None: print('u fail',ab,u,flush=True); break
        prevu=mp.mpf(u)
        vals=[rat(z) for z in [x[8],x[8]+u]+list(x[:8])]
        out.write(' '.join([ab.split(',')[0],ab.split(',')[1],str(u)]+[str(z) for z in vals])+'\n'); out.flush()
        print(ab,u,'imag',mp.nstr(max(abs(mp.im(z)) for z in x),3),flush=True)
