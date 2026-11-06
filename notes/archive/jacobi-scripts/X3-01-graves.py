# X3-01-graves.py  --  Graves-Chasles string theorem: numerical audit.
# Inner ellipse E_in: x = a sin(phi), y = b cos(phi),  a>b>0.
# Outer confocal ellipse E_out: same foci f^2 = a^2-b^2, semiaxes A,B.
# For P on E_out, draw the two tangents to E_in touching at T1,T2 (angles p1,p2).
# Claim (Graves-Chasles):  |P T1| + |P T2| +/- arc_{E_in}(T1,T2)  is a constant L,
# i.e. the inner arc is an ALGEBRAIC function of P plus the constant L.
# Also test whether that arc is an E-integral (2nd kind) and hence gives no F.
import mpmath as mp
from mpmath import mpf, sqrt, pi, sin, cos, atan2, asin

mp.mp.dps = 35
a = mpf(2); b = sqrt(mpf(3)); f2 = a*a - b*b
A = mpf('2.5'); B = sqrt(A*A - f2)
k2_in = 1 - b*b/(a*a)          # parameter m of the inner ellipse
k_in = sqrt(k2_in)

def arc_inner(p1, p2):
    """Euclidean arc length of inner ellipse between eccentric angles p1,p2
       using x=a sin(t), y=b cos(t): ds = a*sqrt(1-k2 sin^2 t) dt."""
    return a*(mp.ellipe(p2, k2_in) - mp.ellipe(p1, k2_in))

def arc_inner_quad(p1, p2):
    f = lambda t: a*sqrt(1 - k2_in*sin(t)**2)
    return mp.quad(f, [p1, p2])

def tangent_angles(P, aa=None, bb=None):
    if aa is None: aa, bb = a, b
    x0, y0 = P
    A1, B1 = x0/aa, y0/bb
    R = sqrt(A1*A1 + B1*B1)
    if R <= 1: return None
    psi = atan2(B1, A1)
    al = asin(1/R)
    return al - psi, pi - al - psi   # two solutions, unordered

def norm_angle(t):
    t = t % (2*pi)
    return t

def two_arcs(p1, p2):
    """positive lengths of both arcs of the inner ellipse joining angles p1,p2."""
    x1, x2 = norm_angle(p1), norm_angle(p2)
    if x2 < x1: x1, x2 = x2, x1
    L1 = arc_inner(x1, x2)          # forward (increasing angle)
    per = 4*a*mp.ellipe(k2_in)
    return L1, per - L1

rows = []
for j in range(12):
    th = 2*pi*mpf(j)/mpf(12)
    P = (A*sin(th), B*cos(th))
    p1, p2 = tangent_angles(P, a, b)
    T1 = (a*sin(p1), b*cos(p1)); T2 = (a*sin(p2), b*cos(p2))
    d1 = sqrt((P[0]-T1[0])**2 + (P[1]-T1[1])**2)
    d2 = sqrt((P[0]-T2[0])**2 + (P[1]-T2[1])**2)
    arc1, arc2 = two_arcs(p1, p2)
    per = arc1 + arc2
    rows.append((th, d1+d2, arc1, arc2, per))

print("a,b =", a, b, " A,B =", A, B, " foci^2 =", f2)
print("inner k^2 =", k2_in, " inner perimeter =", rows[0][4])
print()
print("  theta      |PT1|+|PT2|        short arc        long arc      sum+short       sum+long")
for th, s, sh, lg, per in rows:
    print("%8.5f  %18.12f %18.12f %18.12f %15.12f %15.12f"
          % (th, s, sh, lg, s+sh, s+lg))

def spread(vals):
    m = sum(vals)/len(vals)
    return max(abs(v-m) for v in vals), m

def run_case(a, b, A):
    global k2_in
    f2 = a*a - b*b
    B = sqrt(A*A - f2)
    k2_in = 1 - b*b/(a*a)
    per = 4*a*mp.ellipe(k2_in)
    Ls = []
    data = []
    for j in range(24):
        th = 2*pi*mpf(j)/mpf(24)
        P = (A*sin(th), B*cos(th))
        p1, p2 = tangent_angles(P, a_, b_)
        T1 = (a*sin(p1), b*cos(p1)); T2 = (a*sin(p2), b*cos(p2))
        d1 = sqrt((P[0]-T1[0])**2 + (P[1]-T1[1])**2)
        d2 = sqrt((P[0]-T2[0])**2 + (P[1]-T2[1])**2)
        x1, x2 = sorted((p1 % (2*pi), p2 % (2*pi)))
        L1 = a*(mp.ellipe(x2, k2_in) - mp.ellipe(x1, k2_in))
        L2 = per - L1
        Lrow = max(d1+d2+L1, d1+d2+L2)     # the arc on the side away from P
        Ls.append(Lrow)
        data.append((th, d1+d2, L1, L2))
    sp, mn = spread(Ls)
    return B, per, sp, mn, data

print("\n=== Graves-Chasles: (|PT1|+|PT2|) + far-arc  is constant ===")
for (a_, b_, A_) in [(2, sqrt(3), mpf('2.5')), (3, 2, mpf('3.6'))]:
    B_, per_, sp_, mn_, data_ = run_case(mpf(a_), mpf(b_), A_)
    print("case a,b=%s,%s  A,B=%s,%s" % (a_, mp.nstr(b_,6), A_, mp.nstr(B_,6)))
    print("   perimeter=%s   L=%s   max spread over 24 pts = %.3e"
          % (mp.nstr(per_,20), mp.nstr(mn_,25), sp_))
    # a couple of sample rows
    for th, s, L1, L2 in data_[:3]:
        far = max(s+L1, s+L2)
        print("   theta=%8.5f  |PT1|+|PT2|=%s  far-arc=%s  sum=%s"
              % (th, mp.nstr(s,12), mp.nstr(max(L1,L2),12), mp.nstr(far,18)))
    print("   argmin |sum-L|:", min(range(len(data_)), key=lambda i:
          abs(data_[i][1]+max(data_[i][2],data_[i][3])-mn_)))

# --- inverse-E demonstration: pick a target arc, solve for theta ---
print("\n=== Graves used backwards gives an inverse-E (ellipticEAm), not am ===")
a_=mpf(2); b_=sqrt(mpf(3)); A_=mpf('2.5'); B_, per_, sp_, mn_, data_ = run_case(a_,b_,A_)
def arc_far(th):
    P=(A_*sin(th),B_*cos(th)); p1,p2=tangent_angles(P, a_, b_)
    x1,x2=sorted((p1%(2*pi),p2%(2*pi)))
    L1=a_*(mp.ellipe(x2,k2_in)-mp.ellipe(x1,k2_in)); L2=per_-L1
    return max(L1,L2)
Ttarget = arc_far(mpf('1.0471975511965976'))
lo,hi=mpf(0),mpf('3.14159')
for _ in range(80):
    mid=(lo+hi)/2
    if arc_far(mid) < Ttarget: lo=mid
    else: hi=mid
th_rec=(lo+hi)/2
print("target arc =", mp.nstr(Ttarget,20), " recovered theta =", mp.nstr(th_rec,20),
      " (true 1.0471975511965976)  err=%.2e" % float(abs(th_rec-mpf('1.0471975511965976'))))
print("=> mechanism inverts the 2nd-kind (E) map, i.e. ellipticEAm; no F, no am.")
