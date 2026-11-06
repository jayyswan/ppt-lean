# X5-01: checks supporting the X5 obstruction-theory note.
#   1. F_c(am_c(u)) = u  -> M = F_c is a counterexample to (T3) as stated in R3 2.3.
#   2. am and EAm both solve an autonomous ODE whose associated curve is genus 1
#      (differential algebra cannot separate them).
#   3. sn is doubly periodic; EAm is only quasi-periodic (the "kind" distinction).
#   4. Jacobi epsilon E(am(u)) is non-affine.
# Run: C:\Users\jason\...\python.exe X5-01-theory-checks.py
from mpmath import mp, mpf, ellipfun, ellipf, ellipe, ellipk, sin, cos, sqrt, pi, findroot
mp.dps = 40

def E_inc(phi, m):
    return ellipe(phi, m)

def EAm(v, m):
    # solve E(phi,m)=v for phi in [0,K]
    K = ellipk(m)
    f = lambda p: E_inc(p, m) - v
    return findroot(f, (mpf(0), K))

print("== 1. (T3) counterexample: M = F_c gives F_c(am(u)) = u ==")
for c in (mpf('0.3'), mpf('0.7'), mpf('0.93')):
    worst = mpf(0)
    for u in (mpf('0.4'), mpf('1.1'), mpf('2.0')):
        # am(u) = F^{-1}(u)
        am = findroot(lambda p: ellipf(p, c) - u, u)
        lhs = ellipf(am, c)
        worst = max(worst, abs(lhs - u))
    print(f"   c={float(c):.2f}: max |F(am(u))-u| = {mp.nstr(worst, 5)}")

print("== 2. ODE test: am'^2 = 1-c sin^2(am)  and  EAm'^2 = 1/(1-c sin^2(EAm)) ==")
for c in (mpf('0.3'), mpf('0.7'), mpf('0.93')):
    # am
    wam = mpf(0)
    for u in (mpf('0.4'), mpf('1.3'), mpf('2.1')):
        am = findroot(lambda p: ellipf(p, c) - u, u)
        d = mp.diff(lambda t: findroot(lambda p: ellipf(p, c) - t, t), u)
        wam = max(wam, abs(d**2 - (1 - c*sin(am)**2)))
    # EAm
    weam = mpf(0)
    K = ellipk(c)
    for v in (mpf('0.4')*K, mpf('0.8')*K, mpf('1.1')*K):
        ph = EAm(v, c)
        d = mp.diff(lambda t: EAm(t, c), v)
        weam = max(weam, abs(d**2 - 1/(1 - c*sin(ph)**2)))
    print(f"   c={float(c):.2f}: am-ODE resid {mp.nstr(wam,5)}, EAm-ODE resid {mp.nstr(weam,5)}")

print("== 3. sn periodic (period 4K) vs EAm quasi-periodic (angle quasi-period pi per 2E0) ==")
for c in (mpf('0.3'), mpf('0.7')):
    K = ellipk(c); E0 = ellipe(c)   # complete E = E(pi/2)
    u = mpf('0.37')
    sn_per = abs(ellipfun('sn', u + 4*K, c) - ellipfun('sn', u, c))
    v = mpf('0.4')*K
    ph1 = EAm(v, c); ph2 = EAm(v + 2*E0, c)
    drift = ph2 - ph1 - pi
    print(f"   c={float(c):.2f}: |sn(u+4K)-sn(u)|={mp.nstr(sn_per,4)}; EAm(v+2E0)-EAm(v)-pi={mp.nstr(drift,4)}")

print("== 4. Jacobi epsilon E(am(u)) is non-affine (second divided difference) ==")
for c in (mpf('0.3'), mpf('0.7')):
    us = [mpf('0.2'), mpf('0.9'), mpf('1.7')]
    ys = [E_inc(findroot(lambda p: ellipf(p, c)-u, u), c) for u in us]
    d2 = ((ys[2]-ys[1])/(us[2]-us[1]) - (ys[1]-ys[0])/(us[1]-us[0]))/(us[2]-us[0])
    print(f"   c={float(c):.2f}: 2nd divided difference = {mp.nstr(d2,6)} (should be nonzero)")

print("== genus note (Riemann-Hurwitz, by hand) ==")
print("   am  : w^2=(1-s^2)(1-c s^2), deg 4, 4 simple branch points -> g=1")
print("   EAm : w^2(1-c s^2)=1-s^2,   deg 4, 4 simple branch points -> g=1")
print("   -> both inversions generate strongly normal, non-Liouvillian genus-1 fields.")
