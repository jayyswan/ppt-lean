# B3-04-new-equations.py
# Q3/Q4/Q5: offset-sine / offset-2^x crossings that do NOT reduce to bare crossings;
# foot-of-normal (min distance) equations; involute/cycloid single points; cusp lengths.
import mpmath as mp
import sympy as sp

mp.mp.dps = 50

def section(t):
    print("\n" + "=" * 70)
    print(t)
    print("=" * 70)

# ---------------------------------------------------------------- offset sine x vertical line
section("offset-sine (d) crossed with X=0:  x = d cos x / sqrt(1+cos^2 x)")
for dd in [mp.mpf('0.5'), mp.mpf(1), mp.mpf(2)]:
    f = lambda x: x - dd*mp.cos(x)/mp.sqrt(1+mp.cos(x)**2)
    # find roots on each monotone branch
    for guess in [mp.mpf('0.3'), mp.mpf('1.4'), mp.mpf('2.9')]:
        try:
            r = mp.findroot(f, guess)
            print(f"  d={dd}: x = {mp.nstr(r,30)}  identify={mp.identify(r)}  residual={mp.nstr(f(r),3)}")
        except Exception as ex:
            pass

# ---------------------------------------------------------------- foot of perpendicular
section("foot of perpendicular from fixed P to sine: solves (X-x)+(Y-sin x)cos x = 0")
for (X, Y) in [(mp.mpf(0), mp.mpf(2)), (mp.mpf(1), mp.mpf(1)), (mp.mpf(2), mp.mpf(-1))]:
    f = lambda x: (X - x) + (Y - mp.sin(x))*mp.cos(x)
    hits = []
    grid = [mp.mpf(k)/4 for k in range(-12, 16)]
    for a, b in zip(grid[:-1], grid[1:]):
        if f(a)*f(b) < 0:
            r = mp.findroot(f, (a, b))
            hits.append(r)
    print(f"  P=({X},{Y}):")
    for r in hits:
        d2 = (r-X)**2 + (mp.sin(r)-Y)**2
        print(f"    x={mp.nstr(r,30)}  dist={mp.nstr(mp.sqrt(d2),30)}  identify(x)={mp.identify(r)}")

# ---------------------------------------------------------------- min distance between two curves
section("minimum distance between y=sin x and line y = x/4 + 1  (num. of normal eqs)")
f = lambda x: None  # placeholder
# common normal: normals parallel: slope of sine normal = -1/cos x, line slope 1/4 -> need parallel
# instead just report that tangency search is a critical-point problem, not a crossing
print("  (min distance between two curves requires a common-normal critical point;")
print("   it is an extremum, not a unique crossing -> outside the move set)")

# ---------------------------------------------------------------- curvature data
section("curvature of sine at constructible x: kappa(x) = -sin x/(1+cos^2 x)^{3/2}")
for xv in [mp.mpf('0.7'), mp.mpf('1.3')]:
    k = -mp.sin(xv)/(1+mp.cos(xv)**2)**mp.mpf(1.5)
    print(f"  x={xv}: kappa={mp.nstr(k,30)}  rho={mp.nstr(1/abs(k),30)}  "
          f"center=({mp.nstr(xv + (1/abs(k))*mp.cos(xv),25)},"
          f"{mp.nstr(mp.sin(xv) + (1/abs(k))/mp.sqrt(1+mp.cos(xv)**2),25)})")

# ---------------------------------------------------------------- involute of circle / cycloid point
section("involute of unit circle and cycloid at constructible parameters (single points)")
for s in [mp.mpf('0.6'), mp.mpf('1.4')]:
    # involute: (cos s + s sin s, sin s - s cos s)
    ix, iy = mp.cos(s)+s*mp.sin(s), mp.sin(s)-s*mp.cos(s)
    print(f"  circle involute s={s}: ({mp.nstr(ix,25)}, {mp.nstr(iy,25)})")
for th in [mp.mpf('0.8'), mp.mpf('2.0')]:
    # cycloid of unit rolling circle: (th - sin th, 1 - cos th)
    cx, cy = th-mp.sin(th), 1-mp.cos(th)
    print(f"  cycloid th={th}: ({mp.nstr(cx,25)}, {mp.nstr(cy,25)})")

# ---------------------------------------------------------------- cusped parallel ellipse perimeter
section("parallel ellipse perimeter with cusps (inward, |d|>rho_min=b^2/a)")
aa, bb = mp.mpf(2), mp.mpf(1)
def sigma(th): return mp.sqrt(aa**2*mp.sin(th)**2 + bb**2*mp.cos(th)**2)
# full offset perimeter = int_0^{2pi} |sigma - d*aa*bb/sigma| dth
for dd in [mp.mpf('-0.7'), mp.mpf('-1.5')]:
    P = mp.quad(lambda th: abs(sigma(th) - dd*aa*bb/sigma(th)), [0, 2*mp.pi])
    print(f"  d={dd}: |offset perimeter| = {mp.nstr(P,30)}   P0-2*pi*d={mp.nstr(4*aa*mp.ellipk(1-(bb/aa)**2)-2*mp.pi*dd,30)}")
    # cusp parameter: sigma^2 = (a b d)^{2/3}
    smax2 = (aa*bb*abs(dd))**mp.mpf(2)/mp.mpf(3)
    s2 = (smax2 - bb**2)/aa**2
    print(f"    cusp sin^2 = {mp.nstr(s2,25)} -> sin={mp.nstr(mp.sqrt(s2),20)}, th={mp.nstr(mp.asin(mp.sqrt(s2)),20)}")

# ---------------------------------------------------------------- offset-sine arc_of_length inverse
section("offset-sine arc length inverse: solve int_0^T [sqrt(1+cos^2)-d*sin/(1+cos^2)] = L")
dd = mp.mpf('0.4')
def sdot(th): return mp.sqrt(1+mp.cos(th)**2) - dd*mp.sin(th)/(1+mp.cos(th)**2)
for L in [mp.mpf('1.0'), mp.mpf('2.0')]:
    # sdot may change sign; invert on increasing branch near 0
    def S(T): return mp.quad(sdot, [0, T])
    r = mp.findroot(lambda T: S(T)-L, mp.mpf('1.0'))
    print(f"  d={dd}, L={L}: T={mp.nstr(r,30)}  residual={mp.nstr(S(r)-L,3)}  identify={mp.identify(r)}")
