"""Session 43: analyse conics from cy4.py.  python3 gam_an.py <file.npy> <mode>
Prints for each conic: the decic p5|C (normalised), its real roots, and for mode 1 the shape check
(coefficients s^5..s^9 relative to s^10) and the weight-invariant of the quartic RHS."""
import numpy as np, sys
src = open('cy4.py').read().split("\nif __name__ == '__main__'")[0]
exec(src)
X = np.load(sys.argv[1]); mode = int(sys.argv[2])
for k, x in enumerate(X):
    Q = qpolys(x)
    f = psum(Q, 5)            # low -> high, degree 10
    f = f/np.abs(f).max()
    rts = np.roots(f[::-1])
    real = np.sort(rts[np.abs(rts.imag) < 1e-7].real)
    line = f"{k}: deg10 coeff {f[10]:+.3e}  real roots {len(real)}"
    if mode == 1:
        line += f"  shape |f5..f9|/|f10| = {np.abs(f[5:10]).max()/abs(f[10]):.1e}"
    # check the points q(s) at real roots lie in W
    worst = 0
    for s in real:
        z = Q @ np.array([1, s, s*s])
        z = z/np.linalg.norm(z)
        p = [np.sum(z**j) for j in (1, 2, 3, 4, 5)]
        worst = max(worst, abs(p[0]), abs(p[2]), abs(6*p[3]-p[1]**2), abs(p[4]))
        mind = min(abs(z[i]-z[j]) for i in range(9) for j in range(i+1, 9))
    print(line, f" W-check {worst:.1e}" + (f" min|zi-zj| {mind:.2e}" if len(real) else ''))
