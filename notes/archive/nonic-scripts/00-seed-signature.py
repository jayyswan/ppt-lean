# Route: rational nonic q with r2 conjugate pairs. Want rational phi = poly of degree<=6 in z = psi(beta)
# (psi rational, deg<=6) with p1(phi)=p2(phi)=0. Meyer: a rational indefinite form in >=5 vars is isotropic over Q.
# So the question is whether the trace form restricted to {phi(z): deg phi<=6} ∩ {p1=0} (6-dim) is INDEFINITE.
import numpy as np
rng = np.random.default_rng(0)

def restricted_signature(roots, psi_coeffs):
    w = np.polyval(psi_coeffs, roots)                  # z-values at the 9 roots
    F = np.array([w**k for k in range(7)])             # value vectors of 1, z, ..., z^6
    G = np.real(F @ F.T)                               # Gram of trace form B(f,g)=sum f(l)g(l)  (sum over conj-closed set is real)
    # restrict to p1=0: basis z^k - (Tr z^k / 9)*1, k=1..6
    tr = np.real(F.sum(axis=1))
    P = np.zeros((6, 7)); 
    for k in range(1, 7): P[k-1, k] = 1; P[k-1, 0] = -tr[k] / 9
    H = P @ G @ P.T
    ev = np.linalg.eigvalsh((H + H.T) / 2)
    scale = np.max(np.abs(ev))
    return int((ev > 1e-9*scale).sum()), int((ev < -1e-9*scale).sum())

def random_roots(r2):
    r1 = 9 - 2*r2
    real = list(rng.uniform(-3, 3, r1))
    cplx = []
    for _ in range(r2):
        c = complex(rng.uniform(-3, 3), rng.uniform(0.2, 3)); cplx += [c, c.conjugate()]
    return np.array(real + cplx, dtype=complex)

ident = [1, 0]
print("psi = identity (phi of degree <=6 in beta itself):")
for r2 in range(0, 5):
    tot = 2000; indef = 0
    for _ in range(tot):
        p, n = restricted_signature(random_roots(r2), ident)
        indef += (p > 0 and n > 0)
    print(f"  r2={r2} ({9-2*r2} real roots): indefinite in {indef}/{tot} random configurations")

print("\nr2 in {1,2}: configurations where identity fails -- does some small-integer psi of degree<=6 rescue it?")
for r2 in (1, 2):
    fails = rescued = 0
    tries = 0
    while fails < 200 and tries < 100000:
        tries += 1
        roots = random_roots(r2)
        p, n = restricted_signature(roots, ident)
        if n > 0: continue
        fails += 1
        for attempt in range(3000):
            deg = rng.integers(2, 7)
            psi = rng.integers(-6, 7, deg + 1).astype(float)
            if psi[0] == 0: continue
            p2_, n2_ = restricted_signature(roots, psi)
            if p2_ > 0 and n2_ > 0:
                rescued += 1; break
    print(f"  r2={r2}: {fails} failing configurations, rescued by some integer psi in {rescued}")
