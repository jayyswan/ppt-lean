# usage: python3 mono60.py <gen|L135|Y4> <seed> <loops> [out.pkl]
# Monodromy of the 60 points W ∩ <P, Π_A> as the isotropic plane Π_A (spinor chart A ∈ C^3) moves in loops.
import sys, pickle, time; sys.path.insert(0, '.')
from w60 import *
kind, seed, loops = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
out = sys.argv[4] if len(sys.argv) > 4 else f'mono60_{kind}_{seed}.pkl'
r = np.random.default_rng(seed)
P = real_X_point(seed)
if kind == 'L135': P = newton_real(P, [lambda z: ps(z,3), lambda z: ps(z,5)])
if kind == 'Y4':   P = newton_real(P, [lambda z: ps(z,3), lambda z: Q4(z)])
print('P checks p1 p3 p5 Q4:', ps(P,1), ps(P,3), ps(P,5), Q4(P))
Fr, sg = spinor_frame(P)
c = r.normal(size=4) + 1j*r.normal(size=4)
S = System(P, c)
A0 = r.normal(size=3) + 1j*r.normal(size=3)
V0 = plane(Fr, A0); S.setV(V0)
def distinct(sols, tol=1e-6):
    o = []
    for X in sols:
        if all(np.linalg.norm(X-Y) > tol*max(1, np.linalg.norm(X)) for Y in o): o.append(X)
    return o
base = []
while len(base) < 60:
    base = distinct(base + total_degree(S)); print('base', len(base))
perms = []; t0 = time.time()
for L in range(loops):
    A1 = A0 + 0.8*(r.normal(size=3) + 1j*r.normal(size=3))
    A2 = A0 + 0.8*(r.normal(size=3) + 1j*r.normal(size=3))
    Vs = [V0, plane(Fr, A1), plane(Fr, A2), V0]
    perm = []; good = True
    for X in base:
        Y = X
        for k in range(3):
            Y, ok = param_track(S, Vs[k], Vs[k+1], Y)
            if not ok: good = False; break
        if not good: break
        i, d = match(base, Y)
        if d > 1e-6: good = False; break
        perm.append(i)
    S.setV(V0)
    if good and len(set(perm)) == 60:
        perms.append(perm)
        cyc = []
        seen = set()
        for i in range(60):
            if i in seen: continue
            j, l = i, 0
            while j not in seen: seen.add(j); j = perm[j]; l += 1
            if l > 1: cyc.append(l)
        print('loop', L, 'cycles', sorted(cyc, reverse=True), f'{time.time()-t0:.0f}s', flush=True)
    else:
        print('loop', L, 'failed', flush=True)
pickle.dump(dict(P=P, A0=A0, c=c, base=base, perms=perms), open(out, 'wb'))
from sympy.combinatorics import Permutation, PermutationGroup
if perms:
    G = PermutationGroup([Permutation(p) for p in perms])
    print('orbits', [len(o) for o in G.orbits()])
    if G.is_transitive(): print('primitive', G.is_primitive(), 'order', G.order() if G.order() < 10**40 else '>1e40', 'is S60', G.is_symmetric)
