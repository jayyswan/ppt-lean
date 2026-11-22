# Members of the composition family C^3 + A with each number of real roots, irreducible with group S_9.
import random
from cypari import pari
random.seed(7)
pari('isS9(f) = { my(h7=0,h2=0,D=poldisc(f),v); forprime(p=5,600, if(D%p==0, next); v=vecsort(apply(poldegree, factormod(f,p)[,1]~)); if(v==[1,1,7]||v==[2,7], h7=1); if(#select(d->d==2,v)==1 && #select(d->d%2==0,v)==1, h2=1); if(h7&&h2, return(1))); 0 }')
found = {}
n = 0
while len(found) < 5 and n < 3000000:
    n += 1
    c1 = random.randint(-12,3); c0 = random.randint(-4,4)
    k = random.choice([0,0,1,2,3,5,8,12,20,30,40])
    a3 = -k + random.randint(-1,1); a2 = random.randint(-6,6); a1 = -k*c1 + random.randint(-9,9); a0 = -k*c0 + random.randint(-9,9)
    if a2 == 0: continue
    f = pari('(t^3+(%d)*t+(%d))^3 + (%d)*t^3+(%d)*t^2+(%d)*t+(%d)' % (c1,c0,a3,a2,a1,a0))
    r = int(pari.polsturm(f))
    if r in found: continue
    if not pari.polisirreducible(f): continue
    if not pari('isS9')(f): continue
    found[r] = (c1,c0,a3,a2,a1,a0)
    # nonic for w = C(s):  Res_t(C - w, A + w^3)
    N = pari('polresultant(t^3+(%d)*t+(%d) - w, (%d)*t^3+(%d)*t^2+(%d)*t+(%d) + w^3, t)' % (c1,c0,a3,a2,a1,a0))
    print('r = %d: C = t^3 + (%d) t + (%d), A = (%d) t^3 + (%d) t^2 + (%d) t + (%d) | real roots of the w-nonic: %d' % (r,c1,c0,a3,a2,a1,a0,int(pari.polsturm(N))), flush=True)
print('found', sorted(found), 'after', n, 'trials')
