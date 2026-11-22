# Search u in Z[kappa], kappa^3 = lam, such that D_u: Tr(u x^3)=0 and D_{u^2} have no Q_p-points for some p.
import itertools, sys
lam = 10
def mul(x,y):  # elements of Q(kappa) as (a,b,c)
    a,b,c = x; d,e,f = y
    return (a*d + lam*(b*f+c*e), a*e+b*d+lam*c*f, a*f+b*e+c*d)
def Dform(u):
    a,b,c = u
    def F(p,q,r):
        A0 = p**3+lam*q**3+lam**2*r**3+6*lam*p*q*r
        A1 = 3*p*p*q+3*lam*p*r*r+3*lam*q*q*r
        A2 = 3*p*p*r+3*p*q*q+3*lam*q*r*r
        return a*A0 + lam*(b*A2 + c*A1)
    return F
def check_form(F,u):  # sanity: F(x) = const part of u*x^3
    import random
    for _ in range(5):
        x = tuple(random.randint(-5,5) for _ in range(3))
        assert F(*x) == mul(u,mul(x,mul(x,x)))[0]
def solvable_mod(F,P,N):
    # primitive solutions mod P^n, n=1..N
    sols = [s for s in itertools.product(range(P),repeat=3) if any(v%P for v in s) and F(*s)%P==0]
    mod = P
    for n in range(2,N+1):
        new = []
        for s in sols:
            for t in itertools.product(range(P),repeat=3):
                x = tuple(s[i]+mod*t[i] for i in range(3))
                if F(*x) % (mod*P) == 0: new.append(x)
        mod *= P
        # reduce: keep unique
        sols = list(set(new))
        if not sols: return False, n
        if len(sols) > 20000: return True, n  # give up: assume solvable
    return True, N
res = []
R = range(-2,3)
for u in itertools.product(R,R,R):
    if u==(0,0,0): continue
    F1, F2 = Dform(u), Dform(mul(u,u))
    check_form(F1,u)
    ob1 = [P for P in (2,3,5,7) if not solvable_mod(F1,P,5 if P<5 else 3)[0]]
    if not ob1: continue
    ob2 = [P for P in (2,3,5,7) if not solvable_mod(F2,P,5 if P<5 else 3)[0]]
    if ob2: res.append((u,ob1,ob2)); print(u, ob1, ob2, flush=True)
print("found", len(res))
