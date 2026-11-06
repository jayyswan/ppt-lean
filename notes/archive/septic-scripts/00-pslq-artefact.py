# Does PSLQ at 200 digits with huge maxcoeff "find" low-degree minimal polynomials for RANDOM numbers?
import mpmath, random
mpmath.mp.dps = 210
random.seed(1)
for trial in range(4):
    x = mpmath.mpf(random.randint(10**5, 10**6)) / 1000 + mpmath.rand()   # a random 200-digit real ~ 100-1000, like Delta
    for deg in range(1, 8):
        rel = mpmath.pslq([x**k for k in range(deg+1)], tol=mpmath.mpf(10)**-180, maxcoeff=10**80, maxsteps=10**6)
        if rel:
            val = abs(sum(c * x**k for k, c in enumerate(rel)))
            print(f"trial {trial}: random x -> 'minimal polynomial' of degree {deg}, max|coeff| ~ 1e{len(str(max(abs(c) for c in rel)))-1}, |p(x)| = {mpmath.nstr(val,3)}")
            break
    else:
        print(f"trial {trial}: no relation up to degree 7")
