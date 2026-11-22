# Verify Tr_{K/L}(a^k) for a = al + be*rho + ga*rho^2, rho^3 = m, via numeric conjugates
import cmath, random
w = cmath.exp(2j*cmath.pi/3)
def tr(al,be,ga,m,k):
    r = m**(1/3)
    return sum((al+be*r*w**i+ga*(r*w**i)**2)**k for i in range(3))
def f3(al,be,ga,m): return 3*(al**3+m*be**3+m*m*ga**3+6*m*al*be*ga)
def f5(al,be,ga,m): return 3*(al**5+10*m*(al**2*be**3+2*al**3*be*ga)+m*m*(10*al**2*ga**3+30*al*be**2*ga**2+5*be**4*ga)+5*m**3*be*ga**4)
for _ in range(3):
    al,be,ga,m=[complex(random.uniform(-2,2),random.uniform(-2,2)) for _ in range(4)]
    print(abs(tr(al,be,ga,m,1)-3*al), abs(tr(al,be,ga,m,3)-f3(al,be,ga,m)), abs(tr(al,be,ga,m,5)-f5(al,be,ga,m)))
