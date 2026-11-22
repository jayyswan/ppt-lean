# Session 14: at x54 the w = 0 part of h6 and h7 starts in degree 4, proportional to F = 13 q2^2 - 20 q4.
import sympy as sp
s,u1,u2,u3=sp.symbols('s y1 y2 y3'); I=sp.I
e=[[1,I,-1,-I],[1,-1,1,-1],[1,-I,-1,I]]
z=[s+u1*e[0][j]+u2*e[1][j]+u3*e[2][j] for j in range(4)]+[-4*s]
q2=sp.expand(sum(x**2 for x in z)); q4=sp.expand(sum(x**4 for x in z))
F=sp.expand(13*q2**2-20*q4)
h6_4=(34214400*u3*u1+17107200*u2**2)*s**2+(-10264320*u2*u1**2-10264320*u3**2*u2)*s+(-855360*u1**4+3763584*u3**2*u1**2-1368576*u3*u2**2*u1+1368576*u2**4-855360*u3**4)
print(sp.simplify(sp.expand(h6_4)/F))
