# Session 39: exact identity disc_x(G) = k * (4a^3+27b^2)^15 * A^7 * B^4 (symbolic in a, b, U)
import cypari,time; P=cypari.pari; P.allocatemem(6*10**9)
for l in open('EngineO.gp'):
    l=l.strip()
    if l and not l.startswith('\\\\'): P(l)
t=time.time()
P('D=poldisc(G,x)'); print('disc computed',round(time.time()-t,1),flush=True)
P('Q=D/(Au^7*Bu^4)')
print('quotient is polynomial:',P('type(Q)'), ' value:', P('factor(Q)'), round(time.time()-t,1))
