# Tangent cones at x8 of the radicands, in the Z4xZ4 eigencoordinates.
from newton import *
import sys
setup(1,1,9,'Z4xZ4')
for nm in sys.argv[1].split(','):
    S=pari(rad[nm].replace('**','^'))
    v=int(pari.valuation(S,pari('E')))
    for d in range(v, v+2):
        F=pari.polcoef(S,d,pari('E'))
        print(nm,'deg',d,':',str(F)[:700])
