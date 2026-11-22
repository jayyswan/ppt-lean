import numpy as np, sys
from bl import *
X=find_lines(int(sys.argv[1]),int(sys.argv[2])); np.save('dl_%s.npy'%sys.argv[1],X); print(len(X))
