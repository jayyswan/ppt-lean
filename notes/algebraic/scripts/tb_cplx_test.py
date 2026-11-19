from tb_cplx import *
from tb_core import D_point_from_t
sy=Sys(-0.5)
sol=[mp.mpf('4.8080895596226592707111604935'),mp.mpf('0.196080430392452105807112444329'),mp.mpf('-0.779940516469097561562865782942')]
mu,w=D_point_from_t(sol[2],sy.S.r,sy.S.u,1,1); XT,YT=sy.S.W2.to_short(mu,w)
P=sy.P2(complex(sol[0]),complex(sol[1]),complex(XT),complex(YT))
shift=(P[0].mean(),P[1].mean()); c=sy.cubic(P,shift); scale=np.max(np.abs(c))
z=np.array([complex(sol[0]),complex(sol[1]),complex(XT),complex(YT),complex(mp.mpf('-2.99254308781909985471031571022')),complex(mp.mpf('1.50753437552085137572900804281'))])
r,c=sy.F(z,shift,scale); print('residual at real sol (float):',np.abs(r)); print('shift',shift,'scale',scale)
