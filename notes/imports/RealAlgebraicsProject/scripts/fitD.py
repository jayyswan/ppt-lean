import numpy as np, pickle, sys
from bl import *
Y0,c0,d=pickle.load(open('base.pkl','rb'))
rho=float(sys.argv[1]); n=int(sys.argv[2])
def Dval(Y):
    g=sheets(Y); return np.prod([(g[i]-g[j])**2 for i in range(9) for j in range(i+1,9)])
w=float(sys.argv[3]) if len(sys.argv)>3 else 0.0; Y=track(Y0,[c0,c0+(rho+w)*d,c0+rho*d]) if w else track(Y0,[c0,c0+rho*d]); ss=rho*np.exp(2j*np.pi*np.arange(n)/n); vals=[Dval(Y)]; Ys=[Y]
for k in range(1,n):
    Y=track(Y,[c0+ss[k-1]*d,c0+ss[k]*d],h0=0.02)
    if Y is None: print('fail',k); sys.exit()
    vals.append(Dval(Y)); Ys.append(Y)
vals=np.array(vals); c=np.fft.fft(vals)/n  # c[k] = a_k rho^k for k>=0 ; negative k at c[n-k]
a=np.array([c[k]/rho**k for k in range(n//2)])
print('|coef*rho^k| k=0..40:'); print(' '.join('%.1e'%abs(c[k]) for k in range(41)))
print('negative k (n-1..n-8):',' '.join('%.1e'%abs(c[n-k]) for k in range(1,9)))
pickle.dump((rho,n,ss,vals,Ys),open('D_%g.pkl'%rho,'wb'))
