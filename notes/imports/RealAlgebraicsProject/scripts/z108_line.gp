\\ Session 11: the points of the fact 5 locus Z on the symmetric line s' + L (s^2)',
\\ at a random rational x (vector of conjugates). Same elimination as deg108b.gp (Prop. H.1).
\\ Usage: set SEED before reading. Writes the factor list to z108_<SEED>.out and the
\\ largest factor to z108_<SEED>.pol
setrand(SEED);
until(#Set(x)==9, x = vector(9,j,random(41)-20));
a = vector(9,j,9*x[j]-vecsum(x)); x2 = vector(9,j,x[j]^2); b = vector(9,j,9*x2[j]-vecsum(x2));
mm = prod(j=1,9, 'T - (a[j] + L*b[j]));
u = polcoeff(mm,7,'T)/3; m6 = polcoeff(mm,6,'T); m5 = polcoeff(mm,5,'T); m4 = polcoeff(mm,4,'T); m3 = polcoeff(mm,3,'T); m2 = polcoeff(mm,2,'T); m1 = polcoeff(mm,1,'T); m0 = polcoeff(mm,0,'T);
A5 = m5 - 3*u^2; A4 = m4 - 2*u*m6; A2 = m2 - u^2*m6; A1 = m1 - u*(m3 - u^3);
v2v3 = A5/2; v2sq = A5^2/(4*rho); v1v3 = (A4 + 2*u*rho - v2sq)/2;
v1v2 = v1v3*v2v3/rho; v1sq = v1v3^2/rho;
v0v3 = (A1 + 2*u*v1v2)*4*rho^2/(4*A4*rho - A5^2); v0v2 = v0v3*v2v3/rho;
E2 = v1sq + 2*v0v2 - u^2*rho - A2;
Rn = numerator(E2);
g2 = m6 - rho; g1 = m3 - u^3 - 2*v0v3 - 2*v1v2; g0 = m0 - v0v3^2/rho;
dis = poldisc(X^3 + g2*X^2 + g1*X + g0, X);
Dn = numerator(dis);
res = polresultant(Rn, Dn, rho);
f = factor(res);
fn = Str("z108_", SEED, ".out");
write(fn, "x = ", x);
write(fn, "resultant degree in L ", poldegree(res,L));
for(i=1,#f~, write(fn, "factor degree ", poldegree(f[i,1],L), "  multiplicity ", f[i,2]));
big = 1; for(i=1,#f~, if(poldegree(f[i,1],L) > poldegree(f[big,1],L), big = i));
write(Str("z108_", SEED, ".pol"), f[big,1]);
