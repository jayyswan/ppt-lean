\\ Session 6: is each E-fixed point (E = (Z/2)^3) on the fact 5 hypersurface Z? Restrict the H.1 resultant to random lines through it. Run with run_read.py; output in zfix.out2
zres(a,b) = {
  my(mm = prod(j=1,9, 'T - (a[j] + L*b[j])), u,m6,m5,m4,m3,m2,m1,m0,A5,A4,A2,A1,v2v3,v2sq,v1v3,v1v2,v1sq,v0v3,v0v2,E2,Rn,g2,g1,g0,Dn);

  u = polcoeff(mm,7,'T)/3; m6 = polcoeff(mm,6,'T); m5 = polcoeff(mm,5,'T); m4 = polcoeff(mm,4,'T); m3 = polcoeff(mm,3,'T); m2 = polcoeff(mm,2,'T); m1 = polcoeff(mm,1,'T); m0 = polcoeff(mm,0,'T);
  A5 = m5 - 3*u^2; A4 = m4 - 2*u*m6; A2 = m2 - u^2*m6; A1 = m1 - u*(m3 - u^3);
  v2v3 = A5/2; v2sq = A5^2/(4*rho); v1v3 = (A4 + 2*u*rho - v2sq)/2;
  v1v2 = v1v3*v2v3/rho; v1sq = v1v3^2/rho;
  v0v3 = (A1 + 2*u*v1v2)*4*rho^2/(4*A4*rho - A5^2); v0v2 = v0v3*v2v3/rho;
  E2 = v1sq + 2*v0v2 - u^2*rho - A2; Rn = numerator(E2);
  g2 = m6 - rho; g1 = m3 - u^3 - 2*v0v3 - 2*v1v2; g0 = m0 - v0v3^2/rho;
  Dn = numerator(poldisc(X^3 + g2*X^2 + g1*X + g0, X));
  [polresultant(Rn, Dn, rho), A5, A4, pollead(Rn,rho), polcoeff(Rn,0,rho)]
};
setrand(11);
b0 = vector(9,j,random(41)-20); b0 = vector(9,j,9*b0[j]-vecsum(b0));
a0 = vector(9,j,random(41)-20); a0 = vector(9,j,9*a0[j]-vecsum(a0));
GG = zres(a0,b0);
write("zfix.out2", "generic line: A5 deg ", poldegree(GG[2],L), " A4 deg ", poldegree(GG[3],L), " lead(R) ", factor(GG[4]), "  const(R) deg ", poldegree(GG[5],L));
f = factor(GG[1]); for(i=1,#f~, write("zfix.out2", "  generic factor deg ", poldegree(f[i,1],L), " mult ", f[i,2], "  divides A5: ", GG[2]%f[i,1]==0, "  divides A4: ", GG[3]%f[i,1]==0));
x1 = [0,1,1,1,1,-1,-1,-1,-1]; x2 = [-8,1,1,1,1,1,1,1,1];
{
for(k=1,2, my(x = if(k==1,x1,x2), H, r, ff, z, Z);
  for(trial=1,2,
    my(bb = vector(9,j,random(41)-20)); bb = vector(9,j,9*bb[j]-vecsum(bb));
    H = zres(x, bb); r = H[1];
    \\ strip the spurious factors seen on generic lines: powers of A5 and of the degree-8 factor
    ff = factor(r); Z = 1; z = 0;
    for(i=1,#ff~, if(poldegree(ff[i,1],L)>=1 && H[2]%ff[i,1]!=0 && ff[i,2]==1, Z *= ff[i,1]));
    write("zfix.out2", "point ", k, " line ", trial, ": resultant deg ", poldegree(r,L), " val at L=0: ", valuation(r,L),
      "  factors(deg,mult): ", vector(#ff~,i,[poldegree(ff[i,1],L), ff[i,2]]),
      "  A5 val at 0: ", valuation(H[2],L))));
}
