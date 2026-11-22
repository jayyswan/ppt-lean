# Session 40: (1) A, B absolutely irreducible: Galois group of a rational specialisation is primitive
#   (a factorisation over Qbar into k conjugate factors would give blocks of size 6/k; k=6 or 5 is impossible by weight);
# (2) no pencil relation A^{5m} = alpha B^{6m} + beta Dh^{5m}: U^(30m-2) coefficients differ.
exec(open('load.py').read())
for nm in ('Au','Bu'):
    print(nm,'factors over Q[U,a,b]:',len(P(f'factor({nm})')[0]))
    for (aa,bb) in ((1,'7/3'),(-1,'1/5'),(2,'-3')):
        g=P(f'substvec({nm},[a,b],[{aa},{bb}])')
        g=P(f'{g}*denominator(content({g}))')
        irr=P('polisirreducible')(g); print('   a,b=',aa,bb,'irreducible:',irr,' polgalois:',P('polgalois')(g) if irr else '-')
for m in (1,2,3):
    print('m',m,'U^(30m-2) coeff of A^5m - B^6m:', P(f'polcoef(Au^{5*m}-Bu^{6*m},{30*m-2},U)'))
