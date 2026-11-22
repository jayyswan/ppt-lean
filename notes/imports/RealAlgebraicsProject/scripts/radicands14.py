# Session 14: adds r9 and R14 to radicands13.pkl (run radicands13.py first).
# r9 = 14 p2 h7 + 5 p3 h6: cubic tangent cones at x8 cancel; Hessian along Pi at u_-1 is
#      15360 (a-b)^2 (5a+4b)^2 (5a^3+154a^2b+352ab^2+245b^3)  (exact, exact14.py r9).
# R14: degree 14, order 4 along Pi, normal quartic c1 (sum u^2)^2 + c2 sum u^4 with
#      c2 = -50803200 (a-b)^4 (5a+4b)^4 (15765671a^2+36592820ab+20049155b^2),
#      c1 = 28800 (a-b)^4 (5a+4b)^4 (17937428359a^2+44082799444ab+26790978199b^2)  (exact, exact14.py R14).
#      Found by r14.py (4-dim space in degree 14 with ord c1 >= 4 = ord c2 at a = b); this is the shortest element tried.
import pickle
r = pickle.load(open('radicands13.pkl','rb'))
r['r9'] = '2525*p2**3*p3 - 9072*p2**2*p5 - 10060*p2*p3*p4 + 20160*p2*p7 + 3680*p3**3 - 7200*p3*p6'
r['R14'] = '255533126625*p2**4*p6 - 3845721038580*p2**3*p3*p5 - 52308485775*p2**3*p4**2 + 1027936734300*p2**3*p8 + 2233063864350*p2**2*p3**2*p4 + 3740357980800*p2**2*p3*p7 - 7384956768000*p2**2*p4*p6 + 9689218887168*p2**2*p5**2 + 4460251150400*p2*p3**4 - 15452363612400*p2*p3**2*p6 + 26247975293520*p2*p3*p4*p5 - 10664283772800*p2*p3*p9 + 2596047892200*p2*p4**3 - 4148470771200*p2*p4*p8 - 31188422321280*p2*p5*p7 + 19025376602400*p2*p6**2 - 8149116117120*p3**3*p5 - 2244196479000*p3**2*p4**2 + 21303834350400*p3**2*p8 + 2451403987200*p3*p4*p7 - 23754104611200*p3*p5*p6 + 5661945752400*p4**2*p6 - 37145405744640*p4*p5**2 + 84575077171200*p5*p9 - 27659611728000*p6*p8 - 11573970508800*p7**2'
pickle.dump(r, open('radicands13.pkl','wb'))
print('r9 =', r['r9']); print('R14 =', r['R14'])
