# p ; factors ; label
run(){ timeout 300 python3 hensram64.py "$1" "$2" 60000 16 1; }
# tame leftovers (e in {3,5}, no involution, no exponent-7/9 Kummer factor)
run 11 "x^9+4*11*x^6+11^3"      # (e,f)=(3,3) field, h = x^3+4x^2+1
run 13 "x^9+1*13*x^6+0*13^2*x^3+2*13^3"      # (3,3) field, h = x^3+x^2+2
run 11 "x^3-11;x^5+2*x^4+1;x"         # L3(e=3) x U5 x Q_p
run 13 "x^3-13;x^3-26;x^3-52"               # three distinct ramified cubics, p = 1 mod 3
run 11 "x^5-11;x^3-11;x"                     # L5(e=5) x L3 x Q_p
run 13 "x^6+1*13*x^3+2*13^2;x^3+x^2+2"      # (e,f)=(3,2) sextic x U3
run 13 "x^3-13;x^3-26;x^2-2;x"               # m = 1: two ramified cubics x U2 x Q_p
