(* R4a-bezier-checks.wl
   Task R4a of PLAN-hypergeometric-00-overview: cubic Bezier arc length as 2F1?
   All checks run through the Wolfram kernel (MCP wolfram_WolframLanguageEvaluator).

   Result: a general cubic Bezier's arc length is an incomplete elliptic integral
   combination (algebraic + incomplete F, E, Pi = Appell F1 / FD), NOT a single 2F1.
   The only 2F1 values a Bezier yields are degenerate: the cubic-graph y=C x^3
   (m=4, graph class) and the h=0 / ellipse complete limit K(c)=(pi/2)2F1(1/2,1/2;1;c)
   (elliptic class).  No new source. *)

(* ---------------------------------------------------------------- *)
(* 1. ThirdKind-family Bezier, concrete rational control points      *)
(*    m = 2, h = 1/2, T = 1/2  (arc over t in [0,T])                  *)
(*    Control pts: (0,0) (1/6,0) (7/24,1/8) (29/96,5/16)              *)
(* ---------------------------------------------------------------- *)
m = 2; h = 1/2; T = 1/2;
phi = ArcTan[2/3];              (* thirdKindTan h phi = T *)
c = 1 - m^2; n = 1 + h^2;       (* c = -3, n = 5/4 *)
Q[t_] = ((1 - h t)^2 - m t^2)^2 + ((1 + m) (1 - h t) t)^2;
{q0, q1, q2, q3, q4} = CoefficientList[Q[t], t];
alpha = 2 q0/3 - q3 q1/(24 q4);
beta  = q1/2   - q3 q2/(12 q4);
gamma = q2/3   - q3^2/(8 q4);
anti[t_] = (q3/(12 q4) + t/3) Sqrt[Q[t]];

(* (a) moment reduction  int_0^T sqrt(Q) = [anti(T)-anti(0)] + int (a+b t+g t^2)/sqrt(Q) *)
lhs1 = NIntegrate[Sqrt[Q[t]], {t, 0, T}, WorkingPrecision -> 60];
rhs1 = (anti[T] - anti[0]) +
   NIntegrate[(alpha + beta u + gamma u^2)/Sqrt[Q[u]], {u, 0, T}, WorkingPrecision -> 60];
Print["1a  moment reduction      diff = ", lhs1 - rhs1];

(* (b) pullback t = sin psi/(cos psi + h sin psi):
       int sqrt(Q) = [anti(T)-anti(0)] + int_0^phi (a+b t+g t^2)/Delta dpsi *)
Del[psi_] = Sqrt[1 - c Sin[psi]^2];
tpsi[psi_] = Sin[psi]/(Cos[psi] + h Sin[psi]);
rhs2 = (anti[T] - anti[0]) +
   NIntegrate[(alpha + beta tpsi[p] + gamma tpsi[p]^2)/Del[p], {p, 0, phi}, WorkingPrecision -> 60];
Print["1b  pullback to Legendre diff = ", lhs1 - rhs2];

(* (c) moment 0 is incomplete F on the nose *)
mom0 = NIntegrate[1/Sqrt[Q[t]], {t, 0, T}, WorkingPrecision -> 60];
Print["1c  int dt/sqrtQ - F(phi,c)  = ", mom0 - N[EllipticF[phi, c], 60]];

(* (d) thirdKindMoment_one: the first moment is the third-kind piece at n = 1+h^2 *)
mom1 = NIntegrate[t/Sqrt[Q[t]], {t, 0, T}, WorkingPrecision -> 60];
i1 = NIntegrate[Sin[p] Cos[p]/((1 - n Sin[p]^2) Del[p]), {p, 0, phi}, WorkingPrecision -> 60];
A  = NIntegrate[Sin[p]^2/((1 - n Sin[p]^2) Del[p]), {p, 0, phi}, WorkingPrecision -> 60];
Print["1d  int t dt/sqrtQ, third kind = ", mom1 - (i1 - h A)];

(* (e) Pi = F + n A  (complete/incomplete third kind relation) *)
Pi0 = NIntegrate[1/((1 - n Sin[p]^2) Del[p]), {p, 0, phi}, WorkingPrecision -> 60];
Print["1e  Pi - (F + n A)          = ", Pi0 - (N[EllipticF[phi, c], 60] + n A)];

(* (f) thirdKind_sum_key, symmetrised h and -h, to 99 digits *)
Qm[t_] = ((1 + h t)^2 - m t^2)^2 + ((1 + m) (1 + h t) t)^2;
{r0, r1, r2, r3, r4} = CoefficientList[Qm[t], t];
antim[t_] = (r3/(12 r4) + t/3) Sqrt[Qm[t]];
Tm = Sin[phi]/(Cos[phi] - h Sin[phi]);   (* = 1 *)
piC = h^2 (h^4 - m^2) (m^2 - 1)^2/((h^2 + 1)^2 (h^2 + m^2)^2);
Q4 = (h^2 + 1) (h^2 + m^2);
Fp = N[EllipticF[phi, c], 100]; Ep = N[EllipticE[phi, c], 100];
Aint = NIntegrate[Sin[p]^2/((1 - n Sin[p]^2) Del[p]), {p, 0, phi}, WorkingPrecision -> 100];
TK = n Sin[phi] Cos[phi] Del[phi]/(1 - n Sin[phi]^2);   (* thirdKindAnti at phi *)
rhs3 = (anti[T] - anti[0]) + (antim[Tm] - antim[0]) + 2 alpha Fp + piC Aint
       + 2 gamma/Q4 ((1 - n) Fp - Ep + TK);
L1 = NIntegrate[Sqrt[Q[t]], {t, 0, T}, WorkingPrecision -> 100];
L2 = NIntegrate[Sqrt[Qm[t]], {t, 0, Tm}, WorkingPrecision -> 100];
Print["1f  sum_key diff            = ", (L1 + L2) - rhs3];

(* ---------------------------------------------------------------- *)
(* 2. h = 0 branch: thirdKindQuartic m 0 = firstKindQuartic m         *)
(*    int_0^{tan phi} dt/sqrt((1+t^2)(1+m^2 t^2)) = F(phi, 1-m^2)     *)
(* ---------------------------------------------------------------- *)
mm = 3; cc = 1 - mm^2; ph2 = 1/3; T0 = Tan[ph2];
Q0[t_] = (1 + t^2) (1 + mm^2 t^2);
Print["2   h=0 branch diff         = ",
  NIntegrate[1/Sqrt[Q0[t]], {t, 0, T0}, WorkingPrecision -> 50] - N[EllipticF[ph2, cc], 50]];

(* ---------------------------------------------------------------- *)
(* 3. Closed-loop Bezier p1=p4=(0,0), p2=(1,0), p3=(0,1)              *)
(*    Q = 9(1-8t+26t^2-36t^3+18t^4); all roots complex, Q(0)=Q(1)=9.  *)
(* ---------------------------------------------------------------- *)
xl[t_] = 3 (1 - t)^2 t;  yl[t_] = 3 (1 - t) t^2;
Ql[t_] = Expand[xl'[t]^2 + yl'[t]^2];
Print["3   closed loop Q            = ", Factor[Ql[t]]];
Print["3   closed loop roots        = ", NRoots[Ql[t] == 0, t, 20]];
Print["3   closed loop Q(0),Q(1)    = ", {Ql[0], Ql[1]}];
Print["3   closed loop length       = ", NIntegrate[Sqrt[Ql[t]], {t, 0, 1}, WorkingPrecision -> 60]];

(* ---------------------------------------------------------------- *)
(* 4. The two degenerate 2F1 cases                                    *)
(* ---------------------------------------------------------------- *)
(* (a) graph of a cubic y = C x^3: m = 4, graph family *)
X = 3/5; Cc = 2/7;
Print["4a  m=4 graph 2F1 diff       = ",
  NIntegrate[Sqrt[1 + 9 Cc^2 x^4], {x, 0, X}, WorkingPrecision -> 60]
   - X N[Hypergeometric2F1[-1/2, 1/4, 5/4, -9 Cc^2 X^4], 60]];
(* (b) h=0 / ellipse complete limit: K(c) = (pi/2) 2F1(1/2,1/2;1;c) *)
cm = 1 - (2/3)^2;
Print["4b  K=(pi/2)2F1 diff         = ",
  N[EllipticK[cm], 60] - (Pi/2) N[Hypergeometric2F1[1/2, 1/2, 1, cm], 60]];

(* ---------------------------------------------------------------- *)
(* 5. Graph of a quadratic: speed^2 quadratic -> elementary           *)
(*    int sqrt(1+(2 a t+b)^2) dt, asinh closed form                   *)
(* ---------------------------------------------------------------- *)
aa = 3/7; bb = -2/5; Tq = 4/3; u[t_] = 2 aa t + bb; S[t_] = Sqrt[1 + u[t]^2];
qexact = (1/(4 aa)) ((u[Tq] S[Tq] - u[0] S[0]) + (ArcSinh[u[Tq]] - ArcSinh[u[0]]));
Print["5   quadratic graph diff     = ",
  NIntegrate[Sqrt[1 + (2 aa t + bb)^2], {t, 0, Tq}, WorkingPrecision -> 50] - N[qexact, 50]];
