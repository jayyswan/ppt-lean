# HANDOFF-hypergeometric-R5

Research task R5: does the box machinery move the B6 obstruction?

- [step 0] Created this log. Reading PLAN overview, R1 (B6 analysis), R4 notes,
  Defs.lean, PLAN-bounding-box.md, Box.lean, BoxGraph.lean, BoxOffset.lean.
- [step 1] Read PLAN §2 V4, §4 H6, §5 B6/B7, §6–§7; R1 §1–§4; R4 + R4a/b/c;
  Defs.lean (all constructors); Box.lean W1–W4; BoxGraph.lean; BoxOffset.lean.
  Confirmed the box outputs: parabola/cubic/quartic arc abscissas + offset cusp abscissa.
- [step 2] Wolfram checks (R5-box-b6-checks.wl, run via the Wolfram kernel, not `py`):
  * B6 target A = (1/10)B(1/10,2/5) = Γ(1/10)Γ(2/5)/(10√π) = 1.1905798216203709653…
    [NC 30]; equals ∫₀^∞ dx/√(1+x^10) exactly [NC 25].
  * first-kind *incomplete* integral I(b) = ∫₀^b dx/√(1+x^10) at the four box numbers:
    I(0.44633)=0.44632752, I(0.79071)=0.78739563, I(0.81045)=0.80615035,
    I(3.01515)=1.18755498 — all `< A` [NC 25].
  * PSLQ {1, A, (1/10)B(1/5,3/10), box} at 120 wp / tol 1e−90: **no relation** for all
    four box numbers [NC 120].
  * quartic abscissa b₄ = 0.8104516200584422351… satisfies ∫₀^{b₄}√(1+16x⁶)dx = 1
    (return 1.00000000000000000) [NC 18].
  * offset cusp abscissa: max of x(t) − y'(t)/√(x'²+y'²) on [0,1] is attained at the
    cusp t* = 0.9690856778319226534… (κ(t*)=1) and equals 3.0151518126…; the cusp
    parameter is a root of the honest degree-12 polynomial D(t)³ − w(t)² (D =
    (x'²+y'²), w = x'y''−y'x''), so the abscissa is **algebraic** [NC 40]/[SY].
- [step 3] Found and corrected an R1 transcription slip: the second m=10 period is
  (1/10)B(3/20,7/20) = 0.89354817…, **not** (1/10)B(1/5,3/10) = 0.7748481…; the
  (1/10)B(1/5,3/10) value is Γ(1/5)Γ(3/10)/(10√π), still new at denominators 5,10.
  The headline A is correct as R1/PLAN state it.
- [step 4] Wrote NOTES-hypergeometric-R5.md (answer-in-brief, systematic audit,
  primitives, ledger, scripts table) and R5-box-b6-checks.wl.
- [step 5] Verdict: **B6 is unchanged.** Done.
