# HANDOFF-jacobi-R1a

Task: arc lengths of ellipse-based offset/affine chains.
Deliverable: NOTES-jacobi-R1a.md (repo root). No .lean edits.

- [start] Read PLAN-jacobi-00-overview.md and PLAN-jacobi-R1a-ellipse-chains.md.
- [step1-start] Verified env (mpmath 1.3.0, sympy 1.12, numpy 1.26.4, scipy 1.12.0). Scripts dir exists. Now verifying chain formula (F3) numerically.
- [retry] R1a retry started 2026-09-12T23:49:58.2652248-04:00. Plan read. Will verify (F3) with sympy, not nested mp.diff.
- [step1-done] (F3) verified. One-step identity n'=-(K/Q^{3/2})v exact via sympy (R1a-02, PASS). Depth-3 verified to ~1e-30 with jet/Taylor arithmetic (R1a-03, PASS) for S>0 and sign-flip cases. F3 as written (plain sum) is WRONG once S crosses 0; correct recurrence S_{k+1}=S_k - d_k sign(S_k) det A_(k) K / q_k^{3/2}.
- [step2-done] q_k structure verified symbolically+numerically (R1a-04): q_k=alpha+beta cos2t+gamma sin2t=mu(1-kappa^2 sin^2(t-phi/2))=N_k(z)/(1+z^2), z=tan t. Similarity maps => q_k proportional to q_0; distinct kappa needs non-conformal A_(k).
- [step3-done] Reductions verified (R1a-05/06): sqrt(q_n)=2nd kind; 1/q_k=elementary (symbolic); mixed sqrt(q_n)/q_k^{3/2} has order-3/2 pole at zeros of q_k (numeric eps^1.5 constant), hence non-holomorphic. int dt/q^{3/2}=(E-algebraic)/(a^2-b^2).
- [step4-5-done] Verdict table + assumptions written. NO BREAKTHROUGH: useful negative. First-kind forms are holomorphic; corrections have finite poles, leading term finite there, so no cancellation. Landen and sign-flip loopholes closed; only u-dependent constructions (R3 L1) remain. NOTES-jacobi-R1a.md COMPLETE.
- [correction] Precise classification: correction term sqrt(q_n)/q_k^{3/2} has an order-3/2 (2nd-kind) pole at zeros of q_k, EXCEPT when q_k proportional to q_n where it is lambda^{-3/2}/q_n (third kind, simple pole, nonzero residue). Either way non-holomorphic at finite points; first-kind forms are holomorphic => no first-kind. Notes finalized.
