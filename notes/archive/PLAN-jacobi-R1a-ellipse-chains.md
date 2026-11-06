# PLAN-jacobi-R1a: arc lengths of ellipse-based offset/affine chains

Read `PLAN-jacobi-00-overview.md` first. Research task: **no `.lean` edits**.
Log: `HANDOFF-jacobi-R1a.md`. Deliverable: `NOTES-jacobi-R1a.md` (repo root).

## Question

Take the base `ellipse` / `rectangle`-free class: every curve obtained from an ellipse (or
circle) by any finite chain of `translate`, `scale_x`, `scale_y`, `rotate` (whole degrees, but
combined with scaling any constructible linear map is reachable, so allow any `A ∈ GL₂` with
constructible entries) and `offset` (constructible `d`). Is there a chain whose arc length, in
some parametrisation `T`, is `α·F(φ(T), c) + β` with `φ` algebraic in `(cos T, sin T)` or in
another explicit constructible way, for some `c ≠ 0`?

## Steps

1. Numerically verify the chain formula (F3) of the overview for a depth-3 chain (offset, map,
   offset, map, offset, map) at random parameters. Use `mpmath.diff`, 25+ digits. If it is
   wrong, derive and verify the correct one before anything else.
2. Base `v = (cos t, b·(−sin t))`, so `v × v′ = b` is constant. Write `Q_k(v) = α_k + β_k cos 2t
   + γ_k sin 2t`. Do the "all phases equal" case (`γ_k = 0` after a shift of `t`) and the
   general case.
3. For each term of `ds_n`, identify the elliptic curve it lives on (variable `w = cos 2t` or
   `x = sin²t`) and decompose it as first kind + second kind + third kind + exact, with explicit
   coefficients. Use sympy for the reductions (Hermite reduction / moment recursion), and check
   every reduction numerically.
4. Decide: can the second-kind classes cancel and the exact part vanish identically, leaving
   `c·ω` on one curve? Pay special attention to:
   * `Q_n` constant (final map sends the ellipse's velocity form to a circle's), which makes the
     leading term elementary;
   * two stages with the **same** elliptic curve but different phases `γ_k` (Landen/addition
     relations between shifted angles?);
   * sign flips `|1 − d·…|` past cusps (the constructor does not forbid them).
5. Write the notes: the formula, a table of cases with the decomposition, and a verdict. State
   precisely which assumptions the verdict uses.

## Stop

Stop when you have either a verified breakthrough curve or the verdict table covering the
cases in step 4. Do not wander into polynomial or sine bases; other tasks own those.
