# PLAN-jacobi-R1c: arc lengths of sine and `2^x` chains

Read `PLAN-jacobi-00-overview.md` first. Research task: **no `.lean` edits**.
Log: `HANDOFF-jacobi-R1c.md`. Deliverable: `NOTES-jacobi-R1c.md` (repo root).

## Question

Bases: `sine` (`y = sin x`) and `exp_two` (`y = 2^x`). Closure: constructible linear maps,
translations, `offset`. The speed of any such curve is algebraic in `(cos x, sin x)` resp. in
`2^x`. Is there a curve in this class whose arc length is exactly `α F(φ(T), c) + β`?

## Steps

1. Sine graph under a linear map: `ds = √(q₀ + q₁ cos x + q₂ cos²x) dx`. With `w = cos x`,
   this lives on `y² = (1−w²)(q₀+q₁w+q₂w²)`. Decompose it into kinds. It is `E`-type for
   `y = A sin x`. Are there maps making the second-kind part vanish?
2. Add offsets via (F3), with `v = (1, cos x)` and `v × v′ = −sin x`. Decompose every term. Note
   that `sin x dx = −dw` removes the `√(1−w²)`, so these correction terms live on **different**
   curves `y² = Q_n(w) Q_k(w)`. Can they cancel against step 1's second-kind part? Only if the
   curves are isogenous with compatible classes; check.
3. `2^x`: with `z = 2^x`, `dx = dz/(z ln 2)`, and the speed becomes `√(1 + (ln2)² z²)`. That is
   genus 0 plus logs. Check whether offsets and maps can reach genus 1 here, and if so, what
   kinds appear.
4. Also check the curves where a transcendental base gives an **algebraic** reparametrised arc
   length. For example, is some offset of the sine curve's arc length a first-kind integral in
   the variable `w = cos x`, with the `√(1−w²)` absorbed?
5. Write the notes with a verdict and its assumptions.

## Stop

Stop at a verified breakthrough, or once steps 1–5 are written.
