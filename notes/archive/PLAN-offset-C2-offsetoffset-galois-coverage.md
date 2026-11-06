# PLAN-offset-C2: offset×offset — full Galois data and whole-degree coverage

Read `PLAN-offset-00-overview.md`, `NOTES-offset-A3.md`, and `NOTES-offset-Z.md` §3 (A3 rows).
Log: `HANDOFF-offset-C2.md`; deliverable: `NOTES-offset-C2.md`.

## The question

Z independently confirmed: two cubic-pair offsets meet with honest elimination degree
`96 = q₁·f₉₂`, `q₁ = 45t⁴−24t³+148t²−92t+29` (the speed² of the first base curve), `f₉₂`
irreducible of degree 92 over ℚ, and `Gal(f₉₂/ℚ) = S₉₂` (a 53-cycle + odd permutations, mod 74
primes). What is still open is whether **any** offset×offset family can cover a whole degree, and
what the totality of that trade-off is.

## Questions

1. **Exact `f₉₂` and its field of definition.** Extract the exact integer `f₉₂` (Z did this via
   Wolfram `FactorList[Resultant[G,H,t₂]]`, but only the leading/factor data were stored). Record
   the full coefficient vector in a script so future work need not recompute it.
2. **Real-root statistics.** For a grid of cubic pairs, `(d₁,d₂)`, count real roots of the honest
   elimination polynomial. A3's instance has 12/96 real; how high can the real count go? A high
   real count is the precondition for any totally-real target (B1's frontier).
3. **Coverage.** For a prescribed target degree `n` (say 7), does the offset×offset family have an
   incidence with dimension ≥0 after fixing the target as a factor? Offset×offset has ≤18 raw
   parameters, but the image is *implicit* (two degree-10 curves), so the cofactor analysis of A2
   needs redoing on the incidence variety. Decide whether offset×offset adds anything over A2's
   explicit second curves.
4. **Self-crossing and the centre map.** A3's self-crossing parameter has degree 32 (imprimitive)
   and the centre degree 16. Confirm the imprimitivity and the `(16)²·(32)` elimination split
   independently, and decide whether the degree-halving by symmetry generalises.

## Methods

* Wolfram for the exact `f₉₂` (store coefficients), sympy for modular sampling and resultant
  degree bookkeeping; mpmath for the real counting.
* For coverage: implicitize the offset curve (degree 10), then compute the dimension of
  `{offset₁ ∩ (target · g)}` with the target fixed by a random rational instance (Groebner /
  homotopy count).
* Keep all jobs bounded; use one CAS per question.

## Deliverable

`NOTES-offset-C2.md`: exact `f₉₂` and its Galois group (independent re-check), real-root
statistics, and a verdict on whether offset×offset can cover a whole degree. Tag evidence; report
any negative as the exact class excluded.
