# HANDOFF: two-adic Hilbert symbol closed formula

Goal: in `Pptc/HasseMinkowski/HilbertSymbol/Two.lean` (namespace Pptc.HasseMinkowski), append:
- `hilbertSym_padic_two_adic_eq` : Serre formula for a b : ℚ_[2] nonzero, a = 2^α u, b = 2^β v,
  hilbertSym a b = (-1)^(ε(u)ε(v) + α ω(v) + β ω(u)), ε(u)=0 iff u≡1 mod 4, ω(u) via u≡1 mod 8 test.
- `hilbertSym_padic_two_mul_left` : hilbertSym (a*c) b = hilbertSym a b (nonzero a c), plus symmetry slot.
- HasBilinHilbertSym instance for ℚ_[2] if achievable.

Plan: read Defs.lean, Padic.lean (hilbertSym_padic_odd_eq pattern), Padics/Squares.lean, Two.lean ≤694,
scratch .bak for eps/omg/parityPow helpers. Peel squares to units, use mod-8 obstruction, finish via Serre.

Log:
- created log
