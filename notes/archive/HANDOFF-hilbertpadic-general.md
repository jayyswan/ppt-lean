# HANDOFF: hilbertSym padic odd general formula + bilinearity

Target file: `pptc/Pptc/HasseMinkowski/HilbertSymbol/Padic.lean`, namespace `Pptc.HasseMinkowski`.
(Continue appending to `HANDOFF-hilbertpadic.md` too per task; this is the per-subagent log.)

Goal:
1. `hilbertSym_padic_odd_eq` — general Serre formula with `a = p^α u`, `b = p^β v`.
2. `hilbertSym_padic_odd_mul_left (hp) (a a' b)` — multiplicativity.
3. Maybe `instance : HasBilinHilbertSym ℚ_[p]`.

Key structural notes:
- `hilbertSym : k → k → ℤ` (integer-valued!), and `quadraticChar (ZMod p) : ZMod p →* ℤ`.
- Four cases already proved: case00 (two units → 1), case10 (unit u, val1 c → χ(u)),
  case11_units (p u, p v → χ(-(uv))).
- Plan: reduce α,β mod 2 via `Int.emod_add_ediv` + `p^α = p^(α%2)*(p^(α/2))^2` +
  `hilbertSym_mul_square_eq`; then 4-way case split on (α%2, β%2) ∈ {0,1}².
- `χ(u)^β` for β<0: use `χ(u)^(β%2).toNat`.

## Log
- START: read Padic.lean (700 lines) + old handoff + Defs.lean.
- Design: parityPow b n := if Even n then 1 else b; formula RHS =
  parityPow χ(-1)(αβ) * parityPow χ(u)β * parityPow χ(v)α. Reduce α,β mod 2 with
  p^α = p^(α%2)*(p^(α/2))^2 + hilbertSym_mul_square_eq, then 4 parity cases.
- Confirmed lemma names: Int.even_iff, Int.not_even_iff, Int.emod_two_eq_zero_or_one,
  Even.add/add_odd/add_even/add_odd, Int.even_mul, zpow_add₀, Padic.norm_p_zpow,
  Padic.valuation_mul, quadraticChar_dichotomy.
- NEXT: apply big edit to Padic.lean then lake_check.
- Applied edit; first lake_check failed: (a) `rw [hA,hB]` motive not type correct
  (a,b appear inside padicUnit a ha / dependent proof) -> fixed with conv_lhs;
  (b) duplicate zpow_zero/one_mul in rw lists -> replaced with `simp only`;
  (c) missing 2nd `map_mul` for quadraticChar in mul_left -> added.
- Also spelled coercions as `((padicUnit a ha : ℤ_[p]) : ℚ_[p])`.
- Second lake_check: exit 0, one unused-simp warning (`one_mul` at 880) -> removed.
- THIRD lake_check: `OK - no errors or warnings`.
- Deliverables (namespace Pptc.HasseMinkowski, all at end of Padic.lean):
  * `padicUnit (a : ℚ_[p]) (ha : a ≠ 0) : ℤ_[p]ˣ` (public def) + private `coe_padicUnit`,
    `norm_padicUnit`, `padicUnit_spec`, `padicUnit_mul`.
  * `parityPow (b n : ℤ) : ℤ := if Even n then 1 else b` (public def) + private
    `parityPow_of_even`, `parityPow_of_odd`, `parityPow_add`, `parityPow_mul`.
  * `hilbertSym_padic_odd_eq (hp : p ≠ 2) {a b} (ha : a ≠ 0) (hb : b ≠ 0) :
       hilbertSym a b = parityPow χ(-1) (a.valuation * b.valuation)
         * parityPow χ(toZMod (padicUnit a ha)) b.valuation
         * parityPow χ(toZMod (padicUnit b hb)) a.valuation`
     where χ = quadraticChar (ZMod p). (χ(-1) = (-1)^((p-1)/2), so this is
     (-1)^{αβ(p-1)/2}·χ(u)^β·χ(v)^α.)
  * `hilbertSym_padic_odd_mul_left (hp : p ≠ 2) (a a' b) :
       hilbertSym (a*a') b = hilbertSym a b * hilbertSym a' b`.
- Part 3 (instance HasBilinHilbertSym ℚ_[p]): NOT added, deliberately: the
  multiplicativity lemma requires hp : p ≠ 2, so it is not unconditional over ℚ_[p]
  for p = 2; an instance cannot carry that hypothesis. Documented instead.
- Axioms (lean_verify of `hilbertSym_padic_odd_eq`): only propext, Classical.choice,
  Quot.sound.  DONE.

