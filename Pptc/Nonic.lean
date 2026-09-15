import Pptc.NonicPowerLaw
import Pptc.NonicRecovery
import Pptc.NonicTschirnhaus

/-! # The main nonic constructibility theorem

Conjecture N for the monic separable case: every real root of a monic separable degree-9
rational polynomial with a nonreal root is P-constructible.

The construction is Tschirnhaus reduction: pick rational polynomials `ψ, φ` of degree `≤ 6`
such that the resolvent `φ (companion9' q)` has vanishing `X^8` and `X^7` coefficients.
Then `y = φ (ψ β)` satisfies a degree-`≤ 6` power law, hence is P-constructible
(`resolvent_y_Pconstructible9`), and the composition `φ ∘ ψ` of two degree-`≤ 6`
nonconstant rational polynomials recovers `β` from `y` (`nonic_recovery`).

The only missing ingredient is Meyer's theorem (Hasse--Minkowski): the trace form
`Q f = Tr (f ^ 2)` on `ℚ[x]/(q)` restricts to a 6-dimensional indefinite rational
quadratic form with a rational isotropic vector. This is proved in `Pptc.NonicTschirnhaus`
(via `Pptc.HasseMinkowski.meyer`), and `exists_tschirnhaus9` below discharges it. -/

open Polynomial Matrix

namespace Pconstructible

noncomputable section

/-- Tschirnhaus reduction of a monic separable nonic. Mathematically: after applying a
degree-`≤ 6` rational Tschirnhaus transformation `ψ`, the trace form `Tr(f(ψ x)²)` on the
space of degree-`≤ 6` polynomials becomes indefinite, so by Meyer's theorem
(Hasse–Minkowski, `Pptc.HasseMinkowski.meyer`) it has a nonzero rational isotropic vector
`f`; the pair `(ψ, f)` then kills the `X^8` and `X^7` coefficients of the resolvent
(`Pptc.TschirnhausDatum`, proved in `Pptc.NonicTschirnhaus`). -/
theorem exists_tschirnhaus9 {q : Polynomial ℚ} (hmon : q.Monic) (h9 : q.natDegree = 9)
    (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0) :
    ∃ ψ φ : Polynomial ℚ, ψ.natDegree ≤ 6 ∧ 1 ≤ ψ.natDegree ∧
      φ.natDegree ≤ 6 ∧ 1 ≤ φ.natDegree ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 8 = 0 ∧
      ((aeval (companion9' q) (φ.comp ψ)).charpoly).coeff 7 = 0 :=
  exists_tschirnhaus9_of_datum hmon h9 hsep
    (tschirnhausDatum_of_nonreal hmon h9 hsep hrel)

-- Theorem: Conjecture N in the monic separable case. Given a rational Tschirnhaus pair
-- `ψ, φ` (degree `≤ 6`, nonconstant) whose composition kills the `X^8`/`X^7` resolvent
-- coefficients, `φ (ψ β)` is P-constructible by the power-law step and `β` is recovered
-- from it by the two-step degree-`≤ 6` inversion `nonic_recovery`.
theorem root_Pconstructible_of_rat_nonic_nonreal_sep {q : Polynomial ℚ} (hmon : q.Monic)
    (h9 : q.natDegree = 9) (hsep : q.Separable)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0)
    {β : ℝ} (hβ : aeval β q = 0) : PConstructible β := by
  obtain ⟨ψ, φ, hψdeg, hψnc, hφdeg, hφnc, hk8, hk7⟩ :=
    exists_tschirnhaus9 hmon h9 hsep hrel
  have h9c : q.coeff 9 = 1 := by rw [← h9]; exact hmon.coeff_natDegree
  have hy : PConstructible (aeval β (φ.comp ψ)) :=
    resolvent_y_Pconstructible9 hβ h9c (le_of_eq h9) ⟨hk8, hk7⟩
  exact nonic_recovery hψdeg hψnc hφdeg hφnc hy (by rw [Polynomial.aeval_comp])

-- Theorem: Conjecture N in general (non-monic, possibly reducible `q`). Normalise `q` to a
-- monic `q₀`, then pass to the minimal polynomial `m` of `β`. If `deg m ≤ 8`,
-- `root_Pconstructible_le_eight` applies. Otherwise `m` has degree 9 and divides `q₀`, so a
-- degree count forces `q₀ = m`; thus `q₀` is irreducible over `ℚ`, hence separable (char 0),
-- and the monic separable case `root_Pconstructible_of_rat_nonic_nonreal_sep` finishes.
theorem root_Pconstructible_of_rat_nonic_nonreal {q : Polynomial ℚ} (hq : q ≠ 0)
    (h9 : q.natDegree = 9)
    (hrel : ∃ z : ℂ, (q.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0)
    {β : ℝ} (hβ : aeval β q = 0) : PConstructible β := by
  classical
  have hlc : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  set q₀ : Polynomial ℚ := C q.leadingCoeff⁻¹ * q with hq₀
  have hmon₀ : q₀.Monic :=
    Polynomial.monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
  have h9₀ : q₀.natDegree = 9 := by
    rw [hq₀, Polynomial.natDegree_C_mul (inv_ne_zero hlc), h9]
  have hβ₀ : aeval β q₀ = 0 := by simp [hq₀, hβ]
  have hrel₀ : ∃ z : ℂ, (q₀.map (algebraMap ℚ ℂ)).eval z = 0 ∧ z.im ≠ 0 := by
    obtain ⟨z, hz, hzim⟩ := hrel
    exact ⟨z, by simp [hq₀, hz], hzim⟩
  have hint : IsIntegral ℚ β := ⟨q₀, hmon₀, by rwa [aeval_def] at hβ₀⟩
  set m : Polynomial ℚ := minpoly ℚ β with hm
  have hm_monic : m.Monic := minpoly.monic hint
  have hm_ne : m ≠ 0 := minpoly.ne_zero hint
  have hm_root : aeval β m = 0 := minpoly.aeval ℚ β
  have hm_irred : Irreducible m := minpoly.irreducible hint
  have hm_dvd : m ∣ q₀ := minpoly.dvd ℚ β hβ₀
  by_cases hle : m.natDegree ≤ 8
  · exact root_Pconstructible_le_eight hm_ne hle hm_root
  · have hge : 9 ≤ m.natDegree := by omega
    obtain ⟨h, hh⟩ := hm_dvd
    have h_ne : h ≠ 0 := by
      intro hzero
      exact hmon₀.ne_zero (by rw [hh, hzero, mul_zero])
    have hsum : m.natDegree + h.natDegree = 9 := by
      rw [← h9₀, hh, Polynomial.natDegree_mul hm_ne h_ne]
    have hdeg0 : h.natDegree = 0 := by omega
    have hlc_h : h.leadingCoeff = 1 := by
      have h1 : q₀.leadingCoeff = (m * h).leadingCoeff := by rw [hh]
      rw [hmon₀.leadingCoeff, Polynomial.leadingCoeff_mul, hm_monic.leadingCoeff,
        one_mul] at h1
      exact h1.symm
    have hmon_h : h.Monic := hlc_h
    have h_eq : q₀ = m := by
      rw [hh, (hmon_h.natDegree_eq_zero).mp hdeg0, mul_one]
    have hsep₀ : q₀.Separable := by rw [h_eq]; exact hm_irred.separable
    exact root_Pconstructible_of_rat_nonic_nonreal_sep hmon₀ h9₀ hsep₀ hrel₀ hβ₀

end

end Pconstructible
