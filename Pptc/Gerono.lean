import Pptc.Basic

/-!
# The lemniscate of Gerono from the *Triangle* text warp

The lemniscate of Gerono is the figure eight `x ^ 4 = x ^ 2 - y ^ 2`. It is drawn in four moves:

1. take the text character `◠` (`TextGlyph.upperHalfCircle`, U+25E0 UPPER HALF CIRCLE);
2. apply the *Triangle* warp `(x, y) ↦ (x * y, y)` to it (`PConstructibleCurve.text_triangle`).
   The half circle `x² + y² = 1, y ≥ 0` becomes one lobe, `x ^ 2 = y ^ 2 * (1 - y ^ 2), 0 ≤ y`
   (theorem `triangleWarp_upperSemicircle`);
3. duplicate the lobe and mirror the copy in the `x`-axis, keeping both
   (`PConstructibleCurve.mirror_union`). Together they are the whole figure eight, standing
   upright (theorem `mirror_geronoLobe`);
4. to lay the figure eight on its side, as `x ^ 4 = x ^ 2 - y ^ 2`, swap the two coordinates,
   which is the linear map `[[0, 1], [1, 0]]` (theorem `geronoLemniscate_PConstructibleCurve`).

The three geometric facts (`triangleWarp_upperSemicircle`, `mirror_geronoLobe`,
`swap_geronoVertical`) are proved here from scratch; the `PConstructibleCurve` statements are what
the new text constructors of `Pptc.Defs` buy.
-/

namespace Pconstructible

def geronoLobe : Set (ℝ × ℝ) := {p | p.1 ^ 2 = p.2 ^ 2 * (1 - p.2 ^ 2) ∧ 0 ≤ p.2}
def geronoVertical : Set (ℝ × ℝ) := {p | p.1 ^ 2 = p.2 ^ 2 * (1 - p.2 ^ 2)}
def geronoLemniscate : Set (ℝ × ℝ) := {p | p.1 ^ 4 = p.1 ^ 2 - p.2 ^ 2}
def swapXY (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1)

/-- Item 3: the Triangle warp carries the upper semicircle onto one lobe of the Gerono lemniscate. -/
theorem triangleWarp_upperSemicircle : triangleWarp '' upperSemicircle = geronoLobe := by
  ext ⟨X, Y⟩
  constructor
  · rintro ⟨⟨x, y⟩, ⟨hc, hy⟩, h⟩
    have hc1 : x ^ 2 + y ^ 2 = 1 := hc
    have hy' : 0 ≤ y := hy
    have hXY : x * y = X ∧ y = Y := by simpa [triangleWarp] using h
    obtain ⟨hX, hY⟩ := hXY
    subst hX
    subst hY
    refine ⟨?_, hy'⟩
    show (x * y) ^ 2 = y ^ 2 * (1 - y ^ 2)
    have hx : x ^ 2 = 1 - y ^ 2 := by linarith
    calc (x * y) ^ 2 = x ^ 2 * y ^ 2 := by ring
      _ = (1 - y ^ 2) * y ^ 2 := by rw [hx]
      _ = y ^ 2 * (1 - y ^ 2) := by ring
  · rintro ⟨hX, hY⟩
    have hX' : X ^ 2 = Y ^ 2 * (1 - Y ^ 2) := hX
    have hY' : 0 ≤ Y := hY
    rcases hY'.eq_or_lt with h0 | hpos
    · -- Y = 0 : then X = 0, and the preimage is the end point (1, 0) of the arc
      have hY0 : Y = 0 := h0.symm
      subst hY0
      have hX0 : X = 0 := by
        have : X ^ 2 = 0 := by rw [hX']; ring
        exact pow_eq_zero_iff (two_ne_zero) |>.mp this
      subst hX0
      refine ⟨(1, 0), ⟨?_, le_refl _⟩, ?_⟩
      · show (1 : ℝ) ^ 2 + 0 ^ 2 = 1
        norm_num
      · simp [triangleWarp]
    · -- Y > 0 : preimage is (X / Y, Y)
      have hYne : Y ≠ 0 := ne_of_gt hpos
      have hq : (X / Y) ^ 2 = 1 - Y ^ 2 := by
        rw [div_pow, hX']
        field_simp
      refine ⟨(X / Y, Y), ⟨?_, hY'⟩, ?_⟩
      · show (X / Y) ^ 2 + Y ^ 2 = 1
        linarith
      · show (X / Y * Y, Y) = (X, Y)
        rw [div_mul_cancel₀ X hYne]

/-- Item 4: the lobe together with its mirror image in the x-axis is the whole figure eight. -/
theorem mirror_geronoLobe : geronoLobe ∪ mirrorY '' geronoLobe = geronoVertical := by
  ext ⟨X, Y⟩
  constructor
  · rintro (⟨hX, _⟩ | ⟨⟨a, b⟩, ⟨hab, _⟩, h⟩)
    · exact hX
    · have hab' : a ^ 2 = b ^ 2 * (1 - b ^ 2) := hab
      have hXY : a = X ∧ -b = Y := by simpa [mirrorY] using h
      obtain ⟨hX, hY⟩ := hXY
      subst hX
      subst hY
      show a ^ 2 = (-b) ^ 2 * (1 - (-b) ^ 2)
      rw [neg_sq]
      exact hab'
  · intro hX
    have hX' : X ^ 2 = Y ^ 2 * (1 - Y ^ 2) := hX
    by_cases hY : 0 ≤ Y
    · exact Or.inl ⟨hX', hY⟩
    · right
      refine ⟨(X, -Y), ⟨?_, ?_⟩, ?_⟩
      · show X ^ 2 = (-Y) ^ 2 * (1 - (-Y) ^ 2)
        rw [neg_sq]
        exact hX'
      · show 0 ≤ -Y
        linarith [not_le.mp hY]
      · simp [mirrorY]

/-- Orientation: swapping the two coordinates turns the vertical figure eight into the usual
Gerono lemniscate `x⁴ = x² - y²`. -/
theorem swap_geronoVertical : swapXY '' geronoVertical = geronoLemniscate := by
  ext ⟨x, y⟩
  constructor
  · rintro ⟨⟨a, b⟩, hab, h⟩
    have hab' : a ^ 2 = b ^ 2 * (1 - b ^ 2) := hab
    have hxy : b = x ∧ a = y := by simpa [swapXY] using h
    obtain ⟨hb, ha⟩ := hxy
    subst hb
    subst ha
    show b ^ 4 = b ^ 2 - a ^ 2
    linear_combination hab'
  · intro h
    have h' : x ^ 4 = x ^ 2 - y ^ 2 := h
    refine ⟨(y, x), ?_, ?_⟩
    · show y ^ 2 = x ^ 2 * (1 - x ^ 2)
      linear_combination h'
    · simp [swapXY]

/-! ### What the new tools give -/

/-- The plain glyph `◠`, i.e. the identity warp: the upper semicircle itself is constructible. -/
theorem upperSemicircle_PConstructibleCurve : PConstructibleCurve upperSemicircle :=
  PConstructibleCurve.text_plain TextGlyph.upperHalfCircle

/-- One lobe of the lemniscate is constructible: the Triangle warp applied to the glyph `◠`. -/
theorem geronoLobe_PConstructibleCurve : PConstructibleCurve geronoLobe := by
  have h := PConstructibleCurve.text_triangle TextGlyph.upperHalfCircle
  rwa [TextGlyph.outline_upperHalfCircle, triangleWarp_upperSemicircle] at h

/-- The whole figure eight, standing upright: mirror the lobe and keep both. -/
theorem geronoVertical_PConstructibleCurve : PConstructibleCurve geronoVertical := by
  have h := PConstructibleCurve.mirror_union geronoLobe_PConstructibleCurve
  rwa [mirror_geronoLobe] at h

/-- Coordinate swap `(x, y) ↦ (y, x)` is the linear map `[[0, 1], [1, 0]]`. -/
theorem linearMap_swap : linearMap 0 1 1 0 = swapXY := by
  funext p
  simp [linearMap, swapXY]

/-- The lemniscate of Gerono `x ^ 4 = x ^ 2 - y ^ 2`, in its usual orientation, is constructible. -/
theorem geronoLemniscate_PConstructibleCurve : PConstructibleCurve geronoLemniscate := by
  have h := linearMap_PConstructibleCurve geronoVertical_PConstructibleCurve
    zero_Pconstructible PConstructible.base_one PConstructible.base_one zero_Pconstructible
  rwa [linearMap_swap, swap_geronoVertical] at h

end Pconstructible
