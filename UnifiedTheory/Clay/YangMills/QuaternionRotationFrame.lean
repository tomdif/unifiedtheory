/- Six explicit small SU(2) rotations detect a nonzero squared trace
increment at every unit quaternion, including the trace extrema. -/
import UnifiedTheory.Clay.YangMills.WilsonGroundVarianceBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace UnifiedTheory.Clay.YangMills.QuaternionRotationFrame
noncomputable section
open WilsonSlabOperator
open scoped Quaternion

def axis (c s : ℝ) (i : Fin 3) : ℍ :=
  if i = 0 then ⟨c,s,0,0⟩ else if i = 1 then ⟨c,0,s,0⟩ else ⟨c,0,0,s⟩

theorem axis_zero (c s : ℝ) : axis c s 0 = ⟨c,s,0,0⟩ := rfl
theorem axis_one (c s : ℝ) : axis c s 1 = ⟨c,0,s,0⟩ := rfl
theorem axis_two (c s : ℝ) : axis c s 2 = ⟨c,0,0,s⟩ := rfl

theorem axis_normSq (c s : ℝ) (i : Fin 3) : Quaternion.normSq (axis c s i) = c^2+s^2 := by
  fin_cases i <;> simp [axis, Quaternion.normSq_def', pow_two]

theorem axis_sub_one_normSq (c s : ℝ) (i : Fin 3) :
    Quaternion.normSq (axis c s i-1) = (c-1)^2+s^2 := by
  fin_cases i <;> simp [axis, Quaternion.normSq_def', pow_two]

def cosine (t : ℝ) : ℝ := (1-t^2)/(1+t^2)
def sine (t : ℝ) : ℝ := 2*t/(1+t^2)

theorem circle (t : ℝ) : (cosine t)^2+(sine t)^2 = 1 := by
  unfold cosine sine
  field_simp [show 1+t^2 ≠ 0 by positivity]
  ring

theorem cosine_neg (t : ℝ) : cosine (-t) = cosine t := by simp [cosine]

theorem sine_neg (t : ℝ) : sine (-t) = -sine t := by unfold sine; ring

def rotation (t : ℝ) (i : Fin 3) : Q :=
  ⟨axis (cosine t) (sine t) i, by
    constructor
    · rw [Quaternion.star_mul_self, axis_normSq, circle]
      rfl
    · rw [Quaternion.self_mul_star, axis_normSq, circle]
      rfl⟩

theorem distance_square (t : ℝ) (i : Fin 3) :
    ‖(rotation t i : ℍ)-1‖^2 * (1+t^2) = 4*t^2 := by
  rw [pow_two, ← Quaternion.normSq_eq_norm_mul_self]
  change Quaternion.normSq (axis (cosine t) (sine t) i-1)*(1+t^2) = _
  rw [axis_sub_one_normSq]
  unfold cosine sine
  field_simp [show 1+t^2 ≠ 0 by positivity]
  ring

theorem distance_le (t : ℝ) (i : Fin 3) : ‖(rotation t i : ℍ)-1‖ ≤ 2*|t| := by
  have h := distance_square t i
  have hprod := mul_nonneg (sq_nonneg ‖(rotation t i : ℍ)-1‖) (sq_nonneg t)
  nlinarith [sq_abs t, norm_nonneg ((rotation t i : ℍ)-1), abs_nonneg t]

theorem frame_identity (c s : ℝ) (h : ℍ) :
    (∑ i : Fin 3, ((2*(axis c s i*h).re-2*h.re)^2+
      (2*(axis c (-s) i*h).re-2*h.re)^2)) =
        24*(c-1)^2*h.re^2 + 8*s^2*(h.imI^2+h.imJ^2+h.imK^2) := by
  rw [Fin.sum_univ_three]
  simp only [axis_zero, axis_one, axis_two, Quaternion.re_mul]
  ring

theorem cosine_bounds (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ cosine t ∧ cosine t ≤ 1 := by
  have hs : t^2 ≤ 1 := by nlinarith
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · unfold cosine
    exact (div_le_one (by positivity : 0 < 1+t^2)).mpr (by nlinarith [sq_nonneg t])

theorem deficit_lower (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) : t^2 ≤ 1-cosine t := by
  have hs : 0 ≤ 1-t^2 := by nlinarith
  have he : 1-cosine t = 2*t^2/(1+t^2) := by
    unfold cosine
    field_simp [show 1+t^2 ≠ 0 by positivity]
    ring
  rw [he]
  apply (le_div_iff₀ (by positivity : 0 < 1+t^2)).mpr
  nlinarith [mul_nonneg (sq_nonneg t) hs]

/-- A deterministic lower bound, uniform over every SU(2) holonomy. -/
theorem frame_lower (t : ℝ) (ht : 0 ≤ t) (h1 : t ≤ 1) (h : Q) :
    8*t^4 ≤ ∑ i : Fin 3,
      (((WilsonSingleLinkStaples.character (rotation t i*h)).re-
        (WilsonSingleLinkStaples.character h).re)^2+
       ((WilsonSingleLinkStaples.character (rotation (-t) i*h)).re-
        (WilsonSingleLinkStaples.character h).re)^2) := by
  have hc := cosine_bounds t ht h1
  have hcs := circle t
  have hs : (1-cosine t)^2 ≤ (sine t)^2 := by
    nlinarith [mul_nonneg hc.1 (sub_nonneg.mpr hc.2)]
  have hn : (h : ℍ).re^2+(h : ℍ).imI^2+(h : ℍ).imJ^2+(h : ℍ).imK^2 = 1 := by
    have he : Quaternion.normSq (h : ℍ) = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self, QuaternionSymmetricChange.unit_norm, one_mul]
    simpa only [Quaternion.normSq_def', ← pow_two] using he
  have hd := deficit_lower t ht h1
  have hd2 : t^4 ≤ (1-cosine t)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-cosine t-t^2 by linarith)
      (show 0 ≤ 1-cosine t+t^2 by nlinarith [sq_nonneg t])]
  simp only [WilsonSingleLinkStaples.character_re]
  change 8*t^4 ≤ ∑ i : Fin 3,
    ((2*(axis (cosine t) (sine t) i*(h : ℍ)).re-2*(h : ℍ).re)^2+
      (2*(axis (cosine (-t)) (sine (-t)) i*(h : ℍ)).re-2*(h : ℍ).re)^2)
  simp only [cosine_neg, sine_neg]
  rw [frame_identity]
  have him : 0 ≤ (h : ℍ).imI^2+(h : ℍ).imJ^2+(h : ℍ).imK^2 := by positivity
  nlinarith [mul_nonneg (sq_nonneg (1-cosine t)) (sq_nonneg (h : ℍ).re),
    mul_nonneg (sub_nonneg.mpr hs) him]

end
end UnifiedTheory.Clay.YangMills.QuaternionRotationFrame
