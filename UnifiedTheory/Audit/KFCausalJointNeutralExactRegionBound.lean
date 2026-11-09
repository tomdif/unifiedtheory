/- Explicit state-independent neutral form bounds from the exact physical
clock region. They retain arbitrary correlated charged coefficients and
neutral sources/polynomials. The full charged integral is still required
for a uniform total-response inequality. -/
import UnifiedTheory.Audit.KFCausalClockFloorExactScaleRegion
import UnifiedTheory.Audit.KFCausalJointNeutralRadialEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalJointNeutralExactRegionBound
noncomputable section
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalChargedPairCoordinates (fieldSlope)
open KFCausalNeutralLineDomain (Regular)
open KFCausalNeutralQuarticFormBound (energy first second)
open KFCausalQuarticNeutralDefect (direction)
open KFCausalJointNeutralRadialEstimate (jointArea)

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s

include hε hy in
theorem actual_second_lower (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    4*energy (fun x => direction (2*(r).im) (fieldSlope r) x (f x) (g x))-24*energy f ≤
      second (2*(r).im) (fieldSlope r) f g := by
  have he := KFCausalNeutralQuarticFormBound.second_lower (2*(r).im) (fieldSlope r) f g hf hg hd
  have hb := (field_direction_bounds ε y s hε hy).2
  have hp := mul_le_mul_of_nonneg_right hb (KFCausalNeutralQuarticFormBound.energy_nonnegative f)
  linarith

include hε hy in
theorem actual_curvature_bound (f g : ℝ → ℂ) (hf : Regular f) (hg : Regular g)
    (hd : ∀ x, HasDerivAt f (g x) x) :
    (first (2*(r).im) (fieldSlope r) f g)^2-24*(energy f)^2 ≤
      energy f*second (2*(r).im) (fieldSlope r) f g := by
  have he := KFCausalNeutralQuarticFormBound.curvature_form_bound (2*(r).im) (fieldSlope r) f g hf hg hd
  have hb := (field_direction_bounds ε y s hε hy).2
  have hp := mul_le_mul_of_nonneg_right hb (sq_nonneg (energy f))
  linarith

include hε hy in
theorem joint_curvature_bound (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z ζ : ℂ) :
    let f := fun x : ℝ => KFCausalNeutralLineDomain.family n β b
      (KFCausalNeutralJointCurvatureForm.coefficients n w c z) P ((x:ℂ)+ζ)
    let g := fun x : ℝ => KFCausalNeutralLineDomain.family n β b
      (KFCausalNeutralJointCurvatureForm.coefficients n w c z)
      (fun i => KFCausalNeutralLinePackets.step β (b i) (P i)) ((x:ℂ)+ζ)
    (first (2*(r).im) (fieldSlope r) f g)^2-24*(energy f)^2 ≤
      energy f*second (2*(r).im) (fieldSlope r) f g :=
  actual_curvature_bound ε y s hε hy _ _
    (KFCausalNeutralLineDomain.family_regular n β hβ b _ P ζ)
    (KFCausalNeutralLineDomain.family_regular n β hβ b _ _ ζ)
    (KFCausalNeutralJointCurvatureForm.translated_family_derivative n β b _ P ζ)

include hε hy in
theorem joint_area_lower (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (w : Fin n → ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (z : ℂ) (X : ℝ) (hX : 0 < X) :
    -12*jointArea n β w b c P r z X ≤ deriv (jointArea n β w b c P r z) X := by
  have he : jointArea n β w b c P r z =
      KFCausalNeutralUniformRadialDefect.areaMean n β b
        (KFCausalNeutralJointCurvatureForm.coefficients n w c z) P 0 (2*(r).im) (fieldSlope r) :=
    funext (KFCausalJointNeutralRadialEstimate.jointArea_eq n β w b c P r z)
  rw [he]
  exact KFCausalNeutralUniformRadialDefect.family_area_lower n β b _ P 0 _ _ hβ 12
    (by nlinarith [(field_direction_bounds ε y s hε hy).2]) X hX

include hε hy in
theorem field_direction_inverse_bound :
    0 < ((fieldSlope r)^2+(2*(r).im)^2)⁻¹ ∧ ((fieldSlope r)^2+(2*(r).im)^2)⁻¹ ≤ 1 := by
  have hl := (field_direction_bounds ε y s hε hy).1
  constructor
  · exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one hl)
  · exact inv_le_one_of_one_le₀ hl

#print axioms actual_second_lower
#print axioms actual_curvature_bound
#print axioms joint_curvature_bound
#print axioms joint_area_lower
#print axioms field_direction_inverse_bound
end
end UnifiedTheory.Audit.KFCausalJointNeutralExactRegionBound
