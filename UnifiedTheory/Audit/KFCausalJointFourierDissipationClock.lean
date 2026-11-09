/- Removing the simultaneous imaginary dilation leaves strictly positive
real clock cooling. Its normalized speed and the remaining real field
jet have state-independent bounds, including at zero imaginary shift.
No sign of an integrated charged pairing is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalJointClockJetAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalJointFourierDissipationClock
noncomputable section
open KFCausalClockFloorRelativeShift (scale)
open KFCausalClockFloorExactScaleRegion
open KFCausalNeutralPlaneClockGeometry (velocity denominator)
open KFCausalNeutralPlaneNormalizedGeometry
open KFCausalReciprocalGaussianCoordinates (area)
open KFCausalReciprocalWedgeVelocity (radius)
open KFCausalJointClockCoolingCoercivity

def normalizedRealCooling (t : ℝ) (r : ℂ) : ℝ :=
  r.re*radius r/denominator (1-t) t r

def normalizedDilation (t : ℝ) (r : ℂ) : ℝ :=
  imagNumerator t r/(2*denominator (1-t) t r)

def normalizedFieldJet (t : ℝ) (r : ℂ) : ℝ :=
  -2*normalizedRealCooling t r-3*normalizedDilation t r

theorem real_cooling_identity (t : ℝ) (r : ℂ) :
    (velocity (1-t) t r).re-imaginaryRate t r*r.re =
      t*normalizedRealCooling t r := by
  rw [normalized_velocity_re]
  unfold imaginaryRate normalizedRealCooling
  have he := KFCausalReciprocalWedgeVelocity.numerator_difference t r
  simp only [div_eq_mul_inv,mul_inv_rev]
  linear_combination t*r.re*(denominator (1-t) t r)⁻¹/2*he

theorem dilation_identity (t : ℝ) (r : ℂ) :
    imaginaryRate t r = t*normalizedDilation t r := by
  unfold imaginaryRate normalizedDilation
  ring

theorem field_jet_identity (t : ℝ) (r : ℂ) :
    -2*(velocity (1-t) t r).re-
        imaginaryRate t r*KFCausalChargedPairCoordinates.fieldSlope r =
      t*normalizedFieldJet t r := by
  have he := real_cooling_identity t r
  rw [dilation_identity] at he ⊢
  unfold normalizedFieldJet KFCausalChargedPairCoordinates.fieldSlope
  linear_combination -2*he

variable (ε y s : ℝ) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
local notation "r" => scale ε y s
include hε hy

theorem real_coordinate_bounds : (1/2:ℝ) ≤ (r).re ∧ (r).re ≤ 5/4 := by
  have h := fieldSlope_bounds ε y s hε hy
  unfold KFCausalChargedPairCoordinates.fieldSlope at h
  constructor <;> linarith [h.1,h.2]

theorem imaginary_numerator_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    -6 ≤ imagNumerator t r ∧ imagNumerator t r ≤ -1/2 := by
  have ht0 := ht.1
  have ht1 := ht.2
  have hA := square_re_half_le ε y s hε hy
  have hR := norm_square_le_two ε y s hε hy
  have hR1 := norm_square_one_le ε y s hε hy
  have hB := imaginary_square_le_half ε y s hε hy
  have hA1 := square_re_le_one ε y s hε hy
  have hp : -6 ≤ 1-3*(r).re^2+(r).im^2 ∧
      1-3*(r).re^2+(r).im^2 ≤ -1/2 := by
    constructor <;> nlinarith [sq_nonneg (r).im]
  have hq : -6 ≤ -(radius r*(1+radius r)) ∧
      -(radius r*(1+radius r)) ≤ -1/2 := by
    unfold radius
    constructor <;> nlinarith
  have h1 := mul_le_mul_of_nonneg_left hp.1 (sub_nonneg.mpr ht1)
  have h2 := mul_le_mul_of_nonneg_left hq.1 ht0
  have h3 := mul_le_mul_of_nonneg_left hp.2 (sub_nonneg.mpr ht1)
  have h4 := mul_le_mul_of_nonneg_left hq.2 ht0
  unfold imagNumerator
  unfold radius at h1 h2 h3 h4
  constructor <;> nlinarith

theorem real_cooling_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    (1/8:ℝ) ≤ normalizedRealCooling t r ∧ normalizedRealCooling t r ≤ 10 := by
  have ha := real_coordinate_bounds ε y s hε hy
  have hR1 := norm_square_one_le ε y s hε hy
  have hR2 := norm_square_le_two ε y s hε hy
  change 1 ≤ radius r at hR1
  change radius r ≤ 2 at hR2
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hDp : 0 < denominator (1-t) t r := by linarith [hD.1]
  have hN1 : (1/2:ℝ) ≤ (r).re*radius r := by
    have h := mul_le_mul ha.1 hR1 (by norm_num : (0:ℝ) ≤ 1) (by linarith [ha.1])
    norm_num at h
    exact h
  have hN2 : (r).re*radius r ≤ 5/2 := by
    have h := mul_le_mul ha.2 hR2 (by linarith [hR1]) (by norm_num : (0:ℝ) ≤ 5/4)
    norm_num at h
    exact h
  unfold normalizedRealCooling
  constructor
  · apply (le_div_iff₀ hDp).mpr
    nlinarith [hD.2]
  · apply (div_le_iff₀ hDp).mpr
    nlinarith [hD.1]

theorem dilation_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    -12 ≤ normalizedDilation t r ∧ normalizedDilation t r ≤ 0 := by
  have hN := imaginary_numerator_bounds ε y s hε hy t ht
  have hD := normalized_denominator_bounds ε y s hε hy t ht
  have hDp : 0 < 2*denominator (1-t) t r := by linarith [hD.1]
  unfold normalizedDilation
  constructor
  · apply (le_div_iff₀ hDp).mpr
    nlinarith [hD.1,hN.1]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith [hN.2]) hDp.le

theorem field_jet_bounds (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    -20 ≤ normalizedFieldJet t r ∧ normalizedFieldJet t r ≤ 36 := by
  have hd := real_cooling_bounds ε y s hε hy t ht
  have hl := dilation_bounds ε y s hε hy t ht
  unfold normalizedFieldJet
  constructor <;> linarith [hd.1,hd.2,hl.1,hl.2]

theorem field_jet_square_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) :
    (normalizedFieldJet t r)^2 ≤ 1296 := by
  have h := field_jet_bounds ε y s hε hy t ht
  nlinarith [sq_nonneg (normalizedFieldJet t r+20),
    mul_nonneg (show 0 ≤ normalizedFieldJet t r+36 by linarith [h.1])
      (show 0 ≤ 36-normalizedFieldJet t r by linarith [h.2])]

theorem corrected_field_absorption (t : ℝ) (ht : t ∈ Set.Icc 0 1) (c X : ℝ) :
    2*c*(t*normalizedFieldJet t r*X) ≤
      (t*normalizedRealCooling t r)*X^2+10368*t*c^2 := by
  have hk := field_jet_square_bound ε y s hε hy t ht
  have hd := real_cooling_bounds ε y s hε hy t ht
  have hsq := sq_nonneg (X-8*c*normalizedFieldJet t r)
  have hck := mul_le_mul_of_nonneg_left hk (sq_nonneg c)
  have hx : 2*c*normalizedFieldJet t r*X ≤ X^2/8+10368*c^2 := by
    nlinarith
  have hm := mul_le_mul_of_nonneg_left hx ht.1
  have hdx := mul_le_mul_of_nonneg_right hd.1 (mul_nonneg ht.1 (sq_nonneg X))
  nlinarith

theorem actual_real_cooling_positive :
    0 < (velocity (1-fraction ε s) (fraction ε s) r).re-
      imaginaryRate (fraction ε s) r*(r).re := by
  rw [real_cooling_identity]
  have ht := fraction_bounds ε s hε
  have hd := (real_cooling_bounds ε y s hε hy (fraction ε s) ⟨ht.1.le,ht.2.le⟩).1
  exact mul_pos ht.1 (by linarith)

#print axioms real_cooling_identity
#print axioms dilation_identity
#print axioms field_jet_identity
#print axioms real_coordinate_bounds
#print axioms imaginary_numerator_bounds
#print axioms real_cooling_bounds
#print axioms dilation_bounds
#print axioms field_jet_bounds
#print axioms field_jet_square_bound
#print axioms corrected_field_absorption
#print axioms actual_real_cooling_positive
end
end UnifiedTheory.Audit.KFCausalJointFourierDissipationClock
