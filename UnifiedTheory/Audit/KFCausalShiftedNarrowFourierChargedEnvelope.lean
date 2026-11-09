/- Gaussian absorption for the charged profile and its normalized clock
derivative, uniform in width spacing and clock position. The degree enters
the explicit constants; neutral factors still need their joint L2 bound. -/
import UnifiedTheory.Audit.KFCausalShiftedNarrowFourierClockBounds
import UnifiedTheory.Audit.KFCausalNarrowFourierChargedBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalShiftedNarrowFourierChargedEnvelope
noncomputable section
open KFCausalEuclideanProductCoordinates (Block)
open KFCausalShiftedNarrowFourierGeometry (radius broadRadius_nonnegative radius_re_nonnegative shifted_coefficient_positive)
open KFCausalShiftedNarrowFourierClockDerivative (radiusSlope)
open KFCausalShiftedNarrowFourierClockBounds
open KFCausalNarrowFourierChargedBounds (powerConstant powerConstant_positive power_exp_bound)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalNeutralPlaneClockGeometry (velocity)
open KFCausalShiftedGaussianPureDifferential (realInverse)
open KFCausalClusteredWidthChargedJet (jet)

def radiusFloor : ℝ := Real.exp (-Real.pi/3)/2
def radiusCeiling : ℝ := Real.exp (Real.pi/3)
def momentConstant (n j : ℕ) : ℝ :=
  radiusCeiling^n/radiusFloor^(n+j)*powerConstant (n+j)

theorem constants_positive (n j : ℕ) :
    0 < radiusFloor ∧ 0 < radiusCeiling ∧ 0 < momentConstant n j := by
  have := powerConstant_positive (n+j)
  unfold momentConstant radiusFloor radiusCeiling
  exact ⟨by positivity,by positivity,by positivity⟩

theorem realRadius_nonnegative (α : ℝ) (hα : 0 < α) (u : Block 2) (v : Block 4) :
    0 ≤ realRadius α u v := by
  have := broadRadius_nonnegative v
  unfold realRadius
  positivity

variable (α ε y s : ℝ) (hα : 0 < α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
  (u : Block 2) (v : Block 4)
local notation "Z" => radius ((α:ℂ)*(scale ε y s)^2) u v
local notation "R" => realRadius α u v
local notation "J" => radiusSlope ((α:ℂ)*(scale ε y s)^2)
  (2*(α:ℂ)*scale ε y s*velocity ε (Real.exp s) (scale ε y s)) u v

include hα hε hy

theorem weighted_moment_bound (n j : ℕ) :
    ‖Z‖^n*R^j*Real.exp (-(Z).re) ≤ momentConstant n j*Real.exp (-radiusFloor*R/2) := by
  have hR := realRadius_nonnegative α hα u v
  have hL := (constants_positive n j).1
  have hM := (constants_positive n j).2.1
  have hnorm := actual_radius_norm_bound α ε y s hα hε hy u v
  have hre := actual_radius_lower α ε y s hα hε hy u v
  have hp : (radiusCeiling*R)^n*R^j =
      (radiusCeiling^n/radiusFloor^(n+j))*(radiusFloor*R)^(n+j) := by
    rw [mul_pow,mul_pow,pow_add]
    field_simp
    rw [pow_add]
  calc
    _ ≤ (radiusCeiling*R)^n*R^j*Real.exp (-radiusFloor*R) :=
      mul_le_mul
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm n) (pow_nonneg hR j))
        (Real.exp_le_exp.mpr (by simpa only [neg_mul] using neg_le_neg hre)) (Real.exp_pos _).le (by positivity)
    _ = (radiusCeiling^n/radiusFloor^(n+j))*((radiusFloor*R)^(n+j)*Real.exp (-(radiusFloor*R))) := by
      rw [hp]
      ring
    _ ≤ (radiusCeiling^n/radiusFloor^(n+j))*(powerConstant (n+j)*Real.exp (-(radiusFloor*R)/2)) :=
      mul_le_mul_of_nonneg_left (power_exp_bound (n+j) (radiusFloor*R) (by positivity)) (by positivity)
    _ = _ := by unfold momentConstant; ring

theorem laplace_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ‖KFCausalReciprocalWedgeLaplace.laplaceSum (n+1)
      (KFCausalClusteredWidthProfiles.widths n δ)
      (KFCausalClusteredWidthProfiles.coefficients n δ) Z‖ ≤
      momentConstant n 0*Real.exp (-radiusFloor*R/2) := by
  have hz := radius_re_nonnegative _ (shifted_coefficient_positive α ε y s hα hε hy).le u v
  apply (KFCausalClusteredWidthProfiles.laplaceSum_norm_le n δ hδ Z hz).trans
  rw [mul_comm]
  simpa only [pow_zero,mul_one] using weighted_moment_bound α ε y s hα hε hy u v n 0

theorem normalized_jet_bound (n : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ‖realInverse ε s*jet n δ Z*J‖ ≤
      ((2/ε)*radiusCeiling*((n:ℝ)*momentConstant (n-1) 1+momentConstant n 1))*
        Real.exp (-radiusFloor*R/2) := by
  have hR := realRadius_nonnegative α hα u v
  have hL := (constants_positive n 1).1
  have hM := (constants_positive n 1).2.1
  have hz := radius_re_nonnegative _ (shifted_coefficient_positive α ε y s hα hε hy).le u v
  have hJ := normalized_radius_bound α ε y s hα hε hy u v
  have hjet := KFCausalClusteredWidthChargedJet.jet_norm_le n δ hδ Z hz
  have h1 := weighted_moment_bound α ε y s hα hε hy u v (n-1) 1
  have h2 := weighted_moment_bound α ε y s hα hε hy u v n 1
  simp only [pow_one] at h1 h2
  calc
    _ = ‖jet n δ Z‖*‖realInverse ε s*J‖ := by rw [norm_mul,norm_mul,norm_mul]; ring
    _ ≤ (Real.exp (-(Z).re)*((n:ℝ)*‖Z‖^(n-1)+‖Z‖^n))*((2/ε)*radiusCeiling*R) :=
      mul_le_mul hjet hJ (norm_nonneg _) (by positivity)
    _ = ((2/ε)*radiusCeiling)*
        ((n:ℝ)*(‖Z‖^(n-1)*R*Real.exp (-(Z).re))+‖Z‖^n*R*Real.exp (-(Z).re)) := by ring
    _ ≤ ((2/ε)*radiusCeiling)*
        ((n:ℝ)*(momentConstant (n-1) 1*Real.exp (-radiusFloor*R/2))+
          momentConstant n 1*Real.exp (-radiusFloor*R/2)) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg n)) h2) (by positivity)
    _ = _ := by ring

#print axioms constants_positive
#print axioms realRadius_nonnegative
#print axioms weighted_moment_bound
#print axioms laplace_bound
#print axioms normalized_jet_bound
end
end UnifiedTheory.Audit.KFCausalShiftedNarrowFourierChargedEnvelope
