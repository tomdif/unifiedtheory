/- The isolated radial transport term itself has no uniform upper bound
relative to the actual joint angular energy. One fixed physical coherent
profile suffices. This does not bound or disprove the full clock response. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialNegativeDerivative
import UnifiedTheory.Audit.KFCausalJointNeutralClockTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalJointNeutralRadialTransportObstruction
noncomputable section
open MeasureTheory Set
open KFCausalNeutralRadialActualGeometry (geometry source slice displacement field profile)
open KFCausalNeutralRadialNegativeDerivative (area)
open KFCausalReciprocalWedgeGeometry (first second chart wedge)
open KFCausalReciprocalWedgeVelocity (shrink)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalReciprocalNeutralPositiveForm (profileSum)
open KFCausalReciprocalWedgeLaplace (laplaceSum)
open KFCausalJointNeutralRadialEstimate (jointSlice jointArea)

def weight (z : ℂ) : ℝ := ‖Complex.exp (-z)‖^2
def energy (z : ℂ) (X : ℝ) : ℝ :=
  jointArea 1 1 (fun _ => 1) (fun _ => source) (fun _ => 1) (fun _ => 1) geometry z X
def radialCross (z : ℂ) : ℝ :=
  (-shrink (fraction 1 0) geometry*second 32 geometry z)*deriv (energy z) (first 32 geometry z)

theorem weight_positive (z : ℂ) : 0 < weight z := by
  unfold weight
  exact sq_pos_of_pos (norm_pos_iff.mpr (Complex.exp_ne_zero _))

theorem slice_factor (z : ℂ) (v x : ℝ) :
    jointSlice 1 1 (fun _ => 1) (fun _ => source) (fun _ => 1) (fun _ => 1) geometry z v x =
      weight z*slice v x := by
  unfold jointSlice profileSum laplaceSum
  simp only [Fin.sum_univ_one,Complex.ofReal_one,one_mul,mul_one,neg_mul]
  rw [mul_comm _ (Complex.exp (-z)),norm_mul,mul_pow]
  have he : KFCausalReciprocalNeutralKernel.neutral geometry v x =
      (x:ℂ)+(displacement*v:ℝ)*Complex.I := by
    unfold KFCausalReciprocalNeutralKernel.neutral displacement
    push_cast
    ring
  rw [he]
  unfold weight slice profile field KFCausalChargedPairCoordinates.fieldSlope
  ring

theorem energy_factor (z : ℂ) (X : ℝ) : energy z X = weight z*area X := by
  unfold energy jointArea KFCausalCorrectedAngularComparison.angular
  simp_rw [slice_factor,integral_const_mul]
  rw [intervalIntegral.integral_const_mul]
  unfold area KFCausalNeutralRadialActualObstruction.physicalAngular
  ring

theorem energy_derivative (z : ℂ) (X : ℝ) (hX : 0 < X) :
    HasDerivAt (energy z) (weight z*deriv area X) X := by
  have he : energy z = fun Y => weight z*area Y := funext (energy_factor z)
  rw [he]
  exact ((KFCausalNeutralRadialNegativeDerivative.area_derivative X hX).differentiableAt.hasDerivAt).const_mul _

theorem energy_positive (z : ℂ) (X : ℝ) : 0 < energy z X := by
  rw [energy_factor]
  exact mul_pos (weight_positive z) (KFCausalNeutralRadialNegativeDerivative.area_positive X)

theorem radial_cross_unbounded :
    ∃ X : ℝ, 0 < X ∧ ∀ M : ℝ, ∃ z ∈ wedge 32 geometry,
      first 32 geometry z = X ∧ 0 < energy z X ∧ M*energy z X < radialCross z := by
  obtain ⟨X,hX,hE,hJ⟩ := KFCausalNeutralRadialNegativeDerivative.exists_positive_area_negative_derivative
  have hy : |(1/128:ℝ)| ≤ Real.pi*1/3 := by
    simpa only [mul_one] using KFCausalNeutralRadialActualGeometry.actual_parameters.2.2.2
  have hA := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive 1 (1/128) 0 (by norm_num) hy
  have ha := (KFCausalNeutralPlaneClockGeometry.scale_re_positive 1 (1/128) 0 (by norm_num) hy).ne'
  have hb := KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero 1 (1/128) 0 (by norm_num) hy (by norm_num)
  have ht := KFCausalNeutralPlaneNormalizedGeometry.fraction_bounds 1 0 (by norm_num)
  have hs := KFCausalJointNeutralClockTransport.shrink_positive (fraction 1 0) geometry ht.1 ht.2.le hA
  let k := shrink (fraction 1 0) geometry*(-deriv area X)
  have hk : 0 < k := mul_pos hs (neg_pos.mpr hJ)
  refine ⟨X,hX,?_⟩
  intro M
  let Y := max 0 ((M*area X+1)/k)
  have hY : 0 ≤ Y := le_max_left _ _
  have hm : (M*area X+1)/k ≤ Y := le_max_right _ _
  have hM : M*area X < k*Y := by
    have hh := (div_le_iff₀ hk).mp hm
    nlinarith
  let z := chart 32 geometry X Y
  have hx : first 32 geometry z = X :=
    KFCausalReciprocalWedgeGeometry.first_chart 32 X Y geometry (by norm_num) hA.ne' ha hb
  have hyz : second 32 geometry z = Y :=
    KFCausalReciprocalWedgeGeometry.second_chart 32 X Y geometry (by norm_num) hA.ne' ha hb
  refine ⟨z,KFCausalReciprocalWedgeGeometry.chart_mem_wedge 32 X Y geometry
    (by norm_num) hA.ne' ha hb hX.le hY,hx,energy_positive z X,?_⟩
  rw [radialCross,hx,hyz,(energy_derivative z X hX).deriv,energy_factor]
  have hh := mul_lt_mul_of_pos_left hM (weight_positive z)
  dsimp only [k] at hh
  nlinarith

theorem no_uniform_radial_cross_bound :
    ¬ ∃ M : ℝ, ∀ z ∈ wedge 32 geometry, 0 < first 32 geometry z →
      radialCross z ≤ M*energy z (first 32 geometry z) := by
  rintro ⟨M,hM⟩
  obtain ⟨X,hX,h⟩ := radial_cross_unbounded
  obtain ⟨z,hz,hxz,_,hbad⟩ := h M
  have he := hM z hz (by rwa [hxz])
  rw [hxz] at he
  exact (not_lt_of_ge he) hbad

#print axioms weight_positive
#print axioms slice_factor
#print axioms energy_factor
#print axioms energy_derivative
#print axioms energy_positive
#print axioms radial_cross_unbounded
#print axioms no_uniform_radial_cross_bound
end
end UnifiedTheory.Audit.KFCausalJointNeutralRadialTransportObstruction
