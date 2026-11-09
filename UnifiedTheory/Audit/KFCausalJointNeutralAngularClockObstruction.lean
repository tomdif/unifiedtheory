/- Even the complete fixed-charged-coordinate angular clock derivative
has no uniform relative upper bound, including the changing neutral
geometry and wedge Jacobian. This is not a counterexample to the integral
over charged coordinates or to the proved common-width response bound. -/
import UnifiedTheory.Audit.KFCausalJointNeutralAngularClockJet

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalJointNeutralAngularClockObstruction
noncomputable section
open Set
open KFCausalJointNeutralAngularClockJet
open KFCausalNeutralRadialActualGeometry (geometry)
open KFCausalNeutralRadialNegativeDerivative (area)
open KFCausalReciprocalWedgeGeometry (first second chart wedge)
open KFCausalReciprocalWedgeVelocity (drift shrink)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalReciprocalWedgePrefactor (jacobian)
open KFCausalJointNeutralRadialTransportObstruction (weight weight_positive)

theorem complete_angular_derivative_unbounded :
    ∃ X : ℝ, 0 < X ∧ ∀ M : ℝ, ∃ z ∈ wedge 32 geometry,
      first 32 geometry z = X ∧ 0 < second 32 geometry z ∧ 0 < energy 0 z ∧
      M*energy 0 z < deriv (fun s => energy s z) 0 := by
  obtain ⟨X,hX,hE,hJ⟩ := KFCausalNeutralRadialNegativeDerivative.exists_positive_area_negative_derivative
  have ht := KFCausalNeutralPlaneNormalizedGeometry.fraction_bounds 1 0 (by norm_num)
  have hs := KFCausalJointNeutralClockTransport.shrink_positive (fraction 1 0) geometry
    ht.1 ht.2.le geometry_regular.1
  let k := shrink (fraction 1 0) geometry*(-deriv area X)
  have hk : 0 < k := mul_pos hs (neg_pos.mpr hJ)
  refine ⟨X,hX,?_⟩
  intro M
  let Y := max 1 ((M*area X-clockJet X-deriv area X*drift (fraction 1 0) geometry*X+1)/k)
  have hY : 0 < Y := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hm := le_max_right (1:ℝ)
    ((M*area X-clockJet X-deriv area X*drift (fraction 1 0) geometry*X+1)/k)
  have hm' : M*area X-clockJet X-deriv area X*drift (fraction 1 0) geometry*X+1 ≤ k*Y := by
    have he := (div_le_iff₀ hk).mp hm
    nlinarith
  have hM : M*area X < clockJet X+deriv area X*
      (drift (fraction 1 0) geometry*X-shrink (fraction 1 0) geometry*Y) := by
    dsimp only [k] at hm'
    nlinarith
  let z := chart 32 geometry X Y
  have hx : first 32 geometry z = X := KFCausalReciprocalWedgeGeometry.first_chart
    32 X Y geometry (by norm_num) geometry_regular.1.ne' geometry_regular.2.1 geometry_regular.2.2.1
  have hy : second 32 geometry z = Y := KFCausalReciprocalWedgeGeometry.second_chart
    32 X Y geometry (by norm_num) geometry_regular.1.ne' geometry_regular.2.1 geometry_regular.2.2.1
  refine ⟨z,KFCausalReciprocalWedgeGeometry.chart_mem_wedge 32 X Y geometry
    (by norm_num) geometry_regular.1.ne' geometry_regular.2.1 geometry_regular.2.2.1 hX.le hY.le,
    hx,by rwa [hy],?_,?_⟩
  · rw [energy_zero,hx]
    exact mul_pos (weight_positive z) hE
  · rw [(energy_derivative_zero z (by rwa [hx])).deriv,energy_zero,hx,hy]
    convert mul_lt_mul_of_pos_left hM (weight_positive z) using 1
    ring

theorem weightedEnergy_positive_zero (z : ℂ) : 0 < weightedEnergy 0 z := by
  unfold weightedEnergy
  rw [energy_zero]
  exact mul_pos jacobian_positive (mul_pos (weight_positive z)
    (KFCausalNeutralRadialNegativeDerivative.area_positive _))

theorem weighted_angular_derivative_unbounded :
    ∃ X : ℝ, 0 < X ∧ ∀ M : ℝ, ∃ z ∈ wedge 32 geometry,
      first 32 geometry z = X ∧ 0 < second 32 geometry z ∧ 0 < weightedEnergy 0 z ∧
      M*weightedEnergy 0 z < deriv (fun s => weightedEnergy s z) 0 := by
  obtain ⟨X,hX,h⟩ := complete_angular_derivative_unbounded
  refine ⟨X,hX,?_⟩
  intro M
  obtain ⟨z,hz,hxz,hyz,_,hbad⟩ := h (M-2*drift (fraction 1 0) geometry)
  have hXz : 0 < first 32 geometry z := by rwa [hxz]
  have he : deriv (fun s => weightedEnergy s z) 0 =
      jacobian 32 geometry*(deriv (fun s => energy s z) 0+
        2*drift (fraction 1 0) geometry*energy 0 z) := by
    rw [(weightedEnergy_derivative_zero z hXz).deriv,(energy_derivative_zero z hXz).deriv,energy_zero]
    ring
  refine ⟨z,hz,hxz,hyz,weightedEnergy_positive_zero z,?_⟩
  have hh := mul_lt_mul_of_pos_left hbad jacobian_positive
  rw [he]
  unfold weightedEnergy
  change M*(jacobian 32 geometry*energy 0 z) < _
  nlinarith [hh]

theorem no_uniform_complete_angular_bound :
    ¬ ∃ M : ℝ, ∀ z ∈ wedge 32 geometry,
      0 < first 32 geometry z → 0 < second 32 geometry z →
      deriv (fun s => weightedEnergy s z) 0 ≤ M*weightedEnergy 0 z := by
  rintro ⟨M,hM⟩
  obtain ⟨X,hX,h⟩ := weighted_angular_derivative_unbounded
  obtain ⟨z,hz,hxz,hyz,_,hbad⟩ := h M
  exact (not_lt_of_ge (hM z hz (by rwa [hxz]) hyz)) hbad

#print axioms complete_angular_derivative_unbounded
#print axioms weightedEnergy_positive_zero
#print axioms weighted_angular_derivative_unbounded
#print axioms no_uniform_complete_angular_bound
end
end UnifiedTheory.Audit.KFCausalJointNeutralAngularClockObstruction
