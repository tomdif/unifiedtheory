/- The complete actual clock derivative of the coherent angular witness,
including changing neutral geometry, moving squared radius and the wedge
Jacobian. The neutral source is fixed along this clock curve. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialClockFamily
import UnifiedTheory.Audit.KFCausalReciprocalWedgePrefactor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2600000

namespace UnifiedTheory.Audit.KFCausalJointNeutralAngularClockJet
noncomputable section
open KFCausalNeutralRadialClockFamily (actualScale angular angular_zero angular_differentiable)
open KFCausalNeutralRadialActualGeometry (geometry source)
open KFCausalNeutralRadialNegativeDerivative (area)
open KFCausalReciprocalWedgeGeometry (first second)
open KFCausalReciprocalWedgeVelocity (drift shrink)
open KFCausalNeutralPlaneNormalizedGeometry (fraction)
open KFCausalReciprocalWedgePrefactor (jacobian)
open KFCausalJointNeutralRadialTransportObstruction (weight)
open KFCausalJointNeutralRadialEstimate (jointArea)

def clockJet (X : ℝ) : ℝ := (fderiv ℝ angular (0,Real.sqrt X)) (1,0)
def energy (s : ℝ) (z : ℂ) : ℝ :=
  jointArea 1 1 (fun _ => 1) (fun _ => source) (fun _ => 1) (fun _ => 1)
    (actualScale s) z (first 32 (actualScale s) z)
def weightedEnergy (s : ℝ) (z : ℂ) : ℝ := jacobian 32 (actualScale s)*energy s z

theorem radial_derivative_identification (X : ℝ) (hX : 0 < X) :
    (fderiv ℝ angular (0,Real.sqrt X)) (0,1/(2*Real.sqrt X)) = deriv area X := by
  have hd := (angular_differentiable (0,Real.sqrt X)).hasFDerivAt.comp_hasDerivAt X
    ((hasDerivAt_const X (0:ℝ)).prodMk (Real.hasDerivAt_sqrt hX.ne'))
  have he : (fun t => angular (0,Real.sqrt t)) = area := by
    funext t
    exact angular_zero _
  simp only [Function.comp_def] at hd
  rw [he] at hd
  exact hd.deriv.symm

theorem derivative_split (D : (ℝ × ℝ) →L[ℝ] ℝ) (v k : ℝ) :
    D (1,v*k) = D (1,0)+v*D (0,k) := by
  have he : ((1:ℝ),v*k) = ((1:ℝ),0)+v • ((0:ℝ),k) := by ext <;> simp
  rw [he,map_add,map_smul]
  rfl

theorem moving_angular_derivative (q : ℝ → ℝ) (v : ℝ)
    (hq : HasDerivAt q v 0) (hX : 0 < q 0) :
    HasDerivAt (fun s => angular (s,Real.sqrt (q s)))
      (clockJet (q 0)+v*deriv area (q 0)) 0 := by
  have hs := (Real.hasDerivAt_sqrt hX.ne').comp 0 hq
  have hd := (angular_differentiable (0,Real.sqrt (q 0))).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id 0).prodMk hs)
  have he : (fderiv ℝ angular (0,Real.sqrt (q 0))) (1,1/(2*Real.sqrt (q 0))*v) =
      clockJet (q 0)+v*deriv area (q 0) := by
    rw [mul_comm (1/(2*Real.sqrt (q 0))),derivative_split,radial_derivative_identification (q 0) hX]
    rfl
  rwa [he] at hd

theorem geometry_regular :
    0 < KFCausalReciprocalGaussianCoordinates.area geometry ∧ geometry.re ≠ 0 ∧ geometry.im ≠ 0 ∧
      0 < KFCausalNeutralPlaneClockGeometry.denominator (1-fraction 1 0) (fraction 1 0) geometry := by
  have hy : |(1/128:ℝ)| ≤ Real.pi*1/3 := by
    simpa only [mul_one] using KFCausalNeutralRadialActualGeometry.actual_parameters.2.2.2
  have hA := KFCausalNeutralPlaneClockGeometry.scale_square_re_positive 1 (1/128) 0 (by norm_num) hy
  have ht := KFCausalNeutralPlaneNormalizedGeometry.fraction_bounds 1 0 (by norm_num)
  exact ⟨hA,(KFCausalNeutralPlaneClockGeometry.scale_re_positive 1 (1/128) 0 (by norm_num) hy).ne',
    KFCausalNeutralPlaneClockGeometry.scale_im_ne_zero 1 (1/128) 0 (by norm_num) hy (by norm_num),
    KFCausalNeutralPlaneNormalizedGeometry.normalized_denominator_positive _ _ ⟨ht.1.le,ht.2.le⟩ hA⟩

theorem clock_velocity : HasDerivAt actualScale
    (KFCausalNeutralPlaneClockGeometry.velocity (1-fraction 1 0) (fraction 1 0) geometry) 0 :=
  KFCausalNeutralPlaneNormalizedGeometry.actual_normalized_velocity 1 (1/128) 0 (by norm_num)
    (by simpa only [mul_one] using KFCausalNeutralRadialActualGeometry.actual_parameters.2.2.2)

theorem first_derivative_zero (z : ℂ) : HasDerivAt (fun s => first 32 (actualScale s) z)
    (drift (fraction 1 0) geometry*first 32 geometry z-
      shrink (fraction 1 0) geometry*second 32 geometry z) 0 :=
  KFCausalReciprocalWedgeVelocity.first_derivative actualScale 32 (fraction 1 0) 0 z clock_velocity
    (by norm_num) geometry_regular.1.ne' geometry_regular.2.1 geometry_regular.2.2.1 geometry_regular.2.2.2.ne'

theorem jacobian_derivative_zero : HasDerivAt (fun s => jacobian 32 (actualScale s))
    (2*drift (fraction 1 0) geometry*jacobian 32 geometry) 0 :=
  KFCausalReciprocalWedgePrefactor.jacobian_derivative actualScale 32 (fraction 1 0) 0 clock_velocity
    (by norm_num) geometry_regular.1.ne' geometry_regular.2.1 geometry_regular.2.2.1 geometry_regular.2.2.2.ne'

theorem jacobian_positive : 0 < jacobian 32 geometry := by
  have hA := geometry_regular.1.ne'
  have ha := geometry_regular.2.1
  have hb := geometry_regular.2.2.1
  unfold jacobian KFCausalReciprocalWedgePrefactor.signedJacobian
  exact abs_pos.mpr (div_ne_zero one_ne_zero (by positivity))

theorem energy_factor (s : ℝ) (z : ℂ) : energy s z = weight z*angular (s,Real.sqrt (first 32 (actualScale s) z)) :=
  KFCausalNeutralRadialClockFamily.jointArea_factor s _ z

theorem energy_zero (z : ℂ) : energy 0 z = weight z*area (first 32 geometry z) := by
  rw [energy_factor,angular_zero]
  rfl

theorem energy_derivative_zero (z : ℂ) (hX : 0 < first 32 geometry z) :
    HasDerivAt (fun s => energy s z)
      (weight z*(clockJet (first 32 geometry z)+deriv area (first 32 geometry z)*
        (drift (fraction 1 0) geometry*first 32 geometry z-
          shrink (fraction 1 0) geometry*second 32 geometry z))) 0 := by
  have hd := (moving_angular_derivative _ _ (first_derivative_zero z) hX).const_mul (weight z)
  convert hd using 1
  · funext s
    exact energy_factor s z
  · dsimp only [actualScale,KFCausalNeutralRadialActualGeometry.geometry] at *
    ring

theorem weightedEnergy_derivative_zero (z : ℂ) (hX : 0 < first 32 geometry z) :
    HasDerivAt (fun s => weightedEnergy s z)
      (jacobian 32 geometry*weight z*
        (2*drift (fraction 1 0) geometry*area (first 32 geometry z)+clockJet (first 32 geometry z)+
          deriv area (first 32 geometry z)*(drift (fraction 1 0) geometry*first 32 geometry z-
            shrink (fraction 1 0) geometry*second 32 geometry z))) 0 := by
  have hd := jacobian_derivative_zero.mul (energy_derivative_zero z hX)
  convert hd using 1
  rw [energy_zero]
  change _ = _ + jacobian 32 geometry*_
  ring

#print axioms radial_derivative_identification
#print axioms derivative_split
#print axioms moving_angular_derivative
#print axioms geometry_regular
#print axioms clock_velocity
#print axioms first_derivative_zero
#print axioms jacobian_derivative_zero
#print axioms jacobian_positive
#print axioms energy_factor
#print axioms energy_zero
#print axioms energy_derivative_zero
#print axioms weightedEnergy_derivative_zero
end
end UnifiedTheory.Audit.KFCausalJointNeutralAngularClockJet
