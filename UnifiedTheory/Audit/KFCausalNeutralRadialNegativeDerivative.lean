/- The existing physical radius counterexample has a strictly negative
squared-radius derivative at some positive radius, with positive energy.
The clock geometry is fixed throughout this statement. -/
import UnifiedTheory.Audit.KFCausalNeutralRadialActualObstruction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralRadialNegativeDerivative
noncomputable section
open MeasureTheory Set
open KFCausalNeutralRadialActualObstruction (physicalAngular angular angular_derivative)
open KFCausalNeutralRadialActualGeometry (displacement field marginal)
open KFCausalNeutralRadialCoherentKernel (quartic mass mass_positive)

theorem physicalAngular_differentiable : Differentiable ℝ physicalAngular := by
  have he : physicalAngular = fun ρ => Real.exp 8*mass*angular displacement field ρ :=
    funext KFCausalNeutralRadialActualObstruction.physicalAngular_eq
  rw [he]
  exact fun ρ => ((angular_derivative displacement field ρ).const_mul _).differentiableAt

theorem physicalAngular_positive (ρ : ℝ) : 0 < physicalAngular ρ := by
  rw [KFCausalNeutralRadialActualObstruction.physicalAngular_eq]
  apply mul_pos (mul_pos (Real.exp_pos _) mass_positive)
  unfold angular
  apply div_pos _ (by positivity)
  have hp (θ : ℝ) : 0 < marginal displacement field (ρ*Real.sin θ) := by
    unfold marginal quartic
    positivity
  apply intervalIntegral.integral_pos (by linarith [Real.pi_pos])
    (show ContinuousOn (fun θ => marginal displacement field (ρ*Real.sin θ)) _ from by
      unfold marginal quartic; fun_prop)
    (fun θ _ => (hp θ).le)
  exact ⟨0,⟨by linarith [Real.pi_pos],Real.pi_pos.le⟩,hp 0⟩

theorem exists_negative_radial_derivative :
    ∃ ρ : ℝ, 0 < ρ ∧ deriv physicalAngular ρ < 0 := by
  obtain ⟨a,b,ha,hab,hbad⟩ := KFCausalNeutralRadialActualObstruction.actual_radius_comparison_fails
  obtain ⟨ρ,hρ,he⟩ := exists_deriv_eq_slope physicalAngular hab
    physicalAngular_differentiable.continuous.continuousOn physicalAngular_differentiable.differentiableOn
  refine ⟨ρ,lt_of_le_of_lt ha hρ.1,?_⟩
  rw [he]
  exact div_neg_of_neg_of_pos (sub_neg.mpr hbad) (sub_pos.mpr hab)

def area (X : ℝ) : ℝ := physicalAngular (Real.sqrt X)

theorem area_positive (X : ℝ) : 0 < area X := physicalAngular_positive _

theorem area_derivative (X : ℝ) (hX : 0 < X) :
    HasDerivAt area (deriv physicalAngular (Real.sqrt X)/(2*Real.sqrt X)) X := by
  have hd := (physicalAngular_differentiable (Real.sqrt X)).hasDerivAt.comp X
    (Real.hasDerivAt_sqrt hX.ne')
  simpa only [area,Function.comp_apply,div_eq_mul_inv,one_mul] using hd

theorem exists_positive_area_negative_derivative :
    ∃ X : ℝ, 0 < X ∧ 0 < area X ∧ deriv area X < 0 := by
  obtain ⟨ρ,hρ,hd⟩ := exists_negative_radial_derivative
  have hX : 0 < ρ^2 := sq_pos_of_pos hρ
  refine ⟨ρ^2,hX,area_positive _,?_⟩
  rw [(area_derivative _ hX).deriv,Real.sqrt_sq hρ.le]
  exact div_neg_of_neg_of_pos hd (by positivity)

#print axioms physicalAngular_differentiable
#print axioms physicalAngular_positive
#print axioms exists_negative_radial_derivative
#print axioms area_positive
#print axioms area_derivative
#print axioms exists_positive_area_negative_derivative
end
end UnifiedTheory.Audit.KFCausalNeutralRadialNegativeDerivative
