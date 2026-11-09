/- The first two neutral translation derivatives pass through the
whole-real-line integral. The common integrable bounds are derived for
the finite profile family, not supplied as additional premises. -/
import UnifiedTheory.Audit.KFCausalNeutralTransportDomination

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralIntegralDerivatives
noncomputable section
open MeasureTheory
open scoped Topology
open KFCausalNeutralTransportDomination
open KFCausalNeutralUniformDefect (curve)
open KFCausalNeutralLinePackets (step)
open KFCausalNeutralQuarticTransportForms (velocity rate acceleration)
open KFCausalNeutralQuarticFormBound (energy first second)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (z : ℂ) (η L : ℝ)

def total (v : ℝ) : ℝ := ∫ x, value n β b c P z η L v x
def totalSlope (v : ℝ) : ℝ := ∫ x, slope n β b c P z η L v x
def totalCurvature (v : ℝ) : ℝ := ∫ x, curvature n β b c P z η L v x

theorem first_derivative_data (hβ : 0 < β) (v : ℝ) :
    Integrable (slope n β b c P z η L v) ∧
      HasDerivAt (total n β b c P z η L) (totalSlope n β b c P z η L v) v := by
  obtain ⟨B,D,hB,_,hb⟩ := local_domination n β b c P z η L hβ v
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := value n β b c P z η L) (F' := slope n β b c P z η L) (bound := B)
    (Metric.ball_mem_nhds v (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall (fun t => (value_continuous n β b c P z η L t).aestronglyMeasurable))
    (value_integrable n β b c P z η L hβ v)
    (slope_continuous n β b c P z η L v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x t ht => (hb t ht x).1)) hB
    (Filter.Eventually.of_forall (fun x t _ => value_derivative n β b c P z η L t x))

theorem second_derivative_data (hβ : 0 < β) (v : ℝ) :
    Integrable (curvature n β b c P z η L v) ∧
      HasDerivAt (totalSlope n β b c P z η L) (totalCurvature n β b c P z η L v) v := by
  obtain ⟨B,D,_,hD,hb⟩ := local_domination n β b c P z η L hβ v
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := slope n β b c P z η L) (F' := curvature n β b c P z η L) (bound := D)
    (Metric.ball_mem_nhds v (by norm_num : (0:ℝ)<1))
    (Filter.Eventually.of_forall (fun t => (slope_continuous n β b c P z η L t).aestronglyMeasurable))
    (first_derivative_data n β b c P z η L hβ v).1
    (curvature_continuous n β b c P z η L v).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x t ht => (hb t ht x).2)) hD
    (Filter.Eventually.of_forall (fun x t _ => slope_derivative n β b c P z η L t x))

theorem deriv_total (hβ : 0 < β) :
    deriv (total n β b c P z η L) = totalSlope n β b c P z η L := by
  funext v
  exact (first_derivative_data n β b c P z η L hβ v).2.deriv

theorem deriv_totalSlope (hβ : 0 < β) :
    deriv (totalSlope n β b c P z η L) = totalCurvature n β b c P z η L := by
  funext v
  exact (second_derivative_data n β b c P z η L hβ v).2.deriv

theorem curve_x_derivative (v x : ℝ) :
    HasDerivAt (fun t => curve n β b c P z η L t v)
      (curve n β b c (fun i => step β (b i) (P i)) z η L x v) x := by
  simpa only [curve,add_assoc] using
    KFCausalNeutralJointCurvatureForm.translated_family_derivative n β b c P (z+velocity η L*(v:ℂ)) x

theorem total_form (v : ℝ) :
    total n β b c P z η L v = energy (fun x => curve n β b c P z η L x v) := rfl

theorem totalSlope_form (hβ : 0 < β) (v : ℝ) :
    totalSlope n β b c P z η L v = first η L
      (fun x => curve n β b c P z η L x v)
      (fun x => curve n β b c (fun i => step β (b i) (P i)) z η L x v) :=
  KFCausalNeutralQuarticTransportForms.rate_integral η L _ _
    (curve_regular n β b c P z η L hβ v)
    (curve_regular n β b c _ z η L hβ v) (curve_x_derivative n β b c P z η L v)

theorem totalCurvature_form (hβ : 0 < β) (v : ℝ) :
    totalCurvature n β b c P z η L v = second η L
      (fun x => curve n β b c P z η L x v)
      (fun x => curve n β b c (fun i => step β (b i) (P i)) z η L x v) :=
  KFCausalNeutralQuarticTransportForms.acceleration_integral η L _ _ _
    (curve_regular n β b c P z η L hβ v)
    (curve_regular n β b c _ z η L hβ v)
    (curve_regular n β b c _ z η L hβ v)
    (curve_x_derivative n β b c P z η L v) (curve_x_derivative n β b c _ z η L v)

theorem actual_curvature_bound (hβ : 0 < β) (v : ℝ) :
    (deriv (total n β b c P z η L) v)^2-4*(L^2+η^2)*(total n β b c P z η L v)^2 ≤
      total n β b c P z η L v*deriv (deriv (total n β b c P z η L)) v := by
  rw [deriv_total n β b c P z η L hβ,deriv_totalSlope n β b c P z η L hβ,
    total_form,totalSlope_form n β b c P z η L hβ,totalCurvature_form n β b c P z η L hβ]
  exact KFCausalNeutralQuarticFormBound.curvature_form_bound η L _ _
    (curve_regular n β b c P z η L hβ v)
    (curve_regular n β b c _ z η L hβ v) (curve_x_derivative n β b c P z η L v)

#print axioms first_derivative_data
#print axioms second_derivative_data
#print axioms deriv_total
#print axioms deriv_totalSlope
#print axioms curve_x_derivative
#print axioms total_form
#print axioms totalSlope_form
#print axioms totalCurvature_form
#print axioms actual_curvature_bound
end
end UnifiedTheory.Audit.KFCausalNeutralIntegralDerivatives
