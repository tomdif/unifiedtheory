/- Identify the physical quartic neutral marginal with the translated
energy whose first two integral derivatives and corrected convexity
have been proved. The clock geometry is held fixed in this comparison. -/
import UnifiedTheory.Audit.KFCausalNeutralCorrectedConvexity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslatedMarginal
noncomputable section
open MeasureTheory
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralTransportDomination (value)
open KFCausalNeutralIntegralDerivatives
open KFCausalQuarticPlaneDomination (potential)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (z : ℂ) (η L : ℝ)

def slice (v x : ℝ) : ℝ := potential (x+L*v)*
  ‖family n β b c P ((x:ℂ)+z+(η:ℂ)*Complex.I*(v:ℂ))‖^2
def marginal (v : ℝ) : ℝ := ∫ x, slice n β b c P z η L v x

theorem slice_shift (v x : ℝ) :
    slice n β b c P z η L v x = value n β b c P z η L v (x+L*v) := by
  unfold slice value KFCausalNeutralUniformDefect.curve KFCausalNeutralQuarticTransportForms.velocity
  congr 3
  push_cast
  ring

theorem slice_integrable (hβ : 0 < β) (v : ℝ) :
    Integrable (slice n β b c P z η L v) := by
  change Integrable (fun x => slice n β b c P z η L v x)
  simp_rw [slice_shift]
  exact (KFCausalNeutralTransportDomination.value_integrable n β b c P z η L hβ v).comp_add_right (L*v)

theorem marginal_eq_total (v : ℝ) :
    marginal n β b c P z η L v = total n β b c P z η L v := by
  unfold marginal total
  simp_rw [slice_shift]
  exact integral_add_right_eq_self (value n β b c P z η L v) (L*v)

theorem marginal_derivative (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (marginal n β b c P z η L) (totalSlope n β b c P z η L v) v := by
  have he : marginal n β b c P z η L = total n β b c P z η L := funext (marginal_eq_total n β b c P z η L)
  rw [he]
  exact (first_derivative_data n β b c P z η L hβ v).2

theorem marginal_second_derivative (hβ : 0 < β) (v : ℝ) :
    HasDerivAt (deriv (marginal n β b c P z η L)) (totalCurvature n β b c P z η L v) v := by
  have he : deriv (marginal n β b c P z η L) = totalSlope n β b c P z η L := by
    funext t
    exact (marginal_derivative n β b c P z η L hβ t).deriv
  rw [he]
  exact (second_derivative_data n β b c P z η L hβ v).2

theorem marginal_curvature_bound (hβ : 0 < β) (v : ℝ) :
    (deriv (marginal n β b c P z η L) v)^2-4*(L^2+η^2)*(marginal n β b c P z η L v)^2 ≤
      marginal n β b c P z η L v*deriv (deriv (marginal n β b c P z η L)) v := by
  have he : marginal n β b c P z η L = total n β b c P z η L := funext (marginal_eq_total n β b c P z η L)
  rw [he]
  exact actual_curvature_bound n β b c P z η L hβ v

theorem corrected_marginal_convex (hβ : 0 < β) (a : ℝ) (ha : 2*(L^2+η^2) ≤ a) :
    ConvexOn ℝ Set.univ (fun v => Real.exp (a*v^2)*marginal n β b c P z η L v) := by
  simp_rw [marginal_eq_total]
  exact KFCausalNeutralCorrectedConvexity.corrected_convex n β b c P z η L a hβ ha

omit η L in
theorem actual_corrected_marginal_convex (hβ : 0 < β) (ε h s : ℝ)
    (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) :
    let r := KFCausalClockFloorRelativeShift.scale ε (-h/2) s
    ConvexOn ℝ Set.univ (fun v => Real.exp ((KFCausalNeutralUniformDefect.defectConstant/2)*v^2)*
      marginal n β b c P z (2*r.im) (KFCausalChargedPairCoordinates.fieldSlope r) v) := by
  apply corrected_marginal_convex n β b c P z _ _ hβ
  have he := KFCausalNeutralUniformDefect.geometry_bound ε (-h/2) s hε
    (KFCausalClockFloorShiftedOutput.shift_bound ε h hb)
  linarith

#print axioms slice_shift
#print axioms slice_integrable
#print axioms marginal_eq_total
#print axioms marginal_derivative
#print axioms marginal_second_derivative
#print axioms marginal_curvature_bound
#print axioms corrected_marginal_convex
#print axioms actual_corrected_marginal_convex
end
end UnifiedTheory.Audit.KFCausalNeutralTranslatedMarginal
