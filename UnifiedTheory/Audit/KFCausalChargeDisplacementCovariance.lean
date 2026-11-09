/- Exact covariance of displacement and phase on the full charge-coordinate
L2 space. Both real parameter vectors rotate; no Gaussian or domain
assumption is used in this unitary identity. -/
import UnifiedTheory.Audit.KFCausalChargeModulationFlow
import UnifiedTheory.Audit.KFCausalMixedCircleAction
import UnifiedTheory.Audit.KFCausalFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalChargeDisplacementCovariance
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalPairedRotation
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (JointHilbert)
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalChargeModulationFlow
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalMixedCircleAction (action action_coe)

theorem flow_add (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x y : Space) :
    flowEquiv c hc θ (x+y) = flowEquiv c hc θ x + flowEquiv c hc θ y :=
  ((dilationEquiv c hc).trans ((rotationEquiv θ).trans
    (dilationEquiv c hc).symm)).map_add x y

theorem flow_displacement (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (q : Space) :
    flowEquiv c hc θ (dilate c⁻¹ (parameter θ q)) = dilate c⁻¹ q := by
  simp only [flow_apply,dilate_compose,mul_inv_cancel₀ hc,dilate_one,
    parameter,rotate_compose,add_neg_cancel,rotate_zero]

theorem flow_shift (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x q : Space) :
    flowEquiv c hc θ (x+dilate c⁻¹ (parameter θ q)) =
      flowEquiv c hc θ x+dilate c⁻¹ q := by
  rw [flow_add,flow_displacement]

theorem phase_flow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x k : Space) :
    phase (dilate c k) (flowEquiv c hc θ x) =
      phase (dilate c (parameter θ k)) x := by
  exact congrArg (fun t : ℝ => (Real.fourierChar t : ℂ))
    ((real_inner_comm _ _).trans ((flow_phase c hc θ x k).trans (real_inner_comm _ _)))

def displacement (c : ℝ) (q k : Space) : JointHilbert 2 4 ≃ₗᵢ[ℂ] JointHilbert 2 4 :=
  (translation (dilate c⁻¹ q)).trans (phaseAction (dilate c k))

theorem displacement_coe (c : ℝ) (q k : Space) (f : JointHilbert 2 4) :
    displacement c q k f =ᵐ[volume]
      fun x => phase (dilate c k) x*f (x+dilate c⁻¹ q) := by
  filter_upwards [phaseAction_coe (dilate c k) (translation (dilate c⁻¹ q) f),
    translation_coe (dilate c⁻¹ q) f] with x hx hy
  exact hx.trans (congrArg (fun z : ℂ => phase (dilate c k) x*z) hy)

theorem displacement_zero (c : ℝ) (f : JointHilbert 2 4) : displacement c 0 0 f = f := by
  apply Lp.ext
  filter_upwards [displacement_coe c 0 0 f] with x hx
  have hz (d : ℝ) : dilate d (0 : Space) = 0 := by
    ext i
    cases i <;> simp [dilate]
  simpa [hz,phase] using hx

theorem action_displacement (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (q k : Space)
    (f : JointHilbert 2 4) :
    action c hc θ (displacement c q k f) =
      displacement c (parameter θ q) (parameter θ k) (action c hc θ f) := by
  apply Lp.ext
  filter_upwards [action_coe c hc θ (displacement c q k f),
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae (displacement_coe c q k f),
    displacement_coe c (parameter θ q) (parameter θ k) (action c hc θ f),
    (shift_preserves_volume (dilate c⁻¹ (parameter θ q))).quasiMeasurePreserving.ae
      (action_coe c hc θ f)] with x hx hy hz hw
  change action c hc θ f (x+dilate c⁻¹ (parameter θ q)) =
    f (flowEquiv c hc θ (x+dilate c⁻¹ (parameter θ q))) at hw
  simp only [Function.comp_apply] at hx
  rw [hx,hy,hz,hw,flow_shift,phase_flow]

#print axioms flow_add
#print axioms flow_displacement
#print axioms flow_shift
#print axioms phase_flow
#print axioms displacement_coe
#print axioms displacement_zero
#print axioms action_displacement

end
end UnifiedTheory.Audit.KFCausalChargeDisplacementCovariance
