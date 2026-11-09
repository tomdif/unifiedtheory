/- The normalized charge pullback conjugates translations by its actual
linear flow. Differentiation gives covariance of the full natural momentum
graphs, without a smooth-vector or common-core assumption. -/
import UnifiedTheory.Audit.KFCausalMixedCircleAction
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalNormalizedChargeFlow
open UnifiedTheory.Audit.KFCausalMixedCircleAction
open UnifiedTheory.Audit.KFCausalPairedRotation (rotationIsometry)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum spectralMomentum_graph_derivative)

def linearFlow (c : ℝ) (hc : c ≠ 0) (θ : ℝ) : Joint 2 4 ≃ₗ[ℝ] Joint 2 4 :=
  (dilationEquiv c hc).trans ((rotationIsometry θ).toLinearEquiv.trans (dilationEquiv c hc).symm)

theorem linearFlow_eq (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x : Joint 2 4) :
    linearFlow c hc θ x = flowEquiv c hc θ x := rfl

theorem flow_add (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (x y : Joint 2 4) :
    flowEquiv c hc θ (x+y) = flowEquiv c hc θ x+flowEquiv c hc θ y :=
  (linearFlow c hc θ).map_add x y

theorem flow_smul (c : ℝ) (hc : c ≠ 0) (θ t : ℝ) (x : Joint 2 4) :
    flowEquiv c hc θ (t • x) = t • flowEquiv c hc θ x :=
  (linearFlow c hc θ).map_smul t x

theorem action_reverse (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (f : JointHilbert 2 4) :
    action c hc (-θ) (action c hc θ f) = f := by
  rw [action_compose,add_neg_cancel,action_zero]

theorem translation_action (c : ℝ) (hc : c ≠ 0) (θ : ℝ) (v : Joint 2 4) (f : JointHilbert 2 4) :
    translation v (action c hc θ f) = action c hc θ (translation (flowEquiv c hc θ v) f) := by
  apply Lp.ext
  filter_upwards [translation_coe v (action c hc θ f),
    (shift_preserves_volume v).quasiMeasurePreserving.ae (action_coe c hc θ f),
    action_coe c hc θ (translation (flowEquiv c hc θ v) f),
    (flow_preserves_volume c hc θ).quasiMeasurePreserving.ae
      (translation_coe (flowEquiv c hc θ v) f)] with x ht ha hu hv
  change (action c hc θ f) (x+v) = f (flowEquiv c hc θ (x+v)) at ha
  simp only [Function.comp_apply] at hu
  rw [ht,ha,hu,hv,flow_add]

theorem conjugate_translation (c : ℝ) (hc : c ≠ 0) (θ t : ℝ)
    (v : Joint 2 4) (f : JointHilbert 2 4) :
    action c hc (-θ) (translation (t • v) (action c hc θ f)) =
      translation (t • flowEquiv c hc θ v) f := by
  rw [translation_action,action_reverse,flow_smul]

theorem momentum_graph_reverse (h : ℝ) (hh : h ≠ 0) (c : ℝ) (hc : c ≠ 0) (θ : ℝ)
    (v : Joint 2 4) (f g : JointHilbert 2 4)
    (hfg : (action c hc θ f,g) ∈ (spectralMomentum h v).graph) :
    (f,action c hc (-θ) g) ∈ (spectralMomentum h (flowEquiv c hc θ v)).graph := by
  apply (spectralMomentum_graph_derivative h hh _ _ _).mpr
  have hd := (((action c hc (-θ) : JointHilbert 2 4 →L[ℂ] JointHilbert 2 4).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hh v _ g).mp hfg))
  change HasDerivAt (fun t => action c hc (-θ) (translation (t • v) (action c hc θ f)))
    (action c hc (-θ) ((Complex.I/(h:ℂ)) • g)) 0 at hd
  simpa only [conjugate_translation,map_smul] using hd

#print axioms linearFlow_eq
#print axioms flow_add
#print axioms flow_smul
#print axioms action_reverse
#print axioms translation_action
#print axioms conjugate_translation
#print axioms momentum_graph_reverse

end
end UnifiedTheory.Audit.KFCausalMixedRotationMomentumGraph
