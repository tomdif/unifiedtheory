/- The added antisymmetric-momentum Gaussian commutes with each actual
physical kinetic translation. Strong differentiation proves preservation
of all four natural transverse momentum graphs, without a smooth-state
assumption. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff
import UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionHeatMomentum
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space FrequencyHilbert euclideanPullback)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint JointHilbert Block)
open UnifiedTheory.Audit.KFCausalPairedModeCoordinates (modeIsometry)
open UnifiedTheory.Audit.KFCausalPairedTranslationCoordinates
open UnifiedTheory.Audit.KFCausalSymmetricMomentumCoordinates
open UnifiedTheory.Audit.KFCausalAntisymmetricMomentumCoordinates (antiDirection antiFrequency antiDirection_mode)
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (chargeCoordinates)
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum (transverseMomentum transverseVector)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)
open UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum (spectralMomentum_graph_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorKineticDefect (transverse_graph_iff)
open UnifiedTheory.Audit.KFCausalContractiveMultiplier (multiplyL multiplyL_coe)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (heat heat_coe heatSymbol heatSymbol_measurable heatSymbol_norm)

variable (h δ : ℝ) (hδ : 0 < δ)

def euclideanHeat : FrequencyHilbert →L[ℂ] FrequencyHilbert :=
  (chargeEuclidean.symm : JointHilbert 2 4 →L[ℂ] FrequencyHilbert).comp
    ((multiplyL (heatSymbol h δ) (heatSymbol_measurable h δ) (heatSymbol_norm h δ hδ)).comp
      (chargeEuclidean : FrequencyHilbert →L[ℂ] JointHilbert 2 4))

theorem euclideanHeat_coe (f : FrequencyHilbert) :
    chargeEuclidean (euclideanHeat h δ hδ f) =ᵐ[volume] fun x => heatSymbol h δ x*(chargeEuclidean f) x := by
  change chargeEuclidean (chargeEuclidean.symm (_)) =ᵐ[volume] _
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact multiplyL_coe (heatSymbol h δ) (heatSymbol_measurable h δ) (heatSymbol_norm h δ hδ) _

theorem euclidean_heat (f : Hilbert) :
    euclideanPullback (heat h δ hδ f) = euclideanHeat h δ hδ (euclideanPullback f) := by
  apply chargeEuclidean.injective
  apply Lp.ext
  filter_upwards [heat_coe h δ hδ f,euclideanHeat_coe h δ hδ (euclideanPullback f)] with x hh he
  exact hh.trans he.symm

theorem left_commutes (v : Space) (a : Block 2) (hv : modeIsometry v = leftVector a) (f : FrequencyHilbert) :
    translation v (euclideanHeat h δ hδ f) = euclideanHeat h δ hδ (translation v f) := by
  apply chargeEuclidean.injective
  apply Lp.ext
  filter_upwards [chargeEuclidean_translation_coe v a hv (euclideanHeat h δ hδ f),
    euclideanHeat_coe h δ hδ f,euclideanHeat_coe h δ hδ (translation v f),
    chargeEuclidean_translation_coe v a hv f] with x ht hh he hf
  rw [ht,hh,he,hf]
  ring

theorem right_commutes (v : Space) (b : Block 4) (hv : modeIsometry v = rightVector b) (f : FrequencyHilbert) :
    translation v (euclideanHeat h δ hδ f) = euclideanHeat h δ hδ (translation v f) := by
  apply chargeEuclidean.injective
  rw [chargeEuclidean_rightTranslation v b hv]
  apply Lp.ext
  filter_upwards [translation_coe (rightVector b) (chargeEuclidean (euclideanHeat h δ hδ f)),
    (shift_preserves_volume (rightVector b)).quasiMeasurePreserving.ae (euclideanHeat_coe h δ hδ f),
    euclideanHeat_coe h δ hδ (translation v f),
    translation_coe (rightVector b) (chargeEuclidean f)] with x ht hh he hf
  change chargeEuclidean (euclideanHeat h δ hδ f) (x+rightVector b) =
    heatSymbol h δ (x+rightVector b)*(chargeEuclidean f) (x+rightVector b) at hh
  rw [ht,hh,he,chargeEuclidean_rightTranslation v b hv,hf]
  simp only [heatSymbol,PiLp.add_apply,rightVector,add_zero]

theorem transverse_graph_of_commutes (hne : h ≠ 0) (v : Transverse)
    (hT : ∀ (t : ℝ) (f : FrequencyHilbert),
      translation (t • transverseVector v) (euclideanHeat h δ hδ f) =
        euclideanHeat h δ hδ (translation (t • transverseVector v) f))
    (f g : Hilbert) (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (transverseMomentum h v).graph := by
  have hd := ((euclideanHeat h δ hδ).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    ((spectralMomentum_graph_derivative h hne (transverseVector v) _ _).mp
      ((transverse_graph_iff h v f g).mp hfg))
  rw [transverse_graph_iff,euclidean_heat,euclidean_heat]
  apply (spectralMomentum_graph_derivative h hne (transverseVector v) _ _).mpr
  change HasDerivAt (fun t : ℝ => euclideanHeat h δ hδ (translation (t • transverseVector v) (euclideanPullback f)))
    (euclideanHeat h δ hδ ((Complex.I/(h:ℂ)) • euclideanPullback g)) 0 at hd
  simpa only [hT,map_smul] using hd

theorem transverse_graph_left (hne : h ≠ 0) (v : Transverse) (a : Block 2)
    (hv : modeIsometry (transverseVector v) = leftVector a) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (transverseMomentum h v).graph := by
  apply transverse_graph_of_commutes h δ hδ hne v _ f g hfg
  intro t z
  exact left_commutes h δ hδ (t • transverseVector v) (t • a)
    (by rw [map_smul,hv,leftVector_smul]) z

theorem transverse_graph_right (hne : h ≠ 0) (v : Transverse) (b : Block 4)
    (hv : modeIsometry (transverseVector v) = rightVector b) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (transverseMomentum h v).graph := by
  apply transverse_graph_of_commutes h δ hδ hne v _ f g hfg
  intro t z
  exact right_commutes h δ hδ (t • transverseVector v) (t • b)
    (by rw [map_smul,hv,rightVector_smul]) z

theorem model_graph (hne : h ≠ 0) (i : Fin 4) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h (modelDirections i)).graph) :
    (heat h δ hδ f,heat h δ hδ g) ∈ (transverseMomentum h (modelDirections i)).graph := by
  fin_cases i
  · exact transverse_graph_right h δ hδ hne (symmetricDirection 0) (symmetricBlock 0)
      (symmetricDirection_mode 0) f g hfg
  · exact transverse_graph_right h δ hδ hne (symmetricDirection 1) (symmetricBlock 1)
      (symmetricDirection_mode 1) f g hfg
  · exact transverse_graph_left h δ hδ hne (antiDirection 0) (antiFrequency 0)
      (antiDirection_mode 0) f g hfg
  · exact transverse_graph_left h δ hδ hne (antiDirection 1) (antiFrequency 1)
      (antiDirection_mode 1) f g hfg

#print axioms euclideanHeat_coe
#print axioms euclidean_heat
#print axioms left_commutes
#print axioms right_commutes
#print axioms transverse_graph_of_commutes
#print axioms transverse_graph_left
#print axioms transverse_graph_right
#print axioms model_graph

end
end UnifiedTheory.Audit.KFCausalNeutralPositionHeatMomentum
