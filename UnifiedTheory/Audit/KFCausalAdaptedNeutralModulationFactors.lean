/- The adapted neutral phase preserves the full natural exponential and
ordered matter graphs. Its kinetic covariance has the existing bounded
inverse-clock correction. No charge-averaged domain assertion is made. -/
import UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationFactors
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse (inverseL inverseL_graph)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

theorem exponential_graph_action (ε : ℝ) (hε : 0 < ε) (h a v : ℝ)
    (f g : Hilbert) (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph) :
    (action v f,action v g) ∈ (longitudinalExponential ε hε h a).graph := by
  apply (longitudinal_exponential_graph ε hε h a _ _).mpr
  filter_upwards [coupledFourier_action_coe ε hε v f,coupledFourier_action_coe ε hε v g,
    (KFCausalFourierTranslation.shift_preserves_volume (-spectralVector v)).quasiMeasurePreserving.ae
      ((longitudinal_exponential_graph ε hε h a f g).mp hfg)] with x hf hg hx
  change coupledFourier ε hε g (x + -spectralVector v) =
    (Real.exp (a*KFCausalClockFloorFourierMultiplier.symbol h (x + -spectralVector v)) : ℂ)*
      coupledFourier ε hε f (x + -spectralVector v) at hx
  rw [hf,hg,hx,symbol_shift]

theorem clockHalf_graph_action (ε v : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action v f,action v g) ∈ (clockHalf ε).graph :=
  KFCausalClockFloorKineticModulation.clockHalf_graph_modulation ε (frequency v) f g hfg

theorem inverseL_action (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f : Hilbert) :
    inverseL ε hε (action v f) = action v (inverseL ε hε f) :=
  KFCausalClockFloorKineticModulation.inverseL_modulation ε hε (frequency v) f

theorem inverseHalf_graph_action (ε : ℝ) (hε : 0 < ε) (v : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (action v f,action v g) ∈ (inverseClockHalf ε).graph := by
  rw [inverseL_graph ε hε] at hfg ⊢
  rw [hfg,inverseL_action]

theorem kinetic_graph_action (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
    (v : ℝ) (d : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h d).graph) :
    (action v f,action v (g+((h*frequency v (0,d):ℝ):ℂ) • inverseL ε hε f)) ∈
      (clockMomentum ε h d).graph :=
  KFCausalClockFloorKineticModulation.kinetic_graph_modulation ε hε h hne d (frequency v) f g hfg

theorem ordered_graph_action (ε : ℝ) (hε : 0 < ε) (h v : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (action v f,action v g) ∈ (orderedExponential ε hε h).graph := by
  rw [orderedExponential,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action v u,inverseHalf_graph_action ε hε v f u hu,
    exponential_graph_action ε hε h (1/2) v u g hg⟩

theorem field_graph_action (l : Transverse →L[ℝ] ℝ) (v : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (physicalField l).graph) :
    (action v f,action v g) ∈ (physicalField l).graph := by
  apply (physicalField_graph l _ _).mpr
  filter_upwards [action_coe v f,action_coe v g,(physicalField_graph l f g).mp hfg]
    with x hf hg hx
  rw [hf,hg,hx]
  ring

theorem square_graph_action (l : Transverse →L[ℝ] ℝ) (v : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (fieldSquare l).graph) :
    (action v f,action v g) ∈ (fieldSquare l).graph := by
  apply (fieldSquare_graph l _ _).mpr
  filter_upwards [action_coe v f,action_coe v g,(fieldSquare_graph l f g).mp hfg]
    with x hf hg hx
  rw [hf,hg,hx]
  ring

theorem linear_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h v : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (physicalField l)).graph) :
    (action v f,action v g) ∈ (matterFactor ε hε h (physicalField l)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action v u,ordered_graph_action ε hε h v f u hu,field_graph_action l v u g hg⟩

theorem quadratic_matter_graph_action (ε : ℝ) (hε : 0 < ε) (h v : ℝ)
    (l : Transverse →L[ℝ] ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (matterFactor ε hε h (fieldSquare l)).graph) :
    (action v f,action v g) ∈ (matterFactor ε hε h (fieldSquare l)).graph := by
  rw [matterFactor,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action v u,ordered_graph_action ε hε h v f u hu,square_graph_action l v u g hg⟩

#print axioms exponential_graph_action
#print axioms clockHalf_graph_action
#print axioms inverseL_action
#print axioms inverseHalf_graph_action
#print axioms kinetic_graph_action
#print axioms ordered_graph_action
#print axioms field_graph_action
#print axioms square_graph_action
#print axioms linear_matter_graph_action
#print axioms quadratic_matter_graph_action

end
end UnifiedTheory.Audit.KFCausalAdaptedNeutralModulationFactors
