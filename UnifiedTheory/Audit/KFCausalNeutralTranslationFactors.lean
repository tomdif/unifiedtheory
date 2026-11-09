/- Neutral translation preserves the actual maximal exponential, clock
and kinetic graphs. These are full-domain identities for the existing
ordered factors, not formal commutation on a test core. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
import UnifiedTheory.Audit.KFCausalClockFloorTrialMatter
import UnifiedTheory.Audit.KFCausalClockFloorKineticModulation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space split fourierCoordinates)
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates (coupledFourier)
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalPhysicalTransverseMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum (clockMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition (composition_graph)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem action_inverse (r : ℝ) (f : Hilbert) : action (-r) (action r f) = f := by
  apply Lp.ext
  filter_upwards [action_coe (-r) (action r f),
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector (-r))).quasiMeasurePreserving.ae
      (action_coe r f)] with x ha hb
  change action r f (x+vector (-r)) = _ at hb
  rw [ha,hb]
  change f ((x+vector (-r))+vector r) = f x
  congr 1
  ext i <;> simp [vector,Pi.single_neg]

theorem fourier_action_coe (r : ℝ) (f : Hilbert) :
    fourierCoordinates (action r f) =ᵐ[volume] fun k =>
      KFCausalFourierTranslation.phase (split.symm (vector r)) k*fourierCoordinates f k := by
  change (Lp.fourierTransformₗᵢ Space ℂ) (KFCausalEuclideanConfiguration.euclideanPullback (action r f)) =ᵐ[volume] _
  rw [euclidean_action,KFCausalFourierTranslation.fourier_translation]
  exact KFCausalFourierTranslation.phaseAction_coe _ _

theorem exponential_graph_action (ε : ℝ) (hε : 0 < ε) (h a r : ℝ)
    (f g : Hilbert) (hfg : (f,g) ∈ (longitudinalExponential ε hε h a).graph) :
    (action r f,action r g) ∈ (longitudinalExponential ε hε h a).graph := by
  apply (longitudinal_exponential_graph ε hε h a _ _).mpr
  filter_upwards [coupledFourier_action_coe ε hε r f,coupledFourier_action_coe ε hε r g,
    (longitudinal_exponential_graph ε hε h a f g).mp hfg] with k hf hg hh
  rw [hf,hg,hh]
  ring

theorem clockHalf_graph_action (ε r : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (clockHalf ε).graph) :
    (action r f,action r g) ∈ (clockHalf ε).graph := by
  apply (clockHalf_graph ε _ _).mpr
  filter_upwards [action_coe r f,action_coe r g,
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector r)).quasiMeasurePreserving.ae
      ((clockHalf_graph ε f g).mp hfg)] with x hf hg hh
  change g (x+vector r) = _ at hh
  rw [hf,hg,hh]
  simp [KFCausalLpPhaseTranslation.shift,halfWeight,vector]

theorem inverseHalf_graph_action (ε r : ℝ) (f g : Hilbert) (hfg : (f,g) ∈ (inverseClockHalf ε).graph) :
    (action r f,action r g) ∈ (inverseClockHalf ε).graph := by
  apply (inverseClockHalf_graph ε _ _).mpr
  filter_upwards [action_coe r f,action_coe r g,
    (KFCausalLpPhaseTranslation.shift_preserves volume (vector r)).quasiMeasurePreserving.ae
      ((inverseClockHalf_graph ε f g).mp hfg)] with x hf hg hh
  change g (x+vector r) = _ at hh
  rw [hf,hg,hh]
  simp [KFCausalLpPhaseTranslation.shift,inverseWeight,halfWeight,vector]

theorem momentum_graph_action (h r : ℝ) (v : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (transverseMomentum h v).graph) :
    (action r f,action r g) ∈ (transverseMomentum h v).graph := by
  apply (transverseMomentum_graph h v _ _).mpr
  filter_upwards [fourier_action_coe r f,fourier_action_coe r g,
    (transverseMomentum_graph h v f g).mp hfg] with k hf hg hh
  rw [hf,hg,hh]
  ring

theorem kinetic_graph_action (ε h r : ℝ) (v : Transverse) (f g : Hilbert)
    (hfg : (f,g) ∈ (clockMomentum ε h v).graph) :
    (action r f,action r g) ∈ (clockMomentum ε h v).graph := by
  rw [clockMomentum,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action r u,inverseHalf_graph_action ε r f u hu,momentum_graph_action h r v u g hg⟩

theorem ordered_graph_action (ε : ℝ) (hε : 0 < ε) (h r : ℝ) (f g : Hilbert)
    (hfg : (f,g) ∈ (orderedExponential ε hε h).graph) :
    (action r f,action r g) ∈ (orderedExponential ε hε h).graph := by
  rw [orderedExponential,composition_graph] at hfg ⊢
  obtain ⟨u,hu,hg⟩ := hfg
  exact ⟨action r u,inverseHalf_graph_action ε r f u hu,exponential_graph_action ε hε h (1/2) r u g hg⟩

#print axioms action_inverse
#print axioms fourier_action_coe
#print axioms exponential_graph_action
#print axioms clockHalf_graph_action
#print axioms inverseHalf_graph_action
#print axioms momentum_graph_action
#print axioms kinetic_graph_action
#print axioms ordered_graph_action

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
