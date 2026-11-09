/- Every normalized canonical momentum boost lies in all eight natural
energy-factor domains and the completed unaveraged energy form. This does
not assert charge invariance or membership in the circle-averaged form. -/
import UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
import UnifiedTheory.Audit.KFCausalClockFloorCoherentMatter
import UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPhysicalMomentumModulation
open UnifiedTheory.Audit.KFCausalClockFloorEvolvedCharacteristics (positionFrequency)
open UnifiedTheory.Audit.KFCausalClockFloorBoostedSpectral
open UnifiedTheory.Audit.KFCausalClockFloorBoostedKineticLimit (boostedState boostedState_norm)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialMomentum
open UnifiedTheory.Audit.KFCausalClockFloorTrialMatter (matterFactor)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorKineticModulation
open UnifiedTheory.Audit.KFCausalClockFloorSemiclassicalStates (unitTrial)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalClockFloorFormHamiltonian
open UnifiedTheory.Audit.KFCausalClockFloorJointEnergy (seedEnergy)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalField
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare
open UnifiedTheory.Audit.KFCausalOrderedOperatorComposition

theorem spectralOutput_fieldSquare_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    spectralOutput ε a h hε ha hh hb p ∈ (fieldSquare l).domain :=
  KFCausalClockFloorCoherentMatter.gaussianState_fieldSquare_domain ε a _ _ p.1
    (imaginarySource p.2) (-h/2) hε ha (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h) (KFCausalClockFloorShiftedOutput.shift_bound ε h hb) l

theorem spectralOutput_physicalField_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    spectralOutput ε a h hε ha hh hb p ∈ (physicalField l).domain :=
  fieldSquare_domain_le_physicalField l (spectralOutput_fieldSquare_domain ε a h hε ha hh hb p l)

theorem modulatedTrial_linearMatter_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    modulation (positionFrequency p.1 p.2) (trialState ε a h hε ha hh) ∈
      (matterFactor ε hε h (physicalField l)).domain :=
  (composition_domain _ _ _).mpr ⟨_,modulatedTrial_ordered_graph ε a h hε ha hh hb p,
    spectralOutput_physicalField_domain ε a h hε ha hh hb p l⟩

theorem modulatedTrial_quadraticMatter_domain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) :
    modulation (positionFrequency p.1 p.2) (trialState ε a h hε ha hh) ∈
      (matterFactor ε hε h (fieldSquare l)).domain :=
  (composition_domain _ _ _).mpr ⟨_,modulatedTrial_ordered_graph ε a h hε ha hh hb p,
    spectralOutput_fieldSquare_domain ε a h hε ha hh hb p l⟩

theorem modulatedTrial_commonEnergyDomain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    modulation (positionFrequency p.1 p.2) (trialState ε a h hε ha hh) ∈
      commonEnergyDomain ε hε h v l := by
  apply (commonEnergyDomain_iff ε hε h v l _).mpr
  intro i
  fin_cases i
  · exact LinearPMap.mem_domain_of_mem_graph (clockHalf_graph_modulation ε
      (positionFrequency p.1 p.2) _ _ ((clockHalf ε).mem_graph
        ⟨_,trialState_clockHalf_domain ε a h hε ha hh⟩))
  · exact (kinetic_domain_modulation ε hε h hh (v 0) _ _).mpr
      (trialState_clockMomentum_domain ε a h hε ha hh (v 0))
  · exact (kinetic_domain_modulation ε hε h hh (v 1) _ _).mpr
      (trialState_clockMomentum_domain ε a h hε ha hh (v 1))
  · exact (kinetic_domain_modulation ε hε h hh (v 2) _ _).mpr
      (trialState_clockMomentum_domain ε a h hε ha hh (v 2))
  · exact (kinetic_domain_modulation ε hε h hh (v 3) _ _).mpr
      (trialState_clockMomentum_domain ε a h hε ha hh (v 3))
  · exact modulatedTrial_linearMatter_domain ε a h hε ha hh hb p l
  · exact modulatedTrial_quadraticMatter_domain ε a h hε ha hh hb p l
  · exact LinearPMap.mem_domain_of_mem_graph (modulatedTrial_ordered_graph ε a h hε ha hh hb p)

theorem boostedState_commonEnergyDomain (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration)
    (v : Fin 4 → Transverse) (l : Transverse →L[ℝ] ℝ) :
    boostedState ε a h hε ha hh (positionFrequency p.1 p.2) ∈ commonEnergyDomain ε hε h v l := by
  have he := ((commonEnergyDomain ε hε h v l).restrictScalars ℝ).smul_mem
    (‖trialState ε a h hε ha hh‖⁻¹)
    (modulatedTrial_commonEnergyDomain ε a h hε ha hh hb (h⁻¹ • p) v l)
  rw [positionFrequency_smul] at he
  change (modulation (h⁻¹ • positionFrequency p.1 p.2) : Hilbert →L[ℂ] Hilbert)
    ((‖trialState ε a h hε ha hh‖⁻¹:ℝ) • trialState ε a h hε ha hh) ∈ _
  rw [ContinuousLinearMap.map_smul_of_tower]
  exact he

def formVector (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (m g κ t : ℝ) :
    KFCausalClosedGraphForm.FormSpace
      (formData ε hε h (by nlinarith [abs_nonneg h]) m g κ t) :=
  commonFormVector ε hε h (by nlinarith [abs_nonneg h]) m g κ t
    ⟨boostedState ε a h hε ha hh (positionFrequency p.1 p.2),
      boostedState_commonEnergyDomain ε a h hε ha hh hb p modelDirections pointField⟩

theorem formVector_embedding (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (m g κ t : ℝ) :
    KFCausalClosedGraphForm.embedding _ (formVector ε a h hε ha hh hb p m g κ t) =
      boostedState ε a h hε ha hh (positionFrequency p.1 p.2) := rfl

theorem formVector_embedding_norm (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (m g κ t : ℝ) :
    ‖KFCausalClosedGraphForm.embedding _ (formVector ε a h hε ha hh hb p m g κ t)‖ = 1 :=
  boostedState_norm ε a h hε ha hh (positionFrequency p.1 p.2)

theorem formVector_energy (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (m g κ t : ℝ)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) :
    ‖KFCausalClosedGraphForm.energyOutput _ (formVector ε a h hε ha hh hb p m g κ t)‖^2 =
      seedEnergy ε hε h modelDirections pointField m g κ t
        ⟨boostedState ε a h hε ha hh (positionFrequency p.1 p.2),
          boostedState_commonEnergyDomain ε a h hε ha hh hb p modelDirections pointField⟩ :=
  commonFormVector_energy ε hε h _ m g κ t hm hg hκ _

#print axioms spectralOutput_fieldSquare_domain
#print axioms spectralOutput_physicalField_domain
#print axioms modulatedTrial_linearMatter_domain
#print axioms modulatedTrial_quadraticMatter_domain
#print axioms modulatedTrial_commonEnergyDomain
#print axioms boostedState_commonEnergyDomain
#print axioms formVector_embedding
#print axioms formVector_embedding_norm
#print axioms formVector_energy

end
end UnifiedTheory.Audit.KFCausalClockFloorBoostedCommonDomain
