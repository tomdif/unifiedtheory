/- The new closed defect-invariant ordered subgraph contains the previously
verified nonzero, charge-zero, common-energy-domain physical trial. -/
import UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectClosure
import UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
import UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectTrial
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalClockFloorTrialUnitary
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectPowerGraph
open UnifiedTheory.Audit.KFCausalClockFloorDefectGraphClosure
open UnifiedTheory.Audit.KFCausalClockFloorBoundedInverse
open UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectClosure
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

variable (ε a hbar : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3)

theorem dampedState_eq_packet :
    dampedState ε a hbar hε ha hh =
      state ε a (groundWidth hbar) (neutralWidth hbar) 0 0 hε ha
        (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
        0 0 (by simp; positivity) := by
  apply (straightening ε hε).injective
  apply Lp.ext
  filter_upwards [inverse_damped_euclidean_coe ε a hbar hε ha hh,
    state_coe ε a (groundWidth hbar) (neutralWidth hbar) 0 0 hε ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
      0 0 (by simp; positivity)] with x hx hy
  change (straightening ε hε (dampedState ε a hbar hε ha hh)) x = _ at hx
  rw [hx,hy]
  simp [KFCausalClockFloorDefectPowerGraph.profile,spectralInput,KFCausalClockFloorCoherentFullFourier.euclideanLine,
    KFCausalClockFloorGaussianL1.euclideanLine,KFCausalClockFloorCoherentStrip.line,
    KFCausalClockFloorCoherentStrip.trial,KFCausalClockFloorCoherentStrip.clockPhase,
    KFCausalClockFloorCoherentBounds.coherentPacket,KFCausalClockFloorCoherentBounds.source,
    KFCausalClockFloorFullGaussian.line,KFCausalClockFloorFullGaussian.trial]

theorem trial_orderedGraph :
    ∃ g : Hilbert, (trialState ε a hbar hε ha hh,g) ∈
      orderedGraph ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
        (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) := by
  let i : PacketIndex := (0,0,0)
  refine ⟨(packetPair ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) i).2,?_⟩
  change (inverseL ε hε (trialState ε a hbar hε ha hh),_) ∈
    graphClosure ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
  rw [inverseL_eq]
  change (dampedState ε a hbar hε ha hh,_) ∈
    graphClosure ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
      (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar)
  rw [dampedState_eq_packet ε a hbar hε ha hh]
  exact packetPair_mem_closure ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) i

theorem exists_nonzero_charge_zero_common_orderedGraph :
    ∃ f g : Hilbert, f ≠ 0 ∧ f ∈ zeroSector hbar hh ∧
      f ∈ commonEnergyDomain ε hε hbar modelDirections pointField ∧
      (f,g) ∈ orderedGraph ε hε hbar hbound a (groundWidth hbar) (neutralWidth hbar) ha
        (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) (neutralWidth_bound hbar) := by
  obtain ⟨g,hg⟩ := trial_orderedGraph ε a hbar hε ha hh hbound
  exact ⟨trialState ε a hbar hε ha hh,g,trialState_ne_zero ε a hbar hε ha hh,
    trialState_mem_zeroSector ε a hbar hε ha hh,
    trialState_commonEnergyDomain ε a hbar hε ha hh hbound modelDirections pointField,hg⟩

#print axioms dampedState_eq_packet
#print axioms trial_orderedGraph
#print axioms exists_nonzero_charge_zero_common_orderedGraph

end
end UnifiedTheory.Audit.KFCausalClockFloorOrderedDefectTrial
