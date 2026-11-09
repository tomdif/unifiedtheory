/- The entire finite neutral exponential-polynomial state family and
its pure-clock momentum are in the actual zero-charge sector. -/
import UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralFiniteCharge
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState
open UnifiedTheory.Audit.KFCausalUnboundedNeutralCharge (relation relation_projection)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)

theorem packet_relation (b C : ℂ) (P : Polynomial ℂ) :
    relation (fun x : ℝ => exponentialProfile b C P (x:ℂ))
      (trialState ε a h hε ha hh)
      (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P) := by
  filter_upwards [KFCausalPolynomialGaussianDomain.input_coe ε a h hε ha hh C 0 (neutralSource b) 4 P,
    trialState_coe ε a h hε ha hh] with x hi ht
  rw [hi,ht]
  simp [exponentialProfile,KFCausalClockFloorCoherentDerivative.physicalProfile,
    KFCausalClockFloorCoherentDerivative.clockMultiplier,KFCausalClockFloorCoherentStrip.clockPhase,
    KFCausalClockFloorCoherentMoments.sourcedPacket,KFCausalClockFloorCoherentSources.linearSource,
    neutralSource,Fin.sum_univ_succ,KFCausalChargeGaussianIdentities.configurationProfile]
  ring

theorem packet_projection (b C : ℂ) (P : Polynomial ℂ) :
    zeroProjection h hh
      (KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P) =
      KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P := by
  have hc : Continuous (fun x : ℝ => exponentialProfile b C P (x:ℂ)) := by
    unfold exponentialProfile
    fun_prop
  have hr := packet_relation ε a h hε ha hh b C P
  have hp := relation_projection _ hc.measurable h hh _ _ hr
  rw [zeroProjection_fixes h hh _ (trialState_mem_zeroSector ε a h hε ha hh)] at hp
  exact Lp.ext (hp.trans hr.symm)

theorem packet_mem_zeroSector (b C : ℂ) (P : Polynomial ℂ) :
    KFCausalPolynomialGaussianDomain.input ε a h hε ha hh C 0 (neutralSource b) 4 P ∈
      zeroSector h hh := by
  rw [← packet_projection ε a h hε ha hh b C P]
  exact zeroProjection_mem h hh _

theorem state_mem_zeroSector (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    state ε a h hε ha hh N b C P ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem fun i _ => packet_mem_zeroSector ε a h hε ha hh (b i) (C i) (P i)

theorem momentum_mem_zeroSector (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    momentum ε a h hε ha hh N b C P ∈ zeroSector h hh :=
  KFCausalPureClockZeroProjection.output_zeroSector ε hε h hh _ _
    (KFCausalNeutralFinitePhysicalState.momentum_graph ε a h hε ha hh N b C P)
    (state_mem_zeroSector ε a h hε ha hh N b C P)

theorem state_projection (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    zeroProjection h hh (state ε a h hε ha hh N b C P) = state ε a h hε ha hh N b C P :=
  zeroProjection_fixes h hh _ (state_mem_zeroSector ε a h hε ha hh N b C P)

theorem state_charge_zero (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    (state ε a h hε ha hh N b C P,0) ∈ (standingCharge h hh).graph :=
  (standingCharge_zero_iff h hh _).mpr (state_mem_zeroSector ε a h hε ha hh N b C P)

#print axioms packet_relation
#print axioms packet_projection
#print axioms packet_mem_zeroSector
#print axioms state_mem_zeroSector
#print axioms momentum_mem_zeroSector
#print axioms state_projection
#print axioms state_charge_zero
end
end UnifiedTheory.Audit.KFCausalNeutralFiniteCharge
