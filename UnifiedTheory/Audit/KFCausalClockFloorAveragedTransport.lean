/- The actual averaged energy domain is independent of Hamiltonian time.
The proved bounded transports between completed unaveraged form spaces
lift to its circle-orbit form space and commute with zero projection. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
import UnifiedTheory.Audit.KFCausalAveragedFormTransport
import UnifiedTheory.Audit.KFCausalClockFloorFormTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedTransport
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (hne : hbar ≠ 0)
  (mass2 quartic vacuum : ℝ)

abbrev timeTransfer (s t : ℝ) := by
  let R := KFCausalAveragedFormTransport.transfer (H := Hilbert)
    (E := KFCausalClockFloorFormTransport.FormSpace ε hε hbar hh mass2 quartic vacuum s)
    (F := KFCausalClockFloorFormTransport.FormSpace ε hε hbar hh mass2 quartic vacuum t)
    (group hbar hne) (2*Real.pi)
    (KFCausalClockFloorFormTransport.embedding ε hε hbar hh mass2 quartic vacuum s)
    (KFCausalClockFloorFormTransport.embedding ε hε hbar hh mass2 quartic vacuum t)
  let M := KFCausalClockFloorFormTransport.formTransfer ε hε hbar hh mass2 quartic vacuum s t
  have hR := KFCausalClockFloorFormTransport.transfer_embedding ε hε hbar hh mass2 quartic vacuum s t
  exact R M hR

theorem transfer_embedding (s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    embedding ε hε hbar hh hne mass2 quartic vacuum t
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u) =
        embedding ε hε hbar hh hne mass2 quartic vacuum s u := by
  have h := KFCausalAveragedFormTransport.transfer_embedding (H := Hilbert)
    (E := KFCausalClockFloorFormTransport.FormSpace ε hε hbar hh mass2 quartic vacuum s)
    (F := KFCausalClockFloorFormTransport.FormSpace ε hε hbar hh mass2 quartic vacuum t)
    (group hbar hne) (2*Real.pi)
    (KFCausalClockFloorFormTransport.embedding ε hε hbar hh mass2 quartic vacuum s)
    (KFCausalClockFloorFormTransport.embedding ε hε hbar hh mass2 quartic vacuum t)
  let M := KFCausalClockFloorFormTransport.formTransfer ε hε hbar hh mass2 quartic vacuum s t
  have hM := KFCausalClockFloorFormTransport.transfer_embedding ε hε hbar hh mass2 quartic vacuum s t
  exact h M hM u

theorem transfer_section (s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    sectionMap ε hε hbar hh hne mass2 quartic vacuum t
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u) =
        (KFCausalClockFloorFormTransport.formTransfer ε hε hbar hh mass2 quartic vacuum s t).compLp
          (sectionMap ε hε hbar hh hne mass2 quartic vacuum s u) := rfl

theorem transfer_inverse (s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    timeTransfer ε hε hbar hh hne mass2 quartic vacuum t s
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u) = u := by
  have hi := embedding_injective ε hε hbar hh hne mass2 quartic vacuum s
  apply hi
  exact (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum t s _).trans
    (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t u)

theorem transfer_comp (r s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum r) :
    timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum r s u) =
        timeTransfer ε hε hbar hh hne mass2 quartic vacuum r t u := by
  have hi := embedding_injective ε hε hbar hh hne mass2 quartic vacuum t
  apply hi
  exact (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t _).trans
    ((transfer_embedding ε hε hbar hh hne mass2 quartic vacuum r s u).trans
      (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum r t u).symm)

def timeEquiv (s t : ℝ) : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s ≃L[ℂ]
    AveragedSpace ε hε hbar hh hne mass2 quartic vacuum t where
  toLinearEquiv := {
    toLinearMap := (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t).toLinearMap
    invFun := timeTransfer ε hε hbar hh hne mass2 quartic vacuum t s
    left_inv := transfer_inverse ε hε hbar hh hne mass2 quartic vacuum s t
    right_inv := transfer_inverse ε hε hbar hh hne mass2 quartic vacuum t s }
  continuous_toFun := (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t).continuous
  continuous_invFun := (timeTransfer ε hε hbar hh hne mass2 quartic vacuum t s).continuous

theorem energy_domain_time (s t : ℝ) (f : Hilbert) :
    f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum s).domain ↔
      f ∈ (energyOperator ε hε hbar hh hne mass2 quartic vacuum t).domain := by
  have hs := energy_domain ε hε hbar hh hne mass2 quartic vacuum s f
  have ht := energy_domain ε hε hbar hh hne mass2 quartic vacuum t f
  constructor
  · intro hf
    rcases hs.mp hf with ⟨u, hu⟩
    exact ht.mpr ⟨timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u,
      (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t u).trans hu⟩
  · intro hf
    rcases ht.mp hf with ⟨u, hu⟩
    exact hs.mpr ⟨timeTransfer ε hε hbar hh hne mass2 quartic vacuum t s u,
      (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum t s u).trans hu⟩

theorem projection_transport (s t : ℝ) (u : AveragedSpace ε hε hbar hh hne mass2 quartic vacuum s) :
    projectedForm ε hε hbar hh hne mass2 quartic vacuum t
      (timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t u) =
        timeTransfer ε hε hbar hh hne mass2 quartic vacuum s t
          (projectedForm ε hε hbar hh hne mass2 quartic vacuum s u) := by
  have hi := embedding_injective ε hε hbar hh hne mass2 quartic vacuum t
  apply hi
  have hp := congrArg (KFCausalStandingChargeOperator.zeroProjection hbar hne)
    (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t u)
  exact (projected_embedding ε hε hbar hh hne mass2 quartic vacuum t _).trans
    (hp.trans ((projected_embedding ε hε hbar hh hne mass2 quartic vacuum s u).symm.trans
      (transfer_embedding ε hε hbar hh hne mass2 quartic vacuum s t _).symm))

#print axioms transfer_embedding
#print axioms transfer_section
#print axioms transfer_inverse
#print axioms transfer_comp
#print axioms timeEquiv
#print axioms energy_domain_time
#print axioms projection_transport

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedTransport
