/- The actual zero-charge projection reduces the fixed-time averaged
Hamiltonian: it preserves its operator domain and commutes with its value.
Thus the zero-charge constraint is compatible with the unbounded generator.
A time-dependent evolution theorem still requires its own construction. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
import UnifiedTheory.Audit.KFCausalAveragedProjectionPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorHamiltonianProjection
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalPhysicalCircleAction (group action_full_period)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)

local notation "hb" => hamiltonian_bound ε hbar hbound
local notation "𝒟" => formData ε hε hbar hh hbound mass2 quartic vacuum t
local notation "H" => hamiltonian ε hε hbar hh hbound mass2 quartic vacuum t
local notation "P" => zeroProjection hbar hh

theorem projected_energy_pairing (u v : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t) :
    inner ℂ (energyOutput ε hε hbar hb hh mass2 quartic vacuum t
      (projectedForm ε hε hbar hb hh mass2 quartic vacuum t u))
      (energyOutput ε hε hbar hb hh mass2 quartic vacuum t v) =
        inner ℂ (energyOutput ε hε hbar hb hh mass2 quartic vacuum t u)
          (energyOutput ε hε hbar hb hh mass2 quartic vacuum t
            (projectedForm ε hε hbar hb hh mass2 quartic vacuum t v)) :=
  KFCausalAveragedProjectionPairing.project_energy_pairing (group hbar hh) (2*Real.pi)
    (by positivity) (action_full_period hbar hh) _ _ u v

theorem zeroProjection_hamiltonian_graph (x : (H).domain) :
    (P (x:Hilbert),P (H x)) ∈ (H).graph := by
  have hs := graphFormVector_surjective ε hε hbar hh hbound mass2 quartic vacuum t
    (KFCausalClosedGraphForm.formLift 𝒟 x)
  rcases hs with ⟨u,hu⟩
  have he : embedding ε hε hbar hb hh mass2 quartic vacuum t u = (x:Hilbert) := by
    exact (congrArg (KFCausalClosedGraphForm.embedding 𝒟) hu).trans
      (KFCausalClosedGraphForm.embedding_formLift 𝒟 x)
  have hp : ∀ v : AveragedSpace ε hε hbar hb hh mass2 quartic vacuum t,
      inner ℂ (energyOutput ε hε hbar hb hh mass2 quartic vacuum t
        (projectedForm ε hε hbar hb hh mass2 quartic vacuum t u))
        (energyOutput ε hε hbar hb hh mass2 quartic vacuum t v) =
          inner ℂ (P (H x)) (embedding ε hε hbar hb hh mass2 quartic vacuum t v) := by
    intro v
    have hv := hamiltonian_represents_averaged_form ε hε hbar hh hbound mass2 quartic vacuum t x
      (projectedForm ε hε hbar hb hh mass2 quartic vacuum t v)
    have hpair := congrArg (fun z : KFCausalClosedGraphForm.FormSpace 𝒟 =>
      inner ℂ (KFCausalClosedGraphForm.energyOutput 𝒟 z)
        (energyOutput ε hε hbar hb hh mass2 quartic vacuum t
          (projectedForm ε hε hbar hb hh mass2 quartic vacuum t v))) hu
    have hPv := congrArg (inner ℂ (H x)) (projected_embedding ε hε hbar hb hh mass2 quartic vacuum t v)
    refine (projected_energy_pairing ε hε hbar hh hbound mass2 quartic vacuum t u v).trans
      (hpair.trans (hv.trans (hPv.trans ?_)))
    exact ((ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (zeroProjection_selfAdjoint hbar hh))
      (H x) (embedding ε hε hbar hb hh mass2 quartic vacuum t v)).symm
  have hs := (hamiltonian_domain_characterization ε hε hbar hh hbound mass2 quartic vacuum t
    (projectedForm ε hε hbar hb hh mass2 quartic vacuum t u) (P (H x))).mpr hp
  rcases hs with ⟨hx,hval⟩
  exact ((H).mem_graph_iff').mpr ⟨⟨_,hx⟩,Prod.ext
    ((projected_embedding ε hε hbar hb hh mass2 quartic vacuum t u).trans (congrArg (P) he)) hval⟩

theorem zeroProjection_mem_hamiltonian_domain (x : (H).domain) :
    P (x:Hilbert) ∈ (H).domain :=
  LinearPMap.mem_domain_iff.mpr ⟨_,zeroProjection_hamiltonian_graph ε hε hbar hh hbound mass2 quartic vacuum t x⟩

theorem hamiltonian_zeroProjection (x : (H).domain) :
    H ⟨P (x:Hilbert),zeroProjection_mem_hamiltonian_domain ε hε hbar hh hbound mass2 quartic vacuum t x⟩ =
      P (H x) :=
  (H).mem_graph_snd_inj' ((H).mem_graph _)
    (zeroProjection_hamiltonian_graph ε hε hbar hh hbound mass2 quartic vacuum t x) rfl

theorem hamiltonian_zero_sector (x : (H).domain) (hx : (x:Hilbert) ∈ zeroSector hbar hh) :
    H x ∈ zeroSector hbar hh := by
  have hg := zeroProjection_hamiltonian_graph ε hε hbar hh hbound mass2 quartic vacuum t x
  have he : P (H x) = H x := (H).mem_graph_snd_inj' hg ((H).mem_graph x)
    (zeroProjection_fixes hbar hh _ hx)
  exact (congrArg (fun f : Hilbert => f ∈ zeroSector hbar hh) he).mp (zeroProjection_mem hbar hh _)

theorem hamiltonian_charge_zero (x : (H).domain) (hx : (x:Hilbert) ∈ zeroSector hbar hh) :
    (H x,0) ∈ (standingCharge hbar hh).graph :=
  (standingCharge_zero_iff hbar hh _).mpr
    (hamiltonian_zero_sector ε hε hbar hh hbound mass2 quartic vacuum t x hx)

#print axioms projected_energy_pairing
#print axioms zeroProjection_hamiltonian_graph
#print axioms zeroProjection_mem_hamiltonian_domain
#print axioms hamiltonian_zeroProjection
#print axioms hamiltonian_zero_sector
#print axioms hamiltonian_charge_zero

end
end UnifiedTheory.Audit.KFCausalClockFloorHamiltonianProjection
