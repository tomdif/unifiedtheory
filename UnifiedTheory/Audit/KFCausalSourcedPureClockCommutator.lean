/- Actual joint regularity and pure-clock commutator for arbitrary sourced
Gaussian states. All input/output momentum domains are derived from the
existing Gaussian estimates, including the closed strip endpoints. -/
import UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral
import UnifiedTheory.Audit.KFCausalCoherentLongitudinalDomain
import UnifiedTheory.Audit.KFCausalShiftedGaussianLongitudinalDomain
import UnifiedTheory.Audit.KFCausalShiftedGaussianShearDomain
import UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalSourcedPureClockCommutator
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedClockMomentum (state)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput state_ordered_graph)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalClockFloorJointMomentumCore (regularGraph)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (pureCorrection)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (clockFunction clockFunction_memLp)

variable (ε a α β : ℝ) (hε : 0 < ε) (ha : 0 < a) (hα : 0 < α) (hβ : 0 < β)
  (hw : 32*β ≤ α) (C : ℂ) (p : ℝ) (b : Fin 5 → ℂ)
  (h : ℝ) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
include hh
local notation "S" => state ε a α β hε ha hα hβ hw C p b
local notation "G" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb

theorem state_longitudinal_domain : S ∈ (longitudinalMomentum ε hε h).domain :=
  KFCausalCoherentLongitudinalDomain.profile_domain ε a h hε ha hh C p α β hα hβ hw b

theorem state_shear_domain : S ∈ (shearMomentum h).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (KFCausalCoherentShearDifferential.physicalProfile_graph h hh C p α β hα hβ hw b
      (clockFunction ε a) (clockFunction_memLp ε a hε ha))

theorem shifted_longitudinal_domain : G ∈ (longitudinalMomentum ε hε h).domain := by
  apply (longitudinalMomentum ε hε h).domain.smul_mem
  exact KFCausalShiftedGaussianLongitudinalDomain.gaussianState_domain
    ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h hh

theorem shifted_shear_domain : G ∈ (shearMomentum h).domain := by
  apply (shearMomentum h).domain.smul_mem
  exact KFCausalShiftedGaussianShearDomain.gaussianState_shear_domain
    ε a α β p (-h/2) b hε ha hα hβ hw (shift_bound ε h hb) h hh

theorem state_regular_graph : (S,G) ∈ regularGraph ε hε h :=
  ⟨⟨state_ordered_graph ε a α β hε ha hα hβ hw C p b h hb,
    state_longitudinal_domain ε a α β hε ha hα hβ hw C p b h hh,
    shifted_longitudinal_domain ε a α β hε ha hα hβ hw C p b h hh hb⟩,
    state_shear_domain ε a α β hε ha hα hβ hw C p b h hh,
    shifted_shear_domain ε a α β hε ha hα hβ hw C p b h hh hb⟩

theorem pure_domains : S ∈ (pureMomentum ε hε h).domain ∧ G ∈ (pureMomentum ε hε h).domain :=
  KFCausalClockFloorPureClockVacuumCommutator.core_pure_domains ε hε h hh S G
    (state_regular_graph ε a α β hε ha hα hβ hw C p b h hh hb)

theorem actual_compositions :
    ∃ bf tbf bg jg : Hilbert,
      (S,bf) ∈ (pureMomentum ε hε h).graph ∧ (bf,tbf) ∈ (orderedExponential ε hε h).graph ∧
      (G,bg) ∈ (pureMomentum ε hε h).graph ∧ (G,jg) ∈ (shearMomentum h).graph ∧
      bg-tbf = pureCorrection ε hε h hb G jg :=
  KFCausalClockFloorPureClockVacuumCommutator.core_compositions ε hε h hb hh S G
    (state_regular_graph ε a α β hε ha hα hβ hw C p b h hh hb)

theorem actual_vacuum_response :
    ∃ bf tbf jg : Hilbert,
      (S,bf) ∈ (pureMomentum ε hε h).graph ∧ (bf,tbf) ∈ (orderedExponential ε hε h).graph ∧
      (G,jg) ∈ (shearMomentum h).graph ∧
      (-2/h)*(inner ℂ G tbf).im = response ε hε h hb G jg :=
  KFCausalClockFloorPureClockVacuumResponse.core_response ε hε h hb hh S G
    (state_regular_graph ε a α β hε ha hα hβ hw C p b h hh hb)

#print axioms state_longitudinal_domain
#print axioms state_shear_domain
#print axioms shifted_longitudinal_domain
#print axioms shifted_shear_domain
#print axioms state_regular_graph
#print axioms pure_domains
#print axioms actual_compositions
#print axioms actual_vacuum_response
end
end UnifiedTheory.Audit.KFCausalSourcedPureClockCommutator
