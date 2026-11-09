/- Identify the centered initial state in the restricted neutral packet
class and transport the two explicit completed-form lifts without
changing their physical states. This connects the exact Hamiltonian
pairing to the reference-space weak evolution equation. -/
import UnifiedTheory.Audit.KFCausalChargedPairHamiltonianCoupling
import UnifiedTheory.Audit.KFCausalClockFloorTransitionDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedPairTransitionInitial
noncomputable section
open MeasureTheory
open KFCausalChargedPairHamiltonianForm
open KFCausalChargedPairPotentialCoupling (baseState)
open KFCausalChargedPairDomain (state)
open KFCausalChargedPairCharge (state_neutralClosure_orthogonal)
open KFCausalNeutralSwapConstraint (neutralStates)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalClockFloorAveragedFormTransport
open KFCausalClockFloorAveragedRegularity
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
local notation "ψ₀" => baseState ε a h hε ha hh
local notation "ψ" => state ε a h hε ha hh

theorem baseState_mem_neutralStates : ψ₀ ∈ neutralStates ε h hε hh := by
  refine ⟨1,(fun _ => a),(fun _ => 0),(fun _ => ha),
    (fun _ => 0),(fun _ => 1),(fun _ => 1),?_⟩
  unfold KFCausalNeutralMixedClockState.state
  rw [Fin.sum_univ_one]
  apply Lp.ext
  have hn : neutralSource 0 = 0 := by
    funext i
    fin_cases i <;> rfl
  filter_upwards [KFCausalClockFloorSourcedClockMomentum.state_coe
    ε a (groundWidth h) (neutralWidth h) hε ha
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (neutralWidth_bound h) 1 0 0,
    KFCausalPolynomialGaussianDomain.input_coe ε a h hε ha hh 1 0 (neutralSource 0) 4 1]
    with x hx hy
  change ψ₀ x = _ at hx
  rw [hx,hy,hn]
  simp only [Polynomial.eval_one,one_mul]

theorem baseState_mem_neutralClosure : ψ₀ ∈ closure (neutralStates ε h hε hh) :=
  subset_closure (baseState_mem_neutralStates ε a h hε ha hh)

theorem base_pairing_zero : inner ℂ ψ₀ ψ = 0 :=
  state_neutralClosure_orthogonal ε a h hε ha hh ψ₀
    (baseState_mem_neutralClosure ε a h hε ha hh)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

theorem baseLift_transfer (mass2 quartic vacuum s t : ℝ) :
    formTransfer ε hε h hh hb mass2 quartic vacuum s t
      (baseLift ε a h hε ha hh hb mass2 quartic vacuum s) =
      baseLift ε a h hε ha hh hb mass2 quartic vacuum t := by
  apply embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [transfer_embedding,baseLift_embedding,baseLift_embedding]

theorem pairedLift_transfer (mass2 quartic vacuum s t : ℝ) :
    formTransfer ε hε h hh hb mass2 quartic vacuum s t
      (pairedLift ε a h hε ha hh hb mass2 quartic vacuum s) =
      pairedLift ε a h hε ha hh hb mass2 quartic vacuum t := by
  apply embedding_injective ε hε h hh hb mass2 quartic vacuum t
  rw [transfer_embedding,pairedLift_embedding,pairedLift_embedding]

theorem reference_pairing (s : ℝ) :
    inner ℂ (baseLift ε a h hε ha hh hb 1 1 1 0)
      (referenceFormOperator ε hε h hh hb 1 1 1 s
        (pairedLift ε a h hε ha hh hb 1 1 1 0)) =
      formPairing ε a h hε ha hh hb 1 1 1 s := by
  rw [referenceForm_represents_closed_form,baseLift_transfer,pairedLift_transfer]
  rfl

#print axioms baseState_mem_neutralStates
#print axioms baseState_mem_neutralClosure
#print axioms base_pairing_zero
#print axioms baseLift_transfer
#print axioms pairedLift_transfer
#print axioms reference_pairing
end
end UnifiedTheory.Audit.KFCausalChargedPairTransitionInitial
