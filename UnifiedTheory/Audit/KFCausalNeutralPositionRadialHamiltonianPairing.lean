/- The full radial form response equals the weak commutator of the
existing Hamiltonian on its operator domain. No claim that the radial
observable preserves that stronger operator domain is required. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialHamiltonianPairing
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedHamiltonian (hamiltonian formData)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport (energyOutput embedding)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm (formAction formAction_embedding)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant)
open UnifiedTheory.Audit.KFCausalClosedGraphForm (formLift embedding_formLift hamiltonian_represents_form)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k t : ℝ)
local notation "D" => formData ε hε h hne hh m g k t
local notation "H" => hamiltonian ε hε h hne hh m g k t
local notation "A" => energyOutput ε hε h hne hh m g k t
local notation "J" => embedding ε hε h hne hh m g k t

theorem response_pairing (x y : (H).domain) :
    response ε hε h δ v hδ hh hne m g k t (formLift D x) (formLift D y) =
      inner ℂ (H x) (action h δ v hδ (y:Hilbert))-
        inner ℂ (action h δ (-v) hδ (x:Hilbert)) (H y) := by
  have hx := hamiltonian_represents_form D x
    (formAction ε hε h δ v hδ hh hne m g k t (formLift D y))
  have hy := congrArg (starRingEnd ℂ) (hamiltonian_represents_form D y
    (formAction ε hε h δ (-v) hδ hh hne m g k t (formLift D x)))
  simp only [inner_conj_symm] at hy
  change inner ℂ (A (formLift D x)) (A (formAction ε hε h δ v hδ hh hne m g k t (formLift D y))) =
    inner ℂ (H x) (J (formAction ε hε h δ v hδ hh hne m g k t (formLift D y))) at hx
  change inner ℂ (A (formAction ε hε h δ (-v) hδ hh hne m g k t (formLift D x))) (A (formLift D y)) =
    inner ℂ (J (formAction ε hε h δ (-v) hδ hh hne m g k t (formLift D x))) (H y) at hy
  have ex : J (formAction ε hε h δ v hδ hh hne m g k t (formLift D y)) =
      action h δ v hδ (y:Hilbert) :=
    (formAction_embedding ε hε h δ v hδ hh hne m g k t (formLift D y)).trans
      (congrArg (action h δ v hδ) (embedding_formLift D y))
  have ey : J (formAction ε hε h δ (-v) hδ hh hne m g k t (formLift D x)) =
      action h δ (-v) hδ (x:Hilbert) :=
    (formAction_embedding ε hε h δ (-v) hδ hh hne m g k t (formLift D x)).trans
      (congrArg (action h δ (-v) hδ) (embedding_formLift D x))
  exact congrArg₂ (fun a b : ℂ => a-b)
    (hx.trans (congrArg (fun z => inner ℂ (H x) z) ex))
    (hy.trans (congrArg (fun z => inner ℂ z (H y)) ey))

theorem hamiltonian_normalized_bound (hs : |h| ≤ Real.pi*ε/3) (x y : (H).domain) :
    ‖inner ℂ (H x) (action h δ v hδ (y:Hilbert))-
      inner ℂ (action h δ (-v) hδ (x:Hilbert)) (H y)‖/|h| ≤
        responseConstant ε δ v*‖A (formLift D x)‖*‖A (formLift D y)‖+
        kineticConstant ε δ v*(‖A (formLift D x)‖*‖(y:Hilbert)‖+
          ‖(x:Hilbert)‖*‖A (formLift D y)‖) := by
  have hb := completed_form_normalized_bound ε hε h δ v hδ hh hne m g k t hs (formLift D x) (formLift D y)
  have hc := (congrArg (fun z : ℂ => ‖z‖/|h|)
    (response_pairing ε hε h δ v hδ hh hne m g k t x y)).symm.le.trans hb
  simpa only [embedding,embedding_formLift] using hc

#print axioms response_pairing
#print axioms hamiltonian_normalized_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialHamiltonianPairing
