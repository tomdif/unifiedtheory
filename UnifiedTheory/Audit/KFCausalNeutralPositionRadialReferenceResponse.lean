/- The full radial commutator in the fixed reference form used by the
actual evolution. Its rate is controlled by the actual time-dependent
energy, with no hbar-dependent constant at fixed positive cutoffs. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse
import UnifiedTheory.Audit.KFCausalNeutralReferencePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialReferenceResponse
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy timeEnergy_actual)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm (formAction formAction_transfer)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse (response kineticConstant completed_form_diagonal_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient coefficient_norm)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0) (m g k : ℝ)
local notation "V₀" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "T" => formTransfer ε hε h hne hh m g k
local notation "A" => energyOutput ε hε h hne hh m g k
local notation "Q" => referenceFormOperator ε hε h hne hh m g k
local notation "F" => formAction ε hε h δ v hδ hh hne m g k
local notation "G" => formAction ε hε h δ (-v) hδ hh hne m g k

theorem reference_pairing (t : ℝ) (u w : V₀) :
    inner ℂ u (Q t (F 0 w)) = inner ℂ (A t (T 0 t u)) (A t (F t (T 0 t w))) :=
  (referenceForm_represents_closed_form ε hε h hne hh m g k t u (F 0 w)).trans
    (congrArg (fun z => inner ℂ (A t (T 0 t u)) (A t z))
      (formAction_transfer ε hε h δ v hδ hh hne m g k 0 t w))

def rate (t : ℝ) (u : V₀) : ℂ :=
  coefficient h*(inner ℂ u (Q t (F 0 u))-conj (inner ℂ u (Q t (G 0 u))))

theorem rate_response (t : ℝ) (u : V₀) :
    rate ε hε h δ v hδ hh hne m g k t u =
      coefficient h*response ε hε h δ v hδ hh hne m g k t (T 0 t u) (T 0 t u) := by
  unfold rate
  simp only [reference_pairing,inner_conj_symm]
  rfl

theorem rate_bound (hs : |h| ≤ Real.pi*ε/3) (t : ℝ) (u : V₀) :
    ‖rate ε hε h δ v hδ hh hne m g k t u‖ ≤
      responseConstant ε δ v*timeEnergy ε hε h hne hh m g k t u+
        2*kineticConstant ε δ v*‖J u‖*Real.sqrt (timeEnergy ε hε h hne hh m g k t u) := by
  have he : ‖A t (T 0 t u)‖ = Real.sqrt (timeEnergy ε hε h hne hh m g k t u) := by
    exact (Real.sqrt_sq (norm_nonneg (A t (T 0 t u)))).symm.trans
      (congrArg Real.sqrt (timeEnergy_actual ε hε h hne hh m g k t u))
  have hn (z : ℂ) : ‖coefficient h*z‖ = ‖z‖/|h| := by
    rw [norm_mul,coefficient_norm]
    ring
  calc
    _ = ‖response ε hε h δ v hδ hh hne m g k t (T 0 t u) (T 0 t u)‖/|h| :=
      (congrArg norm (rate_response ε hε h δ v hδ hh hne m g k t u)).trans (hn _)
    _ ≤ responseConstant ε δ v*‖A t (T 0 t u)‖^2+
        2*kineticConstant ε δ v*‖embedding ε hε h hne hh m g k t (T 0 t u)‖*‖A t (T 0 t u)‖ :=
      completed_form_diagonal_bound ε hε h δ v hδ hh hne m g k t hs (T 0 t u)
    _ = responseConstant ε δ v*timeEnergy ε hε h hne hh m g k t u+
        2*kineticConstant ε δ v*‖J u‖*‖A t (T 0 t u)‖ :=
      congrArg₂ (fun a b : ℝ => responseConstant ε δ v*a+2*kineticConstant ε δ v*b*‖A t (T 0 t u)‖)
        (timeEnergy_actual ε hε h hne hh m g k t u)
        (congrArg norm (transfer_embedding ε hε h hne hh m g k 0 t u))
    _ = _ := congrArg (fun a : ℝ => responseConstant ε δ v*timeEnergy ε hε h hne hh m g k t u+
        2*kineticConstant ε δ v*‖J u‖*a) he

#print axioms reference_pairing
#print axioms rate_response
#print axioms rate_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialReferenceResponse
