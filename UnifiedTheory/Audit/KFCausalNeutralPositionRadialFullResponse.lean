/- Full hbar-normalized radial response of the existing averaged
Hamiltonian form. All eight rows contribute, and both observable
actions are the already constructed actions on the completed form.
The positive radial and clock cutoffs are kept fixed. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound (outputAction)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm (OutputSpace transformed correction correction_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing (reflectedOutput outputLp_dual outputLp_difference)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing (responseConstant)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialKineticGraph (responseConstant_nonneg)

abbrev kineticConstant := KFCausalNeutralPositionRadialKineticGraph.responseConstant

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3) (hne : h ≠ 0)

def commutator (f g : Hilbert) (x y : OutputSpace) : ℂ :=
  inner ℂ x (transformed ε hε h δ v hδ hh hne g y)-
    inner ℂ (transformed ε hε h δ (-v) hδ hh hne f x) y

theorem commutator_identity (f g : Hilbert) (x y : OutputSpace) :
    commutator ε hε h δ v hδ hh hne f g x y =
      inner ℂ x ((outputAction ε hε h δ v hδ hh).compLp y-
        (reflectedOutput ε hε h δ v hδ hh).compLp y)+
      (inner ℂ x (correction ε hε h δ v hδ hne g)-
        inner ℂ (correction ε hε h δ (-v) hδ hne f) y) := by
  rw [inner_sub_right,outputLp_dual]
  simp only [commutator,transformed,inner_add_right,inner_add_left]
  ring

theorem commutator_bound (hs : |h| ≤ Real.pi*ε/3) (f g : Hilbert) (x y : OutputSpace) :
    ‖commutator ε hε h δ v hδ hh hne f g x y‖ ≤
      |h| *(responseConstant ε δ v*‖x‖*‖y‖+
        kineticConstant ε δ v*(‖x‖*‖g‖+‖f‖*‖y‖)) := by
  have hm : ‖correction ε hε h δ (-v) hδ hne f‖ ≤ |h| *kineticConstant ε δ v*‖f‖ := by
    simpa only [kineticConstant,KFCausalNeutralPositionRadialKineticGraph.responseConstant,abs_neg] using
      correction_bound ε hε h δ (-v) hδ hne f
  rw [commutator_identity]
  calc
    _ ≤ ‖inner ℂ x ((outputAction ε hε h δ v hδ hh).compLp y-
          (reflectedOutput ε hε h δ v hδ hh).compLp y)‖+
        ‖inner ℂ x (correction ε hε h δ v hδ hne g)-
          inner ℂ (correction ε hε h δ (-v) hδ hne f) y‖ := norm_add_le _ _
    _ ≤ ‖x‖*‖(outputAction ε hε h δ v hδ hh).compLp y-
          (reflectedOutput ε hε h δ v hδ hh).compLp y‖+
        (‖x‖*‖correction ε hε h δ v hδ hne g‖+
          ‖correction ε hε h δ (-v) hδ hne f‖*‖y‖) :=
      add_le_add (norm_inner_le_norm _ _)
        ((norm_sub_le _ _).trans (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)))
    _ ≤ ‖x‖*((|h| *responseConstant ε δ v)*‖y‖)+
        (‖x‖*(|h| *kineticConstant ε δ v*‖g‖)+(|h| *kineticConstant ε δ v*‖f‖)*‖y‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (outputLp_difference ε hε h δ v hδ hh hs y) (norm_nonneg _))
        (add_le_add
          (mul_le_mul_of_nonneg_left (correction_bound ε hε h δ v hδ hne g) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right hm (norm_nonneg _)))
    _ = _ := by ring

theorem normalized_commutator_bound (hs : |h| ≤ Real.pi*ε/3)
    (f g : Hilbert) (x y : OutputSpace) :
    ‖commutator ε hε h δ v hδ hh hne f g x y‖/|h| ≤
      responseConstant ε δ v*‖x‖*‖y‖+kineticConstant ε δ v*(‖x‖*‖g‖+‖f‖*‖y‖) := by
  apply (div_le_iff₀ (abs_pos.mpr hne)).mpr
  exact (commutator_bound ε hε h δ v hδ hh hne hs f g x y).trans_eq (by ring)

open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCompletedForm (formAction formAction_output)
variable (m g k t : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k t
local notation "J" => embedding ε hε h hne hh m g k t
local notation "A" => energyOutput ε hε h hne hh m g k t
local notation "F" => formAction ε hε h δ v hδ hh hne m g k t
local notation "G" => formAction ε hε h δ (-v) hδ hh hne m g k t

def response (u w : V) : ℂ := inner ℂ (A u) (A (F w))-inner ℂ (A (G u)) (A w)

theorem response_eq_commutator (u w : V) :
    response ε hε h δ v hδ hh hne m g k t u w =
      commutator ε hε h δ v hδ hh hne (J u) (J w) (A u) (A w) := by
  exact congrArg₂ (fun a b : OutputSpace => inner ℂ (A u) a-inner ℂ b (A w))
    (formAction_output ε hε h δ v hδ hh hne m g k t w)
    (formAction_output ε hε h δ (-v) hδ hh hne m g k t u)

theorem completed_form_normalized_bound (hs : |h| ≤ Real.pi*ε/3) (u w : V) :
    ‖response ε hε h δ v hδ hh hne m g k t u w‖/|h| ≤
      responseConstant ε δ v*‖A u‖*‖A w‖+
        kineticConstant ε δ v*(‖A u‖*‖J w‖+‖J u‖*‖A w‖) := by
  exact (congrArg (fun z : ℂ => ‖z‖/|h|)
    (response_eq_commutator ε hε h δ v hδ hh hne m g k t u w)).le.trans
      (normalized_commutator_bound ε hε h δ v hδ hh hne hs (J u) (J w) (A u) (A w))

theorem completed_form_diagonal_bound (hs : |h| ≤ Real.pi*ε/3) (u : V) :
    ‖response ε hε h δ v hδ hh hne m g k t u u‖/|h| ≤
      responseConstant ε δ v*‖A u‖^2+2*kineticConstant ε δ v*‖J u‖*‖A u‖ :=
  (completed_form_normalized_bound ε hε h δ v hδ hh hne m g k t hs u u).trans_eq (by ring)

#print axioms commutator_identity
#print axioms commutator_bound
#print axioms normalized_commutator_bound
#print axioms response_eq_commutator
#print axioms completed_form_normalized_bound
#print axioms completed_form_diagonal_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialFullResponse
