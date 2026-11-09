/- The actual eight-factor time-dependent closed forms are represented by
a differentiable bounded-operator curve on the fixed reference form space.
This curve is distinct from the unbounded Hamiltonian on physical L2. -/
import UnifiedTheory.Audit.KFCausalBoundedFormCurve
import UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
noncomputable section
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalFiniteJointGraph
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl

def staticMap (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] Output (Fin 8) Hilbert :=
  staticOutput.comp (energyOutput ε hε hbar hh mass2 quartic vacuum 0)

def growingMap (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] Output (Fin 8) Hilbert :=
  growingOutput.comp (energyOutput ε hε hbar hh mass2 quartic vacuum 0)

theorem staticMap_norm_le_one (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    ‖staticMap ε hε hbar hh mass2 quartic vacuum‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  exact (selected_norm_le (fun i : Fin 8 => i.val<3)
    (energyOutput ε hε hbar hh mass2 quartic vacuum 0 u)).trans
    (energyOutput_norm_le ε hε hbar hh mass2 quartic vacuum 0 u)

theorem growingMap_norm_le_one (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    ‖growingMap ε hε hbar hh mass2 quartic vacuum‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  exact (selected_norm_le (fun i : Fin 8 => ¬ i.val<3)
    (energyOutput ε hε hbar hh mass2 quartic vacuum 0 u)).trans
    (energyOutput_norm_le ε hε hbar hh mass2 quartic vacuum 0 u)

def referenceFormOperator (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  formOperator (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Output (Fin 8) Hilbert)
    (staticMap ε hε hbar hh mass2 quartic vacuum) (growingMap ε hε hbar hh mass2 quartic vacuum) t

def referenceFormDerivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ) :
    FormSpace ε hε hbar hh mass2 quartic vacuum 0 →L[ℂ] FormSpace ε hε hbar hh mass2 quartic vacuum 0 :=
  (2*Real.exp (2*t)) • gram (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Output (Fin 8) Hilbert)
    (growingMap ε hε hbar hh mass2 quartic vacuum)

theorem referenceForm_derivative (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ) :
    HasDerivAt (referenceFormOperator ε hε hbar hh mass2 quartic vacuum)
      (referenceFormDerivative ε hε hbar hh mass2 quartic vacuum t) t :=
  formOperator_derivative _ _ t

theorem referenceForm_derivative_continuous (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum : ℝ) :
    Continuous (referenceFormDerivative ε hε hbar hh mass2 quartic vacuum) :=
  formOperator_derivative_continuous _

theorem referenceForm_norm_le (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ) :
    ‖referenceFormOperator ε hε hbar hh mass2 quartic vacuum t‖ ≤ 1+Real.exp (2*t) :=
  formOperator_norm_le _ _ t (staticMap_norm_le_one ε hε hbar hh mass2 quartic vacuum)
    (growingMap_norm_le_one ε hε hbar hh mass2 quartic vacuum)

theorem referenceForm_derivative_norm_le (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ) :
    ‖referenceFormDerivative ε hε hbar hh mass2 quartic vacuum t‖ ≤ 2*Real.exp (2*t) :=
  formOperator_derivative_norm_le _ t (growingMap_norm_le_one ε hε hbar hh mass2 quartic vacuum)

theorem referenceForm_represents_closed_form (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum t : ℝ)
    (u v : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    inner ℂ u (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) =
    inner ℂ (energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t u))
      (energyOutput ε hε hbar hh mass2 quartic vacuum t (formTransfer ε hε hbar hh mass2 quartic vacuum 0 t v)) := by
  have hp : inner ℂ u (referenceFormOperator ε hε hbar hh mass2 quartic vacuum t v) =
      inner ℂ (staticMap ε hε hbar hh mass2 quartic vacuum u) (staticMap ε hε hbar hh mass2 quartic vacuum v) +
      (Real.exp (2*t) : ℂ) * inner ℂ (growingMap ε hε hbar hh mass2 quartic vacuum u)
        (growingMap ε hε hbar hh mass2 quartic vacuum v) := formOperator_pairing _ _ t u v
  rw [hp,transfer_energyOutput ε hε hbar hh mass2 quartic vacuum 0 t,
    transfer_energyOutput ε hε hbar hh mass2 quartic vacuum 0 t,timeOutput_inner]
  simp only [sub_zero]
  rfl

#print axioms staticMap_norm_le_one
#print axioms growingMap_norm_le_one
#print axioms referenceForm_derivative
#print axioms referenceForm_derivative_continuous
#print axioms referenceForm_norm_le
#print axioms referenceForm_derivative_norm_le
#print axioms referenceForm_represents_closed_form

end
end UnifiedTheory.Audit.KFCausalPhysicalFormRegularity
