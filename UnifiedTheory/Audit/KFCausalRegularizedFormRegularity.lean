/- The actual homogeneous time-dependent closed forms are represented by
a differentiable bounded-operator curve on the fixed reference form space.
This curve is distinct from the unbounded Hamiltonian on physical L2. -/
import UnifiedTheory.Audit.KFCausalBoundedFormCurve
import UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
noncomputable section
open UnifiedTheory.Audit.KFCausalBoundedFormCurve
open UnifiedTheory.Audit.KFCausalRegularizedMomentumClosure
open UnifiedTheory.Audit.KFCausalRegularizedClosedForm
open UnifiedTheory.Audit.KFCausalRegularizedFormEmbedding
open UnifiedTheory.Audit.KFCausalRegularizedFormTransport
open UnifiedTheory.Audit.KFCausalRegularizedFormTimeControl

def clockMap (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] Hilbert :=
  (WithLp.fstL 2 ℂ Hilbert Hilbert).comp (energyOutput ε hε hbar coupling 0)

def momentumMap (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] Hilbert :=
  (WithLp.sndL 2 ℂ Hilbert Hilbert).comp (energyOutput ε hε hbar coupling 0)

theorem clockMap_norm_le_one (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    ‖clockMap ε hε hbar coupling‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  exact (WithLp.norm_fst_le Hilbert (energyOutput ε hε hbar coupling 0 u)).trans
    (WithLp.norm_snd_le Hilbert u.val)

theorem momentumMap_norm_le_one (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    ‖momentumMap ε hε hbar coupling‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro u
  rw [one_mul]
  exact (WithLp.norm_snd_le Hilbert (energyOutput ε hε hbar coupling 0 u)).trans
    (WithLp.norm_snd_le Hilbert u.val)

def referenceFormOperator (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  formOperator (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (clockMap ε hε hbar coupling) (momentumMap ε hε hbar coupling) t

def referenceFormDerivative (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    FormSpace ε hε hbar coupling 0 →L[ℂ] FormSpace ε hε hbar coupling 0 :=
  (2*Real.exp (2*t)) • gram (E := FormSpace ε hε hbar coupling 0) (H := Hilbert)
    (momentumMap ε hε hbar coupling)

theorem referenceForm_derivative (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    HasDerivAt (referenceFormOperator ε hε hbar coupling)
      (referenceFormDerivative ε hε hbar coupling t) t :=
  formOperator_derivative _ _ t

theorem referenceForm_derivative_continuous (ε : ℝ) (hε : 0 < ε) (hbar coupling : ℝ) :
    Continuous (referenceFormDerivative ε hε hbar coupling) :=
  formOperator_derivative_continuous _

theorem referenceForm_norm_le (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    ‖referenceFormOperator ε hε hbar coupling t‖ ≤ 1+Real.exp (2*t) :=
  formOperator_norm_le _ _ t (clockMap_norm_le_one ε hε hbar coupling)
    (momentumMap_norm_le_one ε hε hbar coupling)

theorem referenceForm_derivative_norm_le (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ) :
    ‖referenceFormDerivative ε hε hbar coupling t‖ ≤ 2*Real.exp (2*t) :=
  formOperator_derivative_norm_le _ t (momentumMap_norm_le_one ε hε hbar coupling)

theorem timeOutput_inner (s t : ℝ) (x y : Output) :
    inner ℂ (timeOutput s t x) (timeOutput s t y) =
      inner ℂ (WithLp.ofLp x).1 (WithLp.ofLp y).1 +
      (Real.exp (2*(t-s)) : ℂ) * inner ℂ (WithLp.ofLp x).2 (WithLp.ofLp y).2 := by
  rw [timeOutput_apply,timeOutput_apply,WithLp.prod_inner_apply]
  simp only [inner_smul_left,inner_smul_right,Complex.conj_ofReal]
  rw [show Real.exp (2*(t-s)) = Real.exp (t-s)^2 by rw [two_mul,Real.exp_add,pow_two]]
  push_cast
  ring

theorem referenceForm_represents_closed_form (ε : ℝ) (hε : 0 < ε) (hbar coupling t : ℝ)
    (u v : FormSpace ε hε hbar coupling 0) :
    inner ℂ u (referenceFormOperator ε hε hbar coupling t v) =
    inner ℂ (energyOutput ε hε hbar coupling t (formTransfer ε hε hbar coupling 0 t u))
      (energyOutput ε hε hbar coupling t (formTransfer ε hε hbar coupling 0 t v)) := by
  have hp : inner ℂ u (referenceFormOperator ε hε hbar coupling t v) =
      inner ℂ (clockMap ε hε hbar coupling u) (clockMap ε hε hbar coupling v) +
      (Real.exp (2*t) : ℂ) * inner ℂ (momentumMap ε hε hbar coupling u)
        (momentumMap ε hε hbar coupling v) := formOperator_pairing _ _ t u v
  rw [hp,transfer_energyOutput ε hε hbar coupling 0 t,
    transfer_energyOutput ε hε hbar coupling 0 t,timeOutput_inner]
  simp only [sub_zero]
  rfl

#print axioms clockMap_norm_le_one
#print axioms momentumMap_norm_le_one
#print axioms referenceForm_derivative
#print axioms referenceForm_derivative_continuous
#print axioms referenceForm_norm_le
#print axioms referenceForm_derivative_norm_le
#print axioms referenceForm_represents_closed_form

end
end UnifiedTheory.Audit.KFCausalRegularizedFormRegularity
