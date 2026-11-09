/- Quantitative output control: the deviation from a pure unitary
translation is a degree-two polynomial, with bounded operator coefficients.
The bound vanishes linearly at zero and is uniform in the input state. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput

def linearTerm : Outputs →L[ℂ] Outputs := (1/2:ℂ) • (mix 1-mix (-1))
def quadraticTerm : Outputs →L[ℂ] Outputs :=
  (1/2:ℂ) • (mix 1+mix (-1)) - ContinuousLinearMap.id ℂ Outputs

theorem mix_polynomial (c : ℂ) (y : Outputs) :
    mix c y = y+c • linearTerm y+c^2 • quadraticTerm y := by
  apply PiLp.ext
  intro i
  fin_cases i <;> simp [mix,mixValues,linearTerm,quadraticTerm,smul_add,smul_sub,smul_smul]
  all_goals module

def weightedLinear (w : Fin 8 → ℂ) : Outputs →L[ℂ] Outputs :=
  (scaleOutput w).comp (linearTerm.comp (scaleOutput (fun i => (w i)⁻¹)))
def weightedQuadratic (w : Fin 8 → ℂ) : Outputs →L[ℂ] Outputs :=
  (scaleOutput w).comp (quadraticTerm.comp (scaleOutput (fun i => (w i)⁻¹)))

theorem weightedMix_polynomial (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (y : Outputs) :
    weightedMix w c y = y+c • weightedLinear w y+c^2 • weightedQuadratic w y := by
  have hz : scaleOutput w (scaleOutput (fun i => (w i)⁻¹) y) = y := by
    apply PiLp.ext
    intro i
    change w i • ((w i)⁻¹ • y i) = y i
    rw [smul_smul,mul_inv_cancel₀ (hw i),one_smul]
  change scaleOutput w (mix c (scaleOutput (fun i => (w i)⁻¹) y)) = _
  rw [mix_polynomial,map_add,map_add,map_smul,map_smul,hz]
  rfl

def errorBound (w : Fin 8 → ℂ) (c : ℂ) : ℝ :=
  ‖c‖*‖weightedLinear w‖+‖c‖^2*‖weightedQuadratic w‖

theorem errorBound_nonneg (w : Fin 8 → ℂ) (c : ℂ) : 0 ≤ errorBound w c := by
  unfold errorBound
  positivity

theorem errorBound_neg (w : Fin 8 → ℂ) (c : ℂ) : errorBound w (-c) = errorBound w c := by
  simp only [errorBound,norm_neg]

theorem weightedMix_error (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (y : Outputs) :
    ‖weightedMix w c y-y‖ ≤ errorBound w c*‖y‖ := by
  rw [weightedMix_polynomial w hw]
  have he : y+c • weightedLinear w y+c^2 • weightedQuadratic w y-y =
      c • weightedLinear w y+c^2 • weightedQuadratic w y := by module
  rw [he]
  calc
    _ ≤ ‖c • weightedLinear w y‖+‖c^2 • weightedQuadratic w y‖ := norm_add_le _ _
    _ = ‖c‖*‖weightedLinear w y‖+‖c‖^2*‖weightedQuadratic w y‖ := by rw [norm_smul,norm_smul,norm_pow]
    _ ≤ ‖c‖*(‖weightedLinear w‖*‖y‖)+‖c‖^2*(‖weightedQuadratic w‖*‖y‖) :=
      add_le_add (mul_le_mul_of_nonneg_left ((weightedLinear w).le_opNorm y) (norm_nonneg c))
        (mul_le_mul_of_nonneg_left ((weightedQuadratic w).le_opNorm y) (sq_nonneg ‖c‖))
    _ = _ := by unfold errorBound; ring

theorem outputAction_error (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (r : ℝ) (y : Outputs) :
    ‖outputAction w c r y-translateOutput r y‖ ≤ errorBound w c*‖y‖ := by
  change ‖translateOutput r (weightedMix w c y)-translateOutput r y‖ ≤ _
  rw [← map_sub,translateOutput_norm]
  exact weightedMix_error w hw c y

theorem outputAction_norm (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (r : ℝ) (y : Outputs) :
    ‖outputAction w c r y‖ ≤ (1+errorBound w c)*‖y‖ := by
  have ht := norm_add_le (outputAction w c r y-translateOutput r y) (translateOutput r y)
  rw [sub_add_cancel,translateOutput_norm] at ht
  have he := outputAction_error w hw c r y
  nlinarith

#print axioms mix_polynomial
#print axioms weightedMix_polynomial
#print axioms errorBound_nonneg
#print axioms errorBound_neg
#print axioms weightedMix_error
#print axioms outputAction_error
#print axioms outputAction_norm

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
