/- Adjoint cancellation for all eight energy rows. The residual consists
only of the opposite imaginary shifts in the final three matter rows;
its bound persists under the actual circle average. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialAdjoint
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCutoff (action)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy (factorOutput)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound (outputAction)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm (OutputSpace)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialExponential (shifted)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialShiftPairing
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap outputMap_norm)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3)

include hh in
theorem positive_shift_bound : |h/2| ≤ Real.pi*ε/3 := by
  simpa only [abs_div,abs_neg] using shift_bound ε h hh

def reflectedFactor : Fin 8 → Hilbert →L[ℂ] Hilbert :=
  ![action h δ v hδ,action h δ v hδ,action h δ v hδ,
    action h δ v hδ,action h δ v hδ,
    shifted ε h δ v hε hδ (h/2) (positive_shift_bound ε h hh),
    shifted ε h δ v hε hδ (h/2) (positive_shift_bound ε h hh),
    shifted ε h δ v hε hδ (h/2) (positive_shift_bound ε h hh)]

def reflectedOutput : Output (Fin 8) Hilbert →L[ℂ] Output (Fin 8) Hilbert :=
  outputMap (reflectedFactor ε hε h δ v hδ hh)

theorem factor_dual (i : Fin 8) (f g : Hilbert) :
    inner ℂ f (reflectedFactor ε hε h δ v hδ hh i g) =
      inner ℂ (factorOutput ε δ (-v) hε hδ h hh i f) g := by
  have hp := KFCausalNeutralPositionRadialAdjoint.action_dual h δ v hδ f g
  have hq := shifted_dual ε h δ v hε hδ (h/2) (positive_shift_bound ε h hh)
    (by simpa only [neg_div] using shift_bound ε h hh) f g
  simp only [← neg_div] at hq
  fin_cases i <;> first | exact hp | exact hq

theorem output_dual (x y : Output (Fin 8) Hilbert) :
    inner ℂ x (reflectedOutput ε hε h δ v hδ hh y) =
      inner ℂ (outputAction ε hε h δ (-v) hδ hh x) y := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact factor_dual ε hε h δ v hδ hh i (x i) (y i)

theorem output_difference (hs : |h| ≤ Real.pi*ε/3) (y : Output (Fin 8) Hilbert) :
    ‖outputAction ε hε h δ v hδ hh y-reflectedOutput ε hε h δ v hδ hh y‖ ≤
      (|h| *responseConstant ε δ v)*‖y‖ := by
  have he : outputAction ε hε h δ v hδ hh y-reflectedOutput ε hε h δ v hδ hh y =
      outputMap (fun i => factorOutput ε δ v hε hδ h hh i-reflectedFactor ε hε h δ v hδ hh i) y := by
    apply PiLp.ext
    intro i
    rfl
  rw [he]
  apply outputMap_norm _ _ (mul_nonneg (abs_nonneg _) (responseConstant_nonneg ε δ v hε))
  intro i f
  have h0 : ‖action h δ v hδ f-action h δ v hδ f‖ ≤
      (|h| *responseConstant ε δ v)*‖f‖ := by
    rw [sub_self,norm_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (responseConstant_nonneg ε δ v hε)) (norm_nonneg _)
  have hq := shifted_difference ε h δ v hε hδ hs
    (shift_bound ε h hh) (positive_shift_bound ε h hh) f
  fin_cases i <;> first | exact h0 | exact hq

theorem outputLp_dual (x y : OutputSpace) :
    inner ℂ x ((reflectedOutput ε hε h δ v hδ hh).compLp y) =
      inner ℂ ((outputAction ε hε h δ (-v) hδ hh).compLp x) y := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(reflectedOutput ε hε h δ v hδ hh).coeFn_compLp y,
    (outputAction ε hε h δ (-v) hδ hh).coeFn_compLp x] with θ hy hx
  rw [hy,hx,output_dual]

theorem outputLp_difference (hs : |h| ≤ Real.pi*ε/3) (y : OutputSpace) :
    ‖(outputAction ε hε h δ v hδ hh).compLp y-(reflectedOutput ε hε h δ v hδ hh).compLp y‖ ≤
      (|h| *responseConstant ε δ v)*‖y‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [Lp.coeFn_sub ((outputAction ε hε h δ v hδ hh).compLp y)
      ((reflectedOutput ε hε h δ v hδ hh).compLp y),
    (outputAction ε hε h δ v hδ hh).coeFn_compLp y,
    (reflectedOutput ε hε h δ v hδ hh).coeFn_compLp y] with θ hsub hr hs'
  rw [hsub]
  simp only [Pi.sub_apply,hr,hs']
  exact output_difference ε hε h δ v hδ hh hs (y θ)

#print axioms positive_shift_bound
#print axioms factor_dual
#print axioms output_dual
#print axioms output_difference
#print axioms outputLp_dual
#print axioms outputLp_difference

end
end UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing
