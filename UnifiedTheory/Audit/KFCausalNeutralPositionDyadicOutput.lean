/- The small dyadic shift response survives all eight energy rows and
the actual charge average. Norms are taken after summing the scales. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionDyadicShift
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalNeutralPositionDyadicOutput
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteMultiplierAverage
open UnifiedTheory.Audit.KFCausalDyadicHeatCancellation (width width_pos)
open UnifiedTheory.Audit.KFCausalMixedDyadicStripResponse (responseConstant responseConstant_nonneg)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergy (factorOutput)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialEnergyBound (outputAction)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialOutputPairing (reflectedFactor reflectedOutput positive_shift_bound)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialAveragedForm (OutputSpace)
open UnifiedTheory.Audit.KFCausalJointGraphBoundedCorrection (outputMap outputMap_norm)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect (shift_bound)

variable (ε : ℝ) (hε : 0 < ε) (h δ v : ℝ) (N : ℕ) (hδ : 0 < δ)
  (hh : |h| ≤ 2*Real.pi*ε/3)

def factorDifference (i : Fin 8) : Hilbert →L[ℂ] Hilbert :=
  mean N (fun j => factorOutput ε (width δ j) v hε (width_pos δ hδ j) h hh i-
    reflectedFactor ε hε h (width δ j) v (width_pos δ hδ j) hh i)

theorem output_mean_eq (y : Output (Fin 8) Hilbert) :
    mean N (fun j => outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh y-
      reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh y) =
      outputMap (factorDifference ε hε h δ v N hδ hh) y := by
  apply PiLp.ext
  intro i
  change (PiLp.projₗ 2 (𝕜 := ℂ) (fun _ : Fin 8 => Hilbert) i) (mean N _) = factorDifference ε hε h δ v N hδ hh i (y i)
  rw [mean_map,factorDifference,operator_mean_apply]
  rfl

#print axioms output_mean_eq

theorem output_mean_bound (hN : 0 < N) (y : Output (Fin 8) Hilbert) :
    ‖mean N (fun j => outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh y-
      reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh y)‖ ≤
      (|h| *responseConstant ε δ v N)*‖y‖ := by
  apply (congrArg norm (output_mean_eq ε hε h δ v N hδ hh y)).le.trans
  apply outputMap_norm _ _ (mul_nonneg (abs_nonneg _) (responseConstant_nonneg ε δ v N hε))
  intro i f
  have h0 : ‖(0:Hilbert)‖ ≤ (|h| *responseConstant ε δ v N)*‖f‖ := by
    rw [norm_zero]
    exact mul_nonneg (mul_nonneg (abs_nonneg _) (responseConstant_nonneg ε δ v N hε)) (norm_nonneg _)
  have hq := KFCausalNeutralPositionDyadicShift.action_difference ε h δ v N hε hδ hN hh
    (shift_bound ε h hh) (positive_shift_bound ε h hh) f
  simp only [KFCausalNeutralPositionDyadicShift.action_apply,← mean_sub] at hq
  apply (congrArg norm (operator_mean_apply N
    (fun j => factorOutput ε (width δ j) v hε (width_pos δ hδ j) h hh i-
      reflectedFactor ε hε h (width δ j) v (width_pos δ hδ j) hh i) f)).le.trans
  fin_cases i
  · change ‖mean N (fun j => KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f-
        KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f)‖ ≤ _
    simpa only [sub_self,mean,Finset.sum_const_zero,smul_zero] using h0
  · change ‖mean N (fun j => KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f-
        KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f)‖ ≤ _
    simpa only [sub_self,mean,Finset.sum_const_zero,smul_zero] using h0
  · change ‖mean N (fun j => KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f-
        KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f)‖ ≤ _
    simpa only [sub_self,mean,Finset.sum_const_zero,smul_zero] using h0
  · change ‖mean N (fun j => KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f-
        KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f)‖ ≤ _
    simpa only [sub_self,mean,Finset.sum_const_zero,smul_zero] using h0
  · change ‖mean N (fun j => KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f-
        KFCausalNeutralPositionRadialCutoff.action h (width δ j) v (width_pos δ hδ j) f)‖ ≤ _
    simpa only [sub_self,mean,Finset.sum_const_zero,smul_zero] using h0
  · exact hq
  · exact hq
  · exact hq

#print axioms output_mean_bound

theorem outputLp_mean_bound (hN : 0 < N) (y : OutputSpace) :
    ‖mean N (fun j => (outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y-
      (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y)‖ ≤
      (|h| *responseConstant ε δ v N)*‖y‖ := by
  have hj (j : ℕ) :
      ((outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y-
        (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y : OutputSpace) =ᵐ[KFCausalUnitIntervalOrbit.angleMeasure]
      fun θ => outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh (y θ)-
        reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh (y θ) := by
    filter_upwards [Lp.coeFn_sub ((outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y)
      ((reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).compLp y),
      (outputAction ε hε h (width δ j) v (width_pos δ hδ j) hh).coeFn_compLp y,
      (reflectedOutput ε hε h (width δ j) v (width_pos δ hδ j) hh).coeFn_compLp y] with θ hs ha hb
    rw [hs]
    simp only [Pi.sub_apply,ha,hb]
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [mean_representation N _ _ hj] with θ hθ
  rw [hθ]
  exact output_mean_bound ε hε h δ v N hδ hh hN (y θ)

#print axioms outputLp_mean_bound

end
end UnifiedTheory.Audit.KFCausalNeutralPositionDyadicOutput
