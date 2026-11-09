/- Split the actual five growing output factors into two transverse
kinetic factors and all three ordered factors, on the full angle-L2 space. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorGrowingEnergySplit
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalFiniteJointGraph (Output)
open UnifiedTheory.Audit.KFCausalFiniteOutputRescaling (selected_apply)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyTransport (growingOutput timeOutput timeOutput_apply)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (growingOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (EnergyOutputSpace kinetic kineticOutput kineticOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing (orderedOutput orderedOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedOutputTransport (timeOutputLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem growing_inner_split (x y : Output (Fin 8) Hilbert) :
    inner ℂ (growingOutput x) (growingOutput y) =
      inner ℂ (kineticOutput x) (kineticOutput y)+inner ℂ (orderedOutput x) (orderedOutput y) := by
  rw [PiLp.inner_apply,PiLp.inner_apply,PiLp.inner_apply,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h3 : i.val < 3
  · have hk : ¬ kinetic i := by simp only [kinetic]; omega
    have h5 : i.val < 5 := by omega
    simp only [growingOutput,kineticOutput,orderedOutput,selected_apply,h3,h5,hk,
      not_true_eq_false,if_false,inner_zero_left,add_zero]
  · by_cases h5 : i.val < 5
    · have hk : kinetic i := ⟨by omega,h5⟩
      simp only [growingOutput,kineticOutput,orderedOutput,selected_apply,h3,h5,hk,
        not_false_eq_true,not_true_eq_false,if_true,if_false,inner_zero_left,add_zero]
    · have hk : ¬ kinetic i := by simp only [kinetic]; omega
      simp only [growingOutput,kineticOutput,orderedOutput,selected_apply,h3,h5,hk,
        not_false_eq_true,if_true,if_false,inner_zero_left,zero_add]

theorem lp_growing_inner_split (x y : EnergyOutputSpace) :
    inner ℂ (growingOutputLp x) (growingOutputLp y) =
      inner ℂ (kineticOutputLp x) (kineticOutputLp y)+inner ℂ (orderedOutputLp x) (orderedOutputLp y) := by
  have he : (fun θ => inner ℂ (growingOutputLp x θ) (growingOutputLp y θ)) =ᵐ[angleMeasure]
      fun θ => inner ℂ (kineticOutputLp x θ) (kineticOutputLp y θ)+
        inner ℂ (orderedOutputLp x θ) (orderedOutputLp y θ) := by
    filter_upwards [growingOutput.coeFn_compLp x,growingOutput.coeFn_compLp y,
      kineticOutput.coeFn_compLp x,kineticOutput.coeFn_compLp y,
      orderedOutput.coeFn_compLp x,orderedOutput.coeFn_compLp y] with θ h1 h2 h3 h4 h5 h6
    change inner ℂ (growingOutput.compLp x θ) (growingOutput.compLp y θ) =
      inner ℂ (kineticOutput.compLp x θ) (kineticOutput.compLp y θ)+
        inner ℂ (orderedOutput.compLp x θ) (orderedOutput.compLp y θ)
    rw [h1,h2,h3,h4,h5,h6,growing_inner_split]
  rw [L2.inner_def,integral_congr_ae he,
    integral_add (L2.integrable_inner (𝕜 := ℂ) (kineticOutputLp x) (kineticOutputLp y))
      (L2.integrable_inner (𝕜 := ℂ) (orderedOutputLp x) (orderedOutputLp y)),
    ← L2.inner_def,← L2.inner_def]

theorem lp_growing_norm_split (x : EnergyOutputSpace) :
    ‖growingOutputLp x‖^2 = ‖kineticOutputLp x‖^2+‖orderedOutputLp x‖^2 := by
  apply Complex.ofReal_injective
  simpa only [inner_self_eq_norm_sq_to_K,Complex.ofReal_pow,Complex.ofReal_add] using lp_growing_inner_split x x

theorem growing_time (s t : ℝ) (x : EnergyOutputSpace) :
    growingOutputLp (timeOutputLp s t x) = (Real.exp (t-s):ℂ) • growingOutputLp x := by
  apply Lp.ext
  filter_upwards [growingOutput.coeFn_compLp (timeOutputLp s t x),
    (timeOutput s t).coeFn_compLp x,growingOutput.coeFn_compLp x,
    Lp.coeFn_smul (Real.exp (t-s):ℂ) (growingOutputLp x)] with θ h1 h2 h3 h4
  change growingOutput.compLp (timeOutputLp s t x) θ = _
  rw [h1,h4]
  change growingOutput ((timeOutput s t).compLp x θ) = (Real.exp (t-s):ℂ) • growingOutput.compLp x θ
  rw [h2,h3]
  apply PiLp.ext
  intro i
  by_cases hi : i.val < 3 <;>
    simp only [growingOutput,selected_apply,timeOutput_apply,PiLp.smul_apply,hi,
      not_true_eq_false,not_false_eq_true,if_true,if_false,smul_zero]

#print axioms growing_inner_split
#print axioms lp_growing_inner_split
#print axioms lp_growing_norm_split
#print axioms growing_time
end
end UnifiedTheory.Audit.KFCausalClockFloorGrowingEnergySplit
