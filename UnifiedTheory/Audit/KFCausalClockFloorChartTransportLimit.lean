/- Zero-frequency limit of the actual bounded chart-characteristic
balance. The resulting positive response is the full ordered energy,
including both matter factors and the vacuum factor. -/
import UnifiedTheory.Audit.KFCausalClockFloorChartPhaseEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity
import UnifiedTheory.Audit.KFCausalAveragedOutputTimeContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing
open UnifiedTheory.Audit.KFCausalClockFloorChartPhaseEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorChartPhaseContinuity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (EnergyOutputSpace)
open UnifiedTheory.Audit.KFCausalNeutralReferencePairing (coefficient)

theorem orderedOutputLp_norm_le (x : EnergyOutputSpace) : ‖orderedOutputLp x‖ ≤ ‖x‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [orderedOutput.coeFn_compLp x] with θ hθ
  change ‖orderedOutput.compLp x θ‖ ≤ ‖x θ‖
  rw [hθ]
  exact KFCausalFiniteOutputRescaling.selected_norm_le _ _

theorem difference_slope (h : ℝ) :
    Tendsto (fun r : ℝ => r⁻¹*difference h r) (𝓝[≠] 0) (𝓝 (2*Real.pi*h)) := by
  have hp := (((hasDerivAt_id (0:ℝ)).const_mul (Real.pi*h)).exp).sub
    ((((hasDerivAt_id (0:ℝ)).const_mul (-(Real.pi*h))).exp))
  have he : HasDerivAt (difference h) (2*Real.pi*h) 0 := by
    convert hp using 1
    · funext r
      dsimp only [difference,id_eq,Pi.sub_apply]
      congr 1
      congr 1
      ring
    · simp only [mul_zero,Real.exp_zero,mul_one,id_eq]
      ring
  simpa only [difference,mul_zero,neg_zero,Real.exp_zero,sub_self,sub_zero,zero_add,smul_eq_mul] using he.tendsto_slope_zero

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "O" => timeOutput ε hε h hne hh m g k

def output (s t : ℝ) (w : V) : EnergyOutputSpace := orderedOutputLp (O t (F s t w))
def drift (s t : ℝ) (w : V) : ℝ := ‖output ε hε h hne hh m g k s t w‖^2
def pairing (r s t : ℝ) (w : V) : ℂ :=
  inner ℂ (output ε hε h hne hh m g k s t w)
    (phaseOutputLp ε r (output ε hε h hne hh m g k s t w))

theorem output_continuous (s : ℝ) (w : V) : Continuous (fun t => output ε hε h hne hh m g k s t w) := by
  have hf := (energyOutput ε hε h hne hh m g k 0).continuous.comp
    (formFlow_continuous ε hε h hne hh m g k s w)
  have hc := (KFCausalAveragedOutputTimeContinuity.timeOutputLp_continuous 0).comp
    (continuous_id.prodMk hf)
  have he : (fun t => output ε hε h hne hh m g k s t w) =
      fun t => orderedOutputLp
        (KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t
          (energyOutput ε hε h hne hh m g k 0 (F s t w))) := by
    funext t
    unfold output timeOutput
    rw [transfer_energyOutput]
  rw [he]
  exact orderedOutputLp.continuous.comp hc

theorem drift_continuous (s : ℝ) (w : V) : Continuous (fun t => drift ε hε h hne hh m g k s t w) :=
  (output_continuous ε hε h hne hh m g k s w).norm.pow 2

theorem drift_bounds (s t : ℝ) (w : V) : 0 ≤ drift ε hε h hne hh m g k s t w ∧
    drift ε hε h hne hh m g k s t w ≤ timeEnergy ε hε h hne hh m g k t (F s t w) := by
  refine ⟨sq_nonneg _,?_⟩
  exact (pow_le_pow_left₀ (norm_nonneg _) (orderedOutputLp_norm_le (O t (F s t w))) 2).trans_eq
    (timeEnergy_actual ε hε h hne hh m g k t (F s t w))

theorem pairing_continuous (r s : ℝ) (w : V) : Continuous (fun t => pairing ε hε h hne hh m g k r s t w) :=
  (output_continuous ε hε h hne hh m g k s w).inner (𝕜 := ℂ)
    ((phaseOutputLp ε r).continuous.comp (output_continuous ε hε h hne hh m g k s w))

theorem integrated_pairing_limit (s a b : ℝ) (w : V) :
    Tendsto (fun r => ∫ t in a..b, pairing ε hε h hne hh m g k r s t w) (𝓝 0)
      (𝓝 (∫ t in a..b, (drift ε hε h hne hh m g k s t w:ℂ))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun t => drift ε hε h hne hh m g k s t w)
  · exact Eventually.of_forall (fun r => (pairing_continuous ε hε h hne hh m g k r s w).aestronglyMeasurable)
  · exact Eventually.of_forall (fun r => Eventually.of_forall (fun t _ => lp_pairing_bound ε r _))
  · exact (drift_continuous ε hε h hne hh m g k s w).intervalIntegrable _ _
  · exact Eventually.of_forall (fun t _ => by
      simpa only [phaseOutputLp_zero,inner_self_eq_norm_sq_to_K,Complex.ofReal_pow,drift,pairing] using
        (lp_pairing_continuous ε (output ε hε h hne hh m g k s t w)).continuousAt.tendsto (x := 0))

theorem characteristic_slope_balance (s a b : ℝ) (w : V) :
    Tendsto (fun r : ℝ => r⁻¹ •
      (characteristic ε hε h hne hh m g k r s b w-characteristic ε hε h hne hh m g k r s a w))
      (𝓝[≠] 0) (𝓝 (Complex.I*(2*Real.pi:ℝ)*(∫ t in a..b, (drift ε hε h hne hh m g k s t w:ℂ)))) := by
  have he (r : ℝ) : characteristic ε hε h hne hh m g k r s b w-
      characteristic ε hε h hne hh m g k r s a w =
      coefficient h*(difference h r:ℂ)*(∫ t in a..b, pairing ε hε h hne hh m g k r s t w) := by
    rw [← expectation_integral]
    simp only [exactRate_output,pairing,output,intervalIntegral.integral_const_mul]
  have hc : coefficient h*(2*Real.pi*h:ℝ) = Complex.I*(2*Real.pi:ℝ) := by
    unfold coefficient
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr hne]
  have hl := (((difference_slope h).ofReal).const_mul (coefficient h)).mul
    ((integrated_pairing_limit ε hε h hne hh m g k s a b w).mono_left nhdsWithin_le_nhds)
  rw [hc] at hl
  convert hl using 1
  funext r
  rw [he,Complex.real_smul,Complex.ofReal_mul]
  ring

#print axioms orderedOutputLp_norm_le
#print axioms difference_slope
#print axioms output_continuous
#print axioms drift_continuous
#print axioms drift_bounds
#print axioms pairing_continuous
#print axioms integrated_pairing_limit
#print axioms characteristic_slope_balance
end
end UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit
