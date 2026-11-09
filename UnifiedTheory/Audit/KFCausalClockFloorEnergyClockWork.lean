/- Exact full quantum work after subtracting twice the mean chart clock.
The remaining work is precisely twice the actual transverse kinetic energy.
Only the inherited initial left-moment condition is used for the clock mean. -/
import UnifiedTheory.Audit.KFCausalClockFloorGrowingEnergySplit
import UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
import UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorEnergyClockWork
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity (growingMap)
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorGaugeEnergy (EnergyOutputSpace kineticOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorChartPhasePairing (timeOutput orderedOutputLp)
open UnifiedTheory.Audit.KFCausalAveragedOutputRescaling (growingOutputLp)
open UnifiedTheory.Audit.KFCausalClockFloorGrowingEnergySplit
open UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
open UnifiedTheory.Audit.KFCausalClockFloorChartTransportLimit (drift drift_continuous output)
open UnifiedTheory.Audit.KFCausalClockFloorChartEhrenfest

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "O" => timeOutput ε hε h hne hh m g k
local notation "G" => growingMap ε hε h hne hh m g k
local notation "E" => energy ε hε h hne hh m g k
local notation "Q" => chartMoment ε hε h hne hh m g k
local notation "D" => drift ε hε h hne hh m g k

def kineticEnergy (s t : ℝ) (w : V) : ℝ := ‖kineticOutputLp (O t (F s t w))‖^2
def correctedEnergy (s t : ℝ) (w : V) : ℝ := E s t w-2*Q s t w

theorem reference_growing (t : ℝ) (u : V) :
    growingOutputLp (O t u) = (Real.exp t:ℂ) • G u := by
  have ho : O t u = KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t
      (energyOutput ε hε h hne hh m g k 0 u) :=
    transfer_energyOutput ε hε h hne hh m g k 0 t u
  exact (congrArg growingOutputLp ho).trans (by
    simpa only [sub_zero] using growing_time 0 t (energyOutput ε hε h hne hh m g k 0 u))

theorem power_split (s t : ℝ) (w : V) :
    power ε hε h hne hh m g k s t w = 2*(kineticEnergy ε hε h hne hh m g k s t w+D s t w) := by
  have hn : ‖Real.exp t • G (F s t w)‖^2 = ‖growingOutputLp (O t (F s t w))‖^2 := by
    rw [reference_growing]
    simp only [norm_smul,Complex.norm_real,Real.norm_eq_abs]
  change 2*‖Real.exp t • G (F s t w)‖^2 =
    2*(‖kineticOutputLp (O t (F s t w))‖^2+‖orderedOutputLp (O t (F s t w))‖^2)
  exact congrArg (fun x : ℝ => 2*x) (hn.trans (lp_growing_norm_split _))

theorem kineticEnergy_continuous (s : ℝ) (w : V) :
    Continuous (fun t => kineticEnergy ε hε h hne hh m g k s t w) := by
  have hf := (energyOutput ε hε h hne hh m g k 0).continuous.comp
    (formFlow_continuous ε hε h hne hh m g k s w)
  have hc := (KFCausalAveragedOutputTimeContinuity.timeOutputLp_continuous 0).comp
    (continuous_id.prodMk hf)
  have he : (fun t => O t (F s t w)) =
      fun t => KFCausalClockFloorAveragedOutputTransport.timeOutputLp 0 t
        (energyOutput ε hε h hne hh m g k 0 (F s t w)) :=
    funext (fun t => transfer_energyOutput ε hε h hne hh m g k 0 t (F s t w))
  have ho : Continuous (fun t => O t (F s t w)) := by rw [he]; exact hc
  exact (kineticOutputLp.continuous.comp ho).norm.pow 2

theorem corrected_energy_integral (s a b : ℝ) (ha : s ≤ a) (hb : s ≤ b) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    2*(∫ t in a..b, kineticEnergy ε hε h hne hh m g k s t w) =
      correctedEnergy ε hε h hne hh m g k s b w-correctedEnergy ε hε h hne hh m g k s a w := by
  have hk : IntervalIntegrable (fun t => kineticEnergy ε hε h hne hh m g k s t w) volume a b :=
    (kineticEnergy_continuous ε hε h hne hh m g k s w).intervalIntegrable a b
  have hd : IntervalIntegrable (fun t => D s t w) volume a b :=
    (drift_continuous ε hε h hne hh m g k s w).intervalIntegrable a b
  have hp : (∫ t in a..b, power ε hε h hne hh m g k s t w) =
      ∫ t in a..b, 2*(kineticEnergy ε hε h hne hh m g k s t w+D s t w) := intervalIntegral.integral_congr
    (fun t (_ : t ∈ Set.uIcc a b) => power_split ε hε h hne hh m g k s t w)
  simp only [intervalIntegral.integral_const_mul,intervalIntegral.integral_add hk hd] at hp
  rw [energy_integral ε hε h hne hh m g k s a b w,
    chart_integral_balance ε hε h hne hh m g k s a b ha hb w hw] at hp
  unfold correctedEnergy
  linarith only [hp]

theorem corrected_energy_derivative (s t : ℝ) (ht : s < t) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    HasDerivAt (fun z => correctedEnergy ε hε h hne hh m g k s z w)
      (2*kineticEnergy ε hε h hne hh m g k s t w) t := by
  have hd := (energy_derivative ε hε h hne hh m g k s t w).sub
    ((chart_derivative ε hε h hne hh m g k s t ht w hw).const_mul 2)
  rw [power_split] at hd
  convert hd using 1
  ring

theorem corrected_energy_monotone (s : ℝ) (w : V)
    (hw : Integrable (KFCausalClockFloorInverseGapMoment.density ε (J w))) :
    MonotoneOn (fun t => correctedEnergy ε hε h hne hh m g k s t w) (Set.Ici s) := by
  intro a ha b hb hab
  have hi : 0 ≤ 2*(∫ t in a..b, kineticEnergy ε hε h hne hh m g k s t w) :=
    mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg hab (fun _ _ => sq_nonneg _))
  rw [corrected_energy_integral ε hε h hne hh m g k s a b ha hb w hw] at hi
  exact sub_nonneg.mp hi

#print axioms reference_growing
#print axioms power_split
#print axioms kineticEnergy_continuous
#print axioms corrected_energy_integral
#print axioms corrected_energy_derivative
#print axioms corrected_energy_monotone
end
end UnifiedTheory.Audit.KFCausalClockFloorEnergyClockWork
