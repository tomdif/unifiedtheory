/- The physical unbounded positive-clock expectation along the actual
averaged propagator. Finite moments, a continuous exact rate, integral
balance and a derivative follow by removing bounded clock resolvents.
No Hamiltonian-domain invariance or clock-operator-domain premise is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorClockRegularizedEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorClockMoment
import UnifiedTheory.Audit.KFCausalClockFloorAveragedClockBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorUnboundedClockEhrenfest
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate (rate approxRate)
open UnifiedTheory.Audit.KFCausalClockFloorClockRegularizedEhrenfest (characteristic exactRate)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorClockMoment (moment)

def cutoff (n : ℕ) : ℝ := 1/((n:ℝ)+1)

theorem cutoff_positive (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto : Tendsto cutoff atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "𝒲" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k

def clockMoment (s t : ℝ) (w : 𝒲) : ℝ := moment ε (U s t (J w))

def clockRate (s t : ℝ) (w : 𝒲) : ℂ := rate ε hε h hne hh m g k t (F s t w)

theorem half_clock_graph (s t : ℝ) (w : 𝒲) :
    ∃ y : Hilbert, (U s t (J w),y) ∈ (clockHalf ε).graph ∧ ‖y‖^2 ≤ 2*E t (F s t w) := by
  have hx := KFCausalClockFloorAveragedClockBound.reference_clock_graph_bound ε hε h hne m g k t hh (F s t w)
  simpa only [evolution_embedding] using hx

theorem clockMoment_integrable (s t : ℝ) (w : 𝒲) :
    Integrable (fun x => KFCausalClockFloorFlow.clock ε x.1*‖U s t (J w) x‖^2) volume := by
  have hx := half_clock_graph ε hε h hne hh m g k s t w
  rcases hx with ⟨y,hy,_⟩
  exact KFCausalClockFloorClockMoment.moment_integrable ε hε _ y hy

theorem clockMoment_bound (s t : ℝ) (w : 𝒲) :
    0 ≤ clockMoment ε hε h hne hh m g k s t w ∧
      clockMoment ε hε h hne hh m g k s t w ≤ 2*E t (F s t w) := by
  have hx := half_clock_graph ε hε h hne hh m g k s t w
  rcases hx with ⟨y,hy,hb⟩
  have he := KFCausalClockFloorClockMoment.moment_eq_norm ε hε _ y hy
  change 0 ≤ moment ε (U s t (J w)) ∧ moment ε (U s t (J w)) ≤ _
  rw [he]
  exact ⟨sq_nonneg _,hb⟩

theorem clockRate_continuous (s : ℝ) (w : 𝒲) :
    Continuous (fun t => clockRate ε hε h hne hh m g k s t w) := by
  have hp : Continuous (fun t => (t,F s t w)) :=
    continuous_id.prodMk (formFlow_continuous ε hε h hne hh m g k s w)
  exact (KFCausalClockFloorClockReferenceRate.rate_continuous ε hε h hne hh m g k).comp
    (f := fun t => (t,F s t w)) hp

theorem evolved_energy_continuous (s : ℝ) (w : 𝒲) : Continuous (fun t => E t (F s t w)) := by
  have hp : Continuous (fun t => (t,F s t w)) :=
    continuous_id.prodMk (formFlow_continuous ε hε h hne hh m g k s w)
  exact (KFCausalClockFloorClockReferenceRate.energy_continuous ε hε h hne hh m g k).comp
    (f := fun t => (t,F s t w)) hp

theorem clockRate_bound (s t : ℝ) (w : 𝒲) :
    ‖clockRate ε hε h hne hh m g k s t w‖ ≤ 2*E t (F s t w) :=
  KFCausalClockFloorClockReferenceRate.rate_bound ε hε h hne hh m g k t (F s t w)

theorem clockRate_initial_energy_bound (s t : ℝ) (w : 𝒲) :
    ‖clockRate ε hε h hne hh m g k s t w‖ ≤ 2*(Real.exp (2*|t-s|)*E s w) :=
  (clockRate_bound ε hε h hne hh m g k s t w).trans
    (mul_le_mul_of_nonneg_left (formFlow_energy_bound ε hε h hne hh m g k s t w) (by norm_num))

theorem regularized_expectation_tendsto (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hz : Tendsto b atTop (𝓝 0)) (s t : ℝ) (w : 𝒲) :
    Tendsto (fun n => characteristic ε hε h hne hh m g k (b n) (hb n) s t w)
      atTop (𝓝 (clockMoment ε hε h hne hh m g k s t w:ℂ)) := by
  have hx := half_clock_graph ε hε h hne hh m g k s t w
  rcases hx with ⟨y,hy,_⟩
  exact KFCausalClockFloorClockMoment.complex_expectation_tendsto ε hε _ y hy b hb hz

theorem clock_integral_balance (s a b : ℝ) (w : 𝒲) :
    (∫ t in a..b, clockRate ε hε h hne hh m g k s t w) =
      (clockMoment ε hε h hne hh m g k s b w:ℂ)-(clockMoment ε hε h hne hh m g k s a w:ℂ) := by
  let G : ℕ → ℝ → ℂ := fun n t => exactRate ε hε h hne hh m g k (cutoff n) (cutoff_positive n) s t w
  have hc (n : ℕ) : Continuous (G n) :=
    KFCausalClockFloorClockRegularizedEhrenfest.exactRate_continuous ε hε h hne hh m g k _ _ s w
  have hl (t : ℝ) : Tendsto (fun n => G n t) atTop (𝓝 (clockRate ε hε h hne hh m g k s t w)) :=
    KFCausalClockFloorClockReferenceRate.approxRate_tendsto ε hε h hne hh m g k
      cutoff cutoff_positive cutoff_tendsto t (F s t w)
  have hd (n : ℕ) (t : ℝ) : ‖G n t‖ ≤ 8*E t (F s t w) :=
    KFCausalClockFloorClockReferenceRate.approxRate_bound ε hε h hne hh m g k _ _ t (F s t w)
  have hi : Tendsto (fun n => ∫ t in a..b, G n t) atTop
      (𝓝 (∫ t in a..b, clockRate ε hε h hne hh m g k s t w)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun t => 8*E t (F s t w))
    · exact Eventually.of_forall (fun n => (hc n).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun t _ => hd n t))
    · exact (continuous_const.mul (evolved_energy_continuous ε hε h hne hh m g k s w)).intervalIntegrable _ _
    · exact Eventually.of_forall (fun t _ => hl t)
  have he (n : ℕ) : (∫ t in a..b, G n t) =
      characteristic ε hε h hne hh m g k (cutoff n) (cutoff_positive n) s b w-
        characteristic ε hε h hne hh m g k (cutoff n) (cutoff_positive n) s a w :=
    KFCausalClockFloorClockRegularizedEhrenfest.expectation_integral ε hε h hne hh m g k _ _ s a b w
  have hf := (regularized_expectation_tendsto ε hε h hne hh m g k cutoff cutoff_positive cutoff_tendsto s b w).sub
    (regularized_expectation_tendsto ε hε h hne hh m g k cutoff cutoff_positive cutoff_tendsto s a w)
  exact tendsto_nhds_unique hi (by simpa only [he] using hf)

theorem clock_complex_derivative (s t : ℝ) (w : 𝒲) :
    HasDerivAt (fun z => (clockMoment ε hε h hne hh m g k s z w:ℂ))
      (clockRate ε hε h hne hh m g k s t w) t := by
  have hc := clockRate_continuous ε hε h hne hh m g k s w
  have hd := (intervalIntegral.integral_hasDerivAt_right (a := 0) (b := t)
    (hc.intervalIntegrable 0 t) hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const
      (clockMoment ε hε h hne hh m g k s 0 w:ℂ)
  convert hd using 1
  funext z
  rw [clock_integral_balance,sub_add_cancel]

theorem clock_derivative (s t : ℝ) (w : 𝒲) :
    HasDerivAt (fun z => clockMoment ε hε h hne hh m g k s z w)
      (clockRate ε hε h hne hh m g k s t w).re t := by
  have hd := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t (clock_complex_derivative ε hε h hne hh m g k s t w)
  simpa only [Function.comp_def,Complex.reCLM_apply,Complex.ofReal_re] using hd

#print axioms cutoff_positive
#print axioms cutoff_tendsto
#print axioms half_clock_graph
#print axioms clockMoment_integrable
#print axioms clockMoment_bound
#print axioms clockRate_continuous
#print axioms evolved_energy_continuous
#print axioms clockRate_bound
#print axioms clockRate_initial_energy_bound
#print axioms regularized_expectation_tendsto
#print axioms clock_integral_balance
#print axioms clock_complex_derivative
#print axioms clock_derivative
end
end UnifiedTheory.Audit.KFCausalClockFloorUnboundedClockEhrenfest
