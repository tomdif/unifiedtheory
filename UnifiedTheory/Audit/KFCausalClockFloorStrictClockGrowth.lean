/- Actual unbounded-clock growth, quantitative production bounds and a
controlled comparison with the classical-response energy form.
Strict growth does not assert divergence or quantum clock-defect recovery. -/
import UnifiedTheory.Audit.KFCausalClockFloorStrictClockProduction
import UnifiedTheory.Audit.KFCausalClockFloorClockProductionApproximation
import UnifiedTheory.Audit.KFCausalClockFloorUnboundedClockEhrenfest

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorStrictClockGrowth
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorUnboundedClockEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorClockReferenceRate (output output_actual)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "𝒲" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "O" => output ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "M" => clockMoment ε hε h hne hh m g k
local notation "V" => clockRate ε hε h hne hh m g k

def classicalRate (s t : ℝ) (w : 𝒲) : ℝ :=
  KFCausalClockFloorAveragedClockProduction.classicalProduction ε hε (O t (F s t w))

theorem clockRate_production (s t : ℝ) (w : 𝒲) :
    V s t w = (KFCausalClockFloorAveragedClockProduction.production ε hε h hh (O t (F s t w)):ℂ) :=
  KFCausalClockFloorAveragedClockProduction.clock_response_eq ε hε h hh _

theorem classicalRate_continuous (s : ℝ) (w : 𝒲) :
    Continuous (fun t => classicalRate ε hε h hne hh m g k s t w) := by
  have hp : Continuous (fun t => (t,F s t w)) :=
    continuous_id.prodMk (formFlow_continuous ε hε h hne hh m g k s w)
  have ho := (KFCausalClockFloorClockReferenceRate.output_continuous ε hε h hne hh m g k).comp
    (f := fun t => (t,F s t w)) hp
  exact (KFCausalClockFloorAveragedClockProduction.classicalProduction_continuous ε hε).comp
    (f := fun t => O t (F s t w)) ho

theorem classicalRate_nonnegative (s t : ℝ) (w : 𝒲) : 0 ≤ classicalRate ε hε h hne hh m g k s t w :=
  (KFCausalClockFloorAveragedClockProduction.classicalProduction_bounds ε hε _).1

theorem clockRate_bounds (s t : ℝ) (w : 𝒲) :
    0 ≤ (V s t w).re ∧ (1/2)*classicalRate ε hε h hne hh m g k s t w ≤ (V s t w).re ∧
      (V s t w).re ≤ E t (F s t w) := by
  rw [clockRate_production,Complex.ofReal_re]
  have hp := KFCausalClockFloorAveragedClockProduction.production_bounds ε hε h hne hh (O t (F s t w))
  refine ⟨KFCausalClockFloorAveragedClockProduction.production_nonnegative ε hε h hne hh _,hp.1,?_⟩
  simpa only [output_actual,timeEnergy_actual] using hp.2

theorem clockRate_positive (hk : 0 < k) (s t : ℝ) (w : 𝒲) (hw : J w ≠ 0) : 0 < (V s t w).re := by
  rw [clockRate_production,Complex.ofReal_re,output_actual]
  apply KFCausalClockFloorStrictClockProduction.completed_positive ε hε h hne hh m g k t hk
  intro hz
  have hj := transfer_embedding ε hε h hne hh m g k 0 t (F s t w)
  have hn := formFlow_physical_norm ε hε h hne hh m g k s t w
  have hzero := hj.symm.trans hz
  apply hw
  apply norm_eq_zero.mp
  exact hn.symm.trans (congrArg norm hzero |>.trans norm_zero)

theorem clockMoment_monotone (s : ℝ) (w : 𝒲) : Monotone (fun t => M s t w) :=
  monotone_of_hasDerivAt_nonneg (fun t => clock_derivative ε hε h hne hh m g k s t w)
    (fun t => (clockRate_bounds ε hε h hne hh m g k s t w).1)

theorem clockMoment_strictMono (hk : 0 < k) (s : ℝ) (w : 𝒲) (hw : J w ≠ 0) :
    StrictMono (fun t => M s t w) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(clock_derivative ε hε h hne hh m g k s t w).deriv]
  exact clockRate_positive ε hε h hne hh m g k hk s t w hw

theorem clockRate_classical_error (s t : ℝ) (w : 𝒲) :
    |(V s t w).re-classicalRate ε hε h hne hh m g k s t w| ≤ (2*|h|/ε)*E t (F s t w) := by
  rw [clockRate_production,Complex.ofReal_re]
  have he := KFCausalClockFloorClockProductionApproximation.averaged_error ε hε h hne hh (O t (F s t w))
  simpa only [output_actual,timeEnergy_actual] using he

theorem clockRate_classical_initial_error (s t : ℝ) (w : 𝒲) :
    |(V s t w).re-classicalRate ε hε h hne hh m g k s t w| ≤
      (2*|h|/ε)*(Real.exp (2*|t-s|)*E s w) :=
  (clockRate_classical_error ε hε h hne hh m g k s t w).trans
    (mul_le_mul_of_nonneg_left (formFlow_energy_bound ε hε h hne hh m g k s t w) (by positivity))

theorem clockMoment_real_balance (s a b : ℝ) (w : 𝒲) :
    (∫ t in a..b, (V s t w).re) = M s b w-M s a w :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => clock_derivative ε hε h hne hh m g k s t w)
    ((Complex.continuous_re.comp (clockRate_continuous ε hε h hne hh m g k s w)).intervalIntegrable _ _)

theorem classical_production_budget (s a b : ℝ) (hab : a ≤ b) (w : 𝒲) :
    (1/2)*(∫ t in a..b, classicalRate ε hε h hne hh m g k s t w) ≤ M s b w-M s a w := by
  have hc := classicalRate_continuous ε hε h hne hh m g k s w
  have hv : Continuous (fun t => (V s t w).re) := Complex.continuous_re.comp (clockRate_continuous ε hε h hne hh m g k s w)
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab (continuous_const.mul hc |>.intervalIntegrable a b)
    (hv.intervalIntegrable a b) (fun t _ => (clockRate_bounds ε hε h hne hh m g k s t w).2.1)
  simpa only [Pi.mul_apply,intervalIntegral.integral_const_mul,clockMoment_real_balance] using hi

theorem clockMoment_classical_balance_error (s a b : ℝ) (hab : a ≤ b) (w : 𝒲) :
    |(M s b w-M s a w)-(∫ t in a..b, classicalRate ε hε h hne hh m g k s t w)| ≤
      (2*|h|/ε)*(∫ t in a..b, E t (F s t w)) := by
  have hc := classicalRate_continuous ε hε h hne hh m g k s w
  have hv : Continuous (fun t => (V s t w).re) := Complex.continuous_re.comp (clockRate_continuous ε hε h hne hh m g k s w)
  have he := evolved_energy_continuous ε hε h hne hh m g k s w
  rw [← clockMoment_real_balance,← intervalIntegral.integral_sub (μ := volume) (hv.intervalIntegrable a b) (hc.intervalIntegrable a b),
    ← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in a..b, ‖(V s t w).re-classicalRate ε hε h hne hh m g k s t w‖ :=
      intervalIntegral.norm_integral_le_integral_norm hab
    _ ≤ ∫ t in a..b, (2*|h|/ε)*E t (F s t w) :=
      intervalIntegral.integral_mono_on (μ := volume) hab ((hv.sub hc).norm.intervalIntegrable a b)
        ((continuous_const.mul he).intervalIntegrable a b)
        (fun t _ => by simpa only [Real.norm_eq_abs] using clockRate_classical_error ε hε h hne hh m g k s t w)
    _ = _ := intervalIntegral.integral_const_mul _ _

#print axioms clockRate_production
#print axioms classicalRate_continuous
#print axioms classicalRate_nonnegative
#print axioms clockRate_bounds
#print axioms clockRate_positive
#print axioms clockMoment_monotone
#print axioms clockMoment_strictMono
#print axioms clockRate_classical_error
#print axioms clockRate_classical_initial_error
#print axioms clockMoment_real_balance
#print axioms classical_production_budget
#print axioms clockMoment_classical_balance_error
end
end UnifiedTheory.Audit.KFCausalClockFloorStrictClockGrowth
