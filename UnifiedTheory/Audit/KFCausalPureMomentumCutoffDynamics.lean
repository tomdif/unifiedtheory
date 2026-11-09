/- Actual bounded momentum-response dynamics, with quantitative removal
of Hamiltonian-resolvent smoothing. The observable cutoff is retained;
no first-moment propagation or cutoff-uniform response bound is assumed. -/
import UnifiedTheory.Audit.KFCausalPureMomentumCutoffDomain
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow
import UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPureMomentumCutoffDynamics
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow (formFlow formFlow_physical_norm)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution (evolution evolution_embedding evolution_strong_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution (formFlow_energy_bound)
open UnifiedTheory.Audit.KFCausalClockFloorResolventBalance (expectation expectation_error)
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventEhrenfest
open UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow (residual balance_difference_bound between_window)
open UnifiedTheory.Audit.KFCausalPureMomentumCutoff

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "X" => expectation ε hε h hne hh m g k
local notation "C" => characteristic ε hε h hne hh m g k
local notation "R" => boundedRate ε hε h hne hh m g k
local notation "K" => correctionRate ε hε h hne hh m g k
local notation "Z" => residual ε hε h hne hh m g k

def error (B L a : ℝ) : ℝ :=
  4*Real.sqrt (B/(4*a))+2*Real.sqrt (B/a)*|L|

theorem error_nonnegative (B L a : ℝ) : 0 ≤ error B L a := by unfold error; positivity

theorem error_tendsto (B L : ℝ) (a : ℕ → ℝ) (ha : Tendsto a atTop atTop) :
    Tendsto (fun n => error B L (a n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => Real.sqrt (B/a n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero] using
      (Real.continuous_sqrt.tendsto 0).comp (tendsto_const_nhds.div_atTop ha)
  simpa only [error,mul_zero,zero_mul,add_zero] using
    (KFCausalClockFloorResolventWindow.error_bound_tendsto B 4 a ha).add ((hs.const_mul 2).mul_const |L|)

theorem residual_bound_general (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s r t : ℝ) (v : V) (B : ℝ) (hr : E r (F s r v) ≤ B) (ht : E t (F s t v) ≤ B)
    (hE : ∀ z ∈ Set.uIoc r t, E z (F s z v) ≤ B) :
    ‖Z a D s r t v‖ ≤ ‖D‖*‖J v‖*error B (t-r) a := by
  have he (z : ℝ) (hz : E z (F s z v) ≤ B) :
      ‖C a D s z v-X D s z v‖ ≤ 2*‖D‖*‖J v‖*Real.sqrt (B/(4*a)) :=
    (expectation_error ε hε h hne hh m g k a z ha D s z v).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right hz (by positivity))) (by positivity))
  have hc (z : ℝ) (hz : z ∈ Set.uIoc r t) :
      ‖K a D s z v‖ ≤ 2*‖D‖*‖J v‖*Real.sqrt (B/a) :=
    (correctionRate_bound ε hε h hne hh m g k a ha D s z v).trans
      (mul_le_mul_of_nonneg_left
        (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (hE z hz) ha.le)) (by positivity))
  have hi : ‖∫ z in r..t, K a D s z v‖ ≤ (2*‖D‖*‖J v‖*Real.sqrt (B/a))*|t-r| :=
    intervalIntegral.norm_integral_le_of_norm_le_const hc
  have heq := boundedRate_integral ε hε h hne hh m g k a ha D s r t v
  have htri := balance_difference_bound (C a D s t v) (C a D s r v)
    (X D s t v) (X D s r v) (∫ z in r..t, K a D s z v)
  exact (congrArg (fun z : ℂ => ‖z-(X D s t v-X D s r v)‖) heq).le.trans
    (htri.trans ((add_le_add (add_le_add (he t ht) (he r hr)) hi).trans_eq (by unfold error; ring)))

def budget (s T : ℝ) (v : V) : ℝ := Real.exp (2*T)*E s v

theorem energy_window (s T z : ℝ) (v : V) (hz : |z-s| ≤ T) :
    E z (F s z v) ≤ budget ε hε h hne hh m g k s T v :=
  (formFlow_energy_bound ε hε h hne hh m g k s z v).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
      (timeEnergy_nonneg ε hε h hne hh m g k s v))

theorem residual_window (a : ℝ) (ha : 0 < a) (D : Hilbert →L[ℂ] Hilbert)
    (s T r t : ℝ) (v : V) (hr : |r-s| ≤ T) (ht : |t-s| ≤ T) :
    ‖Z a D s r t v‖ ≤ ‖D‖*‖J v‖*error (budget ε hε h hne hh m g k s T v) (t-r) a :=
  residual_bound_general ε hε h hne hh m g k a ha D s r t v _
    (energy_window ε hε h hne hh m g k s T r v hr)
    (energy_window ε hε h hne hh m g k s T t v ht)
    (fun z hz => energy_window ε hε h hne hh m g k s T z v (between_window s T r t z hr ht hz))

theorem bounded_response_integral_tendsto (D : Hilbert →L[ℂ] Hilbert)
    (s r t : ℝ) (v : V) (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (htop : Tendsto a atTop atTop) :
    Tendsto (fun n => ∫ z in r..t, R (a n) D s z v) atTop
      (𝓝 (X D s t v-X D s r v)) := by
  let T := |r-s|+|t-s|
  have hr : |r-s| ≤ T := le_add_of_nonneg_right (abs_nonneg _)
  have ht : |t-s| ≤ T := le_add_of_nonneg_left (abs_nonneg _)
  have hz : Tendsto (fun n => Z (a n) D s r t v) atTop (𝓝 0) := by
    apply squeeze_zero_norm (fun n => residual_window ε hε h hne hh m g k (a n) (ha n) D s T r t v hr ht)
    simpa only [mul_zero] using
      (error_tendsto (budget ε hε h hne hh m g k s T v) (t-r) a htop).const_mul (‖D‖*‖J v‖)
  have ht' := hz.add_const (X D s t v-X D s r v)
  simpa only [KFCausalClockFloorMovingResolventWindow.residual,sub_add_cancel,zero_add] using ht'

local notation "D" b:arg hb:arg => momentumCutoff ε hε h b hb

theorem momentum_cutoff_residual (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s T r t : ℝ) (v : V) (hr : |r-s| ≤ T) (ht : |t-s| ≤ T) :
    ‖Z a (D b hb) s r t v‖ ≤ b⁻¹*‖J v‖*error (budget ε hε h hne hh m g k s T v) (t-r) a :=
  (residual_window ε hε h hne hh m g k a ha (D b hb) s T r t v hr ht).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (operator_opNorm _ _ _ b hb) (norm_nonneg _)) (error_nonnegative _ _ _))

theorem absolute_cutoff_residual (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (s T r t : ℝ) (v : V) (hr : |r-s| ≤ T) (ht : |t-s| ≤ T) :
    ‖Z a (absoluteCutoff ε hε h b hb) s r t v‖ ≤
      b⁻¹*‖J v‖*error (budget ε hε h hne hh m g k s T v) (t-r) a :=
  (residual_window ε hε h hne hh m g k a ha (absoluteCutoff ε hε h b hb) s T r t v hr ht).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (operator_opNorm _ _ _ b hb) (norm_nonneg _)) (error_nonnegative _ _ _))

theorem momentum_cutoff_response_limit (b : ℝ) (hb : 0 < b) (s r t : ℝ) (v : V)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (htop : Tendsto a atTop atTop) :
    Tendsto (fun n => (∫ z in r..t, R (a n) (D b hb) s z v).re) atTop
      (𝓝 ((X (D b hb) s t v).re-(X (D b hb) s r v).re)) := by
  simpa only [Complex.sub_re] using
    (Complex.continuous_re.tendsto _).comp
      (bounded_response_integral_tendsto ε hε h hne hh m g k (D b hb) s r t v a ha htop)

theorem absolute_cutoff_response_limit (b : ℝ) (hb : 0 < b) (s r t : ℝ) (v : V)
    (a : ℕ → ℝ) (ha : ∀ n, 0 < a n) (htop : Tendsto a atTop atTop) :
    Tendsto (fun n => (∫ z in r..t, R (a n) (absoluteCutoff ε hε h b hb) s z v).re) atTop
      (𝓝 ((X (absoluteCutoff ε hε h b hb) s t v).re-(X (absoluteCutoff ε hε h b hb) s r v).re)) := by
  simpa only [Complex.sub_re] using
    (Complex.continuous_re.tendsto _).comp
      (bounded_response_integral_tendsto ε hε h hne hh m g k (absoluteCutoff ε hε h b hb) s r t v a ha htop)

#print axioms error_nonnegative
#print axioms error_tendsto
#print axioms residual_bound_general
#print axioms energy_window
#print axioms residual_window
#print axioms bounded_response_integral_tendsto
#print axioms momentum_cutoff_residual
#print axioms absolute_cutoff_residual
#print axioms momentum_cutoff_response_limit
#print axioms absolute_cutoff_response_limit
end
end UnifiedTheory.Audit.KFCausalPureMomentumCutoffDynamics
