/- Exact energy work and integrated growing-output control along the
actual full quantum propagator. No strong Hamiltonian-domain propagation
or pure-clock momentum bound is assumed or concluded. -/
import UnifiedTheory.Audit.KFCausalClockFloorRegularizedEnergyBalance
import UnifiedTheory.Audit.KFCausalClockFloorMovingResolventWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
noncomputable section
open Filter MeasureTheory
open scoped Topology
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedRegularity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorStrongFormEvolution
open UnifiedTheory.Audit.KFCausalClockFloorResolventEnergyControl
open UnifiedTheory.Audit.KFCausalClockFloorResolventFormLimit
open UnifiedTheory.Audit.KFCausalClockFloorRegularizedEnergyBalance

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k : ℝ)
local notation "V" => FormSpace ε hε h hne hh m g k 0
local notation "J" => embedding ε hε h hne hh m g k 0
local notation "F" => formFlow ε hε h hne hh m g k
local notation "U" => evolution ε hε h hne hh m g k
local notation "E" => timeEnergy ε hε h hne hh m g k
local notation "G" => growingMap ε hε h hne hh m g k

def energy (s t : ℝ) (w : V) : ℝ := E t (F s t w)
def power (s t : ℝ) (w : V) : ℝ := 2*‖Real.exp t • G (F s t w)‖^2

theorem power_continuous (s : ℝ) (w : V) : Continuous (fun t => power ε hε h hne hh m g k s t w) := by
  have hf := (growingMap ε hε h hne hh m g k).continuous.comp
    (formFlow_continuous ε hε h hne hh m g k s w)
  exact continuous_const.mul ((Real.continuous_exp.smul hf).norm.pow 2)

theorem power_bounds (s t : ℝ) (w : V) :
    0 ≤ power ε hε h hne hh m g k s t w ∧
      power ε hε h hne hh m g k s t w ≤ 2*energy ε hε h hne hh m g k s t w := by
  constructor
  · unfold power; positivity
  · exact mul_le_mul_of_nonneg_left (growing_energy_bound ε hε h hne hh m g k t (F s t w)) (by norm_num)

theorem regularized_value_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop atTop) (s t : ℝ) (w : V) :
    Tendsto (fun n => value ε hε h hne hh m g k (a n) s t w) atTop
      (𝓝 (energy ε hε h hne hh m g k s t w)) := by
  simpa only [value,energy,evolution_embedding] using
    boundedEnergy_tendsto ε hε h hne hh m g k a ha hlim t (F s t w)

theorem regularized_rate_tendsto (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (hlim : Tendsto a atTop atTop) (s t : ℝ) (w : V) :
    Tendsto (fun n => rate ε hε h hne hh m g k (a n) s t w) atTop
      (𝓝 (power ε hε h hne hh m g k s t w)) := by
  simpa only [rate,power,evolution_embedding] using
    ((growingLift_tendsto ε hε h hne hh m g k a ha hlim t (F s t w)).norm.pow 2).const_mul 2

theorem rate_window_bound (a : ℝ) (ha : 0 < a) (s T z : ℝ) (hz : |z-s| ≤ T) (w : V) :
    ‖rate ε hε h hne hh m g k a s z w‖ ≤ 2*Real.exp (2*T)*E s w := by
  have hr : 0 ≤ rate ε hε h hne hh m g k a s z w := by unfold rate; positivity
  rw [Real.norm_eq_abs,abs_of_nonneg hr]
  have hexp : Real.exp (2*|z-s|) ≤ Real.exp (2*T) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hz (by norm_num))
  have he := (formFlow_energy_bound ε hε h hne hh m g k s z w).trans
    (mul_le_mul_of_nonneg_right hexp
      (timeEnergy_nonneg ε hε h hne hh m g k s w))
  have hg := growingLift_form_bound ε hε h hne hh m g k a z ha (F s z w)
  unfold rate
  rw [evolution_embedding]
  nlinarith only [he,hg]

theorem energy_integral (s r t : ℝ) (w : V) :
    (∫ z in r..t, power ε hε h hne hh m g k s z w) =
      energy ε hε h hne hh m g k s t w-energy ε hε h hne hh m g k s r w := by
  let a := fun n : ℕ => (n:ℝ)+1
  have ha (n : ℕ) : 0 < a n := by dsimp [a]; positivity
  have hlim : Tendsto a atTop atTop := tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  let T := |r-s|+|t-s|
  have hi : Tendsto (fun n => ∫ z in r..t, rate ε hε h hne hh m g k (a n) s z w) atTop
      (𝓝 (∫ z in r..t, power ε hε h hne hh m g k s z w)) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 2*Real.exp (2*T)*E s w)
    · exact Eventually.of_forall (fun n => (rate_continuous ε hε h hne hh m g k (a n) (ha n) s w).aestronglyMeasurable)
    · exact Eventually.of_forall (fun n => Eventually.of_forall (fun z hz =>
        rate_window_bound ε hε h hne hh m g k (a n) (ha n) s T z
          (KFCausalClockFloorMovingResolventWindow.between_window s T r t z
            (by dsimp [T]; linarith only [abs_nonneg (t-s)])
            (by dsimp [T]; linarith only [abs_nonneg (r-s)]) hz) w))
    · exact intervalIntegrable_const
    · exact Eventually.of_forall (fun z _ => regularized_rate_tendsto ε hε h hne hh m g k a ha hlim s z w)
  have hj := (regularized_value_tendsto ε hε h hne hh m g k a ha hlim s t w).sub
    (regularized_value_tendsto ε hε h hne hh m g k a ha hlim s r w)
  have he (n : ℕ) := value_integral ε hε h hne hh m g k (a n) (ha n) s r t w
  exact tendsto_nhds_unique hi (by simpa only [he] using hj)

theorem energy_derivative (s t : ℝ) (w : V) :
    HasDerivAt (fun z => energy ε hε h hne hh m g k s z w)
      (power ε hε h hne hh m g k s t w) t := by
  have hc := power_continuous ε hε h hne hh m g k s w
  have hd := intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt
  have he : (fun z => energy ε hε h hne hh m g k s z w) =
      fun z => (∫ u in 0..z, power ε hε h hne hh m g k s u w)+energy ε hε h hne hh m g k s 0 w := by
    funext z
    rw [energy_integral ε hε h hne hh m g k s 0 z w,sub_add_cancel]
  rw [he]
  exact hd.add_const _

theorem energy_monotone (s : ℝ) (w : V) : Monotone (fun t => energy ε hε h hne hh m g k s t w) :=
  monotone_of_hasDerivAt_nonneg (fun t => energy_derivative ε hε h hne hh m g k s t w)
    (fun t => (power_bounds ε hε h hne hh m g k s t w).1)

theorem energy_comparison (s r t : ℝ) (hrt : r ≤ t) (w : V) :
    energy ε hε h hne hh m g k s r w ≤ energy ε hε h hne hh m g k s t w ∧
      energy ε hε h hne hh m g k s t w ≤ Real.exp (2*(t-r))*energy ε hε h hne hh m g k s r w :=
  KFCausalSchrodingerEnergyEstimate.energy_comparison _ _
    (fun z => energy_derivative ε hε h hne hh m g k s z w)
    (fun z => power_bounds ε hε h hne hh m g k s z w) r t hrt

theorem integrated_growing_bound (s r t : ℝ) (hrt : r ≤ t) (w : V) :
    (∫ z in r..t, ‖Real.exp z • G (F s z w)‖^2) ≤
      ((Real.exp (2*(t-r))-1)/2)*energy ε hε h hne hh m g k s r w := by
  have hi := energy_integral ε hε h hne hh m g k s r t w
  simp only [power,intervalIntegral.integral_const_mul] at hi
  have he := (energy_comparison ε hε h hne hh m g k s r t hrt w).2
  nlinarith only [hi,he]

#print axioms power_continuous
#print axioms power_bounds
#print axioms regularized_value_tendsto
#print axioms regularized_rate_tendsto
#print axioms rate_window_bound
#print axioms energy_integral
#print axioms energy_derivative
#print axioms energy_monotone
#print axioms energy_comparison
#print axioms integrated_growing_bound
end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumEnergyBalance
