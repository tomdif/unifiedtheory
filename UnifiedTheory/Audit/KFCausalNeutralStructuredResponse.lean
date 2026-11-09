/- The larger state is constructed from the actual unitary trajectory:
its neutral probability and two finite positive force-output measures.
Their weight is bounded by the physical energy, uniformly in the positive
resolvent scale. This is not a closed classical evolution law. -/
import UnifiedTheory.Audit.KFCausalNeutralForceMeasure
import UnifiedTheory.Audit.KFCausalDisplacedNeutralResolventDynamics
import UnifiedTheory.Audit.KFCausalNeutralResolventLinearLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralStructuredResponse
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState (trajectory trajectory_embedding)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear weightedQuadratic)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalNeutralResolventResponse (responseOutput)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure

structure State where
  probability : ProbabilityMeasure ℝ
  force : FluxPair

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
local notation "f" => evolvedState ε a h hε ha hne hh m g k s p
local notation "x" => trajectory ε a h hε ha hne hh m g k s p
local notation "E" => timeEnergy ε hε h hne hh m g k

def state (r t : ℝ) : State where
  probability := KFCausalNeutralMomentumProbability.snapshot ε a h hε ha hne hh m g k s p t
  force := fromOutput angleMeasure h (energyWeight m g k 0)
    (responseOutput ε hε h hne hh m g k r t (f t))

theorem probability_characteristic (r t v : ℝ) :
    charFun ((state ε a h hε ha hne hh m g k s p r t).probability : Measure ℝ) v =
      KFCausalDisplacedNeutralDynamics.characteristic ε a h hε ha hne hh m g k s p v t :=
  KFCausalNeutralMomentumProbability.snapshot_characteristic ε a h hε ha hne hh m g k s p t v

theorem force_rate (r t v : ℝ) :
    KFCausalDisplacedNeutralResolventDynamics.linearRate ε a h hε ha hne hh m g k s p r t v =
      Complex.I*(v:ℂ)*(state ε a h hε ha hne hh m g k s p r t).force.fourier v :=
  linearRate_fourier angleMeasure h v (energyWeight m g k 0)
    (responseOutput ε hε h hne hh m g k r t (f t))

theorem force_mass_bound (r t : ℝ) (hr : 0 < r) :
    (state ε a h hε ha hne hh m g k s p r t).force.mass ≤
      2*(1+‖weightedLinear (energyWeight m g k 0)‖^2)*E t (x t) := by
  have hy : ‖responseOutput ε hε h hne hh m g k r t (f t)‖^2 ≤ E t (x t) := by
    simpa only [trajectory_embedding,evolvedState] using
      KFCausalNeutralResolventResponse.responseOutput_energy ε hε h hne hh m g k r t hr (x t)
  exact (fromOutput_mass_bound angleMeasure h (energyWeight m g k 0) _).trans
    (mul_le_mul_of_nonneg_left hy (by positivity))

theorem force_evaluate_bound (r t : ℝ) (hr : 0 < r) (q : ℝ →ᵇ ℂ) :
    ‖(state ε a h hε ha hne hh m g k s p r t).force.evaluate q‖ ≤
      (1+‖weightedLinear (energyWeight m g k 0)‖^2)*E t (x t)*‖q‖ := by
  apply (evaluate_bound _ q).trans
  have hb := force_mass_bound ε a h hε ha hne hh m g k s p r t hr
  have he : (state ε a h hε ha hne hh m g k s p r t).force.mass/2 ≤
      (1+‖weightedLinear (energyWeight m g k 0)‖^2)*E t (x t) := by linarith
  exact mul_le_mul_of_nonneg_right he (norm_nonneg q)

theorem force_fourier_continuous (r v : ℝ) (hr : 0 < r) :
    Continuous (fun t => (state ε a h hε ha hne hh m g k s p r t).force.fourier v) :=
  (fourier_continuous angleMeasure h v (energyWeight m g k 0)).comp
    (KFCausalNeutralResolventContinuity.responseOutput_continuous ε hε h hne hh m g k r hr f
      (KFCausalClockFloorAveragedEvolution.evolution_strong_continuous ε hε h hne hh m g k s _))

theorem force_rate_error (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
    (r t v : ℝ) (hr : 0 < r) :
    ‖KFCausalDisplacedNeutralResolventDynamics.rate ε a h hε ha hne hh m g k s p r t v-
      Complex.I*(v:ℂ)*(state ε a h hε ha hne hh m g k s p r t).force.fourier v‖ ≤
      2*|h| *|v|^2*‖weightedQuadratic (energyWeight m g k 0)‖*E t (x t) := by
  rw [← force_rate,KFCausalDisplacedNeutralResolventDynamics.rate_polynomial
    ε a h hε ha hne hh m g k s p hm hg hk r t v hr,add_sub_cancel_left]
  exact KFCausalDisplacedNeutralResolventDynamics.quadraticRate_energy_bound
    ε a h hε ha hne hh m g k s p r t v hr

omit h hne hh in
theorem force_mass_window (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
    (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) (T : ℝ) :
    ∀ᶠ n in atTop, ∀ r : ℝ, 0 < r → ∀ t : ℝ, |t-s| ≤ T →
      (state ε a (h n) hε ha (hne n) (hh n) m g k s p r t).force.mass ≤
        2*(1+‖weightedLinear (energyWeight m g k 0)‖^2)*
          KFCausalClockFloorMovingResolventWindow.windowBudget ε a m g k s T p := by
  filter_upwards [KFCausalClockFloorDisplacedEvolutionBounds.trajectory_energy_window
    ε a hε ha m g k s p hm hg hk h hne hh hz T] with n hn
  intro r hr t ht
  exact (force_mass_bound ε a (h n) hε ha (hne n) (hh n) m g k s p r t hr).trans
    (mul_le_mul_of_nonneg_left (hn t ht) (by positivity))

#print axioms probability_characteristic
#print axioms force_rate
#print axioms force_mass_bound
#print axioms force_evaluate_bound
#print axioms force_fourier_continuous
#print axioms force_rate_error
#print axioms force_mass_window
end
end UnifiedTheory.Audit.KFCausalNeutralStructuredResponse
