/- Charge averages of the actual output drift pairings converge.
The majorants follow from the proved boosted output energy bounds. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftIntegral
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftLimit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyIntegral (boostedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral (boostedFieldOutput)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldEnergyLimit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedAveragedExponentialLimit (boostedOutput_orbit_continuous boostedOutput_uniform_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftSeed (drift_pairing_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportOperator (driftOperator)
open UnifiedTheory.Audit.KFCausalClockFloorRecenteredOutputLimit (eventually_small)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentOrbitContinuity (continuous_angle_memLp)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

theorem driftPair_continuous (ε : ℝ) (hε : 0 < ε) : Continuous (driftPair ε hε) :=
  Complex.continuous_re.comp (continuous_id.inner (driftOperator ε hε).continuous)

def averagedDrift (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) : ℝ :=
  ∫ θ, driftPair ε hε (boostedOutput ε a h hε ha hh hb p (2*Real.pi*θ)) ∂angleMeasure

def averagedDriftLimit (ε a : ℝ) (p : Configuration) : ℝ :=
  ∫ θ, driftLimit ε a p (2*Real.pi*θ) ∂angleMeasure

theorem boostedDrift_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) :
    Integrable (fun θ => driftPair ε hε (boostedOutput ε a h hε ha hh hb p (2*Real.pi*θ))) angleMeasure :=
  (continuous_angle_memLp _ (((driftPair_continuous ε hε).comp
    (boostedOutput_orbit_continuous ε a h hε ha hh hb p)).comp
      (continuous_const.mul continuous_id))).integrable (by norm_num)

theorem averagedDrift_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedDrift ε a (h n) hε ha (hh n) (hb n) p) atTop
      (𝓝 (averagedDriftLimit ε a p)) := by
  obtain ⟨K,hK⟩ := boostedOutput_uniform_bound ε a hε ha p
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1/ε)*K)
  · exact Eventually.of_forall (fun n => (boostedDrift_integrable ε a (h n) hε ha (hh n) (hb n) p).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with θ
    rw [Real.norm_eq_abs]
    exact (drift_pairing_bound ε hε _).trans
      (mul_le_mul_of_nonneg_left (hK (2*Real.pi*θ) (h n) (hh n) (hb n) hn.1 hn.2) (by positivity))
  · exact integrable_const _
  · exact Eventually.of_forall (fun θ => boostedOutput_drift_tendsto ε a hε ha p (2*Real.pi*θ) h hh hb hz)

def averagedFieldDrift (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  ∫ θ, driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p (2*Real.pi*θ) l j) ∂angleMeasure

def averagedFieldDriftLimit (ε a : ℝ) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) : ℝ :=
  ∫ θ, fieldDriftLimit ε a p (2*Real.pi*θ) l j ∂angleMeasure

theorem boostedFieldDrift_integrable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2) :
    Integrable (fun θ => driftPair ε hε (boostedFieldOutput ε a h hε ha hh hb p (2*Real.pi*θ) l j)) angleMeasure :=
  (continuous_angle_memLp _ (((driftPair_continuous ε hε).comp
    (boostedFieldOutput_orbit_continuous ε a h hε ha hh hb p l j)).comp
      (continuous_const.mul continuous_id))).integrable (by norm_num)

theorem averagedFieldDrift_tendsto (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (l : Transverse →L[ℝ] ℝ) (j : Fin 2)
    (h : ℕ → ℝ) (hh : ∀ n, h n ≠ 0) (hb : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
    (hz : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => averagedFieldDrift ε a (h n) hε ha (hh n) (hb n) p l j) atTop
      (𝓝 (averagedFieldDriftLimit ε a p l j)) := by
  obtain ⟨K,hK⟩ := boostedFieldOutput_uniform_bound ε a hε ha p l
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1/ε)*K)
  · exact Eventually.of_forall (fun n => (boostedFieldDrift_integrable ε a (h n) hε ha (hh n) (hb n) p l j).aestronglyMeasurable)
  · filter_upwards [eventually_small ε hε h hz] with n hn
    filter_upwards [] with θ
    rw [Real.norm_eq_abs]
    exact (drift_pairing_bound ε hε _).trans
      (mul_le_mul_of_nonneg_left (hK (2*Real.pi*θ) (h n) (hh n) (hb n) hn.1 hn.2 j) (by positivity))
  · exact integrable_const _
  · exact Eventually.of_forall (fun θ => boostedFieldOutput_drift_tendsto ε a hε ha p (2*Real.pi*θ) l j h hh hb hz)

#print axioms driftPair_continuous
#print axioms boostedDrift_integrable
#print axioms averagedDrift_tendsto
#print axioms boostedFieldDrift_integrable
#print axioms averagedFieldDrift_tendsto

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
