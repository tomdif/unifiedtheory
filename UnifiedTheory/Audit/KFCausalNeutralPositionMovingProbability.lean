/- Time equicontinuity transfers an existing weak position limit to
moving observation times. At the actual initial time, the limit is
derived and equals the origin, so no probability-limit premise remains.
This excludes instantaneous position mass escape in that joint limit. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionTimeContinuity
import UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionMovingProbability
noncomputable section
open MeasureTheory Filter BoundedContinuousFunction
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic (bare)
open UnifiedTheory.Audit.KFCausalNeutralPositionTimeContinuity (moving_time_difference)
open UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit (origin origin_characteristic initial_probability_limit)

theorem probability_characteristic_continuous (ν : ProbabilityMeasure ℝ) :
    Continuous (charFun (ν : Measure ℝ)) := by
  have hc : Continuous (VectorFourier.fourierIntegral Real.probChar (ν : Measure ℝ) (innerₗ ℝ)
      (fun _ : ℝ => (1:ℂ))) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_probChar continuous_inner (integrable_const _)
  apply (hc.comp continuous_neg).congr
  intro t
  exact (charFun_eq_fourierIntegral (μ := (ν : Measure ℝ)) t).symm

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "μ" => fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem moving_probability_limit (t : ℝ) (ν : ProbabilityMeasure ℝ)
    (hν : Tendsto (fun n => μ n t) atTop (𝓝 ν)) (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 t)) :
    Tendsto (fun n => μ n (u n)) atTop (𝓝 ν) := by
  have hdt : Tendsto (fun n => u n-t) atTop (𝓝 (0:ℝ)) := by simpa only [sub_self] using hu.sub_const t
  have hda : Tendsto (fun n => |u n-t|) atTop (𝓝 (0:ℝ)) := by simpa only [abs_zero] using hdt.abs
  have hb : ∀ᶠ n : ℕ in atTop, |t-s| ≤ |t-s|+1 := Eventually.of_forall (fun _ => by linarith)
  have hc : ∀ᶠ n in atTop, |u n-s| ≤ |t-s|+1 := by
    filter_upwards [hda.eventually (gt_mem_nhds (by norm_num : (0:ℝ) < 1))] with n hn
    exact (abs_sub_le (u n) t s).trans (by linarith)
  apply KFCausalCharacteristicRepresentation.weak_convergence (fun n => μ n (u n))
    (charFun (ν : Measure ℝ)) (probability_characteristic_continuous ν) (by simp) _ ν (fun _ => rfl)
  intro v
  have hf := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp hν (innerProbChar v)
  have hf' : Tendsto (fun n => bare ε a (h n) hε ha (hne n) (hh n) m g k s p v t)
      atTop (𝓝 (charFun (ν : Measure ℝ) v)) := by
    simpa only [← charFun_eq_integral_innerProbChar,snapshot_characteristic] using hf
  have he := moving_time_difference ε a hε ha m g k s p hm hg hk h hne hh hz
    (|t-s|+1) |v| (fun _ => t) u (fun _ => v) hb hc (Eventually.of_forall (fun _ => le_rfl)) hdt
  simpa only [sub_add_cancel,zero_add,snapshot_characteristic] using he.add hf'

theorem near_initial_probability_limit (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 s)) :
    Tendsto (fun n => μ n (u n)) atTop (𝓝 origin) :=
  moving_probability_limit ε a hε ha m g k s p hm hg hk h hne hh hz s origin
    (initial_probability_limit ε a hε ha m g k s p h hne hh hz) u hu

theorem near_initial_tight (u : ℕ → ℝ) (hu : Tendsto u atTop (𝓝 s)) :
    IsTightMeasureSet (Set.range (fun n => (μ n (u n) : Measure ℝ))) := by
  apply KFCausalCharacteristicTightness.tight_of_characteristic_limit
    (fun n => μ n (u n)) (fun _ => (1:ℂ)) continuous_const rfl
  intro v
  have hc := (ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ).mp
    (near_initial_probability_limit ε a hε ha m g k s p hm hg hk h hne hh hz u hu) (innerProbChar v)
  simpa only [← charFun_eq_integral_innerProbChar,origin_characteristic] using hc

#print axioms probability_characteristic_continuous
#print axioms moving_probability_limit
#print axioms near_initial_probability_limit
#print axioms near_initial_tight

end
end UnifiedTheory.Audit.KFCausalNeutralPositionMovingProbability
