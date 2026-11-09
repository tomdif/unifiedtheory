/- Uniform neutral-position tails of the actual evolved boosted Born
laws on every finite time window. This closes the position escape gap
at fixed positive clock floor; full phase-space dynamics remain open. -/
import UnifiedTheory.Audit.KFCausalUniformCharacteristicTail
import UnifiedTheory.Audit.KFCausalNeutralPositionLowFrequencyTime

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionWindowTightness
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionProbability (snapshot snapshot_characteristic)
open UnifiedTheory.Audit.KFCausalNeutralPositionInitialLimit (initial_characteristic_limit)
open UnifiedTheory.Audit.KFCausalNeutralPositionLowFrequencyTime (low_frequency_time_window)

variable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (m g k s : ℝ) (p : Configuration)
  (hm : 0 ≤ m) (hg : 0 ≤ g) (hk : 0 ≤ k)
  (h : ℕ → ℝ) (hne : ∀ n, h n ≠ 0) (hh : ∀ n, |h n| ≤ 2*Real.pi*ε/3)
  (hz : Tendsto h atTop (𝓝 0))
local notation "μ" => fun n => snapshot ε a (h n) hε ha (hne n) (hh n) m g k s p
include hm hg hk hz

theorem position_tail_window (T η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      (μ n t : Measure ℝ).real {x | R < |x|} < η := by
  apply KFCausalUniformCharacteristicTail.uniform_tail μ s T
  · intro v
    simpa only [snapshot_characteristic] using initial_characteristic_limit ε a hε ha m g k s p h hne hh hz v
  · intro η hη
    obtain ⟨V,hV,N,hN⟩ := low_frequency_time_window ε a hε ha m g k s p hm hg hk h hne hh hz T η hη
    refine ⟨V,hV,N,?_⟩
    intro n hn v t hv ht
    have hT : 0 ≤ T := (abs_nonneg (t-s)).trans ht
    simpa only [snapshot_characteristic] using hN n hn v s t hv (by simpa only [sub_self,abs_zero] using hT) ht
  · exact hη

theorem position_law_window_tight (T η : ℝ) (hη : 0 < η) :
    ∃ K : Set ℝ, IsCompact K ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      (μ n t : Measure ℝ) Kᶜ < ENNReal.ofReal η := by
  obtain ⟨R,hR,N,hN⟩ := position_tail_window ε a hε ha m g k s p hm hg hk h hne hh hz T η hη
  refine ⟨Set.Icc (-R) R,isCompact_Icc,N,?_⟩
  intro n hn t ht
  have he : (Set.Icc (-R) R)ᶜ = {x : ℝ | R < |x|} := by
    ext x
    simp only [Set.mem_compl_iff,Set.mem_Icc,Set.mem_setOf_eq,← abs_le,not_le]
  rw [he]
  have hb := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg
    (show 0 ≤ (μ n t : Measure ℝ).real {x | R < |x|} by positivity)).mpr (hN n hn t ht)
  simpa only [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hb

theorem sampled_position_law_tight (T : ℝ) (t : ℕ → ℝ)
    (ht : ∀ᶠ n in atTop, |t n-s| ≤ T) :
    IsTightMeasureSet (Set.range (fun n => (μ n (t n) : Measure ℝ))) := by
  apply KFCausalUniformCharacteristicTail.tight_of_eventual_real_tail (fun n => μ n (t n))
  intro η hη
  obtain ⟨R,hR,N,hN⟩ := position_tail_window ε a hε ha m g k s p hm hg hk h hne hh hz T η hη
  refine ⟨R,hR,?_⟩
  filter_upwards [eventually_ge_atTop N,ht] with n hn ht'
  exact (hN n hn (t n) ht').le

theorem sampled_probability_subsequence (T : ℝ) (t : ℕ → ℝ)
    (ht : ∀ᶠ n in atTop, |t n-s| ≤ T) :
    ∃ ν : ProbabilityMeasure ℝ, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      Tendsto (fun n => μ (φ n) (t (φ n))) atTop (𝓝 ν) := by
  have hq := sampled_position_law_tight ε a hε ha m g k s p hm hg hk h hne hh hz T t ht
  have he : {((ν : ProbabilityMeasure ℝ) : Measure ℝ) | ν ∈ Set.range (fun n => μ n (t n))} =
      Set.range (fun n => (μ n (t n) : Measure ℝ)) := by
    ext ν
    constructor
    · rintro ⟨ν',⟨n,rfl⟩,rfl⟩
      exact ⟨n,rfl⟩
    · rintro ⟨n,rfl⟩
      exact ⟨μ n (t n),⟨n,rfl⟩,rfl⟩
  rw [← he] at hq
  obtain ⟨ν,_,φ,hφ,hlim⟩ := (isCompact_closure_of_isTightMeasureSet hq).isSeqCompact
    (fun n => subset_closure (Set.mem_range_self n))
  exact ⟨ν,φ,hφ,hlim⟩

#print axioms position_tail_window
#print axioms position_law_window_tight
#print axioms sampled_position_law_tight
#print axioms sampled_probability_subsequence

end
end UnifiedTheory.Audit.KFCausalNeutralPositionWindowTightness
