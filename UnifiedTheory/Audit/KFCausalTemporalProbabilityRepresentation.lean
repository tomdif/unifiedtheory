/- A jointly continuous limit of actual probability characteristics
represents a weakly continuous probability curve. Moving-time convergence
requires the supplied joint equicontinuity, not just fixed-time limits. -/
import UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
import UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalTemporalProbabilityRepresentation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCharacteristicRepresentation
open UnifiedTheory.Audit.KFCausalAsymptoticCharacteristicCompactness
open UnifiedTheory.Audit.KFCausalCharacteristicCompactUniformity

theorem continuous_probability_curve (ν : ℝ → ProbabilityMeasure ℝ) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (hν : ∀ t v, charFun (ν t : Measure ℝ) v = χ (t,v)) : Continuous ν := by
  apply continuous_iff_seqContinuous.mpr
  intro u t hu
  have hc : Continuous (fun v => χ (t,v)) := hχ.comp (continuous_const.prodMk continuous_id)
  have h0 : χ (t,0) = 1 := by rw [← hν t 0]; simp
  apply weak_convergence (fun n => ν (u n)) (fun v => χ (t,v)) hc h0 _ (ν t) (hν t)
  intro v
  simpa only [hν] using (hχ.tendsto (t,v)).comp (hu.prodMk_nhds tendsto_const_nhds)

theorem represented_curve (μ : ℕ → ℝ → ProbabilityMeasure ℝ) (χ : ℝ × ℝ → ℂ)
    (hχ : Continuous χ) (h0 : ∀ t, χ (t,0) = 1)
    (hc : ∀ t v, Tendsto (fun n => charFun (μ n t : Measure ℝ) v) atTop (𝓝 (χ (t,v)))) :
    ∃ ν : ℝ → ProbabilityMeasure ℝ, Continuous ν ∧
      (∀ t v, charFun (ν t : Measure ℝ) v = χ (t,v)) ∧
      (∀ t, Tendsto (fun n => μ n t) atTop (𝓝 (ν t))) := by
  have he (t : ℝ) := exists_probability_limit (fun n => μ n t) (fun v => χ (t,v))
    (hχ.comp (continuous_const.prodMk continuous_id)) (h0 t) (hc t)
  choose ν hν hsub using he
  exact ⟨ν,continuous_probability_curve ν χ hχ hν,hν,
    fun t => weak_convergence (fun n => μ n t) (fun v => χ (t,v))
      (hχ.comp (continuous_const.prodMk continuous_id)) (h0 t) (hc t) (ν t) (hν t)⟩

theorem moving_time_convergence (μ : ℕ → ℝ → ProbabilityMeasure ℝ)
    (he : EventuallyLocallyEquicontinuous (fun n (z : ℝ × ℝ) => charFun (μ n z.1 : Measure ℝ) z.2))
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (χ : ℝ × ℝ → ℂ) (hχ : Continuous χ)
    (hc : ∀ z, Tendsto (fun n => charFun (μ (φ n) z.1 : Measure ℝ) z.2) atTop (𝓝 (χ z)))
    (ν : ℝ → ProbabilityMeasure ℝ) (hν : ∀ t v, charFun (ν t : Measure ℝ) v = χ (t,v))
    (u : ℕ → ℝ) (t : ℝ) (hu : Tendsto u atTop (𝓝 t)) :
    Tendsto (fun n => μ (φ n) (u n)) atTop (𝓝 (ν t)) := by
  have h0 : χ (t,0) = 1 := by rw [← hν t 0]; simp
  apply weak_convergence (fun n => μ (φ n) (u n)) (fun v => χ (t,v))
    (hχ.comp (continuous_const.prodMk continuous_id)) h0 _ (ν t) (hν t)
  intro v
  exact moving_frequency_limit (fun n (z : ℝ × ℝ) => charFun (μ n z.1 : Measure ℝ) z.2)
    he φ hφ χ hc (t,v) (fun n => (u n,v)) (hu.prodMk_nhds tendsto_const_nhds)

#print axioms continuous_probability_curve
#print axioms represented_curve
#print axioms moving_time_convergence
end
end UnifiedTheory.Audit.KFCausalTemporalProbabilityRepresentation
