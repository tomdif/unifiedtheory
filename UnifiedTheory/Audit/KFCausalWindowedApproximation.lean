/- Actual positive phase-space probabilities approximate every canonical
characteristic of normalized physical states. The selected shrinking
windows and the approximation error are independent of the input state. -/
import UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
import UnifiedTheory.Audit.KFCausalSemiclassicalWindow

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalWindowedApproximation
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block BlockHilbert)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra
open UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates (frequency)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (law phase)
open UnifiedTheory.Audit.KFCausalSemiclassicalWindow

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem exists_state_uniform_approximation (h : ℕ → ℝ) (hz : Tendsto h atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ k f, ‖f‖ = 1 → IsProbabilityMeasure (law (h (φ k)) f (unitWindow 6 k))) ∧
      ∀ z : Frequency (X := Configuration), ∀ η : ℝ, 0 < η →
        ∃ N : ℕ, ∀ k ≥ N, ∀ f : Hilbert, ‖f‖ = 1 →
          ‖(∫ x, phase z x ∂law (h (φ k)) f (unitWindow 6 k))-characteristic volume (h (φ k)) f z‖ < η := by
  obtain ⟨φ,hφ,ht⟩ := translation_subsequence 6 h hz
  refine ⟨φ,hφ,?_,?_⟩
  · intro k f hf
    exact KFCausalPhysicalWindowedLaw.law_probability _ f _ hf (unitWindow_norm 6 k)
  · intro z η hη
    have hc := characteristic_limit 6 h φ ht (KFCausalWindowedCanonicalTests.reflected 6 (frequency z))
    obtain ⟨N,hN⟩ := eventually_atTop.mp (Metric.tendsto_nhds.mp hc η hη)
    refine ⟨N,fun k hk f hf => ?_⟩
    have he := KFCausalPhysicalWindowedLaw.characteristic_error (h (φ k)) f (unitWindow 6 k) z
    rw [hf,one_pow,one_mul] at he
    exact he.trans_lt (by simpa only [dist_eq_norm] using hN k hk)

theorem error_tendsto (h : ℕ → ℝ) (φ : ℕ → ℕ)
    (ha : ∀ z : Frequency (X := Configuration), ∀ η : ℝ, 0 < η →
      ∃ N : ℕ, ∀ k ≥ N, ∀ f : Hilbert, ‖f‖ = 1 →
        ‖(∫ x, phase z x ∂law (h (φ k)) f (unitWindow 6 k))-characteristic volume (h (φ k)) f z‖ < η)
    (f : ℕ → Hilbert) (hf : ∀ k, ‖f k‖ = 1) (z : Frequency (X := Configuration)) :
    Tendsto (fun k => (∫ x, phase z x ∂law (h (φ k)) (f k) (unitWindow 6 k))-
      characteristic volume (h (φ k)) (f k) z) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro η hη
  obtain ⟨N,hN⟩ := ha z η hη
  filter_upwards [eventually_ge_atTop N] with k hk
  simpa only [dist_zero_right] using hN k hk (f k) (hf k)

#print axioms exists_state_uniform_approximation
#print axioms error_tendsto

end
end UnifiedTheory.Audit.KFCausalWindowedApproximation
