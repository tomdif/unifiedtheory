/- Countable-time compactness inside every strictly increasing cutoff subsequence.
The extraction is constructed from the actual averaged approximations. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
import UnifiedTheory.Audit.KFCausalWeakLimitTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceCompactness
noncomputable section
open Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
open UnifiedTheory.Audit.KFCausalWeakLimitTransport

/-- Actual countable-time compactness, with no limit supplied as a hypothesis. -/
theorem exists_countable_sublimit (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (σ : ℕ → ℕ) (hσ : StrictMono σ) {I : Type*} [Countable I] (τ : I → ℝ) :
    ∃ v : I → FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0,
      (∀ i, ‖v i‖ ≤ windowRadius ε hε hbar hh hbound mass2 quartic vacuum s |τ i| w) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i y, Tendsto (fun n => inner ℂ
        (smoothedLift ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s (τ i)
          (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) y) atTop (𝓝 (inner ℂ (v i) y))) ∧
      (∀ i y, Tendsto (fun n => inner ℂ
        (dynamics ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s (τ i)
          (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) y) atTop
        (𝓝 (inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (v i)) y))) ∧
      (∀ i, ‖embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (v i)‖ ≤ ‖embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w‖) := by
  have hc := countable_weak_subsequence
    (fun n i => smoothedLift ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ n)) (cutoff_pos (σ n)) s (τ i)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w))
    (fun i => windowRadius ε hε hbar hh hbound mass2 quartic vacuum s |τ i| w)
    (fun n i => smoothed_window_norm ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ n)) (cutoff_pos (σ n))
      s |τ i| (τ i) (abs_nonneg _) le_rfl w)
  rcases hc with ⟨v,hv,φ,hφ,hlim⟩
  have hphys (i : I) : ∀ y, Tendsto (fun n => inner ℂ
      (dynamics ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s (τ i)
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) y) atTop
      (𝓝 (inner ℂ (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 (v i)) y)) := by
    have he := (smoothed_defect_tendsto ε hε hbar hh hbound mass2 quartic vacuum s (τ i) w).comp (hσ.comp hφ).tendsto_atTop
    have hm := weak_map (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
      (u := fun n => smoothedLift ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s (τ i)
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (x := v i) (hlim i)
    exact weak_limit_of_norm_error (H := Hilbert) he hm
  refine ⟨v,hv,φ,hφ,hlim,hphys,?_⟩
  intro i
  exact weak_norm_le
    (fun n => (dynamics_norm ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s (τ i) _).le)
    (hphys i)


#print axioms exists_countable_sublimit

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceCompactness
