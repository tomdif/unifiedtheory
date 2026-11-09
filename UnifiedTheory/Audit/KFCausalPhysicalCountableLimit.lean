/- One cutoff subsequence converges weakly in the common form space at
all times in any prescribed countable family. The unsmoothed physical
trajectories have the same embedded limits. This is not yet an all-time
solution of the unbounded Schrodinger equation. -/
import UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
import UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
import UnifiedTheory.Audit.KFCausalWeakLimitTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalPhysicalCountableLimit
noncomputable section
open Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalPhysicalFormTransport
open UnifiedTheory.Audit.KFCausalPhysicalFormGeometry
open UnifiedTheory.Audit.KFCausalPhysicalFormTimeControl
open UnifiedTheory.Audit.KFCausalPhysicalYosidaDynamics
open UnifiedTheory.Audit.KFCausalPhysicalSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalPhysicalFormWindowBound
open UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
open UnifiedTheory.Audit.KFCausalWeakLimitTransport

def cutoff (n : ℕ) : ℝ := (n:ℝ)+1

theorem cutoff_pos (n : ℕ) : 0 < cutoff n := by unfold cutoff; positivity

theorem cutoff_tendsto : Tendsto cutoff atTop atTop := by
  simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,cutoff] using
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 1)

theorem smoothed_defect_tendsto (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s t : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) :
    Tendsto (fun n => ‖dynamics ε hε hbar hh mass2 quartic vacuum (cutoff n) (cutoff_pos n) s t
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)-
      smoothedState ε hε hbar hh mass2 quartic vacuum (cutoff n) (cutoff_pos n) s t
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)‖) atTop (𝓝 0) :=
  norm_error_tendsto_zero cutoff_tendsto
    (fun n => smoothed_uniform_defect_bound ε hε hbar hh mass2 quartic vacuum (cutoff n) (cutoff_pos n) s t w)

/-- Actual countable-time compactness, with no limit supplied as a hypothesis. -/
theorem exists_countable_limit (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ Real.pi*ε) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh mass2 quartic vacuum 0) {I : Type*} [Countable I] (τ : I → ℝ) :
    ∃ v : I → FormSpace ε hε hbar hh mass2 quartic vacuum 0,
      (∀ i, ‖v i‖ ≤ windowRadius ε hε hbar hh mass2 quartic vacuum s |τ i| w) ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ i y, Tendsto (fun n => inner ℂ
        (smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s (τ i)
          (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop (𝓝 (inner ℂ (v i) y))) ∧
      (∀ i y, Tendsto (fun n => inner ℂ
        (dynamics ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s (τ i)
          (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop
        (𝓝 (inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 (v i)) y))) ∧
      (∀ i, ‖embedding ε hε hbar hh mass2 quartic vacuum 0 (v i)‖ ≤ ‖embedding ε hε hbar hh mass2 quartic vacuum 0 w‖) := by
  obtain ⟨v,hv,φ,hφ,hlim⟩ := countable_weak_subsequence
    (fun n i => smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff n) (cutoff_pos n) s (τ i)
      (embedding ε hε hbar hh mass2 quartic vacuum 0 w))
    (fun i => windowRadius ε hε hbar hh mass2 quartic vacuum s |τ i| w)
    (fun n i => smoothed_window_norm ε hε hbar hh mass2 quartic vacuum (cutoff n) (cutoff_pos n)
      s |τ i| (τ i) (abs_nonneg _) le_rfl w)
  have hphys (i : I) : ∀ y, Tendsto (fun n => inner ℂ
      (dynamics ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s (τ i)
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) y) atTop
      (𝓝 (inner ℂ (embedding ε hε hbar hh mass2 quartic vacuum 0 (v i)) y)) := by
    have he := (smoothed_defect_tendsto ε hε hbar hh mass2 quartic vacuum s (τ i) w).comp hφ.tendsto_atTop
    have hm := weak_map (E := FormSpace ε hε hbar hh mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh mass2 quartic vacuum 0)
      (u := fun n => smoothedLift ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s (τ i)
        (embedding ε hε hbar hh mass2 quartic vacuum 0 w)) (x := v i) (hlim i)
    exact weak_limit_of_norm_error (H := Hilbert) he hm
  refine ⟨v,hv,φ,hφ,hlim,hphys,?_⟩
  intro i
  exact weak_norm_le
    (fun n => (dynamics_norm ε hε hbar hh mass2 quartic vacuum (cutoff (φ n)) (cutoff_pos (φ n)) s (τ i) _).le)
    (hphys i)

#print axioms cutoff_tendsto
#print axioms smoothed_defect_tendsto
#print axioms exists_countable_limit

end
end UnifiedTheory.Audit.KFCausalPhysicalCountableLimit
