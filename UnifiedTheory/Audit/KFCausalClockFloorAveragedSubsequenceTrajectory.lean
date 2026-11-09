/- Every cutoff subsequence has a further extraction represented by the
already verified all-time weak-trajectory type. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceCompactness
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
import UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakPairing
import UnifiedTheory.Audit.KFCausalWeakLimitFromTests
import UnifiedTheory.Audit.KFCausalRationalCauchyExtension
import UnifiedTheory.Audit.KFCausalPairingCauchyTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 100000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceTrajectory
noncomputable section
open Filter TopologicalSpace
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSmoothedTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormWindowBound
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakPairing
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceCompactness
open UnifiedTheory.Audit.KFCausalHilbertWeakSubsequence
open UnifiedTheory.Audit.KFCausalWeakLimitTransport
open UnifiedTheory.Audit.KFCausalWeakLimitFromTests
open UnifiedTheory.Audit.KFCausalRationalCauchyExtension
open UnifiedTheory.Audit.KFCausalPairingCauchyTransfer

/-- The certificate is constructed from the concrete cutoff trajectories. -/
theorem exists_subsequence_trajectory (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0) (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ V : WeakTrajectory ε hε hbar hh hbound mass2 quartic vacuum s w, V.subsequence = σ ∘ φ := by
  have hcount := exists_countable_sublimit ε hε hbar hh hbound mass2 quartic vacuum s w σ hσ
    (fun q : ℚ => (q:ℝ))
  rcases hcount with ⟨v,_,φ,hφ,_,hphys,_⟩
  have hc (t : ℝ) (y : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) : CauchySeq (fun n => inner ℂ
      (dynamics ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y)) := by
    apply rational_cauchy_extension (fun n z => inner ℂ
      (dynamics ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s z
        (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y))
    · intro T hT
      refine ⟨pairingBound ε hε hbar hh hbound mass2 quartic vacuum s T w y,pairingBound_nonneg ε hε hbar hh hbound mass2 quartic vacuum s T w y,?_⟩
      intro n x z hx hz
      rw [dist_eq_norm]
      exact weak_pairing_lipschitz ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n)))
        s T z x hT hz hx w y
    · intro q
      exact (hphys q (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y)).cauchySeq
  have hex (t : ℝ) : ∃ x : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0,
      ‖x‖ ≤ windowRadius ε hε hbar hh hbound mass2 quartic vacuum s |t| w ∧
      ∀ y, Tendsto (fun n => inner ℂ
        (smoothedLift ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t
          (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) y) atTop (𝓝 (inner ℂ x y)) := by
    apply exists_weak_limit_of_test_cauchy (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0) (embedding_injective ε hε hbar hh hbound mass2 quartic vacuum 0)
    · intro n
      exact smoothed_window_norm ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n)))
        s |t| t (abs_nonneg _) le_rfl w
    · intro y
      have he := (smoothed_defect_tendsto ε hε hbar hh hbound mass2 quartic vacuum s t w).comp (hσ.comp hφ).tendsto_atTop
      exact pairing_cauchy_of_norm_error he (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 y) (hc t y)
  choose x hx hlim using hex
  refine ⟨φ,hφ,⟨σ ∘ φ,hσ.comp hφ,x,hx,hlim,?_⟩,rfl⟩
  intro t
  have he := (smoothed_defect_tendsto ε hε hbar hh hbound mass2 quartic vacuum s t w).comp (hσ.comp hφ).tendsto_atTop
  have hm := weak_map (E := FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) (H := Hilbert)
    (embedding ε hε hbar hh hbound mass2 quartic vacuum 0)
    (u := fun n => smoothedLift ε hε hbar hh hbound mass2 quartic vacuum (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t
      (embedding ε hε hbar hh hbound mass2 quartic vacuum 0 w)) (x := x t) (hlim t)
  exact weak_limit_of_norm_error (H := Hilbert) he hm

#print axioms exists_subsequence_trajectory

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceTrajectory
