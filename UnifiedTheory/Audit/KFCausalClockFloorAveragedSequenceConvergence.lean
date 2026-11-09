/- Strong convergence of the whole integer-cutoff sequence to the actual
averaged unbounded evolution. Every subsequence has a further all-time
limit; proved uniqueness identifies it, and density covers every L2 state. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceTrajectory
import UnifiedTheory.Audit.KFCausalDenseIsometryLimit
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormTransport
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormGeometry
open UnifiedTheory.Audit.KFCausalClockFloorAveragedCountableLimit
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedSubsequenceTrajectory
open UnifiedTheory.Audit.KFCausalClockFloorAveragedWeakNormConservation
open UnifiedTheory.Audit.KFCausalClockFloorAveragedFormFlow
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedYosidaDynamics
open UnifiedTheory.Audit.KFCausalDenseIsometryLimit

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "J" => embedding ε hε hbar hh hbound mass2 quartic vacuum 0
local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "F" => dynamics ε hε hbar hh hbound mass2 quartic vacuum

theorem exists_strong_subsequence (s : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0)
    (σ : ℕ → ℕ) (hσ : StrictMono σ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ t,
      Tendsto (fun n => F (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t (J w))
        atTop (𝓝 (U s t (J w))) := by
  have hv := exists_subsequence_trajectory ε hε hbar hh hbound mass2 quartic vacuum s w σ hσ
  rcases hv with ⟨φ,hφ,V,hseq⟩
  refine ⟨φ,hφ,?_⟩
  intro t
  have hl := cutoff_subsequence_strong_convergence ε hε hbar hh hbound mass2 quartic vacuum s w V t
  have he : U s t (J w) = J (V.formState t) :=
    (evolution_embedding ε hε hbar hh hbound mass2 quartic vacuum s t w).trans
      (congrArg (J) (formFlow_eq_of_witness ε hε hbar hh hbound mass2 quartic vacuum s t w V))
  have hl' : Tendsto (fun n => F (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t (J w))
      atTop (𝓝 (J (V.formState t))) := by
    simpa only [hseq,Function.comp_apply] using hl
  exact (congrArg (fun x : Hilbert => Tendsto
    (fun n => F (cutoff (σ (φ n))) (cutoff_pos (σ (φ n))) s t (J w)) atTop (𝓝 x)) he).mpr hl'

theorem cutoff_dynamics_strong_limit_form (s t : ℝ)
    (w : FormSpace ε hε hbar hh hbound mass2 quartic vacuum 0) :
    Tendsto (fun n => F (cutoff n) (cutoff_pos n) s t (J w)) atTop (𝓝 (U s t (J w))) := by
  apply tendsto_of_subseq_tendsto
  intro σ hσ
  obtain ⟨χ,_,hχ⟩ := strictMono_subseq_of_tendsto_atTop hσ
  have hs := exists_strong_subsequence ε hε hbar hh hbound mass2 quartic vacuum s w (σ ∘ χ) hχ
  rcases hs with ⟨φ,_,hφ⟩
  exact ⟨χ ∘ φ,hφ t⟩

theorem cutoff_dynamics_strong_limit (s t : ℝ) (f : Hilbert) :
    Tendsto (fun n => F (cutoff n) (cutoff_pos n) s t f) atTop (𝓝 (U s t f)) := by
  apply tendsto_of_dense_isometries (J) (embedding_dense ε hε hbar hh hbound mass2 quartic vacuum 0)
    (fun n => F (cutoff n) (cutoff_pos n) s t) (U s t) _ (U s t).isometry atTop _ f
  · intro n
    exact AddMonoidHomClass.isometry_of_norm (F (cutoff n) (cutoff_pos n) s t).toLinearMap
      (dynamics_norm ε hε hbar hh hbound mass2 quartic vacuum (cutoff n) (cutoff_pos n) s t)
  · exact cutoff_dynamics_strong_limit_form ε hε hbar hh hbound mass2 quartic vacuum s t

#print axioms exists_strong_subsequence
#print axioms cutoff_dynamics_strong_limit_form
#print axioms cutoff_dynamics_strong_limit

end
end UnifiedTheory.Audit.KFCausalClockFloorAveragedSequenceConvergence
