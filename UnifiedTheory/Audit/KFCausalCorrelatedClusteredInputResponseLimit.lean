/- Faithfulness of the ordered exponential makes the local full-clock
response bound applicable exactly when the limiting physical input is
nonzero. The bound still depends on the fixed finite family. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputGraphLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredNonzeroResponseLimit
import UnifiedTheory.Audit.KFCausalClockFloorVacuumOutputFaithful

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputResponseLimit
noncomputable section
open Filter
open scoped Topology
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredInputGraphLimit
open KFCausalCorrelatedClusteredPotentialGraphLimit (limitingOutput)
open KFCausalCorrelatedClusteredPhysicalClockLimit (finiteEnergy finiteResponse limitingEnergy limitingResponse)
open KFCausalClockFloorTrialSpectralDomain (orderedExponential)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "u" => limitingState f ε h a p hε hh ha
local notation "V" => limitingOutput f ε h a p hε hh hb ha
local notation "E" => finiteEnergy f ε h a p hε hh hb ha
local notation "R" => finiteResponse f ε h a p hε hh hb ha
local notation "E₀" => limitingEnergy f ε h a p
local notation "R₀" => limitingResponse f ε h a p

theorem output_zero_iff_state_zero : V 0 = 0 ↔ u = 0 := by
  constructor
  · intro hv
    have hg := limiting_ordered_graph f ε h a p hε hh ha hb
    rw [hv] at hg
    exact KFCausalClockFloorVacuumOutputFaithful.ordered_graph_zero ε hε h u hg
  · intro hu
    exact (orderedExponential ε hε h).graph_fst_eq_zero_snd
      (limiting_ordered_graph f ε h a p hε hh ha hb) hu

include hb in
theorem limiting_energy_positive_iff : 0 < E₀ ↔ u ≠ 0 := by
  rw [KFCausalCorrelatedClusteredNonzeroResponseLimit.limiting_energy_positive_iff f ε h a p hε hh hb ha]
  exact not_congr (output_zero_iff_state_zero f ε h a p hε hh ha hb)

theorem relativeResponse_tendsto (hu : u ≠ 0) :
    Tendsto (fun δ => R δ/E δ) (𝓝[>] 0) (𝓝 (R₀/E₀)) :=
  KFCausalCorrelatedClusteredNonzeroResponseLimit.relativeResponse_tendsto f ε h a p hε hh hb ha
    (fun hv => hu ((output_zero_iff_state_zero f ε h a p hε hh ha hb).mp hv))

theorem local_relative_bound (hu : u ≠ 0) :
    ∀ᶠ δ : ℝ in 𝓝[>] 0, |R δ| ≤ (|R₀/E₀|+1)*E δ :=
  KFCausalCorrelatedClusteredNonzeroResponseLimit.local_relative_bound f ε h a p hε hh hb ha
    (fun hv => hu ((output_zero_iff_state_zero f ε h a p hε hh ha hb).mp hv))

#print axioms output_zero_iff_state_zero
#print axioms limiting_energy_positive_iff
#print axioms relativeResponse_tendsto
#print axioms local_relative_bound
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredInputResponseLimit
