/- The actual normalized clock-commutator extension has nonincreasing
error along the constructed averaged Hamiltonian evolution. This uses
the bounded extension on all L2 states; preservation of the unbounded
common composition domain by that evolution is not asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorQuantumClockCommutator
import UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumClockEvolution
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorQuantumClockCommutator
open UnifiedTheory.Audit.KFCausalClockFloorDefectMonotonicity
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hne : hbar ≠ 0)
  (hh : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)
local notation "U" => evolution ε hε hbar hne hh mass2 quartic vacuum
local notation "N" => normalizedCommutator ε hε hbar

theorem evolution_clock_error_antitone (s : ℝ) (f : Hilbert) :
    Antitone (fun t => ‖U s t f-N (U s t f)‖) := by
  simpa only [normalizedCommutator_error_apply ε hε hbar hne] using
    evolution_defect_antitone ε hε hbar hne hh mass2 quartic vacuum s f

theorem evolution_clock_error_le_initial (s t : ℝ) (hst : s ≤ t) (f : Hilbert) :
    ‖U s t f-N (U s t f)‖ ≤ ‖f-N f‖ := by
  simpa only [normalizedCommutator_error_apply ε hε hbar hne] using
    evolution_defect_le_initial ε hε hbar hne hh mass2 quartic vacuum s t hst f

theorem exists_unit_zero_all_future_small_clock_error (s δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧
      f ∈ (KFCausalClockFloorAveragedEnergy.energyOperator ε hε hbar
        (KFCausalClockFloorCoherentCommonDomain.hamiltonian_bound ε hbar hh)
        hne mass2 quartic vacuum s).domain ∧
      ∀ t, s ≤ t → ‖U s t f‖ = 1 ∧
        (U s t f,0) ∈ (KFCausalStandingChargeOperator.standingCharge hbar hne).graph ∧
        ‖U s t f-N (U s t f)‖ < δ := by
  simpa only [normalizedCommutator_error_apply ε hε hbar hne] using
    exists_unit_zero_all_future_small_defect ε hε hbar hne hh mass2 quartic vacuum s δ hδ

#print axioms evolution_clock_error_antitone
#print axioms evolution_clock_error_le_initial
#print axioms exists_unit_zero_all_future_small_clock_error

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumClockEvolution
