/- A proved family of normalized, charge-zero, averaged-energy states
escapes every bounded log-clock region as its clock defect vanishes.
Every member has finite clock energy, but the clock energy diverges along
the family. The actual evolution preserves small defect for a positive
state-dependent interval only; no uniform interval is asserted. -/
import UnifiedTheory.Audit.KFCausalClockFloorSmallDefectStates
import UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
import UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorLargeClockFamily
noncomputable section
open Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorDefectLocalization
open UnifiedTheory.Audit.KFCausalClockFloorDefectEnergy
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf
open UnifiedTheory.Audit.KFCausalClockFloorEnergyClockDomain
open UnifiedTheory.Audit.KFCausalClockFloorSmallDefectStates
open UnifiedTheory.Audit.KFCausalStandingChargeOperator
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (hamiltonian_bound)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEnergy (energyOperator)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolution
open UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection (evolution_zero_sector)

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : hbar ≠ 0)
  (hbound : |hbar| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum : ℝ)

local notation "U" => evolution ε hε hbar hh hbound mass2 quartic vacuum
local notation "D" => defectOperator ε hε
local notation "E" => energyOperator ε hε hbar (hamiltonian_bound ε hbar hbound)
  hh mass2 quartic vacuum

theorem exists_admissible_large_clock_family (s : ℝ) :
    ∃ f g : ℕ → Hilbert,
      (∀ n, ‖f n‖ = 1 ∧ f n ∈ zeroSector hbar hh ∧ f n ∈ (E s).domain ∧
        (f n,0) ∈ (standingCharge hbar hh).graph ∧ (f n,g n) ∈ (clockHalf ε).graph) ∧
      Tendsto (fun n => ‖D (f n)‖) atTop (𝓝 0) ∧
      (∀ S : ℝ, Tendsto (fun n => ‖lowProjection S (f n)‖) atTop (𝓝 0)) ∧
      Tendsto (fun n => ‖g n‖) atTop atTop := by
  have hex := exists_unit_zero_energy_defect_sequence ε hε hbar hh hbound mass2 quartic vacuum s
  obtain ⟨f,hf,hd⟩ := hex
  have hc (n : ℕ) : f n ∈ (clockHalf ε).domain :=
    zero_averaged_energy_clock_domain ε hε hbar (hamiltonian_bound ε hbar hbound)
      mass2 quartic vacuum s hh (f n) (hf n).2.1 (hf n).2.2.1
  let g : ℕ → Hilbert := fun n => clockHalf ε ⟨f n,hc n⟩
  have hg (n : ℕ) : (f n,g n) ∈ (clockHalf ε).graph := (clockHalf ε).mem_graph ⟨f n,hc n⟩
  refine ⟨f,g,fun n => ⟨(hf n).1,(hf n).2.1,(hf n).2.2.1,(hf n).2.2.2,hg n⟩,
    hd,fun S => lowProjection_tendsto_zero atTop ε hε f hd S,?_⟩
  exact defect_limit_forces_clock_norm_atTop atTop ε hε f g hg (fun n => (hf n).1) hd

theorem defect_short_time_control (s : ℝ) (f : Hilbert) (δ : ℝ) (hf : ‖D f‖ < δ) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t-s| < ρ → ‖D (U s t f)‖ < δ := by
  have hi : U s s f = f := congrArg (fun A : Hilbert →L[ℂ] Hilbert => A f)
    (evolution_initial ε hε hbar hh hbound mass2 quartic vacuum s)
  have hc : Continuous (fun t : ℝ => ‖D (U s t f)‖) :=
    ((D).continuous.comp (evolution_strong_continuous ε hε hbar hh hbound mass2 quartic vacuum s f)).norm
  have hev : ∀ᶠ t in 𝓝 s, ‖D (U s t f)‖ < δ :=
    hc.continuousAt.tendsto.eventually (gt_mem_nhds (by rwa [hi]))
  obtain ⟨ρ,hρ,hball⟩ := Metric.eventually_nhds_iff.mp hev
  exact ⟨ρ,hρ,fun t ht => hball (by simpa only [Real.dist_eq] using ht)⟩

/-- Genuine energy-admissible initial data and actual charge-preserving
unitary evolution. The interval may depend on the state and tolerance. -/
theorem exists_admissible_small_defect_interval (s δ : ℝ) (hδ : 0 < δ) :
    ∃ f : Hilbert, ‖f‖ = 1 ∧ f ∈ zeroSector hbar hh ∧ f ∈ (E s).domain ∧
      (∀ t : ℝ, ‖U s t f‖ = 1 ∧ (U s t f,0) ∈ (standingCharge hbar hh).graph) ∧
      ∃ ρ : ℝ, 0 < ρ ∧ ∀ t : ℝ, |t-s| < ρ → ‖D (U s t f)‖ < δ := by
  have hex := exists_unit_zero_energy_small_defect ε hε hbar hh hbound mass2 quartic vacuum s δ hδ
  obtain ⟨f,hf,hz,he,_,hd⟩ := hex
  refine ⟨f,hf,hz,he,fun t => ⟨?_,?_⟩,defect_short_time_control ε hε hbar hh hbound mass2 quartic vacuum s f δ hd⟩
  · exact (evolution_norm ε hε hbar hh hbound mass2 quartic vacuum s t f).trans hf
  · exact (standingCharge_zero_iff hbar hh _).mpr
      (evolution_zero_sector ε hε hbar hh hbound mass2 quartic vacuum s t f hz)

#print axioms exists_admissible_large_clock_family
#print axioms defect_short_time_control
#print axioms exists_admissible_small_defect_interval

end
end UnifiedTheory.Audit.KFCausalClockFloorLargeClockFamily
