/- The existing finite-family Hamiltonian output uses exactly the natural
second outputs already constructed in the clock and potential columns.
Graph uniqueness identifies them without assumptions on composite closure. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
import UnifiedTheory.Audit.KFCausalFinitePotentialHamiltonianDomain
import UnifiedTheory.Audit.KFCausalClockWeightedOriginalHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalFiniteSecondHamiltonianColumns
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalReciprocalNeutralMatterSpectral (matterIndex)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)

def potentialIndex : Option (Fin 2) → Fin 8
  | none => 7
  | some j => matterIndex j

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
local notation "hb₀" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw

def second (j : Fin 8) : Hilbert :=
  KFCausalReciprocalNeutralStrongHamiltonian.seconds n ε h a w p C b P hε ha hh hw hb₀ j

theorem second_graph (j : Fin 8) :
    (ψ,second n ε h a w p C b P hε ha hh hw hb j) ∈ (component ε hε h j).graph := by
  have hs := (component ε hε h j).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralSecondFactors.second_graph
        ε (a i) h (w i) hε (ha i) hh (hw i) hb₀ (C i) (p i) (b i) (P i) j)
  simpa only [second,KFCausalReciprocalNeutralStrongHamiltonian.seconds,state,← prod_mk_sum] using hs

theorem potential_second_eq (i : Option (Fin 2)) :
    second n ε h a w p C b P hε ha hh hw hb (potentialIndex i)=
      KFCausalFiniteOuterClockVacuumMatter.firstOutput n ε h a w p C b P hε ha hh hw hb i := by
  have hg : (ψ,KFCausalFiniteOuterClockVacuumMatter.firstOutput
      n ε h a w p C b P hε ha hh hw hb i) ∈ (component ε hε h (potentialIndex i)).graph := by
    cases i with
    | none => exact KFCausalFiniteOuterClockVacuumMatter.first_graph n ε h a w p C b P hε ha hh hw hb none
    | some j => exact KFCausalFiniteOuterClockVacuumMatter.first_graph n ε h a w p C b P hε ha hh hw hb (some j)
  exact (component ε hε h (potentialIndex i)).mem_graph_snd_inj'
    (second_graph n ε h a w p C b P hε ha hh hw hb (potentialIndex i)) hg rfl

theorem clock_second_eq :
    second n ε h a w p C b P hε ha hh hw hb 0=
      KFCausalClockWeightedOriginalHamiltonian.state ε h hε hh hb n a w p C b P ha hw false := by
  have hs := second_graph n ε h a w p C b P hε ha hh hw hb 0
  rw [component,KFCausalClockMixedClockGraph.actual_clockSecond_eq] at hs
  exact (KFCausalClockFloorClockOperator.clockOperator ε hε).mem_graph_snd_inj' hs
    (KFCausalClockWeightedOriginalHamiltonian.clock_graph ε h hε hh hb n a w p C b P ha hw) rfl

theorem projected_potential_domain (mass2 quartic vacuum t : ℝ) (i : Option (Fin 2)) :
    zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb (potentialIndex i)) ∈
      (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).domain := by
  rw [potential_second_eq]
  exact KFCausalFinitePotentialHamiltonianDomain.projected_hamiltonian_domain
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t i

theorem projected_clock_domain (mass2 quartic vacuum t : ℝ) :
    zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb 0) ∈
      (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).domain := by
  rw [clock_second_eq]
  exact KFCausalClockWeightedOriginalHamiltonian.projected_hamiltonian_domain
    ε h hε hh hb n a w p C b P ha hw false mass2 quartic vacuum t (hamiltonian_strip ε h hε hb)

theorem hamiltonianOutput_sum (mass2 quartic vacuum t : ℝ) :
    KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput
      n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum t =
    ∑ j, (star (energyWeight mass2 quartic vacuum t j)*energyWeight mass2 quartic vacuum t j) •
      zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb j) := by
  simp only [KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput,
    KFCausalJointSecondPairing.secondWeighted,map_sum,map_smul,second]

#print axioms second_graph
#print axioms potential_second_eq
#print axioms clock_second_eq
#print axioms projected_potential_domain
#print axioms projected_clock_domain
#print axioms hamiltonianOutput_sum
end
end UnifiedTheory.Audit.KFCausalFiniteSecondHamiltonianColumns
