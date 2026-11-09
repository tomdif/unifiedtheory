/- Every original finite sourced packet belongs to the square domain of
the full interacting averaged Hamiltonian. All eight projected component
outputs have independently constructed Hamiltonian domains. -/
import UnifiedTheory.Audit.KFCausalFiniteKineticHamiltonianColumns

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquare
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteSecondHamiltonianColumns (second)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum t : ℝ)
local notation "hb₀" => KFCausalSingleGaussianMixedSquare.original_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "H" => hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t

theorem projected_second_domain (j : Fin 8) :
    zeroProjection h hh (second n ε h a w p C b P hε ha hh hw hb j) ∈ (H).domain := by
  fin_cases j
  · exact KFCausalFiniteSecondHamiltonianColumns.projected_clock_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
  · exact KFCausalFiniteKineticHamiltonianColumns.projected_finite_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t 0
  · exact KFCausalFiniteKineticHamiltonianColumns.projected_finite_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t 1
  · exact KFCausalFiniteKineticHamiltonianColumns.projected_finite_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t 2
  · exact KFCausalFiniteKineticHamiltonianColumns.projected_finite_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t 3
  · exact KFCausalFiniteSecondHamiltonianColumns.projected_potential_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t (some 0)
  · exact KFCausalFiniteSecondHamiltonianColumns.projected_potential_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t (some 1)
  · exact KFCausalFiniteSecondHamiltonianColumns.projected_potential_domain
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t none

def firstOutput : Hilbert :=
  KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput
    n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum t

theorem first_graph :
    (ψ,firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈ (H).graph :=
  KFCausalReciprocalNeutralStrongHamiltonian.hamiltonian_graph
    n ε h a w p C b P hε ha hh hw hb₀ mass2 quartic vacuum t

theorem output_domain :
    firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t ∈ (H).domain := by
  unfold firstOutput
  rw [KFCausalFiniteSecondHamiltonianColumns.hamiltonianOutput_sum
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t]
  apply (H).domain.sum_mem
  intro j _
  exact (H).domain.smul_mem _
    (projected_second_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t j)

def secondOutput : Hilbert :=
  H ⟨firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t,
    output_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩

theorem second_graph :
    (firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t,
      secondOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈ (H).graph :=
  (H).mem_graph ⟨_,output_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩

theorem square_graph :
    (ψ,secondOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈
      (composition H H).graph :=
  (composition_graph _ _ _ _).mpr
    ⟨_,first_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t,
      second_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩

include hb in
theorem square_domain : ψ ∈ (composition H H).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (square_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)

theorem hamiltonian_action_domain :
    H ⟨ψ,LinearPMap.mem_domain_of_mem_graph
      (first_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)⟩ ∈ (H).domain := by
  have he := (H).mem_graph_snd_inj'
    ((H).mem_graph ⟨ψ,LinearPMap.mem_domain_of_mem_graph
      (first_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)⟩)
    (first_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) rfl
  dsimp only at he
  rw [he]
  exact output_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t

#print axioms projected_second_domain
#print axioms first_graph
#print axioms output_domain
#print axioms second_graph
#print axioms square_graph
#print axioms square_domain
#print axioms hamiltonian_action_domain
end
end UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquare
