/- Both actual operator compositions are defined on the full finite joint
neutral/reciprocal family. Their difference has exactly the existing full
response as its commutator expectation. No uniform bound or trajectory
expectation derivative is inferred from the domain construction. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonianPureDomain
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalStrongCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongCommutator
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian hamiltonian_selfAdjoint)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3) (mass2 quartic vacuum t : ℝ)
local notation "B" => pureMomentum ε hε h
local notation "H" => hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t
local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Bψ" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C b P hε ha hh hw
local notation "Hψ" => KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput
  n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t
local notation "HBψ" => KFCausalReciprocalNeutralMomentumStrongHamiltonian.hamiltonianOutput
  n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t

def momentumAfterHamiltonian : Hilbert := B ⟨Hψ,
  KFCausalReciprocalNeutralHamiltonianPureDomain.output_domain n ε h a w p C b P hε ha hh hw hb
    mass2 quartic vacuum t⟩
def commutator : Hilbert := HBψ-momentumAfterHamiltonian n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t

theorem momentum_after_graph :
    (Hψ,momentumAfterHamiltonian n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈ (B).graph :=
  (B).mem_graph ⟨Hψ,KFCausalReciprocalNeutralHamiltonianPureDomain.output_domain n ε h a w p C b P
    hε ha hh hw hb mass2 quartic vacuum t⟩

theorem momentum_hamiltonian_graph :
    (ψ,momentumAfterHamiltonian n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈
      (composition B H).graph :=
  (composition_graph B H _ _).mpr ⟨Hψ,
    KFCausalReciprocalNeutralStrongHamiltonian.hamiltonian_graph n ε h a w p C b P hε ha hh hw hb
      mass2 quartic vacuum t,
    momentum_after_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩

theorem both_composition_domains : ψ ∈ (composition H B).domain ∧ ψ ∈ (composition B H).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph
    (KFCausalReciprocalNeutralMomentumStrongHamiltonian.hamiltonian_momentum_graph n ε h a w p C b P
      hε ha hh hw hb mass2 quartic vacuum t),
   LinearPMap.mem_domain_of_mem_graph
    (momentum_hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)⟩

theorem expectation_identity :
    ((Complex.I/(h:ℂ))*inner ℂ ψ (commutator n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)).re =
      KFCausalReciprocalNeutralHamiltonian.fullResponse n ε h a w p C b P hε ha hh hw
        (original_strip ε h hε hb) mass2 quartic vacuum t := by
  rw [KFCausalReciprocalNeutralStrongResponse.response_identity n ε h a w p C b P hε ha hh hw hb]
  exact KFCausalReciprocalStrongCommutator.commutator_response H B
    (hamiltonian_selfAdjoint ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t)
    (pure_selfAdjoint ε hε h hh) ψ Hψ Bψ HBψ _ h
    (KFCausalReciprocalNeutralStrongHamiltonian.hamiltonian_graph n ε h a w p C b P hε ha hh hw hb
      mass2 quartic vacuum t)
    (KFCausalReciprocalNeutralSuperposition.momentum_graph n ε h a w p C b P hε ha hh hw)
    (KFCausalReciprocalNeutralMomentumStrongHamiltonian.hamiltonian_graph n ε h a w p C b P hε ha hh hw hb
      mass2 quartic vacuum t)
    (momentum_after_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)

#print axioms momentum_after_graph
#print axioms momentum_hamiltonian_graph
#print axioms both_composition_domains
#print axioms expectation_identity
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongCommutator
