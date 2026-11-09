/- The full response is the quadratic form of the actual B H-H B
commutator. This removes the domain ambiguity from the uniform-estimate
problem. The general estimate remains open; the existing neutral-vacuum
uniform estimate transfers to the actual commutator with the same constant. -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockLimit
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredUniformStrongResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongCommutatorResponse
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit (inputHamiltonian momentumHamiltonian strong_pairing)
open KFCausalCorrelatedClusteredHamiltonianClockLimit (hamiltonianDerivative hamiltonian_clock_graph)
open KFCausalCorrelatedClusteredStrongResponseLimit (fullEnergy fullResponse energy_identity response_identity)
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_selfAdjoint)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "Hψ" => inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t
local notation "BHψ" => hamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t
local notation "HBψ" => momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t

def commutator : Hilbert := BHψ-HBψ

theorem clock_hamiltonian_pairing : inner ℂ ψ BHψ = inner ℂ b Hψ :=
  (KFCausalOrderedOperatorComposition.selfAdjoint_graph_pairing (pureMomentum ε hε h)
    (pure_selfAdjoint ε hε h hh) ψ b Hψ BHψ
    (KFCausalCorrelatedClusteredPureMomentumLimit.limiting_graph f ε h a p hε hh ha)
    (hamiltonian_clock_graph f ε h a p hε hh ha hb mass2 quartic vacuum t)).symm

theorem commutator_im :
    (inner ℂ ψ (commutator f ε h a p hε hh ha hb mass2 quartic vacuum t)).im =
      -2*(inner ℂ Hψ b).im := by
  rw [commutator,inner_sub_right,Complex.sub_im,clock_hamiltonian_pairing,← strong_pairing]
  have he : (inner ℂ b Hψ).im = -(inner ℂ Hψ b).im := inner_im_symm (𝕜 := ℂ) b Hψ
  rw [he]
  ring

theorem response_commutator_identity :
    fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t =
      (1/h)*(inner ℂ ψ (commutator f ε h a p hε hh ha hb mass2 quartic vacuum t)).im := by
  rw [response_identity,commutator_im]
  ring

theorem response_commutator_norm_bound :
    |fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t| ≤
      (1/|h|)*(‖ψ‖*‖commutator f ε h a p hε hh ha hb mass2 quartic vacuum t‖) := by
  rw [response_commutator_identity,abs_mul,abs_div,abs_one]
  exact mul_le_mul_of_nonneg_left
    ((Complex.abs_im_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)) (by positivity)

theorem lower_bound_iff (C : ℝ) :
    -(C/ε)*fullEnergy f ε h a p hε hh ha hb mass2 quartic vacuum t ≤
      fullResponse f ε h a p hε hh ha hb mass2 quartic vacuum t ↔
    -(C/ε)*(inner ℂ Hψ ψ).re ≤
      (1/h)*(inner ℂ ψ (commutator f ε h a p hε hh ha hb mass2 quartic vacuum t)).im := by
  rw [energy_identity,response_commutator_identity]

omit f ε h a p hε hh ha hb mass2 quartic vacuum t in
theorem exists_uniform_vacuum_commutator :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (d : Fin m → ℕ) (z : Fin m → ℂ)
      (ε h : ℝ) (a : Fin m → ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i)
      (hb : |h| ≤ Real.pi*ε/3) (t : ℝ),
      let f := KFCausalCorrelatedClusteredVacuumUniformLimit.family d z;
      let u₀ := KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a (fun _ => 0) hε hh ha;
      let v₀ := inputHamiltonian f ε h a (fun _ => 0) hε hh ha hb 1 1 1 t;
      -((C+2)/ε)*(inner ℂ v₀ u₀).re ≤
        (1/h)*(inner ℂ u₀ (commutator f ε h a (fun _ => 0) hε hh ha hb 1 1 1 t)).im := by
  obtain ⟨C,hC,hbound⟩ := KFCausalCorrelatedClusteredUniformStrongResponse.exists_uniform_full_response
  refine ⟨C,hC,?_⟩
  intro m d z ε h a hε hh ha hb t
  have hi := hbound m d z ε h a hε hh ha hb t
  rwa [energy_identity,response_commutator_identity] at hi

#print axioms clock_hamiltonian_pairing
#print axioms commutator_im
#print axioms response_commutator_identity
#print axioms response_commutator_norm_bound
#print axioms lower_bound_iff
#print axioms exists_uniform_vacuum_commutator
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongCommutatorResponse
