/- Actual mixed growing/full-Hamiltonian graphs on the original finite
sourced states, including the growing square. These initial-state domains
do not assert that the full nonautonomous flow preserves them. -/
import UnifiedTheory.Audit.KFCausalClockFloorTwoTimeGrowingGraph
import UnifiedTheory.Audit.KFCausalFiniteGrowingHamiltonianOutput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalFiniteGrowingMixedDomains
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteHamiltonianSquare (firstOutput)
open KFCausalFiniteHamiltonianTimeDerivative (mixedOutput)
open KFCausalFiniteGrowingHamiltonianOutput (growingOutput)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum : ℝ)
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "F" => firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "M" => mixedOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "gψ" => growingOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "H" => KFCausalClockFloorAveragedHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "G" => KFCausalClockFloorGrowingHamiltonian.hamiltonian ε hε h hh hb₀ mass2 quartic vacuum

def growingAfterHamiltonian (s : ℝ) : Hilbert :=
  (Real.exp 2-1)⁻¹ • (M s 1-M s 0)

def hamiltonianAfterGrowing (s : ℝ) : Hilbert :=
  H s ⟨gψ,KFCausalFiniteGrowingHamiltonianOutput.growing_output_domain
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩

local notation "HG" => hamiltonianAfterGrowing n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum
local notation "GH" => growingAfterHamiltonian n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum

def growingSquare : Hilbert := (Real.exp 2-1)⁻¹ • (HG 1-HG 0)

local notation "GG" => growingSquare n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum

theorem hamiltonian_output_graph (s : ℝ) : (F s,GH s) ∈ (G).graph := by
  have hg := KFCausalClockFloorTwoTimeGrowingGraph.difference_graph
    ε hε h hh hb₀ mass2 quartic vacuum 0 1 (by norm_num) (F s) (M s 0) (M s 1)
      (KFCausalFiniteHamiltonianTimeDerivative.mixed_graph
        n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s 0)
      (KFCausalFiniteHamiltonianTimeDerivative.mixed_graph
        n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s 1)
  simpa only [growingAfterHamiltonian,mul_one,mul_zero,Real.exp_zero] using hg

theorem growing_output_graph (s : ℝ) : (gψ,HG s) ∈ (H s).graph :=
  (H s).mem_graph ⟨gψ,KFCausalFiniteGrowingHamiltonianOutput.growing_output_domain
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩

theorem growing_square_output_graph : (gψ,GG) ∈ (G).graph := by
  have hg := KFCausalClockFloorTwoTimeGrowingGraph.difference_graph
    ε hε h hh hb₀ mass2 quartic vacuum 0 1 (by norm_num) gψ (HG 0) (HG 1)
      (growing_output_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum 0)
      (growing_output_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum 1)
  simpa only [growingSquare,mul_one,mul_zero,Real.exp_zero] using hg

theorem growing_after_hamiltonian_graph (s : ℝ) :
    (ψ,GH s) ∈ (composition G (H s)).graph :=
  (composition_graph G (H s) ψ (GH s)).mpr ⟨F s,
    KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s,
    hamiltonian_output_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩

theorem hamiltonian_after_growing_graph (s : ℝ) :
    (ψ,HG s) ∈ (composition (H s) G).graph :=
  (composition_graph (H s) G ψ (HG s)).mpr ⟨gψ,
    KFCausalFiniteGrowingHamiltonianOutput.growing_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum,
    growing_output_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s⟩

theorem growing_square_graph : (ψ,GG) ∈ (composition G G).graph :=
  (composition_graph G G ψ GG).mpr ⟨gψ,
    KFCausalFiniteGrowingHamiltonianOutput.growing_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum,
    growing_square_output_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum⟩

theorem composition_domains (s : ℝ) :
    ψ ∈ (composition G (H s)).domain ∧
    ψ ∈ (composition (H s) G).domain ∧ ψ ∈ (composition G G).domain :=
  ⟨LinearPMap.mem_domain_of_mem_graph
      (growing_after_hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s),
    LinearPMap.mem_domain_of_mem_graph
      (hamiltonian_after_growing_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum s),
    LinearPMap.mem_domain_of_mem_graph
      (growing_square_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum)⟩

#print axioms hamiltonian_output_graph
#print axioms growing_output_graph
#print axioms growing_square_output_graph
#print axioms growing_after_hamiltonian_graph
#print axioms hamiltonian_after_growing_graph
#print axioms growing_square_graph
#print axioms composition_domains
end
end UnifiedTheory.Audit.KFCausalFiniteGrowingMixedDomains
