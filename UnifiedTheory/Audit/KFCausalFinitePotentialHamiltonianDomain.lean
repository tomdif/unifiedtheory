/- The projected vacuum, quadratic-matter and quartic-matter outputs
of every original finite sourced state lie in the actual averaged
Hamiltonian domain. All eight natural second-component graphs are used.
No Hamiltonian-square domain or evolution invariance is asserted. -/
import UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph
import UnifiedTheory.Audit.KFCausalFiniteOuterClockVacuumMatter
import UnifiedTheory.Audit.KFCausalFiniteOuterSymmetricVacuumMatter
import UnifiedTheory.Audit.KFCausalFiniteOuterAntisymmetricVacuumMatter
import UnifiedTheory.Audit.KFCausalFiniteOuterMatterProjected
import UnifiedTheory.Audit.KFCausalFiniteSourcedMatterSquare

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalFinitePotentialHamiltonianDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection zeroProjection_mem)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalFiniteOuterClockVacuumMatter (firstOutput)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ j, 0 < a j)
  (hh : h ≠ 0) (hw : ∀ j, 1 ≤ w j) (hb : |h| ≤ ε/10)

def vacuumOutput : Option (Fin 2) → Hilbert
  | none => KFCausalFiniteSourcedMixedVacuum.projectedOutput n ε h a w p C b P hε ha hh hw hb
  | some j => KFCausalFiniteSourcedMatterSquare.projectedOutput n ε h a w p C b P j hε ha hh hw hb

def componentOutputs (i : Option (Fin 2)) : Fin 8 → Hilbert :=
  ![KFCausalFiniteOuterClockVacuumMatter.projectedOutput n ε h a w p C b P hε ha hh hw hb i,
    KFCausalFiniteOuterSymmetricVacuumMatter.projectedOutput n ε h a w p C b P hε ha hh hw hb i 0,
    KFCausalFiniteOuterSymmetricVacuumMatter.projectedOutput n ε h a w p C b P hε ha hh hw hb i 1,
    KFCausalFiniteOuterAntisymmetricVacuumMatter.projectedOutput n ε h a w p C b P hε ha hh hw hb i 0,
    KFCausalFiniteOuterAntisymmetricVacuumMatter.projectedOutput n ε h a w p C b P hε ha hh hw hb i 1,
    KFCausalFiniteOuterMatterProjected.projectedOutput n ε h a w p C b P hε ha hh hw hb i 0,
    KFCausalFiniteOuterMatterProjected.projectedOutput n ε h a w p C b P hε ha hh hw hb i 1,
    vacuumOutput n ε h a w p C b P hε ha hh hw hb i]

private theorem vacuum_graph (i : Option (Fin 2)) :
    (zeroProjection h hh (firstOutput n ε h a w p C b P hε ha hh hw hb i),
      vacuumOutput n ε h a w p C b P hε ha hh hw hb i) ∈
        (KFCausalClockFloorVacuumSquare.square ε hε h).graph := by
  cases i with
  | none => exact KFCausalFiniteSourcedMixedVacuum.projected_graph n ε h a w p C b P hε ha hh hw hb
  | some j => exact KFCausalFiniteSourcedMatterSquare.projected_graph n ε h a w p C b P j hε ha hh hw hb

theorem component_graphs (i : Option (Fin 2)) (j : Fin 8) :
    (zeroProjection h hh (firstOutput n ε h a w p C b P hε ha hh hw hb i),
      componentOutputs n ε h a w p C b P hε ha hh hw hb i j) ∈
        (component ε hε h j).graph := by
  fin_cases j
  · change (_,_) ∈ (KFCausalOrderedOperatorComposition.composition
      (KFCausalEnergyReverseFactors.reverseFactor ε hε h modelDirections pointField 0)
      (KFCausalClockFloorCommonDomain.energyFactor ε hε h modelDirections pointField 0)).graph
    rw [KFCausalClockMixedClockGraph.actual_clockSecond_eq]
    exact KFCausalFiniteOuterClockVacuumMatter.projected_graph n ε h a w p C b P hε ha hh hw hb i
  · exact KFCausalFiniteOuterSymmetricVacuumMatter.projected_graph n ε h a w p C b P hε ha hh hw hb i 0
  · exact KFCausalFiniteOuterSymmetricVacuumMatter.projected_graph n ε h a w p C b P hε ha hh hw hb i 1
  · exact KFCausalFiniteOuterAntisymmetricVacuumMatter.projected_graph n ε h a w p C b P hε ha hh hw hb i 0
  · exact KFCausalFiniteOuterAntisymmetricVacuumMatter.projected_graph n ε h a w p C b P hε ha hh hw hb i 1
  · exact KFCausalFiniteOuterMatterProjected.projected_matter_graph n ε h a w p C b P hε ha hh hw hb i 0
  · exact KFCausalFiniteOuterMatterProjected.projected_matter_graph n ε h a w p C b P hε ha hh hw hb i 1
  · exact vacuum_graph n ε h a w p C b P hε ha hh hw hb i

theorem hamiltonian_strip (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ ε/10) :
    |h| ≤ 2*Real.pi*ε/3 := by
  have hp := mul_lt_mul_of_pos_right Real.pi_gt_three hε
  linarith

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) (i : Option (Fin 2)) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (componentOutputs n ε h a w p C b P hε ha hh hw hb i))

theorem projected_hamiltonian_graph (mass2 quartic vacuum t : ℝ) (i : Option (Fin 2)) :
    (zeroProjection h hh (firstOutput n ε h a w p C b P hε ha hh hw hb i),
      hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t i) ∈
        (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh
    (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t _ (zeroProjection_mem h hh _)
    (componentOutputs n ε h a w p C b P hε ha hh hw hb i)
    (component_graphs n ε h a w p C b P hε ha hh hw hb i)

theorem projected_hamiltonian_domain (mass2 quartic vacuum t : ℝ) (i : Option (Fin 2)) :
    zeroProjection h hh (firstOutput n ε h a w p C b P hε ha hh hw hb i) ∈
      (hamiltonian ε hε h hh (hamiltonian_strip ε h hε hb) mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (projected_hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t i)

#print axioms component_graphs
#print axioms hamiltonian_strip
#print axioms projected_hamiltonian_graph
#print axioms projected_hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalFinitePotentialHamiltonianDomain
