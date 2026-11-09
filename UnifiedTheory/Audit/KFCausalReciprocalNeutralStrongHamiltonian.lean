/- The full finite joint neutral/reciprocal family belongs to the actual
interacting averaged Hamiltonian operator domain. All eight second
actions are constructed, and their weighted charge projection is H psi. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (state output state_zeroSector output_graph)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw

def seconds (j : Fin 8) : Hilbert := ∑ i,
  KFCausalReciprocalNeutralSecondFactors.second ε (a i) h (w i) hε (ha i) hh (hw i) hb
    (C i) (p i) (b i) (P i) j

theorem reverse_graph (j : Fin 8) :
    (output n ε h a w p C b P hε ha hh hw hb₀ j,seconds n ε h a w p C b P hε ha hh hw hb j) ∈
      (reverseFactor ε hε h modelDirections pointField j).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField j).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralSecondFactors.reverse_graph ε (a i) h (w i) hε (ha i) hh (hw i) hb
        (C i) (p i) (b i) (P i) j
  simpa only [output,seconds,← prod_mk_sum] using hs

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (seconds n ε h a w p C b P hε ha hh hw hb))

theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (ψ,hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t ψ
    (state_zeroSector n ε h a w p C b P hε ha hh hw)
    (output n ε h a w p C b P hε ha hh hw hb₀) (seconds n ε h a w p C b P hε ha hh hw hb)
    (output_graph n ε h a w p C b P hε ha hh hw hb₀) (reverse_graph n ε h a w p C b P hε ha hh hw hb)

include hb in
theorem hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    ψ ∈ (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)

theorem hamiltonian_action (mass2 quartic vacuum t : ℝ) :
    hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t
      ⟨ψ,hamiltonian_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩ =
        hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t :=
  (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph_snd_inj'
    ((hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph
      ⟨ψ,hamiltonian_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩)
    (hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) rfl

#print axioms reverse_graph
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms hamiltonian_action
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
