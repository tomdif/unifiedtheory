/- The actual clock momentum of the full finite joint neutral/reciprocal
family belongs to the interacting averaged Hamiltonian operator domain.
Constructing all eight second actions yields the actual composition H B. -/
import UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumSecondFactors
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralSuperposition
import UnifiedTheory.Audit.KFCausalFixedStrongHamiltonian

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumStrongHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalReciprocalNeutralSuperposition (momentum momentumOutput momentum_zeroSector momentumOutput_graph)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalPhysicalEnergyFactors (modelDirections energyWeight)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalEnergyReverseFactors (reverseFactor)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalOrderedOperatorComposition (composition composition_graph)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => momentum n ε h a w p C b P hε ha hh hw

def seconds (j : Fin 8) : Hilbert := ∑ i,
  KFCausalReciprocalNeutralMomentumSecondFactors.second ε (a i) h (w i) hε (ha i) hh (hw i) hb
    (C i) (p i) (b i) (P i) j

theorem reverse_graph (j : Fin 8) :
    (momentumOutput n ε h a w p C b P hε ha hh hw hb₀ j,seconds n ε h a w p C b P hε ha hh hw hb j) ∈
      (reverseFactor ε hε h modelDirections pointField j).graph := by
  have hs := (reverseFactor ε hε h modelDirections pointField j).graph.sum_mem
    fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      KFCausalReciprocalNeutralMomentumSecondFactors.reverse_graph ε (a i) h (w i) hε (ha i) hh (hw i) hb
        (C i) (p i) (b i) (P i) j
  simpa only [momentumOutput,seconds,← prod_mk_sum] using hs

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (seconds n ε h a w p C b P hε ha hh hw hb))

theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (ψ,hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  KFCausalFixedStrongHamiltonian.hamiltonian_graph ε h hε hh hb₀ mass2 quartic vacuum t ψ
    (momentum_zeroSector n ε h a w p C b P hε ha hh hw)
    (momentumOutput n ε h a w p C b P hε ha hh hw hb₀) (seconds n ε h a w p C b P hε ha hh hw hb)
    (momentumOutput_graph n ε h a w p C b P hε ha hh hw hb₀) (reverse_graph n ε h a w p C b P hε ha hh hw hb)

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

theorem hamiltonian_momentum_graph (mass2 quartic vacuum t : ℝ) :
    (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw,
      hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ∈
      (composition (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t)
        (pureMomentum ε hε h)).graph :=
  (composition_graph _ _ _ _).mpr ⟨ψ,
    KFCausalReciprocalNeutralSuperposition.momentum_graph n ε h a w p C b P hε ha hh hw,
    hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩

theorem strong_pairing (mass2 quartic vacuum t : ℝ) :
    inner ℂ
      (KFCausalReciprocalNeutralStrongHamiltonian.hamiltonianOutput
        n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) ψ =
      inner ℂ (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw)
        (hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t) :=
  KFCausalOrderedOperatorComposition.selfAdjoint_graph_pairing _
    (KFCausalClockFloorAveragedHamiltonian.hamiltonian_selfAdjoint
      ε hε h hh hb₀ mass2 quartic vacuum t) _ _ _ _
    (KFCausalReciprocalNeutralStrongHamiltonian.hamiltonian_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)
    (hamiltonian_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)

theorem response_identity (mass2 quartic vacuum t : ℝ) :
    KFCausalReciprocalNeutralHamiltonian.fullResponse n ε h a w p C b P hε ha hh hw hb₀
      mass2 quartic vacuum t =
      (-2/h)*(inner ℂ (KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw)
        (hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t)).im := by
  rw [KFCausalReciprocalNeutralStrongResponse.response_identity
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t,
    strong_pairing n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t]

#print axioms reverse_graph
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms hamiltonian_action
#print axioms hamiltonian_momentum_graph
#print axioms strong_pairing
#print axioms response_identity
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralMomentumStrongHamiltonian
