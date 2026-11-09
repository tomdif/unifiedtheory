/- The constructed correlated states and their initial pure-clock momenta
belong to the same averaged Hamiltonian domain whose full forward evolution
has already been constructed. This bridge gives their strong Schrodinger
equations and preserves zero charge. It does not identify evolution of the
initial momentum with the momentum of the evolved state, or assert preservation
of Dom(BH) or Dom(HB). -/
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockLimit
import UnifiedTheory.Audit.KFCausalClockFloorFullDomainDynamics
import UnifiedTheory.Audit.KFCausalClockFloorAveragedEvolutionProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainEvolution
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalClockFloorAveragedEvolution (evolution)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum : ℝ)
local notation "hb₀" => KFCausalGaussianVacuumSquare.original_strip ε h hε hb
local notation "ψ" => KFCausalCorrelatedClusteredInputGraphLimit.limitingState f ε h a p hε hh ha
local notation "b" => KFCausalCorrelatedClusteredPureMomentumLimit.limitingMomentum f ε h a p hε hh ha
local notation "H" => hamiltonian ε hε h hh hb₀ mass2 quartic vacuum
local notation "U" => evolution ε hε h hh hb₀ mass2 quartic vacuum
local notation "c" => (-Complex.I*((1/h:ℝ):ℂ))

def inputVector (s : ℝ) : (H s).domain :=
  ⟨ψ,input_hamiltonian_domain f ε h a p hε hh ha hb mass2 quartic vacuum s⟩

def momentumVector (s : ℝ) : (H s).domain :=
  ⟨b,momentum_hamiltonian_domain f ε h a p hε hh ha hb mass2 quartic vacuum s⟩

theorem inputVector_value (s : ℝ) :
    H s (inputVector f ε h a p hε hh ha hb mass2 quartic vacuum s) =
      inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s :=
  (H s).mem_graph_snd_inj' ((H s).mem_graph _)
    (input_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s) rfl

theorem momentumVector_value (s : ℝ) :
    H s (momentumVector f ε h a p hε hh ha hb mass2 quartic vacuum s) =
      momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s :=
  (H s).mem_graph_snd_inj' ((H s).mem_graph _)
    (momentum_hamiltonian_graph f ε h a p hε hh ha hb mass2 quartic vacuum s) rfl

theorem input_initial_derivative (s : ℝ) :
    HasDerivAt (fun t => U s t ψ)
      (c • inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s) s := by
  simpa only [inputVector_value] using
    KFCausalClockFloorDomainSchrodinger.hamiltonian_initial ε hε h hh hb₀ mass2 quartic vacuum s
      (inputVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem momentum_initial_derivative (s : ℝ) :
    HasDerivAt (fun t => U s t b)
      (c • momentumHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum s) s := by
  simpa only [momentumVector_value] using
    KFCausalClockFloorDomainSchrodinger.hamiltonian_initial ε hε h hh hb₀ mass2 quartic vacuum s
      (momentumVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem input_forward_domain (s t : ℝ) (hst : s ≤ t) : U s t ψ ∈ (H t).domain :=
  KFCausalClockFloorFullDomainDynamics.forward_domain ε hε h hh hb₀ mass2 quartic vacuum s t hst
    (inputVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem momentum_forward_domain (s t : ℝ) (hst : s ≤ t) : U s t b ∈ (H t).domain :=
  KFCausalClockFloorFullDomainDynamics.forward_domain ε hε h hh hb₀ mass2 quartic vacuum s t hst
    (momentumVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem input_forward_schrodinger (s t : ℝ) (hst : s ≤ t) :
    ∃ hx : U s t ψ ∈ (H t).domain,
      HasDerivAt (fun r => U s r ψ) (c • H t ⟨U s t ψ,hx⟩) t :=
  KFCausalClockFloorFullDomainDynamics.forward_schrodinger ε hε h hh hb₀ mass2 quartic vacuum s t hst
    (inputVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem momentum_forward_schrodinger (s t : ℝ) (hst : s ≤ t) :
    ∃ hx : U s t b ∈ (H t).domain,
      HasDerivAt (fun r => U s r b) (c • H t ⟨U s t b,hx⟩) t :=
  KFCausalClockFloorFullDomainDynamics.forward_schrodinger ε hε h hh hb₀ mass2 quartic vacuum s t hst
    (momentumVector f ε h a p hε hh ha hb mass2 quartic vacuum s)

theorem input_evolution_zero_sector (s t : ℝ) :
    U s t ψ ∈ KFCausalStandingChargeOperator.zeroSector h hh :=
  KFCausalClockFloorAveragedEvolutionProjection.evolution_zero_sector ε hε h hh hb₀ mass2 quartic vacuum s t ψ
    (KFCausalCorrelatedClusteredInputGraphLimit.limitingState_zeroSector f ε h a p hε hh ha)

theorem momentum_evolution_zero_sector (s t : ℝ) :
    U s t b ∈ KFCausalStandingChargeOperator.zeroSector h hh :=
  KFCausalClockFloorAveragedEvolutionProjection.evolution_zero_sector ε hε h hh hb₀ mass2 quartic vacuum s t b
    (KFCausalCorrelatedClusteredPureMomentumLimit.momentum_zeroSector f ε h a p hε hh ha)

#print axioms inputVector_value
#print axioms momentumVector_value
#print axioms input_initial_derivative
#print axioms momentum_initial_derivative
#print axioms input_forward_domain
#print axioms momentum_forward_domain
#print axioms input_forward_schrodinger
#print axioms momentum_forward_schrodinger
#print axioms input_evolution_zero_sector
#print axioms momentum_evolution_zero_sector
end
end UnifiedTheory.Audit.KFCausalCorrelatedHamiltonianDomainEvolution
