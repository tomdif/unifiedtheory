/- Original finite sourced states evolve in the square domain of the actual
self-adjoint averaged Hamiltonian at every fixed physical parameter.  Both
Hamiltonian outputs are the previously constructed outputs, with every
coupling retained.  Time here is the autonomous group parameter; no claim
about nonautonomous square-domain or clock-composition invariance is made. -/
import UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquare
import UnifiedTheory.Audit.KFCausalClockFloorFrozenSquareEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquareEvolution
noncomputable section
open KFCausalReciprocalNeutralSuperposition (state)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalFinitePotentialHamiltonianDomain (hamiltonian_strip)
open KFCausalFiniteHamiltonianSquare (firstOutput secondOutput)
open KFCausalOrderedOperatorComposition (composition)

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i)
  (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ ε/10)
  (mass2 quartic vacuum r : ℝ)
local notation "hb₀" => hamiltonian_strip ε h hε hb
local notation "ψ" => state n ε h a w p C b P hε ha hh hw
local notation "ψ₁" => firstOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r
local notation "ψ₂" => secondOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r
local notation "T" => hamiltonian ε hε h hh hb₀ mass2 quartic vacuum r
local notation "U" => KFCausalClockFloorFrozenEvolution.evolution
  ε hε h hh hb₀ mass2 quartic vacuum r (1/h)

theorem evolved_first_graph (t : ℝ) : (U t ψ,U t ψ₁) ∈ (T).graph :=
  KFCausalClockFloorFrozenSquareEvolution.evolution_graph
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ ψ₁
    (KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r) t

theorem evolved_second_graph (t : ℝ) : (U t ψ₁,U t ψ₂) ∈ (T).graph :=
  KFCausalClockFloorFrozenSquareEvolution.evolution_graph
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ₁ ψ₂
    (KFCausalFiniteHamiltonianSquare.second_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r) t

theorem evolved_square_graph (t : ℝ) :
    (U t ψ,U t ψ₂) ∈ (composition T T).graph :=
  KFCausalClockFloorFrozenSquareEvolution.evolution_square_graph
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ ψ₂
    (KFCausalFiniteHamiltonianSquare.square_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r) t

theorem evolved_square_domain (t : ℝ) : U t ψ ∈ (composition T T).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (evolved_square_graph n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r t)

theorem first_derivative (t : ℝ) :
    HasDerivAt (fun s => U s ψ) ((-Complex.I*((1/h:ℝ):ℂ)) • U t ψ₁) t :=
  KFCausalClockFloorFrozenSquareEvolution.first_derivative_of_graph
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ ψ₁
    (KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r) t

theorem second_derivative (t : ℝ) :
    HasDerivAt (fun s => deriv (fun v => U v ψ) s)
      (((-((1/h)^2):ℝ):ℂ) • U t ψ₂) t :=
  KFCausalClockFloorFrozenSquareEvolution.second_derivative_of_graph_pair
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ ψ₁ ψ₂
    (KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r)
    (KFCausalFiniteHamiltonianSquare.second_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r) t

theorem second_derivative_continuous :
    Continuous (fun t => deriv (fun s => deriv (fun v => U v ψ) s) t) :=
  KFCausalClockFloorFrozenSquareEvolution.second_derivative_continuous
    ε hε h hh hb₀ mass2 quartic vacuum r (1/h) ψ ψ₁ ψ₂
    (KFCausalFiniteHamiltonianSquare.first_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r)
    (KFCausalFiniteHamiltonianSquare.second_graph
      n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum r)

#print axioms evolved_first_graph
#print axioms evolved_second_graph
#print axioms evolved_square_graph
#print axioms evolved_square_domain
#print axioms first_derivative
#print axioms second_derivative
#print axioms second_derivative_continuous
end
end UnifiedTheory.Audit.KFCausalFiniteHamiltonianSquareEvolution
