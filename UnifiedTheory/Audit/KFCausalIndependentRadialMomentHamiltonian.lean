/- Full interacting Hamiltonian graphs for the actual left and right radial
moment states. The clock, all four kinetic rows, both matter rows and the
vacuum row are assembled from their constructed natural component graphs. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentClock
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentKinetic
import UnifiedTheory.Audit.KFCausalIndependentRadialMomentMatterGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalIndependentRadialMomentHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalIndependentRadialPacketMoments (momentState)
open KFCausalIndependentRadialMomentClock (weightedState)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalStandingChargeOperator (zeroSector zeroProjection)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorBoundedInverse (inverseL)

def leftDegree (side : Bool) : ℕ := if side then 0 else 1
def rightDegree (side : Bool) : ℕ := if side then 1 else 0

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
  (hb : |h| ≤ ε/10) (side : Bool)
local notation "m" => leftDegree side
local notation "n" => rightDegree side
local notation "ψ" => momentState ε a h wL wR C p b P hε ha hh hL hR m n

include hb in
theorem component_graph_exists (j : Fin 8) : ∃ z : Hilbert, (ψ,z) ∈ (component ε hε h j).graph := by
  have hk (i : Fin 4) : ∃ z : Hilbert,
      (ψ,z) ∈ (component ε hε h (KFCausalIndependentRadialPolynomialKinetic.kineticIndex i)).graph := by
    cases side
    · exact KFCausalIndependentRadialMomentKinetic.moment_left_kinetic_graph
        ε a h wL wR C p b P hε ha hh hL hR i
    · exact KFCausalIndependentRadialMomentKinetic.moment_right_kinetic_graph
        ε a h wL wR C p b P hε ha hh hL hR i
  fin_cases j
  · exact ⟨_,KFCausalIndependentRadialMomentClock.clock_component_graph
      ε a h wL wR C p b P hε ha hh hL hR hb m n⟩
  · exact hk 0
  · exact hk 1
  · exact hk 2
  · exact hk 3
  · exact ⟨_,KFCausalIndependentRadialMomentMatterGraph.matter_graph
      ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb 0⟩
  · exact ⟨_,KFCausalIndependentRadialMomentMatterGraph.matter_graph
      ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb 1⟩
  · exact ⟨_,KFCausalIndependentRadialMomentExponential.vacuum_graph
      ε h a wL wL wR C p b P m n hε hh ha hL hR le_rfl hb⟩

def componentOutput (j : Fin 8) : Hilbert :=
  (component_graph_exists ε a h wL wR C p b P hε ha hh hL hR hb side j).choose

theorem component_graph (j : Fin 8) :
    (ψ,componentOutput ε a h wL wR C p b P hε ha hh hL hR hb side j) ∈
      (component ε hε h j).graph :=
  (component_graph_exists ε a h wL wR C p b P hε ha hh hL hR hb side j).choose_spec

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (componentOutput ε a h wL wR C p b P hε ha hh hL hR hb side))

theorem hamiltonian_graph (hstrip : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) :
    (ψ,hamiltonianOutput ε a h wL wR C p b P hε ha hh hL hR hb side mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh hstrip mass2 quartic vacuum t _
    (KFCausalIndependentRadialMomentCharge.momentState_zeroSector
      ε a h wL wR C p b P hε ha hh hL hR m n) _
    (component_graph ε a h wL wR C p b P hε ha hh hL hR hb side)

include hb in
theorem hamiltonian_domain (hstrip : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) :
    ψ ∈ (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε a h wL wR C p b P hε ha hh hL hR hb side hstrip mass2 quartic vacuum t)

def weightedComponent (inverse : Bool) (j : Fin 8) : Hilbert :=
  KFCausalClockWeightedIndependentHamiltonian.clockAction ε h a hε ha hb inverse
    (KFCausalAnalyticClockSecondTransport.secondShift h j)
    (by unfold KFCausalAnalyticClockSecondTransport.secondShift; split_ifs <;> simp)
    (componentOutput ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb side j)

theorem weighted_component_graph (inverse : Bool) (j : Fin 8) :
    (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse,
      weightedComponent ε a h wL wR C p b P hε ha hh hL hR hb side inverse j) ∈
      (component ε hε h j).graph :=
  KFCausalAnalyticClockSecondTransport.second_graph
    (KFCausalGaussianHolomorphicClockWeight.multiplier ε a inverse) h
    (KFCausalGaussianHolomorphicClockWeight.bound ε h a inverse)
    (KFCausalGaussianHolomorphicClockWeight.multiplier_analytic ε h a inverse hε hb)
    (KFCausalGaussianHolomorphicClockWeight.bound_nonnegative ε h a inverse hε)
    (KFCausalGaussianHolomorphicClockWeight.multiplier_bound ε h a inverse hε hb ha) ε hε hh j _ _
    (component_graph ε (a/2) h wL wR C p b P hε (by positivity) hh hL hR hb side j)

def weightedHamiltonianOutput (inverse : Bool) (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (weightedComponent ε a h wL wR C p b P hε ha hh hL hR hb side inverse))

theorem weighted_hamiltonian_graph (inverse : Bool) (hstrip : |h| ≤ 2*Real.pi*ε/3)
    (mass2 quartic vacuum t : ℝ) :
    (weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse,
      weightedHamiltonianOutput ε a h wL wR C p b P hε ha hh hL hR hb side inverse mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh hstrip mass2 quartic vacuum t _
    (KFCausalIndependentRadialMomentClock.weightedState_zeroSector
      ε a h wL wR C p b P hε ha hh hL hR hb m n inverse) _
    (weighted_component_graph ε a h wL wR C p b P hε ha hh hL hR hb side inverse)

theorem weighted_hamiltonian_domain (inverse : Bool) (hstrip : |h| ≤ 2*Real.pi*ε/3)
    (mass2 quartic vacuum t : ℝ) :
    weightedState ε a h wL wR C p b P hε ha hh hL hR hb m n inverse ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (weighted_hamiltonian_graph ε a h wL wR C p b P hε ha hh hL hR hb side inverse hstrip mass2 quartic vacuum t)

include hb in
theorem inverse_hamiltonian_domain (hstrip : |h| ≤ 2*Real.pi*ε/3) (mass2 quartic vacuum t : ℝ) :
    inverseL ε hε (inverseL ε hε ψ) ∈
      (hamiltonian ε hε h hh hstrip mass2 quartic vacuum t).domain := by
  rw [← KFCausalIndependentRadialMomentClock.inverse_state_eq
    ε a h wL wR C p b P hε ha hh hL hR hb m n]
  exact weighted_hamiltonian_domain ε a h wL wR C p b P hε ha hh hL hR hb side true hstrip mass2 quartic vacuum t

#print axioms component_graph_exists
#print axioms component_graph
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms weighted_component_graph
#print axioms weighted_hamiltonian_graph
#print axioms weighted_hamiltonian_domain
#print axioms inverse_hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalIndependentRadialMomentHamiltonian
