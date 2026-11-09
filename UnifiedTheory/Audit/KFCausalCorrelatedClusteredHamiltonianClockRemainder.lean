/- The original finite B H outputs are constructed. Their clock/kinetic
part converges, and the full limiting B H domain and derivative-limit
problem reduce exactly to the three retained potential second actions. -/
import UnifiedTheory.Audit.KFCausalProjectedSecondClockDecomposition
import UnifiedTheory.Audit.KFCausalCorrelatedClusteredStrongHamiltonianLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2800000

namespace UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockRemainder
noncomputable section
open MeasureTheory Filter
open scoped Topology
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalCorrelatedClusteredProfiles (Family)
open KFCausalCorrelatedClusteredAllSecondLimit (inputSeconds inputSeconds_tendsto)
open KFCausalCorrelatedClusteredClockKineticSecondCommutator (lowIndex derivative derivative_graph derivative_tendsto)
open KFCausalCorrelatedClusteredFiniteSecondPureClock (finiteDerivative finite_derivative_graph)
open KFCausalCorrelatedClusteredOriginalKineticSeconds (finiteSeconds)
open KFCausalCorrelatedClusteredStrongHamiltonianLimit (inputHamiltonian finiteInputHamiltonian)
open KFCausalProjectedSecondClockDecomposition
open KFCausalClockFloorPureClockMomentum (pureMomentum pure_closed)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalPhysicalEnergyFactors (energyWeight)

variable {m : ℕ} (f : Family m) (ε h : ℝ) (a p : Fin m → ℝ)
  (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ Real.pi*ε/3)
  (mass2 quartic vacuum t : ℝ)
local notation "B" => pureMomentum ε hε h
local notation "c" => energyWeight mass2 quartic vacuum t
local notation "L" => inputSeconds f ε h a p hε hh ha hb
local notation "S" => finiteSeconds f ε h a p hε hh ha hb
local notation "d" => derivative f ε h a p hε hh ha hb
local notation "D" => finiteDerivative f ε h a p hε hh ha hb
local notation "Hψ" => inputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t

def clockKineticPart : Hilbert := low h hh c L
def potentialPart : Hilbert := high h hh c L
def clockKineticDerivative : Hilbert := lowDerivative h hh c d
def finiteHamiltonianDerivative (δ : ℝ) : Hilbert := total h hh c (D δ)
def finiteClockKineticDerivative (δ : ℝ) : Hilbert := low h hh c (D δ)
def finitePotentialDerivative (δ : ℝ) : Hilbert := high h hh c (D δ)

theorem hamiltonian_split : Hψ=clockKineticPart f ε h a p hε hh ha hb mass2 quartic vacuum t+
    potentialPart f ε h a p hε hh ha hb mass2 quartic vacuum t := total_split h hh c L

theorem finite_hamiltonian_derivative_graph (δ : ℝ) (hδ : 0 < δ) :
    (finiteInputHamiltonian f ε h a p hε hh ha hb mass2 quartic vacuum t δ,
      finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ) ∈ (B).graph :=
  total_graph h hh c ε hε (S δ) (D δ)
    (finite_derivative_graph f ε h a p hε hh ha hb δ hδ)

theorem finite_potential_derivative_graph (δ : ℝ) (hδ : 0 < δ) :
    (high h hh c (S δ),finitePotentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ) ∈ (B).graph :=
  high_graph h hh c ε hε (S δ) (D δ)
    (fun j => finite_derivative_graph f ε h a p hε hh ha hb δ hδ (highIndex j))

theorem clockKinetic_derivative_graph :
    (clockKineticPart f ε h a p hε hh ha hb mass2 quartic vacuum t,
      clockKineticDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) ∈ (B).graph :=
  low_graph h hh c ε hε L d (derivative_graph f ε h a p hε hh ha hb)

theorem clockKinetic_part_tendsto :
    Tendsto (fun δ => low h hh c (S δ)) (𝓝[>] 0)
      (𝓝 (clockKineticPart f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_const_nhds.smul (inputSeconds_tendsto f ε h a p hε hh ha hb (lowIndex j)))

theorem potential_part_tendsto :
    Tendsto (fun δ => high h hh c (S δ)) (𝓝[>] 0)
      (𝓝 (potentialPart f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_const_nhds.smul (inputSeconds_tendsto f ε h a p hε hh ha hb (highIndex j)))

theorem clockKinetic_derivative_tendsto :
    Tendsto (finiteClockKineticDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0)
      (𝓝 (clockKineticDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t)) := by
  apply (zeroProjection h hh).continuous.tendsto _ |>.comp
  exact tendsto_finset_sum Finset.univ (fun j _ =>
    tendsto_const_nhds.smul (derivative_tendsto f ε h a p hε hh ha hb j))

theorem hamiltonian_clock_domain_iff : Hψ ∈ (B).domain ↔
    potentialPart f ε h a p hε hh ha hb mass2 quartic vacuum t ∈ (B).domain :=
  total_domain_iff h hh c ε hε L (LinearPMap.mem_domain_of_mem_graph
    (clockKinetic_derivative_graph f ε h a p hε hh ha hb mass2 quartic vacuum t))

theorem finite_derivative_split (δ : ℝ) :
    finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ =
      finiteClockKineticDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ+
      finitePotentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t δ := total_split h hh c (D δ)

theorem derivative_limit_iff (w : Hilbert) :
    Tendsto (finiteHamiltonianDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0)
      (𝓝 (clockKineticDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t+w)) ↔
    Tendsto (finitePotentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0) (𝓝 w) := by
  have hl := clockKinetic_derivative_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t
  constructor
  · intro ht
    simpa only [finite_derivative_split,add_sub_cancel_left] using ht.sub hl
  · intro ht
    simpa only [← finite_derivative_split] using hl.add ht

theorem potential_graph_of_derivative_limit (w : Hilbert)
    (hw : Tendsto (finitePotentialDerivative f ε h a p hε hh ha hb mass2 quartic vacuum t) (𝓝[>] 0) (𝓝 w)) :
    (potentialPart f ε h a p hε hh ha hb mass2 quartic vacuum t,w) ∈ (B).graph := by
  apply (pure_closed ε hε h hh).mem_of_tendsto
    ((potential_part_tendsto f ε h a p hε hh ha hb mass2 quartic vacuum t).prodMk_nhds hw)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact finite_potential_derivative_graph f ε h a p hε hh ha hb mass2 quartic vacuum t δ hδ

#print axioms hamiltonian_split
#print axioms finite_hamiltonian_derivative_graph
#print axioms finite_potential_derivative_graph
#print axioms clockKinetic_derivative_graph
#print axioms clockKinetic_part_tendsto
#print axioms potential_part_tendsto
#print axioms clockKinetic_derivative_tendsto
#print axioms hamiltonian_clock_domain_iff
#print axioms finite_derivative_split
#print axioms derivative_limit_iff
#print axioms potential_graph_of_derivative_limit
end
end UnifiedTheory.Audit.KFCausalCorrelatedClusteredHamiltonianClockRemainder
