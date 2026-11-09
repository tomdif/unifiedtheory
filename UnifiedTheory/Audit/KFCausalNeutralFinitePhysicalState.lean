/- The finite neutral profile family consists of actual Hilbert states.
Their pure-clock momenta and all eight ordered energy-factor outputs
are derived from graph linearity. -/
import UnifiedTheory.Audit.KFCausalNeutralCrossPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalClockFloorCommonDomain (energyFactor commonEnergyDomain commonEnergyDomain_iff)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockMomentum (pureMomentum)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles (neutralSource)

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ)

def state : Hilbert := ∑ i,
  KFCausalPolynomialGaussianDomain.input ε a h hε ha hh (C i) 0 (neutralSource (b i)) 4 (P i)
def momentum : Hilbert := ∑ i,
  KFCausalPolynomialMomentumDomain.momentum ε a h hε ha hh 0 (neutralSource (b i)) 4 (C i) (P i)

variable (hb : |h| ≤ 2*Real.pi*ε/3)

def output (j : Fin 8) : Hilbert := ∑ i,
  KFCausalPolynomialGaussianDomain.output ε a h hε ha hh (C i) 0 (neutralSource (b i)) 4 hb
    (P i) modelDirections pointField j
def momentumOutput (j : Fin 8) : Hilbert := ∑ i,
  KFCausalPolynomialMomentumDomain.momentumFactor ε a h hε ha hh 0 (neutralSource (b i)) 4 (C i) hb
    (P i) modelDirections pointField j

theorem momentum_graph :
    (state ε a h hε ha hh N b C P,momentum ε a h hε ha hh N b C P) ∈
      (pureMomentum ε hε h).graph := by
  have hs := (pureMomentum ε hε h).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      KFCausalPolynomialMomentumDomain.momentum_graph ε a h hε ha hh 0
        (neutralSource (b i)) 4 (C i) (P i))
  simpa only [state,momentum,← prod_mk_sum] using hs

theorem output_graph (j : Fin 8) :
    (state ε a h hε ha hh N b C P,output ε a h hε ha hh N b C P hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      KFCausalPolynomialGaussianDomain.output_graph ε a h hε ha hh (C i) 0
        (neutralSource (b i)) 4 hb (P i) modelDirections pointField j)
  simpa only [state,output,← prod_mk_sum] using hs

theorem momentumOutput_graph (j : Fin 8) :
    (momentum ε a h hε ha hh N b C P,momentumOutput ε a h hε ha hh N b C P hb j) ∈
      (energyFactor ε hε h modelDirections pointField j).graph := by
  have hs := (energyFactor ε hε h modelDirections pointField j).graph.sum_mem
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin N))) =>
      KFCausalPolynomialMomentumDomain.momentumFactor_graph ε a h hε ha hh 0
        (neutralSource (b i)) 4 (C i) hb (P i) modelDirections pointField j)
  simpa only [momentum,momentumOutput,← prod_mk_sum] using hs

include hb in
theorem common_domains :
    state ε a h hε ha hh N b C P ∈ commonEnergyDomain ε hε h modelDirections pointField ∧
      momentum ε a h hε ha hh N b C P ∈ commonEnergyDomain ε hε h modelDirections pointField :=
  ⟨(commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr fun j =>
      LinearPMap.mem_domain_of_mem_graph (output_graph ε a h hε ha hh N b C P hb j),
    (commonEnergyDomain_iff ε hε h modelDirections pointField _).mpr fun j =>
      LinearPMap.mem_domain_of_mem_graph (momentumOutput_graph ε a h hε ha hh N b C P hb j)⟩

#print axioms momentum_graph
#print axioms output_graph
#print axioms momentumOutput_graph
#print axioms common_domains
end
end UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalState
