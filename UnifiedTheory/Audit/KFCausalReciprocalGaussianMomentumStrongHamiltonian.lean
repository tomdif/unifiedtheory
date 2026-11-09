/- The actual clock momentum of the reciprocal Gaussian belongs to the
full interacting averaged Hamiltonian operator domain. All eight reverse
factor graphs are proved. Finite complex sums remain actual momentum pairs. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumMatterSquare
import UnifiedTheory.Audit.KFCausalReciprocalGaussianStrongReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumStrongHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalStandingChargeOperator (zeroProjection)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalReciprocalGaussianMomentumMatterSquare
open KFCausalReciprocalGaussianStrongReduction (momentumSeconds momentum_hamiltonian_graph_of_matter)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "hb₀" => original_strip ε h hε hb
local notation "ψ" => KFCausalReciprocalGaussianMomentum.momentum ε a h w hε ha hh hw

def seconds : Fin 8 → Hilbert := momentumSeconds ε a h w hε ha hh hw hb
  (linearOutput ε a h w hε ha hh hw hb) (quadraticOutput ε a h w hε ha hh hw hb)

def output (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (seconds ε a h w hε ha hh hw hb))

theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (ψ,output ε a h w hε ha hh hw hb mass2 quartic vacuum t) ∈
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph :=
  momentum_hamiltonian_graph_of_matter ε a h w hε ha hh hw hb _ _
    (linear_reverse_graph ε a h w hε ha hh hw hb)
    (quadratic_reverse_graph ε a h w hε ha hh hw hb) mass2 quartic vacuum t

include hb in
theorem hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    ψ ∈ (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε a h w hε ha hh hw hb mass2 quartic vacuum t)

theorem hamiltonian_action (mass2 quartic vacuum t : ℝ) :
    hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t
      ⟨ψ,hamiltonian_domain ε a h w hε ha hh hw hb mass2 quartic vacuum t⟩ =
        output ε a h w hε ha hh hw hb mass2 quartic vacuum t := by
  have he := (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph_snd_inj'
    ((hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).mem_graph
      ⟨ψ,hamiltonian_domain ε a h w hε ha hh hw hb mass2 quartic vacuum t⟩)
    (hamiltonian_graph ε a h w hε ha hh hw hb mass2 quartic vacuum t) rfl
  exact he

theorem finite_sum_graph (n : ℕ) (a w : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 1 ≤ w i) (c : Fin n → ℂ) (mass2 quartic vacuum t : ℝ) :
    (∑ i, c i • KFCausalReciprocalGaussianMomentum.momentum ε (a i) h (w i) hε (ha i) hh (hw i),
      ∑ i, c i • output ε (a i) h (w i) hε (ha i) hh (hw i) hb mass2 quartic vacuum t) ∈
        (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph := by
  have hs := (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph.sum_mem
    (fun i (_ : i ∈ Finset.univ) =>
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).graph.smul_mem (c i)
        (hamiltonian_graph ε (a i) h (w i) hε (ha i) hh (hw i) hb mass2 quartic vacuum t))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

include hb in
theorem finite_sum_domain (n : ℕ) (a w : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 1 ≤ w i) (c : Fin n → ℂ) (mass2 quartic vacuum t : ℝ) :
    (∑ i, c i • KFCausalReciprocalGaussianMomentum.momentum ε (a i) h (w i) hε (ha i) hh (hw i)) ∈
      (hamiltonian ε hε h hh hb₀ mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (finite_sum_graph ε h hε hh hb n a w ha hw c mass2 quartic vacuum t)

theorem finite_sum_clock_graph (n : ℕ) (a w : Fin n → ℝ) (ha : ∀ i, 0 < a i)
    (hw : ∀ i, 1 ≤ w i) (c : Fin n → ℂ) :
    (∑ i, c i • KFCausalReciprocalGaussianCharge.state ε (a i) h (w i) hε (ha i) hh (by have := hw i; linarith),
      ∑ i, c i • KFCausalReciprocalGaussianMomentum.momentum ε (a i) h (w i) hε (ha i) hh (hw i)) ∈
        (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph := by
  have hs := (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph.sum_mem
    (fun i (_ : i ∈ Finset.univ) =>
      (KFCausalClockFloorPureClockMomentum.pureMomentum ε hε h).graph.smul_mem (c i)
        (KFCausalReciprocalGaussianMomentum.momentum_graph ε (a i) h (w i) hε (ha i) hh (hw i)))
  simpa only [Prod.smul_mk,← prod_mk_sum] using hs

#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms hamiltonian_action
#print axioms finite_sum_graph
#print axioms finite_sum_domain
#print axioms finite_sum_clock_graph
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianMomentumStrongHamiltonian
