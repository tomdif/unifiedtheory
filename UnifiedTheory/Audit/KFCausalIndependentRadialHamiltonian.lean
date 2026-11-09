/- Independent charged radial widths give actual natural component and
Hamiltonian graphs. The two unitary squeezes transport primitive graph
witnesses from the sourced polynomial seed; no graph differentiability
or domain invariance under width differentiation is assumed. -/
import UnifiedTheory.Audit.KFCausalIndependentRadialDoubleSqueeze
import UnifiedTheory.Audit.KFCausalPairedSqueezeSecondTransport
import UnifiedTheory.Audit.KFCausalReciprocalSecondFactorTransport
import UnifiedTheory.Audit.KFCausalPolynomialSecondFactors
import UnifiedTheory.Audit.KFCausalNaturalSecondHamiltonianGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 2048

namespace UnifiedTheory.Audit.KFCausalIndependentRadialHamiltonian
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalIndependentRadialDoubleSqueeze
  (reciprocalParameter pairedParameter neutralParameter seedWidth seedWidth_positive
    seedWidth_bound normalization seed state_transport)
open KFCausalIndependentRadialPackets (state state_zeroSector)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalNaturalSecondHamiltonianGraph (component)
open KFCausalStandingChargeOperator (zeroProjection zeroSector)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalGaussianVacuumSquare (original_strip)

variable (ε a h wL wR : ℝ) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ)
  (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hL : 1 ≤ wL) (hR : 1 ≤ wR)
  (hb : |h| ≤ Real.pi*ε/3)

def seedSecond (j : Fin 8) : Hilbert :=
  KFCausalPolynomialSecondFactors.second ε a (groundWidth h) (seedWidth h wL wR)
    hε ha (groundWidth_positive h hh) (seedWidth_positive h wL wR hh)
    (seedWidth_bound h wL wR hh hR) h hb C p
    (neutralSource ((Real.exp (-(neutralParameter wL wR)):ℂ)*b)) 4
    (rescaledPolynomial (neutralParameter wL wR) P) j

def componentOutput (j : Fin 8) : Hilbert :=
  (normalization wL wR:ℂ) •
    (KFCausalPairedSqueezeSecondTransport.factorScale (-(pairedParameter wL wR)) j^2 •
      KFCausalPairedSqueezeTransport.transport (-(pairedParameter wL wR))
        (KFCausalReciprocalSqueezeEnergy.factorScale (-(reciprocalParameter wL wR)) j^2 •
          KFCausalReciprocalSqueezeTransport.transport (-(reciprocalParameter wL wR))
            (seedSecond ε a h wL wR C p b P hε ha hh hR hb j)))

theorem component_graph (j : Fin 8) :
    (state ε a h wL wR C p b P hε ha hh hL hR,
      componentOutput ε a h wL wR C p b P hε ha hh hR hb j) ∈
        (component ε hε h j).graph := by
  have hs : (seed ε a h wL wR C p b P hε ha hh hR,
      seedSecond ε a h wL wR C p b P hε ha hh hR hb j) ∈
        (component ε hε h j).graph :=
    KFCausalPolynomialSecondFactors.second_graph ε a (groundWidth h) (seedWidth h wL wR)
      hε ha (groundWidth_positive h hh) (seedWidth_positive h wL wR hh)
      (seedWidth_bound h wL wR hh hR) h hb C p
      (neutralSource ((Real.exp (-(neutralParameter wL wR)):ℂ)*b)) 4
      (rescaledPolynomial (neutralParameter wL wR) P) j
  have hr := KFCausalReciprocalSecondFactorTransport.second_graph_transport ε hε h
    (-(reciprocalParameter wL wR)) j _ _ hs
  have hp := KFCausalPairedSqueezeSecondTransport.second_graph_transport ε hε h
    (-(pairedParameter wL wR)) j _ _ hr
  rw [state_transport ε a h wL wR C p b P hε ha hh hL hR]
  exact (component ε hε h j).graph.smul_mem (normalization wL wR:ℂ) hp

def hamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (componentOutput ε a h wL wR C p b P hε ha hh hR hb))

theorem hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (state ε a h wL wR C p b P hε ha hh hL hR,
      hamiltonianOutput ε a h wL wR C p b P hε ha hh hR hb mass2 quartic vacuum t) ∈
        (hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh
    (original_strip ε h hε hb) mass2 quartic vacuum t _
    (state_zeroSector ε a h wL wR C p b P hε ha hh hL hR) _
    (component_graph ε a h wL wR C p b P hε ha hh hL hR hb)

theorem hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    state ε a h wL wR C p b P hε ha hh hL hR ∈
      (hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (hamiltonian_graph ε a h wL wR C p b P hε ha hh hL hR hb mass2 quartic vacuum t)

section Finite
variable (n : ℕ) (a wL wR p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (ha : ∀ i, 0 < a i)
  (hL : ∀ i, 1 ≤ wL i) (hR : ∀ i, 1 ≤ wR i)

def finiteState : Hilbert :=
  ∑ i, state ε (a i) h (wL i) (wR i) (C i) (p i) (b i) (P i) hε (ha i) hh (hL i) (hR i)

def finiteComponentOutput (j : Fin 8) : Hilbert :=
  ∑ i, componentOutput ε (a i) h (wL i) (wR i) (C i) (p i) (b i) (P i)
    hε (ha i) hh (hR i) hb j

theorem finiteState_zeroSector :
    finiteState ε h hε hh n a wL wR p C b P ha hL hR ∈ zeroSector h hh :=
  (zeroSector h hh).sum_mem (fun i _ =>
    state_zeroSector ε (a i) h (wL i) (wR i) (C i) (p i) (b i) (P i)
      hε (ha i) hh (hL i) (hR i))

theorem finite_component_graph (j : Fin 8) :
    (finiteState ε h hε hh n a wL wR p C b P ha hL hR,
      finiteComponentOutput ε h hε hh hb n a wL wR p C b P ha hR j) ∈
        (component ε hε h j).graph := by
  have hs := (component ε hε h j).graph.sum_mem (fun i (_ : i ∈ Finset.univ) =>
    component_graph ε (a i) h (wL i) (wR i) (C i) (p i) (b i) (P i)
      hε (ha i) hh (hL i) (hR i) hb j)
  simpa only [finiteState,finiteComponentOutput,← prod_mk_sum] using hs

def finiteHamiltonianOutput (mass2 quartic vacuum t : ℝ) : Hilbert :=
  zeroProjection h hh (secondWeighted (energyWeight mass2 quartic vacuum t)
    (finiteComponentOutput ε h hε hh hb n a wL wR p C b P ha hR))

theorem finite_hamiltonian_graph (mass2 quartic vacuum t : ℝ) :
    (finiteState ε h hε hh n a wL wR p C b P ha hL hR,
      finiteHamiltonianOutput ε h hε hh hb n a wL wR p C b P ha hR mass2 quartic vacuum t) ∈
        (hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t).graph :=
  KFCausalNaturalSecondHamiltonianGraph.hamiltonian_graph ε h hε hh
    (original_strip ε h hε hb) mass2 quartic vacuum t _
    (finiteState_zeroSector ε h hε hh n a wL wR p C b P ha hL hR) _
    (finite_component_graph ε h hε hh hb n a wL wR p C b P ha hL hR)

theorem finite_hamiltonian_domain (mass2 quartic vacuum t : ℝ) :
    finiteState ε h hε hh n a wL wR p C b P ha hL hR ∈
      (hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t).domain :=
  LinearPMap.mem_domain_of_mem_graph
    (finite_hamiltonian_graph ε h hε hh hb n a wL wR p C b P ha hL hR mass2 quartic vacuum t)
end Finite

#print axioms component_graph
#print axioms hamiltonian_graph
#print axioms hamiltonian_domain
#print axioms finiteState_zeroSector
#print axioms finite_component_graph
#print axioms finite_hamiltonian_graph
#print axioms finite_hamiltonian_domain
end
end UnifiedTheory.Audit.KFCausalIndependentRadialHamiltonian
