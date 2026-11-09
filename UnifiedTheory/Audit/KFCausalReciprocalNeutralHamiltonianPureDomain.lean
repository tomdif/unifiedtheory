/- The constructed full Hamiltonian output of the finite joint family
lies in the actual pure-clock domain. Polynomial second-output domains,
reciprocal transport, finite sums and charge projection discharge every
domain obligation for the opposite composition B H_t. -/
import UnifiedTheory.Audit.KFCausalPolynomialSecondPureDomain
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongHamiltonian
import UnifiedTheory.Audit.KFCausalReciprocalHamiltonianPureDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonianPureDomain
noncomputable section
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalReciprocalGaussianDomain (baseWidth baseWidth_positive baseWidth_bound)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalReciprocalNeutralPackets (rescaledPolynomial)
open KFCausalNeutralExponentialProfiles (neutralSource)
open KFCausalReciprocalHamiltonianPureDomain (transport_domain)
open KFCausalReciprocalNeutralStrongHamiltonian (seconds hamiltonianOutput hamiltonian_domain hamiltonian_action)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalGaussianVacuumSquare (original_strip)

theorem packet_second_domain (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hw : 1 ≤ w) (hb : |h| ≤ Real.pi*ε/3) (C : ℂ) (p : ℝ) (b : ℂ) (P : Polynomial ℂ) (j : Fin 8) :
    KFCausalReciprocalNeutralSecondFactors.second ε a h w hε ha hh hw hb C p b P j ∈
      (pureMomentum ε hε h).domain := by
  let t := Real.log w/2
  have ht : 0 ≤ t := div_nonneg (Real.log_nonneg hw) (by norm_num)
  exact (pureMomentum ε hε h).domain.smul_mem _ ((pureMomentum ε hε h).domain.smul_mem _
    (transport_domain ε hε h hh (-t) _
      (KFCausalPolynomialSecondPureDomain.second_domain ε a (groundWidth h) (baseWidth h t)
        hε ha (groundWidth_positive h hh) (baseWidth_positive h hh t) (baseWidth_bound h hh t ht)
        h hh hb C p (neutralSource ((Real.exp (-t):ℂ)*b)) 4 (rescaledPolynomial t P) j)))

variable (n : ℕ) (ε h : ℝ) (a w p : Fin n → ℝ) (C b : Fin n → ℂ)
  (P : Fin n → Polynomial ℂ) (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0)
  (hw : ∀ i, 1 ≤ w i) (hb : |h| ≤ Real.pi*ε/3)
local notation "B" => pureMomentum ε hε h

theorem seconds_domain (j : Fin 8) : seconds n ε h a w p C b P hε ha hh hw hb j ∈ (B).domain :=
  (B).domain.sum_mem (fun i _ => packet_second_domain ε (a i) h (w i) hε (ha i) hh (hw i) hb
    (C i) (p i) (b i) (P i) j)

theorem output_domain (mass2 quartic vacuum t : ℝ) :
    hamiltonianOutput n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t ∈ (B).domain := by
  have hs : secondWeighted (energyWeight mass2 quartic vacuum t)
      (seconds n ε h a w p C b P hε ha hh hw hb) ∈ (B).domain :=
    (B).domain.sum_mem (fun j _ => (B).domain.smul_mem _
      (seconds_domain n ε h a w p C b P hε ha hh hw hb j))
  exact LinearPMap.mem_domain_of_mem_graph (KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _
    ((B).mem_graph ⟨_,hs⟩))

theorem action_domain (mass2 quartic vacuum t : ℝ) :
    hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t
      ⟨KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw,
        hamiltonian_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩ ∈ (B).domain := by
  rw [hamiltonian_action n ε h a w p C b P hε ha hh hw hb]
  exact output_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t

#print axioms packet_second_domain
#print axioms seconds_domain
#print axioms output_domain
#print axioms action_domain
end
end UnifiedTheory.Audit.KFCausalReciprocalNeutralHamiltonianPureDomain
