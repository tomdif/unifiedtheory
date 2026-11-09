/- Every actual second Hamiltonian output of the reciprocal Gaussian is
in the pure-clock domain. Sums and charge projection preserve that domain,
so B H_t psi is defined for every finite reciprocal superposition. -/
import UnifiedTheory.Audit.KFCausalFullClockPureDomain
import UnifiedTheory.Audit.KFCausalKineticSecondPureDomain
import UnifiedTheory.Audit.KFCausalReciprocalSuperpositionStrongResponse
import UnifiedTheory.Audit.KFCausalPureClockZeroProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalReciprocalHamiltonianPureDomain
noncomputable section
open KFCausalConfigurationTestSpace (Hilbert)
open KFCausalClockFloorPureClockMomentum (pureMomentum)
open KFCausalReciprocalSqueezeTransport (transport)
open KFCausalReciprocalGaussianDomain
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalReciprocalGaussianStrongHamiltonian (seconds output)
open KFCausalJointSecondPairing (secondWeighted)
open KFCausalPhysicalEnergyFactors (energyWeight)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalGaussianVacuumSquare (original_strip)

theorem transport_domain (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : h ≠ 0)
    (t : ℝ) (f : Hilbert) (hf : f ∈ (pureMomentum ε hε h).domain) :
    transport t f ∈ (pureMomentum ε hε h).domain :=
  LinearPMap.mem_domain_of_mem_graph (KFCausalReciprocalGaussianMomentum.pure_graph_transport ε hε h hh t _ _
    ((pureMomentum ε hε h).mem_graph ⟨f,hf⟩))

variable (ε a h w : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hw : 1 ≤ w)
  (hb : |h| ≤ Real.pi*ε/3)
local notation "t" => Real.log w/2
local notation "ht" => div_nonneg (Real.log_nonneg hw) (by norm_num : (0:ℝ) ≤ 2)
local notation "α" => groundWidth h
local notation "β" => baseWidth h t
local notation "hα" => groundWidth_positive h hh
local notation "hβ" => baseWidth_positive h hh t
local notation "hbw" => baseWidth_bound h hh t ht
local notation "B" => pureMomentum ε hε h

theorem clock_domain :
    KFCausalReciprocalGaussianClockKineticSquare.clockOutput ε a h w hε ha hh hw ∈ (B).domain :=
  (B).domain.smul_mem _ (transport_domain ε hε h hh (-t) _
    (KFCausalFullClockPureDomain.output_domain ε a α β hε ha hα hβ hbw 1 0 0 h hh))

include hw in
theorem kinetic_domain (i : Fin 4) :
    KFCausalReciprocalGaussianClockKineticSquare.kineticOutput ε a h w hε ha hh i ∈ (B).domain :=
  (B).domain.smul_mem _ ((B).domain.smul_mem _ (transport_domain ε hε h hh (-t) _
    (KFCausalKineticSecondPureDomain.square_domain ε a α β hε ha hα hβ hbw h hh _)))

theorem linear_domain :
    KFCausalReciprocalGaussianMatterSquare.linearOutput ε a h w hε ha hh hw hb ∈ (B).domain :=
  (B).domain.smul_mem _ ((B).domain.smul_mem _ (transport_domain ε hε h hh (-t) _
    (KFCausalGaussianSecondPureClockDomain.matter_square_domain ε a α β hε ha hα hβ hbw h hh hb 0)))

theorem quadratic_domain :
    KFCausalReciprocalGaussianMatterSquare.quadraticOutput ε a h w hε ha hh hw hb ∈ (B).domain :=
  (B).domain.smul_mem _ ((B).domain.smul_mem _ (transport_domain ε hε h hh (-t) _
    (KFCausalGaussianSecondPureClockDomain.matter_square_domain ε a α β hε ha hα hβ hbw h hh hb 1)))

theorem vacuum_domain :
    KFCausalReciprocalGaussianVacuumSquare.stateOutput ε a h w hε ha hh hw hb ∈ (B).domain :=
  (B).domain.smul_mem _ (transport_domain ε hε h hh (-t) _
    (KFCausalGaussianSecondPureClockDomain.vacuum_square_domain ε a α β hε ha hα hβ hbw h hh hb 1 0 0))

theorem seconds_domain (j : Fin 8) : seconds ε a h w hε ha hh hw hb j ∈ (B).domain := by
  fin_cases j
  · exact clock_domain ε a h w hε ha hh hw
  · exact kinetic_domain ε a h w hε ha hh hw 0
  · exact kinetic_domain ε a h w hε ha hh hw 1
  · exact kinetic_domain ε a h w hε ha hh hw 2
  · exact kinetic_domain ε a h w hε ha hh hw 3
  · exact linear_domain ε a h w hε ha hh hw hb
  · exact quadratic_domain ε a h w hε ha hh hw hb
  · exact vacuum_domain ε a h w hε ha hh hw hb

theorem output_domain (mass2 quartic vacuum τ : ℝ) :
    output ε a h w hε ha hh hw hb mass2 quartic vacuum τ ∈ (B).domain := by
  have hs : secondWeighted (energyWeight mass2 quartic vacuum τ) (seconds ε a h w hε ha hh hw hb) ∈ (B).domain :=
    (B).domain.sum_mem (fun j _ => (B).domain.smul_mem _ (seconds_domain ε a h w hε ha hh hw hb j))
  exact LinearPMap.mem_domain_of_mem_graph (KFCausalPureClockZeroProjection.projected_graph ε hε h hh _ _
    ((B).mem_graph ⟨_,hs⟩))

theorem action_domain (mass2 quartic vacuum τ : ℝ) :
    hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum τ
      ⟨KFCausalReciprocalGaussianCharge.state ε a h w hε ha hh (by linarith),
        KFCausalReciprocalGaussianStrongHamiltonian.hamiltonian_domain ε a h w hε ha hh hw hb mass2 quartic vacuum τ⟩ ∈ (B).domain := by
  rw [KFCausalReciprocalGaussianStrongHamiltonian.hamiltonian_action ε a h w hε ha hh hw hb]
  exact output_domain ε a h w hε ha hh hw hb mass2 quartic vacuum τ

omit a w ha hw in
theorem finite_output_domain (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (mass2 quartic vacuum τ : ℝ) :
    KFCausalReciprocalSuperpositionStrongResponse.hamiltonianOutput n ε h a w c hε ha hh hw hb
      mass2 quartic vacuum τ ∈ (B).domain :=
  (B).domain.sum_mem (fun i _ => (B).domain.smul_mem (c i)
    (output_domain ε (a i) h (w i) hε (ha i) hh (hw i) hb mass2 quartic vacuum τ))

omit a w ha hw in
theorem finite_action_domain (n : ℕ) (a w : Fin n → ℝ) (c : Fin n → ℂ)
    (ha : ∀ i, 0 < a i) (hw : ∀ i, 1 ≤ w i) (mass2 quartic vacuum τ : ℝ) :
    hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum τ
      ⟨KFCausalReciprocalSuperpositionFactors.state n ε h a w c hε ha hh hw,
        KFCausalReciprocalSuperpositionStrongResponse.hamiltonian_domain n ε h a w c hε ha hh hw hb mass2 quartic vacuum τ⟩ ∈
      (B).domain := by
  rw [KFCausalReciprocalSuperpositionStrongResponse.hamiltonian_action n ε h a w c hε ha hh hw hb]
  exact finite_output_domain ε h hε hh hb n a w c ha hw mass2 quartic vacuum τ

#print axioms transport_domain
#print axioms clock_domain
#print axioms kinetic_domain
#print axioms linear_domain
#print axioms quadratic_domain
#print axioms vacuum_domain
#print axioms seconds_domain
#print axioms output_domain
#print axioms action_domain
#print axioms finite_output_domain
#print axioms finite_action_domain
end
end UnifiedTheory.Audit.KFCausalReciprocalHamiltonianPureDomain
