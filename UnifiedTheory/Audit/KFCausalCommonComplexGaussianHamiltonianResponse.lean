/- The actual full Hamiltonian response has a uniform lower bound for every
nonnegative mass, quartic and vacuum coupling, including zero. The state
class has arbitrary coherent charged widths and amplitudes, one common
complex neutral source and P=1. The strong operator pairing retains the
original narrower shift strip and its constructed Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalCommonComplexGaussianPotentialResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonComplexGaussianHamiltonianResponse
noncomputable section
open KFCausalCommonComplexQuarticJointAngular (source)
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
open KFCausalReciprocalNeutralConstantResponse (clockKinetic_lower)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralStrongHamiltonian (hamiltonian_domain hamiltonian_action)

variable (mass2 quartic vacuum : ℝ) (n : ℕ) (ε h A D : ℝ)
  (a w p : Fin n → ℝ) (C : Fin n → ℂ)
  (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i)
local notation "b" => fun _ : Fin n => source A D
local notation "P" => fun _ : Fin n => (1:Polynomial ℂ)

private theorem full_energy_split (hb : |h|≤2*Real.pi*ε/3)
    (hmass : 0≤mass2) (hquartic : 0≤quartic) (hvacuum : 0≤vacuum) (t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_energy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticEnergy potentialEnergy factorEnergy
  ring

private theorem full_response_split (hb : |h|≤2*Real.pi*ε/3)
    (hmass : 0≤mass2) (hquartic : 0≤quartic) (hvacuum : 0≤vacuum) (t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_response n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticResponse potentialResponse factorRate
  norm_num [Complex.add_im,Complex.div_im,Complex.mul_im]
  ring

private theorem potentialEnergy_nonnegative (hb : |h|≤2*Real.pi*ε/3)
    (hmass : 0≤mass2) (hquartic : 0≤quartic) (hvacuum : 0≤vacuum) :
    0≤potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  unfold potentialEnergy
  positivity

theorem full_bound : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤2*Real.pi*ε/3) (t : ℝ),
    -(M/ε)*fullEnergy n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb mass2 quartic vacuum t≤
    fullResponse n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb mass2 quartic vacuum t := by
  obtain ⟨M₀,hM₀,hbound⟩ :=
    KFCausalCommonComplexGaussianPotentialResponse.potential_response_lower
  let M := max M₀ 1
  have hM : 0≤M := le_trans zero_le_one (le_max_right M₀ 1)
  have hM₀M : M₀≤M := le_max_left M₀ 1
  have h1M : (1/4:ℝ)≤M := by linarith [le_max_right M₀ 1]
  refine ⟨M,hM,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw hb t
  have hp0 := hbound mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C
    hε ha hh hw hb
  have hpe := potentialEnergy_nonnegative mass2 quartic vacuum n ε h A D a w p C
    hε ha hh hw hb hmass hquartic hvacuum
  have hμ : M₀/ε≤M/ε := div_le_div_of_nonneg_right hM₀M hε.le
  have hp := (mul_le_mul_of_nonneg_right (neg_le_neg hμ) hpe).trans hp0
  have hc := clockKinetic_lower n ε h a w p C (fun _=>source A D) hε ha hh hw hb t
  have he := clockKinetic_nonnegative n ε h a w p C (fun _=>source A D) (fun _=>1)
    hε ha hh hw hb t
  have hκ : 1/(4*ε)≤M/ε := by
    rw [show 1/(4*ε)=(1/4)/ε by ring]
    exact div_le_div_of_nonneg_right h1M hε.le
  have hk := (mul_le_mul_of_nonneg_right (neg_le_neg hκ) he).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [full_energy_split mass2 quartic vacuum n ε h A D a w p C hε ha hh hw hb
      hmass hquartic hvacuum t,
    full_response_split mass2 quartic vacuum n ε h A D a w p C hε ha hh hw hb
      hmass hquartic hvacuum t]
  convert hs using 1
  ring

theorem hamiltonian_bound : ∃ M : ℝ,0≤M ∧ ∀ (mass2 quartic vacuum : ℝ),
    0≤mass2→0≤quartic→0≤vacuum→
    ∀ (n : ℕ) (ε h A D : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
    (hε : 0<ε) (ha : ∀i,0<a i) (hh : h≠0) (hw : ∀i,1≤w i)
    (hb : |h|≤Real.pi*ε/3) (t : ℝ),
    let ψ := KFCausalReciprocalNeutralSuperposition.state n ε h a w p C
      (fun _=>source A D) (fun _=>1) hε ha hh hw;
    let Bψ := KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C
      (fun _=>source A D) (fun _=>1) hε ha hh hw;
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t;
    let ψH : H.domain := ⟨ψ,hamiltonian_domain n ε h a w p C
      (fun _=>source A D) (fun _=>1) hε ha hh hw hb mass2 quartic vacuum t⟩;
    -(M/ε)*(inner ℂ (H ψH) ψ).re≤(-2/h)*(inner ℂ (H ψH) Bψ).im := by
  obtain ⟨M,hM,hbound⟩ := full_bound
  refine ⟨M,hM,?_⟩
  intro mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw hb t
  dsimp only
  rw [hamiltonian_action n ε h a w p C (fun _=>source A D) (fun _=>1)
      hε ha hh hw hb mass2 quartic vacuum t,
    ←KFCausalReciprocalNeutralStrongResponse.energy_identity
      n ε h a w p C (fun _=>source A D) (fun _=>1) hε ha hh hw hb mass2 quartic vacuum t,
    ←KFCausalReciprocalNeutralStrongResponse.response_identity
      n ε h a w p C (fun _=>source A D) (fun _=>1) hε ha hh hw hb mass2 quartic vacuum t]
  exact hbound mass2 quartic vacuum hmass hquartic hvacuum n ε h A D a w p C hε ha hh hw
    (original_strip ε h hε hb) t

#print axioms full_bound
#print axioms hamiltonian_bound
end
end UnifiedTheory.Audit.KFCausalCommonComplexGaussianHamiltonianResponse
