/- The actual full Hamiltonian response has the same uniform lower bound
for every nonnegative mass, quartic and vacuum coupling, including zero.
The state class has arbitrary coherent charged widths and amplitudes, one
common purely imaginary neutral source and P=1. The strong operator pairing retains
the original narrower shift strip and its constructed Hamiltonian domain. -/
import UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianPotentialResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianHamiltonianResponse
noncomputable section
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
open KFCausalReciprocalNeutralConstantResponse (clockKinetic_lower)
open KFCausalWeightedReciprocalNeutralPotentialTransport (potentialEnergy potentialResponse)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralStrongHamiltonian (hamiltonian_domain hamiltonian_action)

variable (mass2 quartic vacuum : ℝ) (n : ℕ) (ε h D : ℝ)
  (a w p : Fin n → ℝ) (C : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
local notation "b" => fun _ : Fin n => (D:ℂ)*Complex.I
local notation "P" => fun _ : Fin n => (1:Polynomial ℂ)

private theorem full_energy_split (hb : |h| ≤ 2*Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (t : ℝ) :
    fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticEnergy n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialEnergy mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_energy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticEnergy potentialEnergy factorEnergy
  ring

private theorem full_response_split (hb : |h| ≤ 2*Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (t : ℝ) :
    fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t =
      clockKineticResponse n ε h a w p C b P hε ha hh hw hb t+
        Real.exp (2*t)*potentialResponse mass2 quartic vacuum n ε h a w p C b P hε ha hh hw hb := by
  rw [physical_response n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t hmass hquartic hvacuum]
  unfold clockKineticResponse potentialResponse factorRate
  norm_num [Complex.add_im,Complex.div_im,Complex.mul_im]
  ring

theorem full_bound (hb : |h| ≤ 2*Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (t : ℝ) :
    -(136/ε)*fullEnergy n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t ≤
      fullResponse n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t := by
  have hp := KFCausalCommonImaginaryGaussianPotentialResponse.potential_response_lower
    mass2 quartic vacuum n ε h D a w p C hε ha hh hw hb hmass hquartic hvacuum
  have hc := clockKinetic_lower n ε h a w p C b hε ha hh hw hb t
  have he := clockKinetic_nonnegative n ε h a w p C b P hε ha hh hw hb t
  have hκ : 1/(4*ε) ≤ 136/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hε.le
  have hk := (mul_le_mul_of_nonneg_right (neg_le_neg hκ) he).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [full_energy_split mass2 quartic vacuum n ε h D a w p C hε ha hh hw hb hmass hquartic hvacuum,
    full_response_split mass2 quartic vacuum n ε h D a w p C hε ha hh hw hb hmass hquartic hvacuum]
  convert hs using 1
  ring

local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Bψ" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C b P hε ha hh hw

theorem hamiltonian_bound (hb : |h| ≤ Real.pi*ε/3)
    (hmass : 0 ≤ mass2) (hquartic : 0 ≤ quartic) (hvacuum : 0 ≤ vacuum) (t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb) mass2 quartic vacuum t;
    let ψH : H.domain := ⟨ψ,hamiltonian_domain n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t⟩;
    -(136/ε)*(inner ℂ (H ψH) ψ).re ≤ (-2/h)*(inner ℂ (H ψH) Bψ).im := by
  dsimp only
  rw [hamiltonian_action n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t]
  rw [← KFCausalReciprocalNeutralStrongResponse.energy_identity
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t,
    ← KFCausalReciprocalNeutralStrongResponse.response_identity
    n ε h a w p C b P hε ha hh hw hb mass2 quartic vacuum t]
  exact full_bound mass2 quartic vacuum n ε h D a w p C hε ha hh hw
    (original_strip ε h hε hb) hmass hquartic hvacuum t

#print axioms full_bound
#print axioms hamiltonian_bound
end
end UnifiedTheory.Audit.KFCausalCommonImaginaryGaussianHamiltonianResponse
