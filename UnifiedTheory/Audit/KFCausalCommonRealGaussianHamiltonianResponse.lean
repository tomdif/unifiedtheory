/- A uniform lower bound for the actual full Hamiltonian response at unit
potential couplings, on finite reciprocal families with a common real neutral
source and constant neutral polynomials. The strong pairing uses the original
Hamiltonian action and retains its narrower shift strip. -/
import UnifiedTheory.Audit.KFCausalCommonRealGaussianPotentialResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralConstantResponse
import UnifiedTheory.Audit.KFCausalReciprocalNeutralStrongResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalCommonRealGaussianHamiltonianResponse
noncomputable section
open KFCausalReciprocalNeutralHamiltonian (fullEnergy fullResponse)
open KFCausalReciprocalNeutralKineticResponse
open KFCausalReciprocalNeutralConstantResponse (clockKinetic_lower)
open KFCausalGaussianVacuumSquare (original_strip)
open KFCausalClockFloorAveragedHamiltonian (hamiltonian)
open KFCausalReciprocalNeutralStrongHamiltonian (hamiltonian_domain hamiltonian_action)

variable (n : ℕ) (ε h B : ℝ) (a w p : Fin n → ℝ) (C : Fin n → ℂ)
  (hε : 0 < ε) (ha : ∀ i, 0 < a i) (hh : h ≠ 0) (hw : ∀ i, 1 ≤ w i)
local notation "b" => fun _ : Fin n => (B:ℂ)
local notation "P" => fun _ : Fin n => (1:Polynomial ℂ)

theorem full_bound (hb : |h| ≤ 2*Real.pi*ε/3) (t : ℝ) :
    -(136/ε)*fullEnergy n ε h a w p C b P hε ha hh hw hb 1 1 1 t ≤
      fullResponse n ε h a w p C b P hε ha hh hw hb 1 1 1 t := by
  have hp := KFCausalCommonRealGaussianPotentialResponse.potential_bound
    n ε h B a w p C hε ha hh hw hb
  have hc := clockKinetic_lower n ε h a w p C b hε ha hh hw hb t
  have he := clockKinetic_nonnegative n ε h a w p C b P hε ha hh hw hb t
  have hκ : 1/(4*ε) ≤ 136/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by norm_num) hε.le
  have hk := (mul_le_mul_of_nonneg_right (neg_le_neg hκ) he).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [unit_full_energy,unit_full_response]
  convert hs using 1
  ring

local notation "ψ" => KFCausalReciprocalNeutralSuperposition.state n ε h a w p C b P hε ha hh hw
local notation "Bψ" => KFCausalReciprocalNeutralSuperposition.momentum n ε h a w p C b P hε ha hh hw

theorem hamiltonian_bound (hb : |h| ≤ Real.pi*ε/3) (t : ℝ) :
    let H := hamiltonian ε hε h hh (original_strip ε h hε hb) 1 1 1 t;
    let ψH : H.domain := ⟨ψ,hamiltonian_domain n ε h a w p C b P hε ha hh hw hb 1 1 1 t⟩;
    -(136/ε)*(inner ℂ (H ψH) ψ).re ≤ (-2/h)*(inner ℂ (H ψH) Bψ).im := by
  dsimp only
  rw [hamiltonian_action n ε h a w p C b P hε ha hh hw hb 1 1 1 t]
  rw [← KFCausalReciprocalNeutralStrongResponse.energy_identity
    n ε h a w p C b P hε ha hh hw hb 1 1 1 t,
    ← KFCausalReciprocalNeutralStrongResponse.response_identity
    n ε h a w p C b P hε ha hh hw hb 1 1 1 t]
  exact full_bound n ε h B a w p C hε ha hh hw (original_strip ε h hε hb) t

#print axioms full_bound
#print axioms hamiltonian_bound
end
end UnifiedTheory.Audit.KFCausalCommonRealGaussianHamiltonianResponse
