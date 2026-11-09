/- Uniform full completed-Hamiltonian response with independent clocks.
The actual potential pairing equals the previously bounded density; the
clock and kinetic factors supply the remaining lower bound. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockOrderedBridge
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockFullBound
noncomputable section
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanMixedClockHamiltonian
open KFCausalPairedSpanMixedClockOrderedBridge (potentialEnergy_integral potentialResponse_integral)

theorem exists_uniform_potential_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a b p q : ℝ,
      ∀ (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b) (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients),
        -((C+2)/ε)*potentialEnergy ε a b h p q hε ha hbw hh hb c ≤
          potentialResponse ε a b h p q hε ha hbw hh hb c := by
  obtain ⟨C,hC,hbound⟩ := KFCausalPairedSpanMixedClockResponse.exists_uniform_potential_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a b p q hε ha hbw hb c
  rw [potentialEnergy_integral,potentialResponse_integral]
  exact (hbound ε a b p q hε ha hbw hb c).2

theorem exists_uniform_full_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a b p q : ℝ,
      ∀ (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b) (hb : |h| ≤ 2*Real.pi*ε/3)
        (c : Coefficients) (t : ℝ),
        -((C+2)/ε)*fullEnergy ε a b h p q hε ha hbw hh hb c 1 1 1 t ≤
          fullResponse ε a b h p q hε ha hbw hh hb c 1 1 1 t := by
  obtain ⟨C,hC,hpot⟩ := exists_uniform_potential_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a b p q hε ha hbw hb c t
  have hp := hpot ε a b p q hε ha hbw hb c
  have hc := clockKinetic_lower ε a b h p q hε ha hbw hh hb c t
  have hE : 0 ≤ clockKineticEnergy ε a b h p q hε ha hbw hh hb c t := by
    unfold clockKineticEnergy KFCausalPairedSpanMixedClockDomain.factorEnergy
    positivity
  have hκ : 1/(4*ε) ≤ (C+2)/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hk : -((C+2)/ε)*clockKineticEnergy ε a b h p q hε ha hbw hh hb c t ≤
      clockKineticResponse ε a b h p q hε ha hbw hh hb c t :=
    (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hE).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [unit_full_energy,unit_full_response]
  convert hs using 1
  ring

#print axioms exists_uniform_potential_response
#print axioms exists_uniform_full_response
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockFullBound
