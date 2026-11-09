/- Full completed-form response bound for every reciprocal Gaussian w>=1.
One constant depends only on h, not width w, epsilon, Gaussian clock width,
or Hamiltonian time. Arbitrary superpositions require a separate estimate. -/
import UnifiedTheory.Audit.KFCausalReciprocalGaussianClockBound
import UnifiedTheory.Audit.KFCausalReciprocalGaussianClockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalReciprocalGaussianUniformResponse
noncomputable section
open MeasureTheory
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorShiftedOutput (shift_bound)
open KFCausalReciprocalGaussianClockMarginal
open KFCausalReciprocalGaussianResponse
open KFCausalReciprocalGaussianHamiltonian (fullEnergy fullResponse)

theorem exists_uniform_potential_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a w : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a) (hw : 1 ≤ w)
      (hb : |h| ≤ 2*Real.pi*ε/3),
      -((C+2)/ε)*potentialEnergy ε a h w hε ha hh hw hb ≤
        potentialResponse ε a h w hε ha hh hw hb := by
  obtain ⟨C,hC,hB⟩ := KFCausalReciprocalGaussianClockBound.uniform_width_clock_bound
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h)
  refine ⟨C,hC,?_⟩
  intro ε a w hε ha hw hb
  rw [potentialEnergy_clock_integral,potentialResponse_clock_integral]
  exact hB w ε a 0 (-h/2) hw hε ha (shift_bound ε h hb)

theorem exists_uniform_full_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a w : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a) (hw : 1 ≤ w)
      (hb : |h| ≤ 2*Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*fullEnergy ε a h w hε ha hh hw hb 1 1 1 t ≤
        fullResponse ε a h w hε ha hh hw hb 1 1 1 t := by
  obtain ⟨C,hC,hpot⟩ := exists_uniform_potential_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a w hε ha hw hb t
  have hp := hpot ε a w hε ha hw hb
  have hc := clockKinetic_lower ε a h w hε ha hh hw hb t
  have hE : 0 ≤ clockKineticEnergy ε a h w hε ha hh hw hb t := by
    unfold clockKineticEnergy factorEnergy
    positivity
  have hκ : 1/(4*ε) ≤ (C+2)/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hk : -((C+2)/ε)*clockKineticEnergy ε a h w hε ha hh hw hb t ≤
      clockKineticResponse ε a h w hε ha hh hw hb t :=
    (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hE).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [unit_full_energy, unit_full_response]
  convert hs using 1
  ring

#print axioms exists_uniform_potential_response
#print axioms exists_uniform_full_response
end
end UnifiedTheory.Audit.KFCausalReciprocalGaussianUniformResponse
