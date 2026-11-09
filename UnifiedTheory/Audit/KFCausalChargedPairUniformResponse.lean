/- Uniform relative lower response bound for the actual paired quadratic
state in the completed unit-coupling Hamiltonian form. Clock width and
Hamiltonian time are unrestricted. This is a fixed-state diagonal bound;
it does not assert a bound for superpositions or an evolving trajectory. -/
import UnifiedTheory.Audit.KFCausalChargedPairKernelGrowth
import UnifiedTheory.Audit.KFCausalChargedPairClockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000

namespace UnifiedTheory.Audit.KFCausalChargedPairUniformResponse
noncomputable section
open MeasureTheory
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorShiftedOutput (shift_bound)
open KFCausalChargedPairClockMarginal
open KFCausalChargedPairHamiltonianResponse
open KFCausalPositiveKernelClockResponse (energy weakResponse reducedResponse)

theorem physicalKernel_smooth (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ContDiff ℝ 1 (physicalKernel ε h) :=
  KFCausalChargedPairKernelGrowth.actual_kernel_smooth (groundWidth h) (neutralWidth h)
    ε (-h/2) (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (neutralWidth_bound h) hε (shift_bound ε h hb)

theorem physicalKernel_positive (ε h s : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : 0 < physicalKernel ε h s :=
  KFCausalChargedPairKernelGrowth.actual_kernel_positive (groundWidth h) (neutralWidth h)
    ε (-h/2) s (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (neutralWidth_bound h) hε (shift_bound ε h hb)

theorem exists_uniform_physical_kernel_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ s, |deriv (physicalKernel ε h) s| ≤ C*physicalKernel ε h s := by
  obtain ⟨C,hC,hb⟩ := KFCausalChargedPairKernelGrowth.exists_uniform_derivative_bound
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh)
      (neutralWidth_positive h hh) (neutralWidth_bound h)
  exact ⟨C,hC,fun ε hε he s => hb ε (-h/2) s hε (shift_bound ε h he)⟩

theorem exists_uniform_potential_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a)
      (hb : |h| ≤ 2*Real.pi*ε/3),
      potentialResponse ε a h hε ha hh hb =
        (∫ s, reducedResponse ε a 0 (-h/2) (physicalKernel ε h) s) ∧
      -((C+2)/ε)*potentialEnergy ε a h hε ha hh hb ≤
        potentialResponse ε a h hε ha hh hb := by
  obtain ⟨C,hC,hd⟩ := exists_uniform_physical_kernel_bound h hh
  refine ⟨C,hC,?_⟩
  intro ε a hε ha hb
  have he := KFCausalPositiveKernelClockResponse.full_clock_identity_and_bound
    ε a 0 (-h/2) C (physicalKernel ε h) hε (shift_bound ε h hb) hC
    (physicalKernel_smooth ε h hε hh hb)
    (fun s => (physicalKernel_positive ε h s hε hh hb).le) (hd ε hε hb)
    (clock_energy_integrable ε a h hε ha hh hb)
    (clock_response_integrable ε a h hε ha hh hb)
  rw [← potentialEnergy_clock_integral ε a h hε ha hh hb,
    ← potentialResponse_clock_integral ε a h hε ha hh hb] at he
  exact he

theorem exists_uniform_full_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a)
      (hb : |h| ≤ 2*Real.pi*ε/3) (t : ℝ),
      -((C+2)/ε)*fullEnergy ε a h hε ha hh hb 1 1 1 t ≤
        fullResponse ε a h hε ha hh hb 1 1 1 t := by
  obtain ⟨C,hC,hpot⟩ := exists_uniform_potential_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a hε ha hb t
  have hp := (hpot ε a hε ha hb).2
  have hc := clockKinetic_lower ε a h hε ha hh hb t
  have hE : 0 ≤ clockKineticEnergy ε a h hε ha hh hb t := by
    unfold clockKineticEnergy KFCausalChargedPairFactorResponse.factorEnergy
    positivity
  have hκ : 1/(4*ε) ≤ (C+2)/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hk : -((C+2)/ε)*clockKineticEnergy ε a h hε ha hh hb t ≤
      clockKineticResponse ε a h hε ha hh hb t :=
    (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hE).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [unit_full_energy, unit_full_response]
  convert hs using 1
  ring

#print axioms physicalKernel_smooth
#print axioms physicalKernel_positive
#print axioms exists_uniform_physical_kernel_bound
#print axioms exists_uniform_potential_response
#print axioms exists_uniform_full_response
end
end UnifiedTheory.Audit.KFCausalChargedPairUniformResponse
