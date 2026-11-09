/- Uniform full Hamiltonian response on the complex centered/paired/corrected-quartic span.
One constant controls all relative amplitudes and phases, every common
positive Gaussian clock width, and all Hamiltonian times. The interference
terms are included in the actual operator pairings throughout. -/
import UnifiedTheory.Audit.KFCausalQuarticSpanGrowth
import UnifiedTheory.Audit.KFCausalQuarticTripleClockMarginal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalQuarticTripleUniformResponse
noncomputable section
open MeasureTheory
open KFCausalQuarticTripleDomain (Coefficients)
open KFCausalQuarticTripleOrderedOutputs (embedCoefficients)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalClockFloorShiftedOutput (shift_bound)
open KFCausalQuarticTripleClockMarginal
open KFCausalQuarticTripleHamiltonian
open KFCausalPositiveKernelClockResponse (reducedResponse)

theorem physicalKernel_smooth (ε h : ℝ) (c : Coefficients) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) : ContDiff ℝ 1 (physicalKernel ε h c) :=
  KFCausalQuarticSpanGrowth.actual_kernel_smooth (groundWidth h) (neutralWidth h)
    ε (-h/2) (embedCoefficients (groundWidth h) c) (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (neutralWidth_bound h) hε (shift_bound ε h hb)

theorem exists_uniform_physical_kernel_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (c : Coefficients) (s : ℝ),
        |deriv (physicalKernel ε h c) s| ≤ C*physicalKernel ε h c s := by
  obtain ⟨C,hC,hb⟩ := KFCausalQuarticSpanGrowth.exists_uniform_derivative_bound
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh)
      (neutralWidth_positive h hh) (neutralWidth_bound h)
  exact ⟨C,hC,fun ε hε he c s => hb ε (-h/2) hε (shift_bound ε h he) (embedCoefficients (groundWidth h) c) s⟩

theorem exists_uniform_potential_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a)
      (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients),
      potentialResponse ε a h hε ha hh hb c =
        (∫ s, reducedResponse ε a 0 (-h/2) (physicalKernel ε h c) s) ∧
      -((C+2)/ε)*potentialEnergy ε a h hε ha hh hb c ≤
        potentialResponse ε a h hε ha hh hb c := by
  obtain ⟨C,hC,hd⟩ := exists_uniform_physical_kernel_bound h hh
  refine ⟨C,hC,?_⟩
  intro ε a hε ha hb c
  have he := KFCausalPositiveKernelClockResponse.full_clock_identity_and_bound
    ε a 0 (-h/2) C (physicalKernel ε h c) hε (shift_bound ε h hb) hC
    (physicalKernel_smooth ε h c hε hh hb)
    (fun s => KFCausalQuarticSpanKernel.kernel_nonnegative _ _ _ (embedCoefficients (groundWidth h) c)) (hd ε hε hb c)
    (clock_energy_integrable ε a h hε ha hh hb c)
    (clock_response_integrable ε a h hε ha hh hb c)
  rw [← potentialEnergy_clock_integral ε a h hε ha hh hb c,
    ← potentialResponse_clock_integral ε a h hε ha hh hb c] at he
  exact he

theorem exists_uniform_full_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a : ℝ, ∀ (hε : 0 < ε) (ha : 0 < a)
      (hb : |h| ≤ 2*Real.pi*ε/3) (c : Coefficients) (t : ℝ),
      -((C+2)/ε)*fullEnergy ε a h hε ha hh hb c 1 1 1 t ≤
        fullResponse ε a h hε ha hh hb c 1 1 1 t := by
  obtain ⟨C,hC,hpot⟩ := exists_uniform_potential_response h hh
  refine ⟨C,hC,?_⟩
  intro ε a hε ha hb c t
  have hp := (hpot ε a hε ha hb c).2
  have hc := clockKinetic_lower ε a h hε ha hh hb c t
  have hE : 0 ≤ clockKineticEnergy ε a h hε ha hh hb c t := by
    unfold clockKineticEnergy KFCausalQuarticTripleDomain.factorEnergy
    positivity
  have hκ : 1/(4*ε) ≤ (C+2)/ε := by
    rw [show 1/(4*ε) = (1/4)/ε by ring]
    exact div_le_div_of_nonneg_right (by linarith) hε.le
  have hk : -((C+2)/ε)*clockKineticEnergy ε a h hε ha hh hb c t ≤
      clockKineticResponse ε a h hε ha hh hb c t :=
    (mul_le_mul_of_nonneg_right (neg_le_neg hκ) hE).trans hc
  have hs := add_le_add hk (mul_le_mul_of_nonneg_left hp (Real.exp_pos (2*t)).le)
  rw [unit_full_energy,unit_full_response]
  convert hs using 1
  ring

#print axioms physicalKernel_smooth
#print axioms exists_uniform_physical_kernel_bound
#print axioms exists_uniform_potential_response
#print axioms exists_uniform_full_response
end
end UnifiedTheory.Audit.KFCausalQuarticTripleUniformResponse
