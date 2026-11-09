/- A uniform lower bound for the actual potential response of every
finite neutral packet superposition, allowing a separate positive width
and arbitrary real frequency in each clock factor. No evolution-domain
or charged-excitation extension is asserted. -/
import UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralMixedClockBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
  (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse (physicalWeights)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockPairing (clockCoefficients)
open UnifiedTheory.Audit.KFCausalNeutralMixedClockPotential

theorem potentialEnergy_nonnegative (ε h : ℝ) (N : ℕ) (a p : Fin N → ℝ)
    (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (ha : ∀ i, 0 < a i) (hb : |h| ≤ 2*Real.pi*ε/3) :
    0 ≤ potentialEnergy ε h N a p b C P hε hh ha hb := by
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg _ (sq_nonneg _)
  fin_cases n <;> norm_num [physicalWeights]

theorem exists_uniform_physical_response_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hb : |h| ≤ 2*Real.pi*ε/3,
      ∀ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
        (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
        -((M+2)/ε)*potentialEnergy ε h N a p b C P hε hh ha hb ≤
          potentialResponse ε h N a p b C P hε hh ha hb := by
  obtain ⟨M,hM,hbound⟩ := KFCausalNeutralFiniteResponse.exists_uniform_response_bound
    (groundWidth h) (groundWidth_positive h hh)
  refine ⟨M,hM,?_⟩
  intro ε hε hb N a p ha b C P
  have hp (s : ℝ) := hbound (neutralWidth h) ε (-h/2)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)
    (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num))
    N b (clockCoefficients ε h N a p C s) P s
  rw [← realEnergy_integral ε h N a p b C P hε hh ha hb,
    ← realResponse_integral ε h N a p b C P hε hh ha hb,← integral_const_mul]
  apply integral_mono ((realEnergy_integrable ε h N a p b C P hε hh ha hb).const_mul _)
    (realResponse_integrable ε h N a p b C P hε hh ha hb)
  intro s
  simpa only [wholeEnergy_frozen,wholeResponse_frozen,
    KFCausalNeutralFiniteResponse.realKernel] using hp s

theorem physical_response_lower_exists (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ (N : ℕ) (a p : Fin N → ℝ) (ha : ∀ i, 0 < a i)
      (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
      -κ*potentialEnergy ε h N a p b C P hε hh ha hb ≤
        potentialResponse ε h N a p b C P hε hh ha hb := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_physical_response_bound h hh
  exact ⟨(M+2)/ε,by positivity,hbound ε hε hb⟩

#print axioms potentialEnergy_nonnegative
#print axioms exists_uniform_physical_response_bound
#print axioms physical_response_lower_exists
end
end UnifiedTheory.Audit.KFCausalNeutralMixedClockBound
