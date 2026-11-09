/- The actual signed ordered-potential response is bounded below on
every finite neutral exponential-polynomial state. The same constant
works for all sources, coefficients, degrees, counts and choices of the
common Gaussian clock width.
No density or invariance assertion for the full evolution is made. -/
import UnifiedTheory.Audit.KFCausalNeutralFinitePotential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse (physicalWeights)
open UnifiedTheory.Audit.KFCausalNeutralCrossPairing (clockWeight clockWeight_nonnegative)
open UnifiedTheory.Audit.KFCausalNeutralFinitePotential

theorem potentialEnergy_nonnegative (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    0 ≤ potentialEnergy ε a h hε ha hh hb N b C P := by
  apply Finset.sum_nonneg
  intro n _
  apply mul_nonneg _ (sq_nonneg _)
  fin_cases n <;> norm_num [physicalWeights]

theorem exists_uniform_physical_response_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, ∀ hε : 0 < ε, ∀ hb : |h| ≤ 2*Real.pi*ε/3,
      ∀ a : ℝ, ∀ ha : 0 < a, ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
        -((M+2)/ε)*potentialEnergy ε a h hε ha hh hb N b C P ≤
          potentialResponse ε a h hε ha hh hb N b C P := by
  obtain ⟨M,hM,hbound⟩ := KFCausalNeutralFiniteResponse.exists_uniform_response_bound
    (groundWidth h) (groundWidth_positive h hh)
  refine ⟨M,hM,?_⟩
  intro ε hε hb a ha N b C P
  have hp (s : ℝ) := hbound (neutralWidth h) ε (-h/2)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)
    (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)) N b C P s
  rw [← realEnergy_integral ε a h hε ha hh hb N b C P,
    ← realResponse_integral ε a h hε ha hh hb N b C P,← integral_const_mul]
  apply integral_mono ((realEnergy_integrable ε a h hε ha hh hb N b C P).const_mul _)
    (realResponse_integrable ε a h hε ha hh hb N b C P)
  intro s
  convert mul_le_mul_of_nonneg_left (hp s) (clockWeight_nonnegative ε a h s) using 1
  ring

theorem physical_response_lower_exists (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0)
    (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ a : ℝ, ∀ ha : 0 < a,
      ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ),
        -κ*potentialEnergy ε a h hε ha hh hb N b C P ≤
          potentialResponse ε a h hε ha hh hb N b C P := by
  obtain ⟨M,hM,hbound⟩ := exists_uniform_physical_response_bound h hh
  exact ⟨(M+2)/ε,by positivity,hbound ε hε hb⟩

#print axioms potentialEnergy_nonnegative
#print axioms exists_uniform_physical_response_bound
#print axioms physical_response_lower_exists
end
end UnifiedTheory.Audit.KFCausalNeutralFinitePhysicalBound
