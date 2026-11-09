/- A uniform relative response lower bound for all neutral position
and momentum displacements, all clock positions and all finite neutral
polynomials. The constant is independent of those displacements. -/
import UnifiedTheory.Audit.KFCausalNeutralDisplacedKernel
import UnifiedTheory.Audit.KFCausalCenteredPolynomialResponseBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralDisplacedResponseBound
noncomputable section
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse
open UnifiedTheory.Audit.KFCausalHermiteResponseHierarchy
open UnifiedTheory.Audit.KFCausalNeutralProfileGrowth
open UnifiedTheory.Audit.KFCausalNeutralDisplacedSources
open UnifiedTheory.Audit.KFCausalNeutralDisplacedKernel
open UnifiedTheory.Audit.KFCausalCenteredPolynomialResponseBound (derivative_le_of_exponential_growth)

theorem realKernel_nonnegative (ε h Q K : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    0 ≤ realKernel ε h Q K P s := by
  exact kernel_self_nonnegative ε h (neutralParameter Q) (neutralParameter K) (physicalWeights 1 1 1) P hε hh hb
    (fun n => by fin_cases n <;> norm_num [physicalWeights]) s

theorem exists_uniform_kernel_growth (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (Q K : ℝ) (P : Polynomial ℂ) (s t : ℝ), s ≤ t →
        realKernel ε h Q K P t ≤ Real.exp (C*(t-s))*realKernel ε h Q K P s := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_profileEnergy_growth (groundWidth h) (groundWidth_positive h hh)
  refine ⟨C,hC,?_⟩
  intro ε hε hb Q K P s t hst
  rw [realKernel_eq_profileEnergy ε h Q K P hε hh hb,
    realKernel_eq_profileEnergy ε h Q K P hε hh hb]
  exact hg (neutralWidth h) ε (-h/2) hε (shift_bound ε h hb)
    (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)) (displacedProfile h Q K P) s t hst
    (displacedProfile_integrable ε h Q K P hε hh hb s)
    (displacedProfile_integrable ε h Q K P hε hh hb t)

theorem exists_uniform_kernel_derivative (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (Q K : ℝ) (P : Polynomial ℂ) (s : ℝ),
        deriv (realKernel ε h Q K P) s ≤ C*realKernel ε h Q K P s := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_kernel_growth h hh
  refine ⟨C,hC,?_⟩
  intro ε hε hb Q K P s
  exact derivative_le_of_exponential_growth _ C
    (fun u => (realKernel_derivative ε h Q K P hε hh hb u).differentiableAt) (hg ε hε hb Q K P) s

theorem exists_uniform_reducedResponse_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (Q K : ℝ) (P : Polynomial ℂ) (s : ℝ),
        -((C+2)/ε)*realKernel ε h Q K P s ≤
          (reducedResponse ε h (neutralParameter Q) (neutralParameter K) (physicalWeights 1 1 1) P P s).re := by
  obtain ⟨C,hC,hd⟩ := exists_uniform_kernel_derivative h hh
  refine ⟨C,hC,?_⟩
  intro ε hε hb Q K P s
  have hT := realKernel_nonnegative ε h Q K P hε hh hb s
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hec : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right
    (coefficient_lower ε (-h/2) s hε (shift_bound ε h hb)) hT
  have hder : deriv (realKernel ε h Q K P) s/clock ε s ≤ (C/ε)*realKernel ε h Q K P s := by
    calc
      _ ≤ (C*realKernel ε h Q K P s)/clock ε s :=
        div_le_div_of_nonneg_right (hd ε hε hb Q K P s) hc.le
      _ = (C/clock ε s)*realKernel ε h Q K P s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC hε hec) hT
  rw [reducedResponse_neutral_re ε h Q K P hε hh hb]
  have he : -((C+2)/ε)*realKernel ε h Q K P s =
      -(2/ε)*realKernel ε h Q K P s-(C/ε)*realKernel ε h Q K P s := by ring
  rw [he]
  linarith

theorem neutral_polynomial_bound_exists (ε h : ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ Q K s,
      PolynomialBound ε h (neutralParameter Q) (neutralParameter K) (physicalWeights 1 1 1) κ s := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_reducedResponse_bound h hh
  exact ⟨(C+2)/ε,by positivity,fun Q K s P => hbound ε hε hb Q K P s⟩

theorem neutral_hermite_bound_exists (ε h : ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ Q K B s N,
      CutoffBound ε h (neutralParameter Q) (neutralParameter K) (physicalWeights 1 1 1) B κ s N := by
  obtain ⟨κ,hκ,hbound⟩ := neutral_polynomial_bound_exists ε h hε hh hb
  refine ⟨κ,hκ,?_⟩
  intro Q K B s N
  exact (polynomial_bound_iff_cutoffs ε h (neutralParameter Q) (neutralParameter K)
    (physicalWeights 1 1 1) B hε hh hb κ s).mp (hbound Q K s) N

#print axioms realKernel_nonnegative
#print axioms exists_uniform_kernel_growth
#print axioms exists_uniform_kernel_derivative
#print axioms exists_uniform_reducedResponse_bound
#print axioms neutral_polynomial_bound_exists
#print axioms neutral_hermite_bound_exists
end
end UnifiedTheory.Audit.KFCausalNeutralDisplacedResponseBound
