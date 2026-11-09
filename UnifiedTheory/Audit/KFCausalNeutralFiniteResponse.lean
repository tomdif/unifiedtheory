/- A relative lower bound for the complete differentiated neutral
superposition kernel. The constant is uniform in the number of sources,
all complex coefficients, all polynomial degrees, and clock position. -/
import UnifiedTheory.Audit.KFCausalNeutralFiniteGram

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralFiniteResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open UnifiedTheory.Audit.KFCausalNeutralProfileMarginal (profileEnergyDensity)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralFiniteGram
open UnifiedTheory.Audit.KFCausalCenteredPolynomialResponseBound (derivative_le_of_exponential_growth)

def realKernel (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) : ℝ :=
  (energyKernel ε y α β N b C P s).re
def reducedResponse (ε y α β : ℝ) (N : ℕ) (b C : Fin N → ℂ)
    (P : Fin N → Polynomial ℂ) (s : ℝ) : ℂ :=
  (coefficient ε y s:ℂ)*energyKernel ε y α β N b C P s-
    energyDerivative ε y α β N b C P s/(clock ε s:ℂ)

theorem realKernel_derivative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    HasDerivAt (realKernel ε y α β N b C P) (energyDerivative ε y α β N b C P s).re s :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (energyKernel_derivative α β ε y s hα hβ hw hε hy N b C P)

theorem reducedResponse_re (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    (reducedResponse ε y α β N b C P s).re =
      coefficient ε y s*realKernel ε y α β N b C P s-
        deriv (realKernel ε y α β N b C P) s/clock ε s := by
  rw [(realKernel_derivative α β ε y s hα hβ hw hε hy N b C P).deriv]
  simp only [reducedResponse,Complex.sub_re,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.div_ofReal_re,realKernel]

theorem realKernel_nonnegative (α β ε y s : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hε : 0 < ε) (hy : |y| ≤ Real.pi*ε/3)
    (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) :
    0 ≤ realKernel ε y α β N b C P s := by
  rw [realKernel,energyKernel_re α β ε y s hα hβ hw hε hy]
  apply integral_nonneg
  intro q
  unfold profileEnergyDensity
  exact mul_nonneg (mul_nonneg (sq_nonneg _)
    (KFCausalQuarticPlaneDomination.potential_positive _).le) (sq_nonneg _)

theorem exists_uniform_kernel_growth (α : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s t : ℝ), s ≤ t →
        realKernel ε y α β N b C P t ≤ Real.exp (M*(t-s))*realKernel ε y α β N b C P s := by
  obtain ⟨M,hM,hg⟩ := exists_uniform_finiteProfile_growth α hα
  refine ⟨M,hM,?_⟩
  intro β ε y hβ hw hε hy hy0 N b C P s t hst
  simp only [realKernel,energyKernel_re α β ε y t hα hβ hw hε hy,
    energyKernel_re α β ε y s hα hβ hw hε hy]
  exact hg β ε y hβ hw hε hy hy0 N b C P s t hst

theorem exists_uniform_kernel_derivative (α : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
        deriv (realKernel ε y α β N b C P) s ≤ M*realKernel ε y α β N b C P s := by
  obtain ⟨M,hM,hg⟩ := exists_uniform_kernel_growth α hα
  refine ⟨M,hM,?_⟩
  intro β ε y hβ hw hε hy hy0 N b C P s
  exact derivative_le_of_exponential_growth _ M
    (fun u => (realKernel_derivative α β ε y u hα hβ hw hε hy N b C P).differentiableAt)
    (hg β ε y hβ hw hε hy hy0 N b C P) s

theorem exists_uniform_response_bound (α : ℝ) (hα : 0 < α) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ β ε y : ℝ, 0 < β → 32*β ≤ α →
      0 < ε → |y| ≤ Real.pi*ε/3 → y ≠ 0 →
      ∀ (N : ℕ) (b C : Fin N → ℂ) (P : Fin N → Polynomial ℂ) (s : ℝ),
        -((M+2)/ε)*realKernel ε y α β N b C P s ≤
          (reducedResponse ε y α β N b C P s).re := by
  obtain ⟨M,hM,hd⟩ := exists_uniform_kernel_derivative α hα
  refine ⟨M,hM,?_⟩
  intro β ε y hβ hw hε hy hy0 N b C P s
  have hT := realKernel_nonnegative α β ε y s hα hβ hw hε hy N b C P
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hec : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right (coefficient_lower ε y s hε hy) hT
  have hder : deriv (realKernel ε y α β N b C P) s/clock ε s ≤
      (M/ε)*realKernel ε y α β N b C P s := by
    calc
      _ ≤ (M*realKernel ε y α β N b C P s)/clock ε s :=
        div_le_div_of_nonneg_right (hd β ε y hβ hw hε hy hy0 N b C P s) hc.le
      _ = (M/clock ε s)*realKernel ε y α β N b C P s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hM hε hec) hT
  rw [reducedResponse_re α β ε y s hα hβ hw hε hy]
  have he : -((M+2)/ε)*realKernel ε y α β N b C P s =
      -(2/ε)*realKernel ε y α β N b C P s-(M/ε)*realKernel ε y α β N b C P s := by ring
  rw [he]
  linarith

#print axioms realKernel_derivative
#print axioms reducedResponse_re
#print axioms realKernel_nonnegative
#print axioms exists_uniform_kernel_growth
#print axioms exists_uniform_kernel_derivative
#print axioms exists_uniform_response_bound
end
end UnifiedTheory.Audit.KFCausalNeutralFiniteResponse
