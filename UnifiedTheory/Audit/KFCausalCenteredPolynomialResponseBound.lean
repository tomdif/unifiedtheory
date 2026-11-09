/- A uniform relative lower bound for the actual centered projected
ordered response, and therefore every centered Hermite cutoff. This
does not extend to arbitrary displaced source families or trajectories. -/
import UnifiedTheory.Audit.KFCausalCenteredPolynomialKernel
import UnifiedTheory.Audit.KFCausalHermiteResponseHierarchy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalCenteredPolynomialResponseBound
noncomputable section
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient coefficient_lower)
open UnifiedTheory.Audit.KFCausalWeightedPolynomialLocalResponse
open UnifiedTheory.Audit.KFCausalHermiteResponseHierarchy
open UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth
open UnifiedTheory.Audit.KFCausalCenteredPolynomialKernel

theorem derivative_le_of_exponential_growth (f : ℝ → ℝ) (C : ℝ)
    (hf : Differentiable ℝ f)
    (hg : ∀ s t, s ≤ t → f t ≤ Real.exp (C*(t-s))*f s) (s : ℝ) :
    deriv f s ≤ C*f s := by
  let g := fun t : ℝ => Real.exp (-C*t)*f t
  have ha : Antitone g := by
    intro u v huv
    have hi := mul_le_mul_of_nonneg_left (hg u v huv) (Real.exp_pos (-C*v)).le
    calc
      g v ≤ Real.exp (-C*v)*(Real.exp (C*(v-u))*f u) := hi
      _ = g u := by
        dsimp [g]
        rw [← mul_assoc,← Real.exp_add]
        congr 2
        ring
  have hd : HasDerivAt g (Real.exp (-C*s)*(deriv f s-C*f s)) s := by
    convert (((hasDerivAt_id s).const_mul (-C)).exp).mul (hf s).hasDerivAt using 1
    dsimp
    ring
  have hn : deriv g s ≤ 0 := ha.deriv_nonpos
  rw [hd.deriv] at hn
  by_contra h
  have hp := mul_pos (Real.exp_pos (-C*s)) (sub_pos.mpr (lt_of_not_ge h))
  linarith

theorem realKernel_nonnegative (ε h : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    0 ≤ realKernel ε h P s := by
  exact kernel_self_nonnegative ε h 0 0 (physicalWeights 1 1 1) P hε hh hb
    (fun n => by fin_cases n <;> norm_num [physicalWeights]) s

theorem exists_uniform_kernel_growth (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (P : Polynomial ℂ) (s t : ℝ), s ≤ t →
        realKernel ε h P t ≤ Real.exp (C*(t-s))*realKernel ε h P s := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_centeredEnergy_growth (groundWidth h) (groundWidth_positive h hh)
  refine ⟨C,hC,?_⟩
  intro ε hε hb P s t hst
  rw [realKernel_eq_centeredEnergy ε h P hε hh hb,
    realKernel_eq_centeredEnergy ε h P hε hh hb]
  exact hg (neutralWidth h) ε (-h/2) (neutralWidth_positive h hh)
    (by unfold neutralWidth; linarith) hε (shift_bound ε h hb)
    (div_ne_zero (neg_ne_zero.mpr hh) (by norm_num)) P s t hst

theorem exists_uniform_kernel_derivative (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (P : Polynomial ℂ) (s : ℝ),
        deriv (realKernel ε h P) s ≤ C*realKernel ε h P s := by
  obtain ⟨C,hC,hg⟩ := exists_uniform_kernel_growth h hh
  refine ⟨C,hC,?_⟩
  intro ε hε hb P s
  exact derivative_le_of_exponential_growth _ C
    (fun u => (realKernel_derivative ε h P hε hh hb u).differentiableAt) (hg ε hε hb P) s

theorem exists_uniform_reducedResponse_bound (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → |h| ≤ 2*Real.pi*ε/3 →
      ∀ (P : Polynomial ℂ) (s : ℝ),
        -((C+2)/ε)*realKernel ε h P s ≤
          (reducedResponse ε h 0 0 (physicalWeights 1 1 1) P P s).re := by
  obtain ⟨C,hC,hd⟩ := exists_uniform_kernel_derivative h hh
  refine ⟨C,hC,?_⟩
  intro ε hε hb P s
  have hT := realKernel_nonnegative ε h P hε hh hb s
  have hc : 0 < clock ε s := by unfold clock; positivity
  have hec : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hcoef := mul_le_mul_of_nonneg_right
    (coefficient_lower ε (-h/2) s hε (shift_bound ε h hb)) hT
  have hder : deriv (realKernel ε h P) s/clock ε s ≤ (C/ε)*realKernel ε h P s := by
    calc
      _ ≤ (C*realKernel ε h P s)/clock ε s :=
        div_le_div_of_nonneg_right (hd ε hε hb P s) hc.le
      _ = (C/clock ε s)*realKernel ε h P s := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left hC hε hec) hT
  rw [reducedResponse_zero_re ε h P hε hh hb]
  have he : -((C+2)/ε)*realKernel ε h P s =
      -(2/ε)*realKernel ε h P s-(C/ε)*realKernel ε h P s := by ring
  rw [he]
  linarith

theorem centered_polynomial_bound_exists (ε h : ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ s, PolynomialBound ε h 0 0 (physicalWeights 1 1 1) κ s := by
  obtain ⟨C,hC,hbound⟩ := exists_uniform_reducedResponse_bound h hh
  exact ⟨(C+2)/ε,by positivity,fun s P => hbound ε hε hb P s⟩

theorem centered_hermite_bound_exists (ε h B : ℝ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ s N, CutoffBound ε h 0 0 (physicalWeights 1 1 1) B κ s N :=
  (uniform_clock_bound_iff ε h 0 0 (physicalWeights 1 1 1) B hε hh hb).mp
    (centered_polynomial_bound_exists ε h hε hh hb)

#print axioms derivative_le_of_exponential_growth
#print axioms realKernel_nonnegative
#print axioms exists_uniform_kernel_growth
#print axioms exists_uniform_kernel_derivative
#print axioms exists_uniform_reducedResponse_bound
#print axioms centered_polynomial_bound_exists
#print axioms centered_hermite_bound_exists
end
end UnifiedTheory.Audit.KFCausalCenteredPolynomialResponseBound
