/- Integrable local bounds for the first and second pointwise neutral
transport derivatives. These bounds are derived for the actual finite
Gaussian exponential-polynomial sum, with every cross term retained. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationEnvelope
import Mathlib.Analysis.Calculus.ParametricIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralTransportDomination
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalNeutralUniformDefect (curve)
open KFCausalNeutralLinePackets (step entire)
open KFCausalNeutralLineDomain (family Regular)
open KFCausalNeutralQuarticTransportForms (velocity rate acceleration)
open KFCausalQuarticPlaneDomination (potential potential_positive)

variable (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
  (z : ℂ) (η L : ℝ)

def value (v x : ℝ) : ℝ := potential x*‖curve n β b c P z η L x v‖^2
def slope (v x : ℝ) : ℝ := rate η L x (curve n β b c P z η L x v)
  (curve n β b c (fun i => step β (b i) (P i)) z η L x v)
def curvature (v x : ℝ) : ℝ := acceleration η L x (curve n β b c P z η L x v)
  (curve n β b c (fun i => step β (b i) (P i)) z η L x v)
  (curve n β b c (fun i => step β (b i) (step β (b i) (P i))) z η L x v)

theorem curve_regular (hβ : 0 < β) (v : ℝ) :
    Regular (fun x => curve n β b c P z η L x v) := by
  simpa only [curve,add_assoc] using
    KFCausalNeutralLineDomain.family_regular n β hβ b c P (z+velocity η L*(v:ℂ))

theorem value_integrable (hβ : 0 < β) (v : ℝ) : Integrable (value n β b c P z η L v) := by
  exact KFCausalNeutralLineDomain.weight_norm_integrable _ (curve_regular n β b c P z η L hβ v) 0

theorem value_continuous (v : ℝ) : Continuous (value n β b c P z η L v) := by
  unfold value curve family entire potential
  fun_prop

theorem slope_continuous (v : ℝ) : Continuous (slope n β b c P z η L v) := by
  unfold slope rate curve family entire potential
  fun_prop

theorem curvature_continuous (v : ℝ) : Continuous (curvature n β b c P z η L v) := by
  unfold curvature acceleration curve family entire potential
  fun_prop

theorem value_derivative (v x : ℝ) :
    HasDerivAt (fun t => value n β b c P z η L t x) (slope n β b c P z η L v x) v :=
  KFCausalNeutralUniformDefect.pointwise_energy_derivative n β b c P z η L x v

theorem slope_derivative (v x : ℝ) :
    HasDerivAt (fun t => slope n β b c P z η L t x) (curvature n β b c P z η L v x) v :=
  KFCausalNeutralUniformDefect.pointwise_rate_derivative n β b c P z η L x v

omit n β b c P z in
theorem rate_bound (x : ℝ) (f g : ℂ) :
    ‖rate η L x f g‖ ≤ 2*‖velocity η L‖*(potential x*‖f‖*‖g‖) := by
  calc
    ‖rate η L x f g‖ = 2*potential x*|(conj f*(velocity η L*g)).re| := by
      simp [rate,abs_of_pos (potential_positive x)]
    _ ≤ 2*potential x*‖conj f*(velocity η L*g)‖ :=
      mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (mul_nonneg (by norm_num) (potential_positive x).le)
    _ = _ := by simp only [norm_mul,Complex.norm_conj]; ring

omit n β b c P z in
theorem acceleration_bound (x : ℝ) (f g k : ℂ) :
    ‖acceleration η L x f g k‖ ≤
      2*‖velocity η L‖^2*(potential x*‖g‖*‖g‖+potential x*‖f‖*‖k‖) := by
  have ha : |‖velocity η L*g‖^2+(conj f*(velocity η L^2*k)).re| ≤
      ‖velocity η L*g‖^2+‖conj f*(velocity η L^2*k)‖ := by
    apply (abs_add_le _ _).trans
    rw [abs_of_nonneg (sq_nonneg ‖velocity η L*g‖)]
    exact add_le_add le_rfl (Complex.abs_re_le_norm _)
  calc
    ‖acceleration η L x f g k‖ =
        2*potential x*|‖velocity η L*g‖^2+(conj f*(velocity η L^2*k)).re| := by
      simp [acceleration,abs_of_pos (potential_positive x)]
    _ ≤ 2*potential x*(‖velocity η L*g‖^2+‖conj f*(velocity η L^2*k)‖) :=
      mul_le_mul_of_nonneg_left ha (mul_nonneg (by norm_num) (potential_positive x).le)
    _ = _ := by simp only [norm_mul,Complex.norm_conj,norm_pow]; ring

theorem local_domination (hβ : 0 < β) (v₀ : ℝ) :
    ∃ B D : ℝ → ℝ, Integrable B ∧ Integrable D ∧
      ∀ v ∈ Metric.ball v₀ 1, ∀ x,
        ‖slope n β b c P z η L v x‖ ≤ B x ∧ ‖curvature n β b c P z η L v x‖ ≤ D x := by
  let R := ‖z‖+‖velocity η L‖*(|v₀|+1)
  have hR : 0 ≤ R := by unfold R; positivity
  have hr (v : ℝ) (hv : v ∈ Metric.ball v₀ 1) : ‖z+velocity η L*(v:ℂ)‖ ≤ R := by
    have hd : |v-v₀| < 1 := by simpa only [Metric.mem_ball,Real.dist_eq] using hv
    have hh := abs_add_le (v-v₀) v₀
    have hv' : |v| ≤ |v₀|+1 := by simpa only [sub_add_cancel] using (show |v-v₀+v₀| ≤ |v₀|+1 by linarith)
    apply (norm_add_le _ _).trans
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
    exact add_le_add_right (mul_le_mul_of_nonneg_left hv' (norm_nonneg (velocity η L))) ‖z‖
  obtain ⟨A,hA,hA2,hAV,hAf⟩ := KFCausalNeutralTranslationEnvelope.family_envelope n β hβ b c P R hR
  obtain ⟨B,hB,hB2,hBV,hBf⟩ := KFCausalNeutralTranslationEnvelope.family_envelope n β hβ b c
    (fun i => step β (b i) (P i)) R hR
  obtain ⟨C,hC,hC2,_,hCf⟩ := KFCausalNeutralTranslationEnvelope.family_envelope n β hβ b c
    (fun i => step β (b i) (step β (b i) (P i))) R hR
  have hi1 : Integrable (fun x => potential x*A x*B x) := hAV.integrable_mul hB2
  have hi2 : Integrable (fun x => potential x*B x*B x) := hBV.integrable_mul hB2
  have hi3 : Integrable (fun x => potential x*A x*C x) := hAV.integrable_mul hC2
  refine ⟨fun x => (2*‖velocity η L‖)*(potential x*A x*B x),
    fun x => (2*‖velocity η L‖^2)*(potential x*B x*B x+potential x*A x*C x),
    hi1.const_mul _, (hi2.add hi3).const_mul _, ?_⟩
  intro v hv x
  have ha : ‖curve n β b c P z η L x v‖ ≤ A x := by
    simpa only [curve,add_assoc] using hAf (z+velocity η L*(v:ℂ)) (hr v hv) x
  have hb : ‖curve n β b c (fun i => step β (b i) (P i)) z η L x v‖ ≤ B x := by
    simpa only [curve,add_assoc] using hBf (z+velocity η L*(v:ℂ)) (hr v hv) x
  have hc : ‖curve n β b c (fun i => step β (b i) (step β (b i) (P i))) z η L x v‖ ≤ C x := by
    simpa only [curve,add_assoc] using hCf (z+velocity η L*(v:ℂ)) (hr v hv) x
  have hp := (potential_positive x).le
  have hab := mul_le_mul (mul_le_mul_of_nonneg_left ha hp) hb (norm_nonneg _) (mul_nonneg hp (hA x))
  have hbb := mul_le_mul (mul_le_mul_of_nonneg_left hb hp) hb (norm_nonneg _) (mul_nonneg hp (hB x))
  have hac := mul_le_mul (mul_le_mul_of_nonneg_left ha hp) hc (norm_nonneg _) (mul_nonneg hp (hA x))
  exact ⟨(rate_bound η L x _ _).trans (mul_le_mul_of_nonneg_left hab (by positivity)),
    (acceleration_bound η L x _ _ _).trans (mul_le_mul_of_nonneg_left (add_le_add hbb hac) (by positivity))⟩

#print axioms curve_regular
#print axioms value_integrable
#print axioms value_continuous
#print axioms slope_continuous
#print axioms curvature_continuous
#print axioms value_derivative
#print axioms slope_derivative
#print axioms rate_bound
#print axioms acceleration_bound
#print axioms local_domination
end
end UnifiedTheory.Audit.KFCausalNeutralTransportDomination
