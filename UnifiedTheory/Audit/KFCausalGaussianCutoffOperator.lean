/- The charged Gaussian cutoff has an actual operator-norm derivative
under a real shift of its argument. The derivative is a bounded L2
multiplier, with norm at most 2 |c| sqrt(delta). -/
import UnifiedTheory.Audit.KFCausalGaussianCutoffTaylor
import UnifiedTheory.Audit.KFCausalLpMultiplierDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalGaussianCutoffOperator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalGaussianCutoffTaylor
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}
variable (δ : ℝ) (hδ : 0 < δ) (l : X → ℝ) (hl : Measurable l) (c : ℝ)

def symbol (t : ℝ) (x : X) : ℂ := amplitude δ (l x+t*c)
def derivativeSymbol (x : X) : ℂ := (c*KFCausalGaussianCutoffTaylor.slope δ (l x):ℝ)

include hl in
theorem symbol_measurable (t : ℝ) : Measurable (symbol δ l c t) := by
  unfold symbol amplitude
  fun_prop

omit [MeasurableSpace X] in
include hδ in
theorem symbol_bound (t : ℝ) (x : X) : ‖symbol δ l c t x‖ ≤ 1 := by
  rw [symbol,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (amplitude_bounds δ hδ.le _).1]
  exact (amplitude_bounds δ hδ.le _).2

def cutoff (t : ℝ) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  multiplyL (symbol δ l c t) (symbol_measurable δ l hl c t) (symbol_bound δ hδ l c t)

include hl in
theorem derivativeSymbol_measurable : Measurable (derivativeSymbol δ l c) := by
  unfold derivativeSymbol KFCausalGaussianCutoffTaylor.slope Real.mulExpNegMulSq
  fun_prop

omit [MeasurableSpace X] in
include hδ in
theorem derivativeSymbol_bound (x : X) : ‖derivativeSymbol δ l c x‖ ≤ |c| *(2*Real.sqrt δ) := by
  rw [derivativeSymbol,Complex.norm_real,Real.norm_eq_abs,abs_mul]
  exact mul_le_mul_of_nonneg_left (slope_bound δ hδ _) (abs_nonneg c)

def derivativeOperator : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  KFCausalBoundedLpMultiplier.operator (derivativeSymbol δ l c) (derivativeSymbol_measurable δ l hl c)
    (|c| *(2*Real.sqrt δ)) (by positivity) (derivativeSymbol_bound δ hδ l c)

theorem cutoff_coe (t : ℝ) (f : Lp ℂ 2 μ) :
    cutoff δ hδ l hl c t f =ᵐ[μ] fun x => symbol δ l c t x*f x :=
  multiplyL_coe _ _ _ f

theorem derivativeOperator_coe (f : Lp ℂ 2 μ) :
    derivativeOperator δ hδ l hl c f =ᵐ[μ] fun x => derivativeSymbol δ l c x*f x :=
  KFCausalBoundedLpMultiplier.operator_coe _ _ _ _ _ f

theorem derivativeOperator_norm (f : Lp ℂ 2 μ) :
    ‖derivativeOperator δ hδ l hl c f‖ ≤ |c| *(2*Real.sqrt δ)*‖f‖ :=
  KFCausalBoundedLpMultiplier.operator_norm _ _ _ _ _ f

omit [MeasurableSpace X] in
include hδ in
theorem symbol_remainder (t : ℝ) (x : X) :
    ‖symbol δ l c t x-symbol δ l c 0 x-(t:ℂ)*derivativeSymbol δ l c x‖ ≤ (2*δ*c^2)*t^2 := by
  simp only [symbol,derivativeSymbol,zero_mul,add_zero,← Complex.ofReal_mul,← Complex.ofReal_sub,
    Complex.norm_real,Real.norm_eq_abs]
  have hr := amplitude_remainder δ hδ (l x) (t*c)
  rw [mul_assoc t c (KFCausalGaussianCutoffTaylor.slope δ (l x))] at hr
  exact hr.trans_eq (by ring)

theorem cutoff_derivative :
    HasDerivAt (cutoff (μ := μ) δ hδ l hl c) (derivativeOperator δ hδ l hl c) 0 :=
  KFCausalLpMultiplierDerivative.operator_derivative _ _ (symbol δ l c) (derivativeSymbol δ l c)
    (cutoff_coe δ hδ l hl c) (derivativeOperator_coe δ hδ l hl c)
    (2*δ*c^2) (by positivity) (symbol_remainder δ hδ l c)

#print axioms symbol_measurable
#print axioms symbol_bound
#print axioms derivativeSymbol_measurable
#print axioms derivativeSymbol_bound
#print axioms cutoff_coe
#print axioms derivativeOperator_coe
#print axioms derivativeOperator_norm
#print axioms symbol_remainder
#print axioms cutoff_derivative

end
end UnifiedTheory.Audit.KFCausalGaussianCutoffOperator
