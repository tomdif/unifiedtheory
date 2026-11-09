/- Integrating Bernstein approximations of a Banach-valued derivative gives
uniform approximation of both a curve and its derivative on the unit interval. -/
import UnifiedTheory.Audit.KFCausalBernsteinPrimitive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalBernsteinC1Approximation
noncomputable section
open MeasureTheory Set Filter
open scoped Topology unitInterval Interval
open UnifiedTheory.Audit.KFCausalBernsteinPrimitive

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def unitCurve (F : ℝ → E) (hF : Continuous F) : C(I,E) :=
  ⟨fun t => F t,hF.comp continuous_subtype_val⟩

def primitiveCurve (n : ℕ) (v : E) (g : C(I,E)) : C(I,E) :=
  unitCurve (valueApprox n v g) (valueApprox_continuous n v g)

omit [CompleteSpace E] in
theorem curve_continuous (F F' : ℝ → E) (hF : ∀ t, HasDerivAt F (F' t) t) :
    Continuous F :=
  continuous_iff_continuousAt.mpr (fun t => (hF t).continuousAt)

theorem value_error_integral (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) (n : ℕ) (t : ℝ) :
    valueApprox n (F 0) (unitCurve F' hF') t-F t =
      ∫ u in 0..t, derivativeApprox n (unitCurve F' hF') u-F' u := by
  rw [intervalIntegral.integral_sub
      ((derivativeApprox_continuous n (unitCurve F' hF')).intervalIntegrable 0 t)
      (hF'.intervalIntegrable 0 t),
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hF u)
      (hF'.intervalIntegrable 0 t),valueApprox_eq_integral]
  abel

theorem value_error_bound (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) (n : ℕ) (t : I) :
    ‖valueApprox n (F 0) (unitCurve F' hF') t-F t‖ ≤
      ‖bernsteinApproximation n (unitCurve F' hF')-unitCurve F' hF'‖ := by
  rw [value_error_integral F F' hF' hF]
  calc
    _ ≤ ‖bernsteinApproximation n (unitCurve F' hF')-unitCurve F' hF'‖*|↑t-0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro u hu
      rw [uIoc_of_le t.property.1] at hu
      let x : I := ⟨u,le_of_lt hu.1,le_trans hu.2 t.property.2⟩
      have hx := (bernsteinApproximation n (unitCurve F' hF')-
        unitCurve F' hF').norm_coe_le_norm x
      simpa only [ContinuousMap.sub_apply,← derivativeApprox_on_unit,unitCurve] using hx
    _ ≤ _ := by
      rw [sub_zero,abs_of_nonneg t.property.1]
      exact mul_le_of_le_one_right (norm_nonneg _) t.property.2

theorem primitiveCurve_error_bound (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) (n : ℕ) :
    ‖primitiveCurve n (F 0) (unitCurve F' hF')-unitCurve F (curve_continuous F F' hF)‖ ≤
      ‖bernsteinApproximation n (unitCurve F' hF')-unitCurve F' hF'‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  exact value_error_bound F F' hF' hF n

omit [CompleteSpace E] in
theorem derivative_converges (F' : ℝ → E) (hF' : Continuous F') :
    Tendsto (fun n => bernsteinApproximation n (unitCurve F' hF')) atTop
      (𝓝 (unitCurve F' hF')) :=
  bernsteinApproximation_uniform (unitCurve F' hF')

theorem primitive_converges (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) :
    Tendsto (fun n => primitiveCurve n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (unitCurve F (curve_continuous F F' hF))) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun n => norm_nonneg _)
    (primitiveCurve_error_bound F F' hF' hF)
    (tendsto_iff_norm_sub_tendsto_zero.mp (derivative_converges F' hF'))

theorem c1_approximation (F F' : ℝ → E) (hF' : Continuous F')
    (hF : ∀ t, HasDerivAt F (F' t) t) :
    (∀ n t, HasDerivAt (valueApprox n (F 0) (unitCurve F' hF'))
      (derivativeApprox n (unitCurve F' hF') t) t) ∧
    Tendsto (fun n => primitiveCurve n (F 0) (unitCurve F' hF')) atTop
      (𝓝 (unitCurve F (curve_continuous F F' hF))) ∧
    Tendsto (fun n => bernsteinApproximation n (unitCurve F' hF')) atTop
      (𝓝 (unitCurve F' hF')) :=
  ⟨fun n t => valueApprox_derivative n (F 0) (unitCurve F' hF') t,
    primitive_converges F F' hF' hF,derivative_converges F' hF'⟩

#print axioms curve_continuous
#print axioms value_error_integral
#print axioms value_error_bound
#print axioms primitiveCurve_error_bound
#print axioms derivative_converges
#print axioms primitive_converges
#print axioms c1_approximation
end
end UnifiedTheory.Audit.KFCausalBernsteinC1Approximation
