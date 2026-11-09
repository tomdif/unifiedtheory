/- Exact scalar linear ODE solution from an integrating factor. -/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalScalarIntegratingFactor
noncomputable section

def primitive (g : ℝ → ℝ) (t : ℝ) : ℝ := ∫ u in (0:ℝ)..t, g u

theorem primitive_derivative (g : ℝ → ℝ) (hg : Continuous g) (t : ℝ) :
    HasDerivAt (primitive g) (g t) t :=
  intervalIntegral.integral_hasDerivAt_right (hg.intervalIntegrable _ _)
    hg.aestronglyMeasurable.stronglyMeasurableAtFilter hg.continuousAt

theorem solution_formula (f g : ℝ → ℝ) (hg : Continuous g)
    (hf : ∀ t, HasDerivAt f (g t*f t) t) (t : ℝ) :
    f t = f 0*Real.exp (primitive g t) := by
  have hd (u : ℝ) : HasDerivAt (fun v => Real.exp (-primitive g v)*f v) 0 u := by
    convert ((primitive_derivative g hg u).neg.exp).mul (hf u) using 1
    ring
  have he := is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt)
    (fun u => (hd u).deriv) t 0
  have h0 : primitive g 0 = 0 := intervalIntegral.integral_same
  rw [h0,neg_zero,Real.exp_zero,one_mul] at he
  have hmul := congrArg (fun r : ℝ => Real.exp (primitive g t)*r) he
  have hcancel : Real.exp (primitive g t)*Real.exp (-primitive g t) = 1 := by
    rw [← Real.exp_add,add_neg_cancel,Real.exp_zero]
  dsimp only at hmul
  rw [← mul_assoc,hcancel,one_mul] at hmul
  exact hmul.trans (mul_comm _ _)

#print axioms primitive_derivative
#print axioms solution_formula

end
end UnifiedTheory.Audit.KFCausalScalarIntegratingFactor
