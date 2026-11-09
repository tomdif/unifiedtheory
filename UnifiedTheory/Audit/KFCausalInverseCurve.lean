/- Differentiation of an actually invertible bounded-operator curve.
Applications must prove invertibility; Ring.inverse's zero fallback is
never used to infer the existence of an inverse. -/
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalInverseCurve
noncomputable section

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

theorem inverseCurve_hasDerivAt (A : ℝ → R) (A' : R) (t : ℝ)
    (hd : HasDerivAt A A' t) (hi : IsUnit (A t)) :
    HasDerivAt (fun s => Ring.inverse (A s))
      (-(Ring.inverse (A t)*A'*Ring.inverse (A t))) t := by
  obtain ⟨u,hu⟩ := hi
  have hf := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hf
  have hh := hf.comp_hasDerivAt t hd
  have hinv : Ring.inverse (A t) = ((u⁻¹ : Rˣ) : R) := by rw [← hu,Ring.inverse_unit]
  simpa only [hinv,ContinuousLinearMap.neg_apply,ContinuousLinearMap.mulLeftRight_apply] using hh

theorem inverseCurve_continuous (A : ℝ → R) (hc : Continuous A) (hi : ∀ t, IsUnit (A t)) :
    Continuous (fun t => Ring.inverse (A t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (differentiableAt_inverse (𝕜 := ℝ) (hi t)).continuousAt.comp hc.continuousAt

theorem inverseCurve_derivative_continuous (A A' : ℝ → R)
    (hc : Continuous A) (hd : Continuous A') (hi : ∀ t, IsUnit (A t)) :
    Continuous (fun t => -(Ring.inverse (A t)*A' t*Ring.inverse (A t))) := by
  have hh := inverseCurve_continuous A hc hi
  exact ((hh.mul hd).mul hh).neg

omit [CompleteSpace R] [NormedAlgebra ℝ R] in
theorem inverseDerivative_norm_le (A B : R) :
    ‖-(Ring.inverse A*B*Ring.inverse A)‖ ≤ ‖Ring.inverse A‖^2*‖B‖ := by
  rw [norm_neg]
  calc
    ‖Ring.inverse A*B*Ring.inverse A‖ ≤ ‖Ring.inverse A*B‖*‖Ring.inverse A‖ := norm_mul_le _ _
    _ ≤ (‖Ring.inverse A‖*‖B‖)*‖Ring.inverse A‖ :=
      mul_le_mul_of_nonneg_right (norm_mul_le _ _) (norm_nonneg _)
    _ = _ := by ring

#print axioms inverseCurve_hasDerivAt
#print axioms inverseCurve_continuous
#print axioms inverseCurve_derivative_continuous
#print axioms inverseDerivative_norm_le

end
end UnifiedTheory.Audit.KFCausalInverseCurve
