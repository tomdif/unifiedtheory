/- Polynomial and complex linear-source factors are bounded after
Gaussian decay. Constants may depend on the source and polynomial; this
is an analytic domain estimate, not a uniform response bound. -/
import UnifiedTheory.Audit.KFCausalTransversePolynomialEnvelope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalComplexPolynomialGaussianAbsorption
noncomputable section
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)

theorem power_radius_bound (n : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    (1+R)^n ≤ Real.exp ((n:ℝ)*R) := by
  have hr : 1+R ≤ Real.exp R := by linarith [Real.add_one_le_exp R]
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ 1+R) hr n
  simpa only [← Real.exp_nat_mul] using hp

theorem complete_square_bound (d A R : ℝ) (hd : 0 < d) :
    A*R-d*R^2 ≤ A^2/(4*d) := by
  apply (le_div_iff₀ (by positivity : 0 < 4*d)).mpr
  nlinarith [sq_nonneg (2*d*R-A)]

theorem source_polynomial_bound (P : Polynomial ℂ) (b z : ℂ)
    (K R d : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d) (hz : ‖z‖ ≤ K*R) :
    ‖P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) ≤
      evalCap P K*Real.exp (((P.natDegree:ℝ)+‖b‖*K)^2/(4*d)) := by
  have hz' : ‖z‖ ≤ K*(1+R) := hz.trans (by nlinarith)
  have hp := eval_bound P K (1+R) hK (by linarith) z hz'
  have hpow := power_radius_bound P.natDegree R hR
  have hsource : ‖Complex.exp (b*z)‖ ≤ Real.exp (‖b‖*K*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (b*z).re ≤ ‖b*z‖ := Complex.re_le_norm _
      _ = ‖b‖*‖z‖ := norm_mul _ _
      _ ≤ ‖b‖*(K*R) := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = _ := by ring
  have hcap := evalCap_nonnegative P K hK
  calc
    _ = (‖P.eval z‖*‖Complex.exp (b*z)‖)*Real.exp (-d*R^2) := by rw [norm_mul]
    _ ≤ ((evalCap P K*Real.exp ((P.natDegree:ℝ)*R))*
        Real.exp (‖b‖*K*R))*Real.exp (-d*R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul (hp.trans (mul_le_mul_of_nonneg_left hpow hcap)) hsource
        (norm_nonneg _) (mul_nonneg hcap (Real.exp_pos _).le)
    _ = evalCap P K*Real.exp (((P.natDegree:ℝ)+‖b‖*K)*R-d*R^2) := by
      rw [show ((P.natDegree:ℝ)+‖b‖*K)*R-d*R^2=
        ((P.natDegree:ℝ)*R+‖b‖*K*R)+(-d*R^2) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (complete_square_bound d _ R hd)) hcap

theorem source_polynomial_constant_nonnegative (P : Polynomial ℂ) (b : ℂ)
    (K d : ℝ) (hK : 0 ≤ K) :
    0 ≤ evalCap P K*Real.exp (((P.natDegree:ℝ)+‖b‖*K)^2/(4*d)) :=
  mul_nonneg (evalCap_nonnegative P K hK) (Real.exp_pos _).le

#print axioms power_radius_bound
#print axioms complete_square_bound
#print axioms source_polynomial_bound
#print axioms source_polynomial_constant_nonnegative
end
end UnifiedTheory.Audit.KFCausalComplexPolynomialGaussianAbsorption
