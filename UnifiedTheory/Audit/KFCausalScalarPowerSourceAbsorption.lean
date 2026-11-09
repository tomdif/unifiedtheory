/- A finite power of a linearly bounded insertion, a neutral polynomial
and a complex source share one Gaussian decay margin. -/
import UnifiedTheory.Audit.KFCausalComplexPolynomialGaussianAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalScalarPowerSourceAbsorption
noncomputable section
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)
open KFCausalComplexPolynomialGaussianAbsorption (power_radius_bound complete_square_bound)

theorem radius_power_source_bound (k : ℕ) (P : Polynomial ℂ) (b z : ℂ)
    (K R d : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d) (hz : ‖z‖ ≤ K*R) :
    R^k*‖P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) ≤
      evalCap P K*Real.exp (((P.natDegree:ℝ)+(k:ℝ)+‖b‖*K)^2/(4*d)) := by
  have hp := eval_bound P K (1+R) hK (by linarith) z (hz.trans (by nlinarith))
  have hpow := power_radius_bound P.natDegree R hR
  have hcap := evalCap_nonnegative P K hK
  have hr : R^k ≤ Real.exp ((k:ℝ)*R) :=
    (pow_le_pow_left₀ hR (by linarith : R ≤ 1+R) k).trans (power_radius_bound k R hR)
  have hs : ‖Complex.exp (b*z)‖ ≤ Real.exp (‖b‖*K*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (b*z).re ≤ ‖b*z‖ := Complex.re_le_norm _
      _ = ‖b‖*‖z‖ := norm_mul _ _
      _ ≤ ‖b‖*(K*R) := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = _ := by ring
  rw [norm_mul]
  calc
    _ ≤ Real.exp ((k:ℝ)*R)*((evalCap P K*Real.exp ((P.natDegree:ℝ)*R))*
        Real.exp (‖b‖*K*R))*Real.exp (-d*R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul hr (mul_le_mul (hp.trans (mul_le_mul_of_nonneg_left hpow hcap)) hs
        (norm_nonneg _) (mul_nonneg hcap (Real.exp_pos _).le))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Real.exp_pos _).le
    _ = evalCap P K*Real.exp (((P.natDegree:ℝ)+(k:ℝ)+‖b‖*K)*R-d*R^2) := by
      rw [show ((P.natDegree:ℝ)+(k:ℝ)+‖b‖*K)*R-d*R^2=
        (k:ℝ)*R+((P.natDegree:ℝ)*R+‖b‖*K*R)+(-d*R^2) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (complete_square_bound d _ R hd)) hcap

theorem linear_power_source_bound (k : ℕ) (P : Polynomial ℂ) (b z v : ℂ)
    (A K R d : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d)
    (hv : ‖v‖ ≤ A*R) (hz : ‖z‖ ≤ K*R) :
    ‖v^k*(P.eval z*Complex.exp (b*z))‖*Real.exp (-d*R^2) ≤
      A^k*(evalCap P K*Real.exp (((P.natDegree:ℝ)+(k:ℝ)+‖b‖*K)^2/(4*d))) := by
  have hi := pow_le_pow_left₀ (norm_nonneg v) hv k
  rw [mul_pow] at hi
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (A^k*R^k)*‖P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hi (norm_nonneg _)) (Real.exp_pos _).le
    _ = A^k*(R^k*‖P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (radius_power_source_bound k P b z K R d hK hR hd hz) (pow_nonneg hA k)

#print axioms radius_power_source_bound
#print axioms linear_power_source_bound
end
end UnifiedTheory.Audit.KFCausalScalarPowerSourceAbsorption
