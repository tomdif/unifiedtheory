/- Two polynomial arguments and an affine-growth factor share a single
Gaussian margin. This treats the full transverse numerator derivatives. -/
import UnifiedTheory.Audit.KFCausalScalarPowerSourceAbsorption

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalTwoPolynomialSourceAbsorption
noncomputable section
open KFCausalTransversePolynomialEnvelope (evalCap evalCap_nonnegative eval_bound)
open KFCausalComplexPolynomialGaussianAbsorption (power_radius_bound complete_square_bound)

def cap (Q P : Polynomial ℂ) (b : ℂ) (A K d : ℝ) (n : ℕ) : ℝ :=
  evalCap Q A*evalCap P K*
    Real.exp (((((n+Q.natDegree+P.natDegree:ℕ):ℝ)+‖b‖*K)^2)/(4*d))

theorem cap_nonnegative (Q P : Polynomial ℂ) (b : ℂ) (A K d : ℝ) (n : ℕ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) : 0 ≤ cap Q P b A K d n := by
  unfold cap
  exact mul_nonneg (mul_nonneg (evalCap_nonnegative Q A hA) (evalCap_nonnegative P K hK))
    (Real.exp_pos _).le

theorem polynomial_source_bound (Q P : Polynomial ℂ) (b x z : ℂ)
    (A K R d : ℝ) (n : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d)
    (hx : ‖x‖ ≤ A*R) (hz : ‖z‖ ≤ K*R) :
    (1+R)^n*‖Q.eval x*P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) ≤
      cap Q P b A K d n := by
  have hQ := eval_bound Q A (1+R) hA (by linarith) x (hx.trans (by nlinarith))
  have hP := eval_bound P K (1+R) hK (by linarith) z (hz.trans (by nlinarith))
  have hQc := evalCap_nonnegative Q A hA
  have hPc := evalCap_nonnegative P K hK
  have hs : ‖Complex.exp (b*z)‖ ≤ Real.exp (‖b‖*K*R) := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    calc
      (b*z).re ≤ ‖b*z‖ := Complex.re_le_norm _
      _ = ‖b‖*‖z‖ := norm_mul _ _
      _ ≤ ‖b‖*(K*R) := mul_le_mul_of_nonneg_left hz (norm_nonneg _)
      _ = _ := by ring
  have hp : ‖Q.eval x*P.eval z*Complex.exp (b*z)‖ ≤
      ((evalCap Q A*(1+R)^Q.natDegree)*(evalCap P K*(1+R)^P.natDegree))*
        Real.exp (‖b‖*K*R) := by
    rw [norm_mul,norm_mul]
    exact mul_le_mul (mul_le_mul hQ hP (norm_nonneg _) (by positivity)) hs
      (norm_nonneg _) (by positivity)
  let N := n+Q.natDegree+P.natDegree
  calc
    _ ≤ (1+R)^n*(((evalCap Q A*(1+R)^Q.natDegree)*
        (evalCap P K*(1+R)^P.natDegree))*Real.exp (‖b‖*K*R))*Real.exp (-d*R^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (Real.exp_pos _).le
    _ = (evalCap Q A*evalCap P K)*((1+R)^N*Real.exp (‖b‖*K*R)*Real.exp (-d*R^2)) := by
      dsimp [N]
      rw [pow_add,pow_add]
      ring
    _ ≤ (evalCap Q A*evalCap P K)*(Real.exp ((N:ℝ)*R)*Real.exp (‖b‖*K*R)*Real.exp (-d*R^2)) := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hQc hPc)
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul_of_nonneg_right (power_radius_bound N R hR) (Real.exp_pos _).le
    _ = (evalCap Q A*evalCap P K)*Real.exp (((N:ℝ)+‖b‖*K)*R-d*R^2) := by
      rw [← Real.exp_add,← Real.exp_add]
      congr 2
      ring
    _ ≤ cap Q P b A K d n :=
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (complete_square_bound d _ R hd)) (mul_nonneg hQc hPc)

theorem weighted_source_bound (Q P : Polynomial ℂ) (b x z g : ℂ)
    (A K G R d : ℝ) (n : ℕ) (hA : 0 ≤ A) (hK : 0 ≤ K) (hG : 0 ≤ G)
    (hR : 0 ≤ R) (hd : 0 < d) (hx : ‖x‖ ≤ A*R) (hz : ‖z‖ ≤ K*R)
    (hg : ‖g‖ ≤ G*(1+R)) :
    ‖g^n*(Q.eval x*P.eval z*Complex.exp (b*z))‖*Real.exp (-d*R^2) ≤
      G^n*cap Q P b A K d n := by
  have hp := pow_le_pow_left₀ (norm_nonneg g) hg n
  rw [mul_pow] at hp
  rw [norm_mul,norm_pow]
  calc
    _ ≤ (G^n*(1+R)^n)*‖Q.eval x*P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (norm_nonneg _)) (Real.exp_pos _).le
    _ = G^n*((1+R)^n*‖Q.eval x*P.eval z*Complex.exp (b*z)‖*Real.exp (-d*R^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (polynomial_source_bound Q P b x z A K R d n hA hK hR hd hx hz) (pow_nonneg hG n)

#print axioms cap_nonnegative
#print axioms polynomial_source_bound
#print axioms weighted_source_bound

end
end UnifiedTheory.Audit.KFCausalTwoPolynomialSourceAbsorption
