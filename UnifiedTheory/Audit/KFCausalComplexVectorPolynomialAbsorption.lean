/- Arbitrary complex multivariate polynomial and linear-source factors
are absorbed by Gaussian decay. The final estimate applies to the actual
rotated complex-shear target vector, including its charged coordinates. -/
import UnifiedTheory.Audit.KFCausalWidthGaussianNeutralMultiplier
import Mathlib.Algebra.MvPolynomial.Monad

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalComplexVectorPolynomialAbsorption
noncomputable section
open KFCausalComplexPolynomialGaussianAbsorption (power_radius_bound complete_square_bound)

def degree {n : ℕ} (m : Fin n →₀ ℕ) : ℕ := ∑ i, m i
def sourceRate {n : ℕ} (b : Fin n → ℂ) (K : ℝ) : ℝ := K*∑ i, ‖b i‖
def absorptionCap {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (b : Fin n → ℂ)
    (K d : ℝ) : ℝ :=
  ∑ m ∈ P.support, ‖P.coeff m‖*K^(degree m)*
    Real.exp (((degree m:ℝ)+sourceRate b K)^2/(4*d))

theorem absorptionCap_nonnegative {n : ℕ} (P : MvPolynomial (Fin n) ℂ)
    (b : Fin n → ℂ) (K d : ℝ) (hK : 0 ≤ K) : 0 ≤ absorptionCap P b K d := by
  exact Finset.sum_nonneg (fun m _ => mul_nonneg
    (mul_nonneg (norm_nonneg _) (pow_nonneg hK _)) (Real.exp_pos _).le)

theorem monomial_bound {n : ℕ} (m : Fin n →₀ ℕ) (z : Fin n → ℂ)
    (K R : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hz : ∀ i, ‖z i‖ ≤ K*R) :
    ‖∏ i, z i^(m i)‖ ≤ K^(degree m)*Real.exp ((degree m:ℝ)*R) := by
  rw [norm_prod]
  simp only [norm_pow]
  have hp : (∏ i, ‖z i‖^(m i)) ≤ ∏ i, (K*(1+R))^(m i) := by
    apply Finset.prod_le_prod (fun i _ => pow_nonneg (norm_nonneg _) _)
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) ((hz i).trans (by nlinarith)) _
  rw [Finset.prod_pow_eq_pow_sum,mul_pow] at hp
  exact hp.trans (mul_le_mul_of_nonneg_left (power_radius_bound (degree m) R hR)
    (pow_nonneg hK _))

theorem source_bound {n : ℕ} (b z : Fin n → ℂ) (K R : ℝ)
    (hz : ∀ i, ‖z i‖ ≤ K*R) :
    ‖Complex.exp (∑ i, b i*z i)‖ ≤ Real.exp (sourceRate b K*R) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  calc
    (∑ i, b i*z i).re ≤ ‖∑ i, b i*z i‖ := Complex.re_le_norm _
    _ ≤ ∑ i, ‖b i*z i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖b i‖*(K*R) := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hz i) (norm_nonneg _)
    _ = sourceRate b K*R := by rw [← Finset.sum_mul]; unfold sourceRate; ring

theorem monomial_source_bound {n : ℕ} (m : Fin n →₀ ℕ) (b z : Fin n → ℂ)
    (K R d : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d)
    (hz : ∀ i, ‖z i‖ ≤ K*R) :
    ‖(∏ i, z i^(m i))*Complex.exp (∑ i, b i*z i)‖*Real.exp (-d*R^2) ≤
      K^(degree m)*Real.exp (((degree m:ℝ)+sourceRate b K)^2/(4*d)) := by
  rw [norm_mul]
  calc
    _ ≤ (K^(degree m)*Real.exp ((degree m:ℝ)*R))*
        Real.exp (sourceRate b K*R)*Real.exp (-d*R^2) := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact mul_le_mul (monomial_bound m z K R hK hR hz) (source_bound b z K R hz)
        (norm_nonneg _) (mul_nonneg (pow_nonneg hK _) (Real.exp_pos _).le)
    _ = K^(degree m)*Real.exp (((degree m:ℝ)+sourceRate b K)*R-d*R^2) := by
      rw [show ((degree m:ℝ)+sourceRate b K)*R-d*R^2=
        ((degree m:ℝ)*R+sourceRate b K*R)+(-d*R^2) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (complete_square_bound d _ R hd)) (pow_nonneg hK _)

theorem polynomial_source_bound {n : ℕ} (P : MvPolynomial (Fin n) ℂ) (b z : Fin n → ℂ)
    (K R d : ℝ) (hK : 0 ≤ K) (hR : 0 ≤ R) (hd : 0 < d)
    (hz : ∀ i, ‖z i‖ ≤ K*R) :
    ‖MvPolynomial.eval z P*Complex.exp (∑ i, b i*z i)‖*Real.exp (-d*R^2) ≤
      absorptionCap P b K d := by
  rw [MvPolynomial.eval_eq',Finset.sum_mul]
  apply (mul_le_mul_of_nonneg_right (norm_sum_le _ _) (Real.exp_pos _).le).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro m _
  calc
    _ = ‖P.coeff m‖*(‖(∏ i, z i^(m i))*Complex.exp (∑ i, b i*z i)‖*
        Real.exp (-d*R^2)) := by simp only [norm_mul]; ring
    _ ≤ _ := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (monomial_source_bound m b z K R d hK hR hd hz) (norm_nonneg (P.coeff m))

theorem actual_target_polynomial_bound (ε h α w c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (hα : 0 < α) (hw : 1 ≤ w) (q : ℂ) (hq : |q.im| ≤ |h|)
    (x : KFCausalEuclideanProductCoordinates.Joint 2 4)
    (P : MvPolynomial (Fin 5) ℂ) (b : Fin 5 → ℂ) (d : ℝ) (hd : 0 < d) :
    ‖MvPolynomial.eval (fun i => KFCausalWidthGaussianHolomorphicQuotient.targetVector ε h α w c η q x i) P*
      Complex.exp (∑ i, b i*KFCausalWidthGaussianHolomorphicQuotient.targetVector ε h α w c η q x i)‖*
      Real.exp (-d*‖KFCausalWidthGaussianHolomorphicQuotient.baselineVector ε α w c (q.re:ℂ) x‖^2) ≤
        absorptionCap P b (20/17) d := by
  apply polynomial_source_bound P b _ (20/17) _ d (by norm_num) (norm_nonneg _) hd
  intro i
  exact (PiLp.norm_apply_le _ i).trans
    (KFCausalWidthGaussianNeutralMultiplier.target_norm_bound ε h α w c η hε hh hα hw q hq x)

theorem actual_multiplier_polynomial_bound (ε h a α W w c η : ℝ) (hε : 0 < ε)
    (hh : |h| ≤ ε/10) (ha : 0 ≤ a) (hα : 0 < α) (hw : 1 ≤ w) (hW : w ≤ W)
    (q : ℂ) (hq : |q.im| ≤ |h|) (x : KFCausalEuclideanProductCoordinates.Joint 2 4)
    (P : MvPolynomial (Fin 5) ℂ) (b : Fin 5 → ℂ) :
    ‖(MvPolynomial.eval (fun i => KFCausalWidthGaussianHolomorphicQuotient.targetVector ε h α w c η q x i) P*
      Complex.exp (∑ i, b i*KFCausalWidthGaussianHolomorphicQuotient.targetVector ε h α w c η q x i))*
      KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c η q x‖ ≤
        (4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2))*absorptionCap P b (20/17) (78/289) := by
  let R := ‖KFCausalWidthGaussianHolomorphicQuotient.baselineVector ε α w c (q.re:ℂ) x‖
  let M := 4*W*ε⁻¹*Real.exp (|h|/ε+4*a*h^2)
  have hWp : 0 < W := by linarith
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hp := actual_target_polynomial_bound ε h α w c η hε hh hα hw q hq x P b
    (78/289) (by norm_num)
  have hg := KFCausalWidthGaussianHolomorphicQuotient.multiplier_gaussian_bound
    ε h a α W w c η hε hh ha hα hw hW q hq x
  have he : Real.exp (-(a/2)*q.re^2+4*a*h^2) ≤ Real.exp (4*a*h^2) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg ha (sq_nonneg q.re)]
  have hg' : ‖KFCausalWidthGaussianHolomorphicQuotient.multiplier ε h a α W w c η q x‖ ≤
      M*Real.exp (-(78/289:ℝ)*R^2) := by
    apply hg.trans
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    calc
      _ ≤ (4*W)*(ε⁻¹*Real.exp (|h|/ε)*Real.exp (4*a*h^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (by positivity)) (by positivity)
      _ = _ := by dsimp [M]; rw [Real.exp_add]; ring
  rw [norm_mul]
  calc
    _ ≤ _*(M*Real.exp (-(78/289:ℝ)*R^2)) :=
      mul_le_mul_of_nonneg_left hg' (norm_nonneg _)
    _ = M*(_*Real.exp (-(78/289:ℝ)*R^2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hM

#print axioms absorptionCap_nonnegative
#print axioms monomial_bound
#print axioms source_bound
#print axioms monomial_source_bound
#print axioms polynomial_source_bound
#print axioms actual_target_polynomial_bound
#print axioms actual_multiplier_polynomial_bound
end
end UnifiedTheory.Audit.KFCausalComplexVectorPolynomialAbsorption
