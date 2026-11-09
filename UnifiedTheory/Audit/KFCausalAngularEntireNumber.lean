/- The circle number form for exp(A(z))*B(z), with A and B complex
polynomials, is obtained from literal finite Taylor polynomials. Both
values and derivatives converge, with an explicit integrable majorant.
No Hardy inequality or boundary-series identity is assumed. -/
import UnifiedTheory.Audit.KFCausalAngularPolynomialNumber
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularEntireNumber
noncomputable section
open MeasureTheory Filter
open scoped ComplexConjugate Topology

def expPartial (A : Polynomial ℂ) (n : ℕ) : Polynomial ℂ :=
  ∑ k ∈ Finset.range n, Polynomial.C ((k.factorial:ℂ)⁻¹)*A^k

theorem partial_eval (A : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    (expPartial A n).eval z=∑k∈Finset.range n,(A.eval z)^k/(k.factorial:ℂ) := by
  simp only [expPartial,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,div_eq_mul_inv,mul_comm]

theorem partial_derivative (A : Polynomial ℂ) (n : ℕ) :
    (expPartial A (n+1)).derivative=expPartial A n*A.derivative := by
  unfold expPartial
  rw [Polynomial.derivative_sum,Finset.sum_range_succ']
  simp only [pow_zero,mul_one,Polynomial.derivative_C,add_zero]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  rw [Polynomial.derivative_C_mul,Polynomial.derivative_pow]
  simp only [Nat.add_sub_cancel]
  have he : (k.factorial:ℂ)⁻¹=((k+1).factorial:ℂ)⁻¹*(k+1:ℕ) := by
    rw [Nat.factorial_succ,Nat.cast_mul]
    have hk : (k.factorial:ℂ)≠0 := by exact_mod_cast Nat.factorial_ne_zero k
    have hn : ((k+1:ℕ):ℂ)≠0 := by exact_mod_cast Nat.succ_ne_zero k
    field_simp
  rw [he,Polynomial.C_mul]
  simp only [Polynomial.C_eq_natCast]
  ring

theorem partial_tendsto (A : Polynomial ℂ) (z : ℂ) :
    Tendsto (fun n => (expPartial A n).eval z) atTop (𝓝 (Complex.exp (A.eval z))) := by
  simp_rw [partial_eval,Complex.exp_eq_exp_ℂ]
  exact (NormedSpace.expSeries_div_hasSum_exp (A.eval z)).tendsto_sum_nat

theorem partial_bound (A : Polynomial ℂ) (n : ℕ) (z : ℂ) :
    ‖(expPartial A n).eval z‖≤Real.exp ‖A.eval z‖ := by
  rw [partial_eval]
  calc
    _ ≤ ∑k∈Finset.range n,‖(A.eval z)^k/(k.factorial:ℂ)‖ := norm_sum_le _ _
    _ = ∑k∈Finset.range n,‖A.eval z‖^k/(k.factorial:ℝ) := by
      simp only [norm_div,norm_pow,Complex.norm_natCast]
    _ ≤ _ := Real.sum_le_exp_of_nonneg (norm_nonneg _) _

theorem number_nonnegative (A B : Polynomial ℂ) (R : ℝ) :
    0≤(∫ theta in 0..(2*Real.pi),
      conj (Complex.exp (A.eval (circleMap 0 R theta))*B.eval (circleMap 0 R theta))*
        (circleMap 0 R theta*Complex.exp (A.eval (circleMap 0 R theta))*
          (A.derivative.eval (circleMap 0 R theta)*B.eval (circleMap 0 R theta)+
            B.derivative.eval (circleMap 0 R theta)))).re := by
  let P (n : ℕ) := expPartial A (n+1)*B
  let f (n : ℕ) (theta : ℝ) :=
    conj ((P n).eval (circleMap 0 R theta))*
      (circleMap 0 R theta*(P n).derivative.eval (circleMap 0 R theta))
  let g (theta : ℝ) :=
    conj (Complex.exp (A.eval (circleMap 0 R theta))*B.eval (circleMap 0 R theta))*
      (circleMap 0 R theta*Complex.exp (A.eval (circleMap 0 R theta))*
        (A.derivative.eval (circleMap 0 R theta)*B.eval (circleMap 0 R theta)+
          B.derivative.eval (circleMap 0 R theta)))
  let bound (theta : ℝ) :=
    Real.exp ‖A.eval (circleMap 0 R theta)‖*‖B.eval (circleMap 0 R theta)‖*
      (‖circleMap 0 R theta‖*(Real.exp ‖A.eval (circleMap 0 R theta)‖*
        (‖A.derivative.eval (circleMap 0 R theta)‖*‖B.eval (circleMap 0 R theta)‖+
          ‖B.derivative.eval (circleMap 0 R theta)‖)))
  have hd (n : ℕ) (z : ℂ) : (P n).derivative.eval z=
      (expPartial A n).eval z*A.derivative.eval z*B.eval z+
        (expPartial A (n+1)).eval z*B.derivative.eval z := by
    simp only [P,Polynomial.derivative_mul,partial_derivative,Polynomial.eval_add,
      Polynomial.eval_mul]
  have hp (n : ℕ) (z : ℂ) : (P n).eval z=(expPartial A (n+1)).eval z*B.eval z :=
    Polynomial.eval_mul
  have hf (n : ℕ) (theta : ℝ) : ‖f n theta‖≤bound theta := by
    dsimp only [f,bound]
    rw [norm_mul,Complex.norm_conj,norm_mul,hp,norm_mul,hd]
    apply mul_le_mul (mul_le_mul_of_nonneg_right (partial_bound A (n+1) _) (norm_nonneg _))
      _ (by positivity) (by positivity)
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    calc
      _ ≤ ‖(expPartial A n).eval (circleMap 0 R theta)*A.derivative.eval (circleMap 0 R theta)*
            B.eval (circleMap 0 R theta)‖+
          ‖(expPartial A (n+1)).eval (circleMap 0 R theta)*B.derivative.eval (circleMap 0 R theta)‖ := norm_add_le _ _
      _ ≤ _ := by
        simp only [norm_mul]
        rw [mul_add]
        simpa only [mul_assoc] using add_le_add
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (partial_bound A n _) (norm_nonneg _)) (norm_nonneg _))
          (mul_le_mul_of_nonneg_right (partial_bound A (n+1) _) (norm_nonneg _))
  have hl (theta : ℝ) : Tendsto (fun n => f n theta) atTop (𝓝 (g theta)) := by
    have he := partial_tendsto A (circleMap 0 R theta)
    have he' := he.comp (tendsto_add_atTop_nat 1)
    have ht := ((continuous_star.continuousAt.tendsto).comp
      (he'.mul_const (B.eval (circleMap 0 R theta)))).mul
        ((((he.mul_const (A.derivative.eval (circleMap 0 R theta))).mul_const
            (B.eval (circleMap 0 R theta))).add
              (he'.mul_const (B.derivative.eval (circleMap 0 R theta)))).const_mul
                (circleMap 0 R theta))
    convert ht using 1
    · ext n
      simp only [f,hp,hd,Function.comp_apply,Complex.star_def]
    · dsimp only [g]
      rw [Complex.star_def]
      congr 1
      ring
  have ht : Tendsto (fun n => ∫theta in 0..(2*Real.pi),f n theta) atTop
      (𝓝 (∫theta in 0..(2*Real.pi),g theta)) := by
    simp only [intervalIntegral.integral_of_le (by positivity : (0:ℝ)≤2*Real.pi)]
    apply tendsto_integral_of_dominated_convergence bound
    · intro n
      exact (by fun_prop : Continuous (f n)).aestronglyMeasurable
    · exact (by fun_prop : Continuous bound).intervalIntegrable _ _ |>.1
    · intro n
      exact Filter.Eventually.of_forall (hf n)
    · exact Filter.Eventually.of_forall hl
  apply ge_of_tendsto (Complex.continuous_re.continuousAt.tendsto.comp ht)
  exact Filter.Eventually.of_forall fun n =>
    KFCausalAngularPolynomialNumber.number_nonnegative (P n) R

#print axioms partial_eval
#print axioms partial_derivative
#print axioms partial_tendsto
#print axioms partial_bound
#print axioms number_nonnegative
end
end UnifiedTheory.Audit.KFCausalAngularEntireNumber
