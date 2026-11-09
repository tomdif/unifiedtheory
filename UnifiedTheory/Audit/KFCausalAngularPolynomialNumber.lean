/- The literal circle number form is nonnegative on every complex polynomial.
Monomial orthogonality and the finite coefficient identity are derived from
actual angular integrals. This is the finite approximation supplier for the
degree-two Hardy estimate; no infinite-series number bound is assumed. -/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Tactic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularPolynomialNumber
noncomputable section
open MeasureTheory
open scoped ComplexConjugate

private theorem exponential_mode (i j : ℕ) :
    (∫ theta in 0..(2*Real.pi),
      Complex.exp (((j:ℂ)-(i:ℂ))*Complex.I*(theta:ℂ)))=
        if i=j then (2*Real.pi:ℝ) else 0 := by
  by_cases hij : i=j
  · subst j
    simp
  · have hc : ((j:ℂ)-(i:ℂ))*Complex.I≠0 := by
      apply mul_ne_zero _ Complex.I_ne_zero
      exact sub_ne_zero.mpr (by exact_mod_cast Ne.symm hij)
    rw [integral_exp_mul_complex hc]
    have he : Complex.exp ((((j:ℂ)-(i:ℂ))*Complex.I)*((2*Real.pi:ℝ):ℂ))=1 := by
      have hp : (((j:ℂ)-(i:ℂ))*Complex.I)*((2*Real.pi:ℝ):ℂ)=
          (j:ℂ)*(2*Real.pi*Complex.I)-(i:ℂ)*(2*Real.pi*Complex.I) := by push_cast; ring
      rw [hp,Complex.exp_sub,Complex.exp_nat_mul,Complex.exp_nat_mul,
        Complex.exp_two_pi_mul_I]
      simp
    rw [he]
    simp [hij]

theorem monomial_pairing (R : ℝ) (i j : ℕ) :
    (∫ theta in 0..(2*Real.pi),
      conj ((circleMap 0 R theta)^i)*(circleMap 0 R theta)^j)=
        if i=j then ((2*Real.pi:ℝ):ℂ)*(R:ℂ)^(2*i) else 0 := by
  have he (theta : ℝ) : conj ((circleMap 0 R theta)^i)*(circleMap 0 R theta)^j=
      (R:ℂ)^(i+j)*Complex.exp (((j:ℂ)-(i:ℂ))*Complex.I*(theta:ℂ)) := by
    simp only [circleMap_zero,map_pow,map_mul,map_natCast,Complex.conj_ofReal,← Complex.exp_conj,
      Complex.conj_I,mul_pow,← Complex.exp_nat_mul]
    rw [pow_add,show ((j:ℂ)-(i:ℂ))*Complex.I*(theta:ℂ)=
      (i:ℂ)*((theta:ℂ)*(-Complex.I))+(j:ℂ)*((theta:ℂ)*Complex.I) by ring,
      Complex.exp_add]
    ring_nf
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul,exponential_mode]
  by_cases hij : i=j
  · subst j
    simp only [if_true,show i+i=2*i by omega]
    ring
  · simp [hij]

theorem finite_pairing (R : ℝ) (s : Finset ℕ) (a b : ℕ→ℂ) :
    (∫ theta in 0..(2*Real.pi),
      conj (∑i∈s,a i*(circleMap 0 R theta)^i)*(∑j∈s,b j*(circleMap 0 R theta)^j))=
        ((2*Real.pi:ℝ):ℂ)*∑i∈s,conj (a i)*b i*(R:ℂ)^(2*i) := by
  have he (theta : ℝ) :
      conj (∑i∈s,a i*(circleMap 0 R theta)^i)*(∑j∈s,b j*(circleMap 0 R theta)^j)=
        ∑i∈s,∑j∈s,(conj (a i)*b j)*
          (conj ((circleMap 0 R theta)^i)*(circleMap 0 R theta)^j) := by
    simp only [map_sum,map_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [he]
  rw [intervalIntegral.integral_finset_sum]
  · have hj (i : ℕ) :
        (∫ theta in 0..(2*Real.pi),∑j∈s,(conj (a i)*b j)*
          (conj ((circleMap 0 R theta)^i)*(circleMap 0 R theta)^j))=
          ∑j∈s,(conj (a i)*b j)*
            (if i=j then ((2*Real.pi:ℝ):ℂ)*(R:ℂ)^(2*i) else 0) := by
      rw [intervalIntegral.integral_finset_sum]
      · simp only [intervalIntegral.integral_const_mul,monomial_pairing]
      · intro j _
        exact (by fun_prop : Continuous _).intervalIntegrable _ _
    simp_rw [hj,mul_ite,mul_zero]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_ite_eq s i]
    simp only [hi,if_true]
    ring
  · intro i _
    exact (by fun_prop : Continuous _).intervalIntegrable _ _

theorem number_eval (P : Polynomial ℂ) (z : ℂ) :
    z*P.derivative.eval z=∑i∈P.support,(i:ℂ)*P.coeff i*z^i := by
  rw [Polynomial.derivative_eval,Polynomial.sum_def,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i=0
  · simp [hi]
  · have he : i-1+1=i := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hi)
    rw [show z*(P.coeff i*(i:ℂ)*z^(i-1))=(i:ℂ)*P.coeff i*(z^(i-1)*z) by ring,
      ← pow_succ,he]

theorem number_nonnegative (P : Polynomial ℂ) (R : ℝ) :
    0≤(∫ theta in 0..(2*Real.pi),
      conj (P.eval (circleMap 0 R theta))*
        (circleMap 0 R theta*P.derivative.eval (circleMap 0 R theta))).re := by
  have hp (z : ℂ) : P.eval z=∑i∈P.support,P.coeff i*z^i :=
    Polynomial.eval_eq_sum
  simp_rw [number_eval,hp]
  rw [finite_pairing R P.support (fun i => P.coeff i) (fun i => (i:ℂ)*P.coeff i)]
  have he (i : ℕ) : conj (P.coeff i)*((i:ℂ)*P.coeff i)*(R:ℂ)^(2*i)=
      ((i:ℝ)*‖P.coeff i‖^2*R^(2*i):ℝ) := by
    rw [show conj (P.coeff i)*((i:ℂ)*P.coeff i)=
      (i:ℂ)*(conj (P.coeff i)*P.coeff i) by ring,Complex.conj_mul']
    push_cast
    rfl
  simp_rw [he]
  rw [← Complex.ofReal_sum,← Complex.ofReal_mul,Complex.ofReal_re]
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg i) (sq_nonneg _))
    (by rw [pow_mul]; exact pow_nonneg (sq_nonneg R) i)

#print axioms monomial_pairing
#print axioms finite_pairing
#print axioms number_eval
#print axioms number_nonnegative
end
end UnifiedTheory.Audit.KFCausalAngularPolynomialNumber
