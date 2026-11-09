/- Resolvent smoothing controls energy and the norm of an operator whose
quadratic form is the derivative of the resolvent. These estimates will
control the correction from a moving-time observable regularization. -/
import UnifiedTheory.Audit.KFCausalFormResolventError

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFormResolventEnergyBounds
noncomputable section
open UnifiedTheory.Audit.KFCausalShiftedForm (complex_inner_square)
open UnifiedTheory.Audit.KFCausalFormResolventError (cross_re_bound)
variable {V H K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

theorem lift_energy_square (J : V →L[ℂ] H) (L : V →L[ℂ] K)
    (a : ℝ) (ha : 0 < a) (f : H) (y : V)
    (hv : inner ℂ (L y) (L y) = (a:ℂ)*inner ℂ (f-J y) (J y)) :
    ‖L y‖^2 ≤ a/4*‖f‖^2 := by
  have he := congrArg Complex.re hv
  simp only [complex_inner_square,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at he
  have hr : (inner ℂ (f-J y) (J y)).re = (inner ℂ (J y) (f-J y)).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hr] at he
  have hb := mul_le_mul_of_nonneg_left (cross_re_bound f (J y)) ha.le
  nlinarith

theorem lift_energy_contraction (J : V →L[ℂ] H) (L : V →L[ℂ] K)
    (a : ℝ) (ha : 0 < a) (x y : V)
    (hv : ∀ z, inner ℂ (L y) (L z) = (a:ℂ)*inner ℂ (J x-J y) (J z)) :
    ‖L y‖ ≤ ‖L x‖ := by
  have he := congrArg Complex.re (hv (x-y))
  simp only [map_sub,complex_inner_square,Complex.mul_re,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero] at he
  rw [inner_sub_right,Complex.sub_re,complex_inner_square,Complex.ofReal_re] at he
  have hi := (Complex.re_le_norm (inner ℂ (L y) (L x))).trans (norm_inner_le_norm _ _)
  have hp := mul_nonneg ha.le (sq_nonneg ‖J x-J y‖)
  nlinarith [norm_nonneg (L x),norm_nonneg (L y)]

theorem scalar_derivative_square (a E n u v : ℝ) (ha : 0 < a) (hE : 0 ≤ E)
    (hn : 0 ≤ n)
    (hp : n^2 ≤ (2/a)*u*v) (he : u^2 ≤ E) (hl : v^2 ≤ a/4*n^2) :
    n^2 ≤ E/a := by
  by_cases hz : n = 0
  · subst n
    simpa only [zero_pow (by decide : (2:ℕ) ≠ 0)] using div_nonneg hE ha.le
  have hnp : 0 < n := lt_of_le_of_ne hn (Ne.symm hz)
  have hs : a*n^2 ≤ 2*u*v := by
    have hm := mul_le_mul_of_nonneg_left hp ha.le
    have hh : a*((2/a)*u*v) = 2*u*v := by field_simp
    nlinarith
  have hs2 := pow_le_pow_left₀ (by positivity : 0 ≤ a*n^2) hs 2
  have hm := mul_le_mul he hl (sq_nonneg v) hE
  have hprod : (a*n^2)*(a*n^2) ≤ (a*n^2)*E := by nlinarith
  have heq : a*n^2 ≤ E := (mul_le_mul_iff_right₀ (by positivity : 0 < a*n^2)).mp hprod
  exact (le_div_iff₀ ha).mpr (by nlinarith)

theorem gram_derivative_square (A : H →L[ℂ] H) (T : H →L[ℂ] K)
    (a : ℝ) (ha : 0 < a) (f : H) (E : ℝ) (hE : 0 ≤ E)
    (hp : ∀ g, inner ℂ (A f) g = -((2/a:ℝ):ℂ)*inner ℂ (T f) (T g))
    (he : ‖T f‖^2 ≤ E) (hl : ∀ g, ‖T g‖^2 ≤ a/4*‖g‖^2) :
    ‖A f‖^2 ≤ E/a := by
  have hn := congrArg norm (hp (A f))
  simp only [complex_inner_square,norm_mul,norm_neg,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sq_nonneg ‖A f‖),
    abs_of_pos (div_pos (by norm_num : (0:ℝ) < 2) ha)] at hn
  have hb := mul_le_mul_of_nonneg_left (norm_inner_le_norm (𝕜 := ℂ) (T f) (T (A f)))
    (by positivity : 0 ≤ 2/a)
  have hpair : ‖A f‖^2 ≤ (2/a)*‖T f‖*‖T (A f)‖ := by nlinarith
  exact scalar_derivative_square a E ‖A f‖ ‖T f‖ ‖T (A f)‖ ha hE
    (norm_nonneg _) hpair he (hl (A f))

#print axioms lift_energy_square
#print axioms lift_energy_contraction
#print axioms scalar_derivative_square
#print axioms gram_derivative_square
end
end UnifiedTheory.Audit.KFCausalFormResolventEnergyBounds
