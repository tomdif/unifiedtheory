/- Bounded physical formulas for a moving resolvent sandwich and its
explicit time-derivative correction. -/
import UnifiedTheory.Audit.KFCausalMovingObservableDerivative
import UnifiedTheory.Audit.KFCausalSandwichCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalMovingSandwichCalculus
noncomputable section
open scoped ComplexConjugate
open UnifiedTheory.Audit.KFCausalBoundedFormCurve (gram)
open UnifiedTheory.Audit.KFCausalSandwichCalculus (sandwichMap sandwich_triple_pairing)

variable {H V K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def correction (R S D : H →L[ℂ] H) : H →L[ℂ] H :=
  S.comp (D.comp R)+R.comp (D.comp S)

theorem sandwich_derivative (R : ℝ → H →L[ℂ] H) (S D : H →L[ℂ] H)
    (t : ℝ) (hR : HasDerivAt R S t) :
    HasDerivAt (fun u => (R u).comp (D.comp (R u))) (correction (R t) S D) t := by
  simpa only [zero_mul,zero_add] using hR.mul ((hasDerivAt_const t D).mul hR)

theorem correction_bound (R S D : H →L[ℂ] H)
    (hR : ∀ x, ‖R x‖ ≤ ‖x‖)
    (hRs : ∀ x y, inner ℂ (R x) y = inner ℂ x (R y))
    (hSs : ∀ x y, inner ℂ (S x) y = inner ℂ x (S y)) (x : H) :
    ‖inner ℂ x (correction R S D x)‖ ≤ 2*‖D‖*‖x‖*‖S x‖ := by
  have he : inner ℂ x (correction R S D x) =
      inner ℂ (S x) (D (R x))+inner ℂ (R x) (D (S x)) := by
    simp only [correction,ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      inner_add_right,hRs,hSs]
  rw [he]
  calc
    _ ≤ ‖inner ℂ (S x) (D (R x))‖+‖inner ℂ (R x) (D (S x))‖ := norm_add_le _ _
    _ ≤ ‖S x‖*(‖D‖*‖R x‖)+‖R x‖*(‖D‖*‖S x‖) :=
      add_le_add ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)))
        ((norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_left (D.le_opNorm _) (norm_nonneg _)))
    _ ≤ ‖S x‖*(‖D‖*‖x‖)+‖x‖*(‖D‖*‖S x‖) :=
      add_le_add (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hR x) (norm_nonneg D)) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hR x) (by positivity))
    _ = _ := by ring

theorem exp_smul_square (t : ℝ) (x : K) :
    ‖Real.exp t • x‖^2 = Real.exp (2*t)*‖x‖^2 := by
  have he : (Real.exp t)^2 = Real.exp (2*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos (Real.exp_pos t),mul_pow,he]

variable [CompleteSpace V] [CompleteSpace H] [CompleteSpace K]

theorem gram_pairing (J : V →L[ℂ] H) (P : V →L[ℂ] V) (B : V →L[ℂ] K)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) (c : ℝ) (f g : H) :
    inner ℂ (sandwichMap J (P*(c • gram B)*P) f) g =
      (c:ℂ)*inner ℂ (B (P (J.adjoint f))) (B (P (J.adjoint g))) := by
  rw [sandwich_triple_pairing J P (c • gram B) hP]
  change inner ℂ (c • B.adjoint (B (P (J.adjoint f)))) (P (J.adjoint g)) = _
  rw [inner_smul_left_eq_smul,B.adjoint_inner_left]
  rfl

def weightedLift (J : V →L[ℂ] H) (P : V →L[ℂ] V) (B : V →L[ℂ] K)
    (a t : ℝ) : H →L[ℂ] K :=
  Real.exp t • (B.comp (a • (P.comp J.adjoint)))

omit [CompleteSpace K] in
theorem weightedLift_apply (J : V →L[ℂ] H) (P : V →L[ℂ] V) (B : V →L[ℂ] K)
    (a t : ℝ) (f : H) :
    weightedLift J P B a t f = Real.exp t • B (a • P (J.adjoint f)) := rfl

theorem scaled_gram_pairing (J : V →L[ℂ] H) (P : V →L[ℂ] V) (B : V →L[ℂ] K)
    (hP : ∀ x y, inner ℂ (P x) y = inner ℂ x (P y)) (a t : ℝ) (ha : 0 < a) (f g : H) :
    inner ℂ ((a • sandwichMap J (-(P*((2*Real.exp (2*t)) • gram B)*P))) f) g =
      -((2/a:ℝ):ℂ)*inner ℂ (weightedLift J P B a t f) (weightedLift J P B a t g) := by
  have hexp : Real.exp t*Real.exp t = Real.exp (2*t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [map_neg,ContinuousLinearMap.smul_apply,ContinuousLinearMap.neg_apply,
    inner_smul_left_eq_smul,inner_neg_left,
    gram_pairing J P B hP (2*Real.exp (2*t)),weightedLift_apply,weightedLift_apply,
    ContinuousLinearMap.map_smul_of_tower,ContinuousLinearMap.map_smul_of_tower]
  simp only [inner_smul_left_eq_smul,inner_smul_right_eq_smul,Complex.real_smul,
    Complex.ofReal_div,Complex.ofReal_mul,Complex.ofReal_ofNat,neg_mul,mul_neg]
  have he : (Real.exp t:ℂ)*(Real.exp t:ℂ) = (Real.exp (2*t):ℂ) := by
    exact_mod_cast hexp
  have hane : (a:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha.ne'
  field_simp
  linear_combination (inner ℂ (B (P (J.adjoint f))) (B (P (J.adjoint g))))*he

#print axioms sandwich_derivative
#print axioms correction_bound
#print axioms exp_smul_square
#print axioms gram_pairing
#print axioms weightedLift_apply
#print axioms scaled_gram_pairing
end
end UnifiedTheory.Audit.KFCausalMovingSandwichCalculus
