/- Full normalized cooling remainder for the repeated-width jet of order
two. Its finite matrix lower bound is preserved under every jet congruence.
Identification with the original Gaussian integral is not assumed here. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeDissipation
noncomputable section
open scoped ComplexOrder
open KFCausalChargedCoolingConfluentThreeCoercivity

def d1 (x y : ℝ) : ℝ := (35+14*y^2)*x^2/4+45/16
def d2 (x y : ℝ) : ℝ :=
  (2247+1284*y^2)*x^4/16+(2205+882*y^2)*x^2/32+2835/256
def z01 (x y : ℝ) : ℂ := (9/4:ℝ)+(x*(4+y^2)/2:ℝ)*Complex.I
def z02 (x y : ℝ) : ℂ :=
  (45/16-7*x^2*(5+2*y^2)/4:ℝ)+(5*x*(4+y^2)/4:ℝ)*Complex.I
def z12 (x y : ℝ) : ℂ :=
  (315/64+49*x^2*(5+2*y^2)/16:ℝ)+
    (27*x^3*(6+3*y^2)/8+35*x*(4+y^2)/32:ℝ)*Complex.I

def remainder (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  hermitianThree 3 (d1 x y) (d2 x y) (z01 x y) (z02 x y) (z12 x y)

def firstMinor (x y : ℝ) : ℝ := 3*d1 x y-Complex.normSq (z01 x y)
def schurDet (x y : ℝ) : ℝ :=
  firstMinor x y*(3*d2 x y-Complex.normSq (z02 x y))-
    Complex.normSq ((3:ℂ)*z12 x y-starRingEnd ℂ (z01 x y)*z02 x y)

theorem first_minor_identity (y : ℝ) (hy : 1-y^2 ≠ 0) :
    firstMinor (y/(1-y^2)) y*(1-y^2)^2 =
      (1+y^2)*(27+97*y^2-2*y^4)/8 := by
  simp only [firstMinor,d1,z01,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  field_simp
  ring

theorem schur_det_identity (y : ℝ) (hy : 1-y^2 ≠ 0) :
    schurDet (y/(1-y^2)) y*(1-y^2)^6 =
      3*(1+y^2)^2*(1215+19950*y^2+88042*y^4+120480*y^6+
        25983*y^8-614*y^10)/256 := by
  change ((3*d1 (y/(1-y^2)) y-Complex.normSq (z01 (y/(1-y^2)) y))*
    (3*d2 (y/(1-y^2)) y-Complex.normSq (z02 (y/(1-y^2)) y))-
    Complex.normSq (((3:ℝ):ℂ)*z12 (y/(1-y^2)) y-
      starRingEnd ℂ (z01 (y/(1-y^2)) y)*z02 (y/(1-y^2)) y))*(1-y^2)^6 = _
  simp only [d1,d2,z01,z02,z12,Complex.normSq_apply,
    Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im,
    Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
    Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im]
  field_simp
  ring

theorem minor_positive (y : ℝ) (hy : |y| < 1) :
    0 < firstMinor (y/(1-y^2)) y ∧ 0 < schurDet (y/(1-y^2)) y := by
  have hy2 : y^2 < 1 := (sq_lt_one_iff_abs_lt_one y).mpr hy
  have hd : 0 < 1-y^2 := by linarith
  have h4 : y^4 ≤ y^2 := by nlinarith [mul_nonneg (sq_nonneg y) hd.le]
  have h10 : y^10 ≤ y^8 := by nlinarith [mul_nonneg (sq_nonneg (y^4)) hd.le]
  have hp : 0 < 27+97*y^2-2*y^4 := by nlinarith [sq_nonneg y]
  have hq : 0 < 1215+19950*y^2+88042*y^4+120480*y^6+25983*y^8-614*y^10 := by
    nlinarith only [h10,sq_nonneg y,sq_nonneg (y^2),sq_nonneg (y^3),sq_nonneg (y^4)]
  have hi := first_minor_identity y hd.ne'
  have hj := schur_det_identity y hd.ne'
  constructor
  · apply pos_of_mul_pos_left (b := (1-y^2)^2) ?_ (by positivity)
    rw [hi]
    positivity
  · apply pos_of_mul_pos_left (b := (1-y^2)^6) ?_ (by positivity)
    rw [hj]
    positivity

theorem remainder_positive (y : ℝ) (hy : |y| < 1) :
    Matrix.PosSemidef (remainder (y/(1-y^2)) y) := by
  have hm := minor_positive y hy
  exact three_by_three_positive _ _ _ _ _ _ (by norm_num) hm.1 hm.2.le

def fullDissipation (x y v s : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  v^2 • cooling x y+(1/s:ℝ) • remainder x y

theorem full_coercivity (y v s : ℝ) (hy : |y| < 1) (hs : 0 < s) :
    Matrix.PosSemidef (fullDissipation (y/(1-y^2)) y v s-
      (v^2/16:ℝ) • gram (y/(1-y^2))) := by
  have h := ((normalized_coercivity y hy).smul (sq_nonneg v)).add
    ((remainder_positive y hy).smul (one_div_nonneg.mpr hs.le))
  convert h using 1
  ext i j
  simp only [fullDissipation,KFCausalChargedCoolingConfluentThreeCoercivity.residual,Matrix.add_apply,Matrix.sub_apply,
    Matrix.smul_apply,Complex.real_smul,smul_eq_mul]
  push_cast
  ring

theorem congruent_coercivity (y v s : ℝ) (hy : |y| < 1) (hs : 0 < s)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.PosSemidef (T*(fullDissipation (y/(1-y^2)) y v s)*T.conjTranspose-
      (v^2/16:ℝ) • (T*gram (y/(1-y^2))*T.conjTranspose)) := by
  have h := (full_coercivity y v s hy hs).mul_mul_conjTranspose_same T
  simpa only [Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] using h

theorem sector_parameters (a b : ℝ) (h : |b| < a) :
    |b/a| < 1 ∧ b/a/(1-(b/a)^2) = a*b/(a^2-b^2) := by
  have ha : 0 < a := lt_of_le_of_lt (abs_nonneg b) h
  have hy : |b/a| < 1 := by
    rw [abs_div,abs_of_pos ha]
    exact (div_lt_one ha).mpr h
  constructor
  · exact hy
  · field_simp

theorem sector_coercivity (a b v s : ℝ) (h : |b| < a) (hs : 0 < s)
    (T : Matrix (Fin 3) (Fin 3) ℂ) :
    Matrix.PosSemidef (T*(fullDissipation (a*b/(a^2-b^2)) (b/a) v s)*T.conjTranspose-
      (v^2/16:ℝ) • (T*gram (a*b/(a^2-b^2)))*T.conjTranspose) := by
  obtain ⟨hy,hx⟩ := sector_parameters a b h
  simpa only [hx,Matrix.smul_mul] using congruent_coercivity (b/a) v s hy hs T

#print axioms first_minor_identity
#print axioms schur_det_identity
#print axioms minor_positive
#print axioms remainder_positive
#print axioms full_coercivity
#print axioms congruent_coercivity
#print axioms sector_parameters
#print axioms sector_coercivity
end
end UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeDissipation
