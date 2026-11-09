/- Exact coercivity of the normalized repeated-width jet of order two.
The kernel-to-jet identification and the original integral transport are
separate obligations; this module proves the finite matrix certificate. -/
import UnifiedTheory.Audit.KFCausalChargedCoolingTwoWidthCoercivity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeCoercivity
noncomputable section
open scoped ComplexOrder

def hermitianThree (d0 d1 d2 : ℝ) (z01 z02 z12 : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![(d0:ℂ),z01,z02; starRingEnd ℂ z01,(d1:ℂ),z12;
    starRingEnd ℂ z02,starRingEnd ℂ z12,(d2:ℂ)]

theorem hermitianThree_sub (d0 d1 d2 e0 e1 e2 t : ℝ) (z01 z02 z12 w01 w02 w12 : ℂ) :
    hermitianThree d0 d1 d2 z01 z02 z12-(t:ℂ) • hermitianThree e0 e1 e2 w01 w02 w12 =
      hermitianThree (d0-t*e0) (d1-t*e1) (d2-t*e2)
        (z01-(t:ℂ)*w01) (z02-(t:ℂ)*w02) (z12-(t:ℂ)*w12) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermitianThree,smul_eq_mul]

theorem three_by_three_positive (d0 d1 d2 : ℝ) (z01 z02 z12 : ℂ)
    (h0 : 0 < d0) (h1 : 0 < d0*d1-Complex.normSq z01)
    (h2 : 0 ≤ (d0*d1-Complex.normSq z01)*(d0*d2-Complex.normSq z02)-
      Complex.normSq ((d0:ℂ)*z12-starRingEnd ℂ z01*z02)) :
    Matrix.PosSemidef (hermitianThree d0 d1 d2 z01 z02 z12) := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [hermitianThree,Matrix.conjTranspose_apply]
  · intro x
    rw [Complex.nonneg_iff]
    have hs1 := mul_nonneg h1.le
      (Complex.normSq_nonneg ((d0:ℂ)*x 0+z01*x 1+z02*x 2))
    have hs2 := Complex.normSq_nonneg
      (((d0*d1-Complex.normSq z01:ℝ):ℂ)*x 1+
        ((d0:ℂ)*z12-starRingEnd ℂ z01*z02)*x 2)
    have hs3 := mul_nonneg h2 (Complex.normSq_nonneg (x 2))
    simp only [dotProduct,Matrix.mulVec,Fin.sum_univ_three,Pi.star_apply,Complex.star_def,
      hermitianThree]
    change 0 ≤ (starRingEnd ℂ (x 0)*((d0:ℂ)*x 0+z01*x 1+z02*x 2)+
      starRingEnd ℂ (x 1)*(starRingEnd ℂ z01*x 0+(d1:ℂ)*x 1+z12*x 2)+
      starRingEnd ℂ (x 2)*(starRingEnd ℂ z02*x 0+starRingEnd ℂ z12*x 1+(d2:ℂ)*x 2)).re ∧
      0 = (starRingEnd ℂ (x 0)*((d0:ℂ)*x 0+z01*x 1+z02*x 2)+
      starRingEnd ℂ (x 1)*(starRingEnd ℂ z01*x 0+(d1:ℂ)*x 1+z12*x 2)+
      starRingEnd ℂ (x 2)*(starRingEnd ℂ z02*x 0+starRingEnd ℂ z12*x 1+(d2:ℂ)*x 2)).im
    constructor
    · apply nonneg_of_mul_nonneg_left (b := (d0*d1-Complex.normSq z01)*d0) ?_
        (mul_pos h1 h0)
      simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.sub_re,
        Complex.sub_im,Complex.mul_re,Complex.mul_im,Complex.conj_re,Complex.conj_im,
        Complex.ofReal_re,Complex.ofReal_im] at hs1 hs2 hs3 ⊢
      nlinarith only [hs1,hs2,hs3]
    · simp only [Complex.add_im,Complex.mul_im,Complex.mul_re,Complex.conj_re,
        Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,Complex.add_re]
      ring

def gram (x : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  hermitianThree 1 (7*x^2/4+15/16) (321*x^4/16+441*x^2/32+945/256)
    ((3/4:ℝ)+(x/2:ℝ)*Complex.I)
    ((-7*x^2/4+15/16:ℝ)+(5*x/4:ℝ)*Complex.I)
    ((49*x^2/16+105/64:ℝ)+(27*x^3/8+35*x/32:ℝ)*Complex.I)

def cooling (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  hermitianThree 2 (7*x^2/2+x*y+3/8)
    (321*x^4/8+27*x^3*y/2+245*x^2/16+35*x*y/8+105/128)
    ((1/2:ℝ)+(x+y:ℝ)*Complex.I)
    ((-7*x^2/2-x*y+3/8:ℝ)+(3*x/2+3*y/2:ℝ)*Complex.I)
    ((35*x^2/8+5*x*y/4+15/32:ℝ)+
      (27*x^3/4+21*x^2*y/4+15*x/16+15*y/16:ℝ)*Complex.I)

def residual (x y : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  cooling x y-((1/16:ℝ):ℂ) • gram x

def d1 (x y : ℝ) : ℝ := 217*x^2/64+x*y+81/256
def d2 (x y : ℝ) : ℝ :=
  9951*x^4/256+27*x^3*y/2+7399*x^2/512+35*x*y/8+2415/4096
def z01 (x y : ℝ) : ℂ := (29/64:ℝ)+(31*x/32+y:ℝ)*Complex.I
def z02 (x y : ℝ) : ℂ :=
  (-217*x^2/64-x*y+81/256:ℝ)+(91*x/64+3*y/2:ℝ)*Complex.I
def z12 (x y : ℝ) : ℂ :=
  (1071*x^2/256+5*x*y/4+375/1024:ℝ)+
    (837*x^3/128+21*x^2*y/4+445*x/512+15*y/16:ℝ)*Complex.I

theorem residual_entries (x y : ℝ) :
    residual x y = hermitianThree (31/16) (d1 x y) (d2 x y)
      (z01 x y) (z02 x y) (z12 x y) := by
  unfold residual cooling gram
  rw [hermitianThree_sub]
  congr 1
  · norm_num
  · unfold d1; ring
  · unfold d2; ring
  · unfold z01; push_cast; ring
  · unfold z02; push_cast; ring
  · unfold z12; push_cast; ring

def firstMinor (x y : ℝ) : ℝ := (31/16)*d1 x y-Complex.normSq (z01 x y)
def schurDet (x y : ℝ) : ℝ :=
  firstMinor x y*((31/16)*d2 x y-Complex.normSq (z02 x y))-
    Complex.normSq (((31/16:ℝ):ℂ)*z12 x y-starRingEnd ℂ (z01 x y)*z02 x y)

theorem first_minor_identity (y : ℝ) (hy : 1-y^2 ≠ 0) :
    firstMinor (y/(1-y^2)) y*(1-y^2)^2 =
      (1+y^2)*(835+6979*y^2-2048*y^4)/2048 := by
  simp only [firstMinor,d1,z01,Complex.normSq_apply,Complex.add_re,Complex.add_im,
    Complex.mul_re,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,
    Complex.I_re,Complex.I_im]
  field_simp
  ring

theorem schur_det_identity (y : ℝ) (hy : 1-y^2 ≠ 0) :
    schurDet (y/(1-y^2)) y*(1-y^2)^6 =
      31*(1+y^2)^3*(56499+495001*y^2+26131865*y^4-
        8096589*y^6-235520*y^8)/16777216 := by
  simp only [schurDet,firstMinor,d1,d2,z01,z02,z12,Complex.normSq_apply,
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
  have h6 : y^6 ≤ y^4 := by nlinarith [mul_nonneg (sq_nonneg (y^2)) hd.le]
  have h8 : y^8 ≤ y^4 := by
    have h41 : y^4 ≤ 1 := h4.trans hy2.le
    nlinarith [mul_nonneg (sq_nonneg (y^2)) (sub_nonneg.mpr h41)]
  have hp : 0 < 835+6979*y^2-2048*y^4 := by nlinarith [sq_nonneg y]
  have hq : 0 < 56499+495001*y^2+26131865*y^4-8096589*y^6-235520*y^8 := by
    nlinarith only [h6,h8,sq_nonneg y,sq_nonneg (y^2)]
  have hi := first_minor_identity y hd.ne'
  have hj := schur_det_identity y hd.ne'
  constructor
  · apply pos_of_mul_pos_left (b := (1-y^2)^2) ?_ (by positivity)
    rw [hi]
    positivity
  · apply pos_of_mul_pos_left (b := (1-y^2)^6) ?_ (by positivity)
    rw [hj]
    positivity

theorem normalized_coercivity (y : ℝ) (hy : |y| < 1) :
    Matrix.PosSemidef (residual (y/(1-y^2)) y) := by
  rw [residual_entries]
  have hm := minor_positive y hy
  exact three_by_three_positive _ _ _ _ _ _ (by norm_num) hm.1 hm.2.le

#print axioms hermitianThree_sub
#print axioms three_by_three_positive
#print axioms residual_entries
#print axioms first_minor_identity
#print axioms schur_det_identity
#print axioms minor_positive
#print axioms normalized_coercivity
end
end UnifiedTheory.Audit.KFCausalChargedCoolingConfluentThreeCoercivity
