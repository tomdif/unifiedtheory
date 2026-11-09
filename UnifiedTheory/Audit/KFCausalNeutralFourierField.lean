/- The physical neutral field becomes an exact frequency derivative plus
its complex shear. Arbitrary field powers and all finite interference are
retained, with actual L1 and L2 domains for each Fourier transform. -/
import UnifiedTheory.Audit.KFCausalNeutralFourierShift
import Mathlib.Analysis.Fourier.FourierTransformDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000

namespace UnifiedTheory.Audit.KFCausalNeutralFourierField
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalNeutralLineDomain (family)
open KFCausalNeutralLinePackets (entire)
open KFCausalNeutralFourierShift
open KFCausalGaussianContourShift (horizontal)

def fieldPolynomial (j : ℕ) (q : ℂ) (P : Polynomial ℂ) : Polynomial ℂ :=
  (Polynomial.X+Polynomial.C q)^j*P

theorem family_field (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (j : ℕ) (q z : ℂ) :
    family n β b c (fun i => fieldPolynomial j q (P i)) z = (z+q)^j*family n β b c P z := by
  unfold family entire fieldPolynomial
  simp only [Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_C,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

def fieldLine (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (j : ℕ) (d y x : ℝ) : ℂ := ((x+d:ℝ):ℂ)^j*line n β b c P y x

def spectrum (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (j : ℕ) (q : ℂ) : ℝ → ℂ :=
  𝓕 (line n β b c (fun i => fieldPolynomial j q (P i)) 0)

theorem fieldLine_identity (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (j : ℕ) (d y : ℝ) :
    fieldLine n β b c P j d y =
      line n β b c (fun i => fieldPolynomial j ((d:ℂ)-(y:ℂ)*Complex.I) (P i)) y := by
  funext x
  unfold fieldLine line horizontal
  rw [family_field]
  congr 2
  push_cast
  ring

theorem fieldLine_integrable (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (d y : ℝ) :
    Integrable (fieldLine n β b c P j d y) := by
  rw [fieldLine_identity]
  exact line_integrable n β hβ b c _ y

theorem fieldLine_memLp (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (d y : ℝ) :
    MemLp (fieldLine n β b c P j d y) 2 volume := by
  rw [fieldLine_identity]
  exact line_memLp n β hβ b c _ y

theorem fieldLine_fourier (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (d y k : ℝ) :
    (𝓕 (fieldLine n β b c P j d y)) k =
      (Real.exp (-2*Real.pi*k*y):ℂ)*spectrum n β b c P j ((d:ℂ)-(y:ℂ)*Complex.I) k := by
  rw [fieldLine_identity]
  exact fourier_shift n β hβ b c _ y k

theorem fieldLine_fourier_square (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (d y k : ℝ) :
    ‖(𝓕 (fieldLine n β b c P j d y)) k‖^2 =
      Real.exp (-4*Real.pi*k*y)*‖spectrum n β b c P j ((d:ℂ)-(y:ℂ)*Complex.I) k‖^2 := by
  rw [fieldLine_fourier n β hβ,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _),← Real.exp_nat_mul]
  congr 2
  ring

theorem spectrum_continuous (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (q : ℂ) :
    Continuous (spectrum n β b c P j q) :=
  VectorFourier.fourierIntegral_continuous (L := innerₗ ℝ) Real.continuous_fourierChar continuous_inner
    (line_integrable n β hβ b c _ 0)

theorem line_step (n : ℕ) (β : ℝ) (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ)
    (j : ℕ) (q : ℂ) (x : ℝ) :
    (x:ℂ)*line n β b c (fun i => fieldPolynomial j q (P i)) 0 x =
      line n β b c (fun i => fieldPolynomial (j+1) q (P i)) 0 x-
        q*line n β b c (fun i => fieldPolynomial j q (P i)) 0 x := by
  simp only [line,horizontal,Complex.ofReal_zero,zero_mul,add_zero,family_field,pow_succ]
  ring

theorem spectrum_derivative (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (q : ℂ) (k : ℝ) :
    HasDerivAt (spectrum n β b c P j q)
      ((-2*(Real.pi:ℂ)*Complex.I)*(spectrum n β b c P (j+1) q k-q*spectrum n β b c P j q k)) k := by
  let f := line n β b c (fun i => fieldPolynomial j q (P i)) 0
  let g := line n β b c (fun i => fieldPolynomial (j+1) q (P i)) 0
  have hf : Integrable f := line_integrable n β hβ b c _ 0
  have hg : Integrable g := line_integrable n β hβ b c _ 0
  have hx : Integrable (fun x : ℝ => x • f x) := by
    have hi := family_polynomial_integrable n β hβ b c (fun i => fieldPolynomial j q (P i)) 0 Polynomial.X
    simpa only [f,line,horizontal,Polynomial.eval_X,Complex.ofReal_zero,zero_mul,add_zero,Complex.real_smul] using hi
  have hd := Real.hasDerivAt_fourier hf hx k
  change HasDerivAt (𝓕 f) _ k
  convert hd using 1
  change (-2*(Real.pi:ℂ)*Complex.I)*((𝓕 g) k-q*(𝓕 f) k) =
    (𝓕 (fun x : ℝ => (-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)) • f x)) k
  have he : (fun x : ℝ => (-2*(Real.pi:ℂ)*Complex.I*(x:ℂ)) • f x) =
      fun x => (-2*(Real.pi:ℂ)*Complex.I)*(g x-q*f x) := by
    funext x
    simp only [smul_eq_mul]
    rw [show g x-q*f x = (x:ℂ)*f x from (line_step n β b c P j q x).symm]
    ring
  rw [he]
  have hmul := congrFun (VectorFourier.fourierIntegral_const_smul Real.fourierChar volume
    (innerₗ ℝ) (fun x => g x-q*f x) (-2*(Real.pi:ℂ)*Complex.I)) k
  change (𝓕 (fun x => (-2*(Real.pi:ℂ)*Complex.I)*(g x-q*f x))) k =
    (-2*(Real.pi:ℂ)*Complex.I)*(𝓕 (fun x => g x-q*f x)) k at hmul
  rw [hmul]
  congr 1
  simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul,mul_sub,mul_left_comm _ q]
  have hfg : Integrable (fun x : ℝ => (Real.fourierChar (-inner ℝ x k):ℂ)*g x) := by
    simpa only [Circle.smul_def,smul_eq_mul] using (Real.fourierIntegral_convergent_iff k).mpr hg
  have hff : Integrable (fun x : ℝ => (Real.fourierChar (-inner ℝ x k):ℂ)*f x) := by
    simpa only [Circle.smul_def,smul_eq_mul] using (Real.fourierIntegral_convergent_iff k).mpr hf
  rw [integral_sub hfg (hff.const_mul q),integral_const_mul]

theorem spectrum_field_recursion (n : ℕ) (β : ℝ) (hβ : 0 < β)
    (b c : Fin n → ℂ) (P : Fin n → Polynomial ℂ) (j : ℕ) (q : ℂ) (k : ℝ) :
    spectrum n β b c P (j+1) q k =
      (Complex.I/(2*(Real.pi:ℂ)))*deriv (spectrum n β b c P j q) k+q*spectrum n β b c P j q k := by
  rw [(spectrum_derivative n β hβ b c P j q k).deriv]
  have hp : (Real.pi:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  field_simp
  ring_nf
  simp [Complex.I_sq]

#print axioms family_field
#print axioms fieldLine_identity
#print axioms fieldLine_integrable
#print axioms fieldLine_memLp
#print axioms fieldLine_fourier
#print axioms fieldLine_fourier_square
#print axioms spectrum_continuous
#print axioms line_step
#print axioms spectrum_derivative
#print axioms spectrum_field_recursion
end
end UnifiedTheory.Audit.KFCausalNeutralFourierField
