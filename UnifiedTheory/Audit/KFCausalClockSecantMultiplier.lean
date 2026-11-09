/- A bounded real clock multiplier converts the norm derivative of the
actual unforced shear curve into the physical weighted shear pairing.
The imaginary part cancels by the actual self-adjoint shear graph. -/
import UnifiedTheory.Audit.KFCausalClockSecantRatio
import UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve
import UnifiedTheory.Audit.KFCausalBoundedClockCharge

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockSecantMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockSecantRatio
open UnifiedTheory.Audit.KFCausalImaginaryShearCoefficient (coefficient coefficient_bound)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root rootValue root_coe)
open UnifiedTheory.Audit.KFCausalActualImaginaryShearCurve (coefficientOperator coefficientOperator_coe)
open UnifiedTheory.Audit.KFCausalBoundedClockCharge (multiplier multiplier_coe multiplier_norm)
open UnifiedTheory.Audit.KFCausalClockShearRealMultiplier (real_symmetric real_shear_pairing)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)

variable (ε h : ℝ) (hε : 0 < ε) (hb : |h| ≤ 2*Real.pi*ε/3) (hh : h ≠ 0)

def value (s : ℝ) : ℝ := Real.sqrt (ratio ε h s)

include hε hb hh

theorem value_continuous : Continuous (value ε h) := (ratio_continuous ε h hε hb hh).sqrt

theorem value_square (s : ℝ) : (value ε h s)^2 = ratio ε h s :=
  Real.sq_sqrt (ratio_nonnegative ε h hε hb hh s)

theorem value_bound (s : ℝ) : ‖(value ε h s:ℂ)‖ ≤ Real.sqrt (ε/4) := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (show 0 ≤ value ε h s from Real.sqrt_nonneg _)]
  exact Real.sqrt_le_sqrt (ratio_bound ε h hε hb hh s)

def operator : Hilbert →L[ℂ] Hilbert := multiplier (fun s => (value ε h s:ℂ))
  (Complex.continuous_ofReal.comp (value_continuous ε h hε hb hh)).measurable
  (Real.sqrt (ε/4)) (Real.sqrt_nonneg _) (value_bound ε h hε hb hh)

theorem operator_coe (f : Hilbert) : operator ε h hε hb hh f =ᵐ[volume]
    fun x => (value ε h x.1:ℂ)*f x := multiplier_coe _ _ _ _ _ f

theorem operator_norm_sq (f : Hilbert) : ‖operator ε h hε hb hh f‖^2 ≤ (ε/4)*‖f‖^2 := by
  have he := multiplier_norm (fun s => (value ε h s:ℂ))
    (Complex.continuous_ofReal.comp (value_continuous ε h hε hb hh)).measurable
    (Real.sqrt (ε/4)) (Real.sqrt_nonneg _) (value_bound ε h hε hb hh) f
  calc
    _ ≤ (Real.sqrt (ε/4)*‖f‖)^2 := pow_le_pow_left₀ (norm_nonneg _) he 2
    _ = _ := by rw [mul_pow,Real.sq_sqrt (by positivity : 0 ≤ ε/4)]

theorem imaginary_bound (s : ℝ) : ‖((ratio ε h s*(coefficient ε h s).im:ℝ):ℂ)‖ ≤ 1/8 := by
  rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_nonneg (ratio_nonnegative ε h hε hb hh s)]
  calc
    _ ≤ (ε/4)*‖coefficient ε h s‖ := mul_le_mul (ratio_bound ε h hε hb hh s)
      (Complex.abs_im_le_norm _) (abs_nonneg _) (by positivity)
    _ ≤ (ε/4)*(1/(2*ε)) := mul_le_mul_of_nonneg_left (coefficient_bound ε h s hε hh hb) (by positivity)
    _ = _ := by field_simp; norm_num

def imaginaryOperator : Hilbert →L[ℂ] Hilbert :=
  multiplier (fun s => ((ratio ε h s*(coefficient ε h s).im:ℝ):ℂ))
    (Complex.continuous_ofReal.comp ((ratio_continuous ε h hε hb hh).mul
      (Complex.continuous_im.comp (KFCausalImaginaryShearCoefficient.coefficient_smooth ε h hε hb).continuous))).measurable
    (1/8) (by norm_num) (imaginary_bound ε h hε hb hh)

theorem imaginaryOperator_coe (f : Hilbert) : imaginaryOperator ε h hε hb hh f =ᵐ[volume]
    fun x => ((ratio ε h x.1*(coefficient ε h x.1).im:ℝ):ℂ)*f x := multiplier_coe _ _ _ _ _ f

theorem coefficient_split (s : ℝ) :
    (value ε h s:ℂ)*(value ε h s:ℂ)*coefficient ε h s =
      (rootValue ε h s:ℂ)*(rootValue ε h s:ℂ)+
        Complex.I*((ratio ε h s*(coefficient ε h s).im:ℝ):ℂ) := by
  have hs := value_square ε h hε hb hh s
  have hr := ratio_identity ε h hε hb hh s
  apply Complex.ext <;>
    simp only [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.I_re,Complex.I_im,mul_zero,zero_mul,
      add_zero,zero_add,one_mul,sub_zero]
  · simpa only [pow_two] using (congrArg (fun x : ℝ => x*(coefficient ε h s).re) hs).trans hr
  · simpa only [pow_two] using congrArg (fun x : ℝ => x*(coefficient ε h s).im) hs

local notation "M" => operator ε h hε hb hh
local notation "C" => coefficientOperator ε h hε hb hh
local notation "W" => root ε hε h hb hh
local notation "Q" => imaginaryOperator ε h hε hb hh

theorem operator_identity (f : Hilbert) : M (M (C f)) = W (W f)+Complex.I • Q f := by
  apply Lp.ext
  filter_upwards [operator_coe ε h hε hb hh (M (C f)),operator_coe ε h hε hb hh (C f),
    coefficientOperator_coe ε h hε hb hh f,root_coe ε hε h hb hh (W f),root_coe ε hε h hb hh f,
    imaginaryOperator_coe ε h hε hb hh f,Lp.coeFn_add (W (W f)) (Complex.I • Q f),
    Lp.coeFn_smul Complex.I (Q f)] with x h0 h1 hc h2 h3 hq ha hs
  rw [h0,h1,hc,ha]
  simp only [Pi.add_apply,hs,Pi.smul_apply,smul_eq_mul,h2,h3,hq]
  calc
    _ = ((value ε h x.1:ℂ)*(value ε h x.1:ℂ)*coefficient ε h x.1)*f x := by ring
    _ = _ := by rw [coefficient_split ε h hε hb hh x.1]; ring

theorem pairing_real (f j : Hilbert) (hg : (f,j) ∈ (shearMomentum h).graph) :
    (inner ℂ (M f) (M (C j))).re = (inner ℂ (W f) (W j)).re := by
  rw [real_symmetric M (value ε h) (operator_coe ε h hε hb hh) f (M (C j)),operator_identity,
    inner_add_right,inner_smul_right,
    ← real_symmetric W (rootValue ε h) (root_coe ε hε h hb hh) f (W j)]
  have hi := real_shear_pairing Q (fun s => ratio ε h s*(coefficient ε h s).im)
    (imaginaryOperator_coe ε h hε hb hh) h hh f j hg
  simp only [Complex.add_re,Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,hi,sub_zero,add_zero]

#print axioms value_continuous
#print axioms value_square
#print axioms value_bound
#print axioms operator_coe
#print axioms operator_norm_sq
#print axioms imaginary_bound
#print axioms imaginaryOperator_coe
#print axioms coefficient_split
#print axioms operator_identity
#print axioms pairing_real
end
end UnifiedTheory.Audit.KFCausalClockSecantMultiplier
