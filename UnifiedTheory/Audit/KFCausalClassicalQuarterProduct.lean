/- Explicit quarter-orbit polynomial estimates for the classical matter
candidate. These do not identify a quantum response or change its Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalQuarterProduct
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargeMean

def field (c a b θ : ℝ) : ℝ := c+a*Real.cos θ+b*Real.sin θ

def size (c a b : ℝ) : ℝ := c^2+a^2+b^2

def product (c a b θ : ℝ) : ℝ :=
  (c^2-(a*Real.cos θ+b*Real.sin θ)^2)*(c^2-(-a*Real.sin θ+b*Real.cos θ)^2)

def constantTerm (c a b : ℝ) : ℝ := c^4-c^2*(a^2+b^2)+(a^2+b^2)^2/8

def cosineTerm (a b : ℝ) : ℝ := -(a^4-6*a^2*b^2+b^4)/8

def sineTerm (a b : ℝ) : ℝ := -a*b*(a^2-b^2)/2

theorem field_quarter_product (c a b θ : ℝ) :
    field c a b θ*field c a b (θ+Real.pi/2)*field c a b (θ+Real.pi)*
      field c a b (θ+Real.pi/2+Real.pi) = product c a b θ := by
  simp only [field,Real.cos_add_pi_div_two,Real.sin_add_pi_div_two,
    Real.cos_add_pi,Real.sin_add_pi,product]
  ring

theorem rotation_squares (a b θ : ℝ) :
    (a*Real.cos θ+b*Real.sin θ)^2+(-a*Real.sin θ+b*Real.cos θ)^2 = a^2+b^2 := by
  linear_combination (a^2+b^2)*(Real.sin_sq_add_cos_sq θ)

theorem product_fourier (c a b θ : ℝ) :
    product c a b θ = constantTerm c a b+cosineTerm a b*Real.cos (4*θ)+sineTerm a b*Real.sin (4*θ) := by
  have hp : (a*Real.cos θ+b*Real.sin θ)*(-a*Real.sin θ+b*Real.cos θ) =
      a*b*Real.cos (2*θ)+(b^2-a^2)/2*Real.sin (2*θ) := by
    rw [Real.cos_two_mul,Real.sin_two_mul]
    linear_combination -a*b*(Real.sin_sq_add_cos_sq θ)
  have he : product c a b θ = c^4-c^2*(a^2+b^2)+
      (a*b*Real.cos (2*θ)+(b^2-a^2)/2*Real.sin (2*θ))^2 := by
    rw [← hp,← rotation_squares a b θ]
    unfold product
    ring
  rw [he]
  unfold constantTerm cosineTerm sineTerm
  have hc := Real.cos_sq (2*θ)
  have hs := Real.sin_sq_eq_half_sub (2*θ)
  have ht := Real.sin_two_mul (2*θ)
  rw [show 2*(2*θ) = 4*θ by ring] at hc hs ht
  linear_combination (a*b)^2*hc+((b^2-a^2)/2)^2*hs-(a*b*(b^2-a^2)/2)*ht

theorem mean_comp_four (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) : mean (fun θ => f (4*θ)) = mean f := by
  have he := hp.intervalIntegral_add_zsmul_eq 4 0 (fun x y => hf.intervalIntegrable x y)
  simp only [zero_add,zsmul_eq_mul,Int.cast_ofNat] at he
  unfold mean
  rw [intervalIntegral.integral_comp_mul_left f (by norm_num : (4:ℝ) ≠ 0)]
  simp only [mul_zero]
  rw [he]
  simp only [smul_eq_mul]
  ring

theorem product_square_mean (c a b : ℝ) :
    mean (fun θ => product c a b θ^2) = constantTerm c a b^2+(a^2+b^2)^4/128 := by
  let f := fun θ => (Real.cos θ*cosineTerm a b+Real.sin θ*sineTerm a b+constantTerm c a b)^2
  have he : (fun θ => product c a b θ^2) = fun θ => f (4*θ) := by
    funext θ
    rw [product_fourier]
    dsimp [f]
    ring
  rw [he,mean_comp_four f (by dsimp [f]; fun_prop) (by
    intro θ
    dsimp [f]
    rw [Real.cos_add_two_pi,Real.sin_add_two_pi])]
  change mean (fun θ => (Real.cos θ*cosineTerm a b+Real.sin θ*sineTerm a b+constantTerm c a b)^2) = _
  rw [affine_square_mean]
  unfold cosineTerm sineTerm
  ring

theorem scalar_coercivity (C R : ℝ) (hC : 0 ≤ C) (hR : 0 ≤ R) :
    (C+R)^4 ≤ 16384*((C^2-C*R+R^2/8)^2+R^4/128) := by
  by_cases h : C ≤ 2*R
  · have h1 : (C+R)^2 ≤ (3*R)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 := pow_le_pow_left₀ (sq_nonneg (C+R)) h1 2
    nlinarith [sq_nonneg (C^2-C*R+R^2/8)]
  · have h1 : (C+R)^2 ≤ (2*C)^2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    have h2 := pow_le_pow_left₀ (sq_nonneg (C+R)) h1 2
    have hm : C^2/2 ≤ C^2-C*R+R^2/8 := by nlinarith [mul_nonneg hC (show 0 ≤ C-2*R by linarith),sq_nonneg R]
    have hm2 := pow_le_pow_left₀ (by positivity : 0 ≤ C^2/2) hm 2
    nlinarith [sq_nonneg (R^2)]

theorem product_mean_lower (c a b : ℝ) :
    size c a b^4 ≤ 16384*mean (fun θ => product c a b θ^2) := by
  rw [product_square_mean]
  convert scalar_coercivity (c^2) (a^2+b^2) (sq_nonneg c) (by positivity) using 1 <;>
    simp only [size,constantTerm] <;> ring

#print axioms field_quarter_product
#print axioms rotation_squares
#print axioms product_fourier
#print axioms mean_comp_four
#print axioms product_square_mean
#print axioms scalar_coercivity
#print axioms product_mean_lower
end
end UnifiedTheory.Audit.KFCausalClassicalQuarterProduct
