/- Explicit coercivity of the actual low-degree classical charge profiles.
The constant is derived by a four-point arithmetic-geometric estimate. -/
import UnifiedTheory.Audit.KFCausalClassicalQuarterProduct

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalQuarterExponential
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics (second second_continuous)
open UnifiedTheory.Audit.KFCausalClassicalQuarterProduct

def quarterMean (f : ℝ → ℝ) (θ : ℝ) : ℝ :=
  (f θ+f (θ+Real.pi/2)+f (θ+Real.pi)+f (θ+Real.pi/2+Real.pi))/4

theorem mean_shift (f : ℝ → ℝ) (hp : Function.Periodic f (2*Real.pi)) (d : ℝ) :
    mean (fun θ => f (θ+d)) = mean f := by
  unfold mean
  rw [intervalIntegral.integral_comp_add_right]
  congr 1
  simpa only [zero_add,add_comm (2*Real.pi) d] using hp.intervalIntegral_add_eq d 0

theorem mean_quarterMean (f : ℝ → ℝ) (hf : Continuous f)
    (hp : Function.Periodic f (2*Real.pi)) : mean (quarterMean f) = mean f := by
  have he : quarterMean f = fun θ =>
      (f θ+f (θ+Real.pi/2)+f (θ+Real.pi)+f (θ+(Real.pi/2+Real.pi)))*(1/4:ℝ) := by
    funext θ
    unfold quarterMean
    rw [add_assoc θ]
    ring
  rw [he,mean_mul_const,mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop),mean_add _ _ hf (by fun_prop)]
  rw [mean_shift f hp,mean_shift f hp,mean_shift f hp]
  ring

theorem second_quarter_sum (b : Fin 4 → ℝ) (θ : ℝ) :
    second b θ+second b (θ+Real.pi/2)+second b (θ+Real.pi)+
      second b (θ+Real.pi/2+Real.pi) = 0 := by
  simp only [second,Real.cos_add_pi_div_two,Real.sin_add_pi_div_two,
    Real.cos_add_pi,Real.sin_add_pi]
  ring

theorem four_mean_power (A B C D : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C) (hD : 0 ≤ D) : A*B*C*D ≤ ((A+B+C+D)/4)^4 := by
  have h1 : 4*A*B ≤ (A+B)^2 := by nlinarith [sq_nonneg (A-B)]
  have h2 : 4*C*D ≤ (C+D)^2 := by nlinarith [sq_nonneg (C-D)]
  have h3 := mul_le_mul h1 h2 (by positivity : 0 ≤ 4*C*D) (sq_nonneg (A+B))
  have h4 : 4*(A+B)*(C+D) ≤ (A+B+C+D)^2 := by nlinarith [sq_nonneg ((A+B)-(C+D))]
  have h5 := pow_le_pow_left₀ (by positivity : 0 ≤ 4*(A+B)*(C+D)) h4 2
  nlinarith only [h3,h5]

theorem exponential_product (x y z w α β γ δ : ℝ) (hs : α+β+γ+δ = 0) :
    (x*y*z*w)^2 ≤ ((x^2*Real.exp α+y^2*Real.exp β+z^2*Real.exp γ+w^2*Real.exp δ)/4)^4 := by
  have he : Real.exp α*Real.exp β*Real.exp γ*Real.exp δ = 1 := by
    rw [← Real.exp_add,← Real.exp_add,← Real.exp_add,hs,Real.exp_zero]
  have hp := four_mean_power (x^2*Real.exp α) (y^2*Real.exp β)
    (z^2*Real.exp γ) (w^2*Real.exp δ) (by positivity) (by positivity) (by positivity) (by positivity)
  have hid : (x^2*Real.exp α)*(y^2*Real.exp β)*(z^2*Real.exp γ)*(w^2*Real.exp δ) = (x*y*z*w)^2 := by
    calc
      _ = (x*y*z*w)^2*(Real.exp α*Real.exp β*Real.exp γ*Real.exp δ) := by ring
      _ = _ := by rw [he,mul_one]
  exact hid.symm.le.trans hp

theorem product_bound (c a b θ : ℝ) : |product c a b θ| ≤ size c a b^2 := by
  have hr := rotation_squares a b θ
  have h0 : 0 ≤ size c a b := by unfold size; positivity
  have h1 : |c^2-(a*Real.cos θ+b*Real.sin θ)^2| ≤ size c a b := by
    apply abs_le.mpr
    unfold size
    constructor <;> nlinarith [sq_nonneg c,sq_nonneg (a*Real.cos θ+b*Real.sin θ),sq_nonneg (-a*Real.sin θ+b*Real.cos θ)]
  have h2 : |c^2-(-a*Real.sin θ+b*Real.cos θ)^2| ≤ size c a b := by
    apply abs_le.mpr
    unfold size
    constructor <;> nlinarith [sq_nonneg c,sq_nonneg (a*Real.cos θ+b*Real.sin θ),sq_nonneg (-a*Real.sin θ+b*Real.cos θ)]
  simpa only [product,abs_mul,pow_two] using mul_le_mul h1 h2 (abs_nonneg _) h0

theorem field_square_bound (c a b θ : ℝ) : field c a b θ^2 ≤ 2*size c a b := by
  have hr := rotation_squares a b θ
  unfold field size
  nlinarith [sq_nonneg (c-(a*Real.cos θ+b*Real.sin θ)),sq_nonneg (-a*Real.sin θ+b*Real.cos θ)]

theorem field_fourth_bound (c a b θ : ℝ) : field c a b θ^4 ≤ 4*size c a b^2 := by
  have h := pow_le_pow_left₀ (sq_nonneg (field c a b θ)) (field_square_bound c a b θ) 2
  nlinarith only [h]

theorem cube_control (S A X : ℝ) (hS : 0 ≤ S) (hA : 0 ≤ A)
    (hX : X ≤ S^4) (hY : X ≤ A^4) : X ≤ S^3*A := by
  by_cases h : A ≤ S
  · have hp := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hA h 3) hA
    nlinarith only [hp,hY]
  · have hp := mul_le_mul_of_nonneg_left (le_of_not_ge h) (pow_nonneg hS 3)
    nlinarith only [hp,hX]

def squareDensity (c a b : ℝ) (v : Fin 4 → ℝ) (θ : ℝ) : ℝ :=
  field c a b θ^2*Real.exp (second v θ)

def fourthDensity (c a b : ℝ) (v : Fin 4 → ℝ) (θ : ℝ) : ℝ :=
  field c a b θ^4*Real.exp (second v θ)

theorem density_continuous (c a b : ℝ) (v : Fin 4 → ℝ) :
    Continuous (squareDensity c a b v) ∧ Continuous (fourthDensity c a b v) := by
  unfold squareDensity fourthDensity field second
  constructor <;> fun_prop

theorem density_periodic (c a b : ℝ) (v : Fin 4 → ℝ) :
    Function.Periodic (squareDensity c a b v) (2*Real.pi) ∧
      Function.Periodic (fourthDensity c a b v) (2*Real.pi) := by
  constructor <;> intro θ <;>
    simp only [squareDensity,fourthDensity,field,second,Real.cos_add_two_pi,Real.sin_add_two_pi]

theorem square_point_bound (c a b : ℝ) (v : Fin 4 → ℝ) (θ : ℝ) :
    product c a b θ^2 ≤ size c a b^3*quarterMean (squareDensity c a b v) θ := by
  have hp := exponential_product (field c a b θ) (field c a b (θ+Real.pi/2))
    (field c a b (θ+Real.pi)) (field c a b (θ+Real.pi/2+Real.pi)) _ _ _ _ (second_quarter_sum v θ)
  rw [field_quarter_product] at hp
  have hx := pow_le_pow_left₀ (abs_nonneg (product c a b θ)) (product_bound c a b θ) 2
  rw [sq_abs] at hx
  apply cube_control (size c a b) _ _ (by unfold size; positivity)
    (by positivity) _ hp
  nlinarith only [hx]

theorem fourth_point_bound (c a b : ℝ) (v : Fin 4 → ℝ) (θ : ℝ) :
    product c a b θ^2 ≤ size c a b^2*quarterMean (fourthDensity c a b v) θ := by
  have hp := exponential_product ((field c a b θ)^2) ((field c a b (θ+Real.pi/2))^2)
    ((field c a b (θ+Real.pi))^2) ((field c a b (θ+Real.pi/2+Real.pi))^2)
    _ _ _ _ (second_quarter_sum v θ)
  have he : ((field c a b θ)^2*(field c a b (θ+Real.pi/2))^2*
      (field c a b (θ+Real.pi))^2*(field c a b (θ+Real.pi/2+Real.pi))^2)^2 =
      |product c a b θ|^4 := by
    have ha : |product c a b θ|^4 = (product c a b θ)^4 := by
      rw [pow_abs, abs_of_nonneg (by positivity)]
    rw [ha, ← field_quarter_product]
    ring
  rw [he] at hp
  have hb : |product c a b θ| ≤ quarterMean (fourthDensity c a b v) θ := by
    apply (pow_le_pow_iff_left₀ (abs_nonneg _) (by unfold quarterMean fourthDensity; positivity) (by norm_num : (4:ℕ) ≠ 0)).mp
    convert hp using 1
    unfold quarterMean fourthDensity
    ring
  have h1 := mul_le_mul_of_nonneg_right (product_bound c a b θ) (abs_nonneg (product c a b θ))
  have h2 := mul_le_mul_of_nonneg_left hb (sq_nonneg (size c a b))
  nlinarith only [h1,h2,sq_abs (product c a b θ)]

theorem square_mean_lower (c a b : ℝ) (v : Fin 4 → ℝ) :
    size c a b ≤ 16384*mean (squareDensity c a b v) := by
  have hm := mean_mono (fun θ => product c a b θ^2)
    (fun θ => quarterMean (squareDensity c a b v) θ*size c a b^3)
    (by unfold product; fun_prop) (by have hc := (density_continuous c a b v).1; unfold quarterMean; fun_prop)
    (fun θ => by simpa only [mul_comm] using square_point_bound c a b v θ)
  rw [mean_mul_const,mean_quarterMean _ (density_continuous c a b v).1 (density_periodic c a b v).1] at hm
  have hc := product_mean_lower c a b
  by_cases hs : size c a b = 0
  · rw [hs]
    exact mul_nonneg (by norm_num) (mean_nonnegative _ (fun θ => by unfold squareDensity; positivity))
  have hpos : 0 < size c a b := lt_of_le_of_ne (by unfold size; positivity) (Ne.symm hs)
  apply (mul_le_mul_iff_right₀ (pow_pos hpos 3)).mp
  nlinarith only [hc,hm]

theorem fourth_mean_lower (c a b : ℝ) (v : Fin 4 → ℝ) :
    size c a b^2 ≤ 16384*mean (fourthDensity c a b v) := by
  have hm := mean_mono (fun θ => product c a b θ^2)
    (fun θ => quarterMean (fourthDensity c a b v) θ*size c a b^2)
    (by unfold product; fun_prop) (by have hc := (density_continuous c a b v).2; unfold quarterMean; fun_prop)
    (fun θ => by simpa only [mul_comm] using fourth_point_bound c a b v θ)
  rw [mean_mul_const,mean_quarterMean _ (density_continuous c a b v).2 (density_periodic c a b v).2] at hm
  have hc := product_mean_lower c a b
  by_cases hs : size c a b = 0
  · rw [hs,zero_pow (by norm_num : (2:ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (mean_nonnegative _ (fun θ => by unfold fourthDensity; positivity))
  have hpos : 0 < size c a b := lt_of_le_of_ne (by unfold size; positivity) (Ne.symm hs)
  apply (mul_le_mul_iff_right₀ (pow_pos hpos 2)).mp
  nlinarith only [hc,hm]

theorem square_coercivity (c a b : ℝ) (v : Fin 4 → ℝ) :
    mean (fun θ => field c a b θ^2) ≤ 32768*mean (squareDensity c a b v) := by
  have hu := mean_mono (fun θ => field c a b θ^2) (fun _ => 2*size c a b)
    (by unfold field; fun_prop) continuous_const (field_square_bound c a b)
  rw [mean_const] at hu
  linarith [square_mean_lower c a b v]

theorem fourth_coercivity (c a b : ℝ) (v : Fin 4 → ℝ) :
    mean (fun θ => field c a b θ^4) ≤ 65536*mean (fourthDensity c a b v) := by
  have hu := mean_mono (fun θ => field c a b θ^4) (fun _ => 4*size c a b^2)
    (by unfold field; fun_prop) continuous_const (field_fourth_bound c a b)
  rw [mean_const] at hu
  linarith [fourth_mean_lower c a b v]

#print axioms mean_shift
#print axioms mean_quarterMean
#print axioms second_quarter_sum
#print axioms four_mean_power
#print axioms exponential_product
#print axioms product_bound
#print axioms field_square_bound
#print axioms field_fourth_bound
#print axioms cube_control
#print axioms density_continuous
#print axioms density_periodic
#print axioms square_point_bound
#print axioms fourth_point_bound
#print axioms square_mean_lower
#print axioms fourth_mean_lower
#print axioms square_coercivity
#print axioms fourth_coercivity
end
end UnifiedTheory.Audit.KFCausalClassicalQuarterExponential
