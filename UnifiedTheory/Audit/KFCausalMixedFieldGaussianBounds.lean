/- A physical point field at one complex clock argument is controlled by
the sheared Gaussian at another argument. The field and Gaussian shifts
remain distinct; no field/exponential commutation is used. -/
import UnifiedTheory.Audit.KFCausalClockFloorFieldMoments
import UnifiedTheory.Audit.KFCausalMatterOrderedDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalMixedFieldGaussianBounds
noncomputable section
open KFCausalClockFloorShearBounds
open KFCausalClockFloorFieldMoments (packet_half_norm linear_exp_absorption)
open KFCausalTransverseDilationFlow (flow scale)
open KFCausalMatterOrderedDomain (pointField)

def field (z : ℂ) (x : Grouped) : ℂ :=
  (x.2:ℂ)+(3*complexScale z-2)*(mix x.1:ℂ)

theorem field_real (s : ℝ) (x : Grouped) :
    field (s:ℂ) x = (pointField (flow s ![x.1 0,x.1 1,x.1 2,x.1 3,x.2]):ℂ) := by
  have hs : complexScale (s:ℂ) = (scale s:ℂ) := by
    simp [complexScale,scale,Complex.ofReal_exp]
  simp only [field,hs,KFCausalMatterOrderedDomain.pointField_apply,flow,mix]
  push_cast
  ring

theorem field_analytic (x : Grouped) (z : ℂ) :
    AnalyticAt ℂ (fun z => field z x) z := by
  unfold field complexScale
  fun_prop

private theorem add_norm_square (u v : ℂ) :
    ‖u+v‖^2 ≤ 2*(‖u‖^2+‖v‖^2) := by
  have h := (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg u) (norm_nonneg v))).mpr
    (norm_add_le u v)
  nlinarith [sq_nonneg (‖u‖-‖v‖)]

theorem scale_re_square (z : ℂ) : (complexScale z).re^2 ≤ Real.exp z.re := by
  have h := (sq_le_sq₀ (abs_nonneg (complexScale z).re) (norm_nonneg (complexScale z))).mpr
    (Complex.abs_re_le_norm (complexScale z))
  simpa only [sq_abs,complexScale_norm_square] using h

theorem coefficient_square (z v : ℂ) :
    ‖3*complexScale z-2*((complexScale v).re:ℂ)‖^2 ≤
      18*Real.exp z.re+8*Real.exp v.re := by
  have hb := add_norm_square (3*complexScale z) (-2*((complexScale v).re:ℂ))
  have hv := scale_re_square v
  have hn : ‖(-2:ℂ)*((complexScale v).re:ℂ)‖^2 = 4*(complexScale v).re^2 := by
    rw [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
    norm_num
  have hz : ‖(3:ℂ)*complexScale z‖^2 = 9*Real.exp z.re := by
    rw [norm_mul,mul_pow,complexScale_norm_square]
    norm_num
  rw [hn,hz] at hb
  have he : 3*complexScale z+-2*((complexScale v).re:ℂ) =
      3*complexScale z-2*((complexScale v).re:ℂ) := by ring
  rw [he] at hb
  nlinarith

theorem field_square_bound (z v : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hzv : Real.exp z.re ≤ M*Real.exp v.re) (x : Grouped) :
    ‖field z x‖^2 ≤ 2*(x.2+shift v x.1)^2+
      (72*M+32)*Real.exp v.re*squared x.1 := by
  have he : field z x = ((x.2+shift v x.1:ℝ):ℂ)+
      (3*complexScale z-2*((complexScale v).re:ℂ))*(mix x.1:ℂ) := by
    unfold field shift
    push_cast
    ring
  have ha := add_norm_square ((x.2+shift v x.1:ℝ):ℂ)
    ((3*complexScale z-2*((complexScale v).re:ℂ))*(mix x.1:ℂ))
  rw [← he,norm_mul,mul_pow,Complex.norm_real,Complex.norm_real,
    Real.norm_eq_abs,Real.norm_eq_abs,sq_abs,sq_abs] at ha
  have hc := coefficient_square z v
  have hc' : ‖3*complexScale z-2*((complexScale v).re:ℂ)‖^2 ≤
      (18*M+8)*Real.exp v.re := by nlinarith
  have hm := mul_le_mul hc' (mix_square_bound x.1)
    (sq_nonneg (mix x.1)) (by positivity : 0 ≤ (18*M+8)*Real.exp v.re)
  nlinarith

def momentConstant (α β M : ℝ) : ℝ := 2/β+4*(72*M+32)/α

theorem momentConstant_nonnegative (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hM : 0 ≤ M) : 0 ≤ momentConstant α β M := by
  unfold momentConstant
  positivity

theorem field_quadratic_bound (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hM : 0 ≤ M) (z v : ℂ) (hv : |v.im| ≤ Real.pi/3)
    (hzv : Real.exp z.re ≤ M*Real.exp v.re) (x : Grouped) :
    ‖field z x‖^2 ≤ momentConstant α β M*(quadratic α β v x.1 x.2).re := by
  have hl := quadratic_re_lower α β hα.le hβ.le hw v hv x.1 x.2
  have hs := squared_nonnegative x.1
  have hR : (x.2+shift v x.1)^2 ≤ (quadratic α β v x.1 x.2).re/β := by
    apply (le_div_iff₀ hβ).mpr
    nlinarith [mul_nonneg (show 0 ≤ α/4*Real.exp v.re by positivity) hs]
  have hS : Real.exp v.re*squared x.1 ≤ 4*(quadratic α β v x.1 x.2).re/α := by
    apply (le_div_iff₀ hα).mpr
    nlinarith [mul_nonneg hβ.le (sq_nonneg (x.2+shift v x.1))]
  calc
    _ ≤ 2*(x.2+shift v x.1)^2+(72*M+32)*Real.exp v.re*squared x.1 :=
      field_square_bound z v M hM hzv x
    _ ≤ 2*((quadratic α β v x.1 x.2).re/β)+
        (72*M+32)*(4*(quadratic α β v x.1 x.2).re/α) := by
      have h1 := mul_le_mul_of_nonneg_left hR (by norm_num : (0:ℝ) ≤ 2)
      have h2 := mul_le_mul_of_nonneg_left hS (by positivity : 0 ≤ 72*M+32)
      nlinarith
    _ = _ := by unfold momentConstant; ring

theorem quadratic_packet_bound (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hM : 0 ≤ M) (z v : ℂ) (hv : |v.im| ≤ Real.pi/3)
    (hzv : Real.exp z.re ≤ M*Real.exp v.re) (x : Grouped) :
    ‖field z x^2*packet α β v x‖ ≤
      (2*momentConstant α β M)*‖packet (α/2) (β/2) v x‖ := by
  have hf := field_quadratic_bound α β M hα hβ hw hM z v hv hzv x
  have hc := momentConstant_nonnegative α β M hα hβ hM
  have hb := mul_le_mul_of_nonneg_right hf (Real.exp_pos (-(quadratic α β v x.1 x.2).re)).le
  have ha := mul_le_mul_of_nonneg_left
    (linear_exp_absorption (quadratic α β v x.1 x.2).re) hc
  rw [norm_mul,norm_pow,packet_half_norm]
  rw [packet,Complex.norm_exp,Complex.neg_re]
  nlinarith

theorem quartic_packet_bound (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (hM : 0 ≤ M) (z v : ℂ) (hv : |v.im| ≤ Real.pi/3)
    (hzv : Real.exp z.re ≤ M*Real.exp v.re) (x : Grouped) :
    ‖field z x^4*packet α β v x‖ ≤
      (4*momentConstant α β M*momentConstant (α/2) (β/2) M)*
        ‖packet (α/4) (β/4) v x‖ := by
  have h1 := quadratic_packet_bound α β M hα hβ hw hM z v hv hzv x
  have h2 := quadratic_packet_bound (α/2) (β/2) M (by positivity) (by positivity)
    (by linarith) hM z v hv hzv x
  have hc := momentConstant_nonnegative α β M hα hβ hM
  have h := (mul_le_mul_of_nonneg_left h1 (sq_nonneg ‖field z x‖)).trans
    (show ‖field z x‖^2*((2*momentConstant α β M)*‖packet (α/2) (β/2) v x‖) ≤
      (2*momentConstant α β M)*((2*momentConstant (α/2) (β/2) M)*
        ‖packet ((α/2)/2) ((β/2)/2) v x‖) from by
      have hs := mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2*momentConstant α β M)
      simpa only [norm_mul,norm_pow,mul_assoc,mul_left_comm] using hs)
  norm_num only [show (α/2)/2=α/4 by ring,show (β/2)/2=β/4 by ring] at h
  simp only [norm_mul,norm_pow] at h ⊢
  convert h using 1 <;> ring

#print axioms field_real
#print axioms field_analytic
#print axioms scale_re_square
#print axioms coefficient_square
#print axioms field_square_bound
#print axioms momentConstant_nonnegative
#print axioms field_quadratic_bound
#print axioms quadratic_packet_bound
#print axioms quartic_packet_bound
end
end UnifiedTheory.Audit.KFCausalMixedFieldGaussianBounds
