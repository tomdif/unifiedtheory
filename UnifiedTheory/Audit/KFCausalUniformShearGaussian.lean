/- A complex shear in a bounded strip has a uniform positive isotropic
Gaussian bound. The neutral shear is retained in the quadratic form.
This supplies an integrable majorant for the interpolation, without
assuming its Hilbert-space differentiability. -/
import UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalUniformShearGaussian
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds
open UnifiedTheory.Audit.KFCausalClockFloorCoherentBounds

def shearBound (M : ℝ) : ℝ := 2*(Real.exp (M/2)+1)
def confinement (α β M : ℝ) : ℝ :=
  min (((α/4)*Real.exp (-M))/(1+4*(shearBound M)^2)) (β/2)

theorem confinement_positive (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β) :
    0 < confinement α β M := by
  unfold confinement
  positivity

theorem scale_bound (M : ℝ) (z : ℂ) (hz : z.re ≤ M) :
    ‖complexScale z‖ ≤ Real.exp (M/2) := by
  rw [complexScale,Complex.norm_exp,Complex.div_ofNat_re]
  exact Real.exp_le_exp.mpr (by linarith)

theorem shear_coefficient_bound (M : ℝ) (z : ℂ) (hz : z.re ≤ M) :
    |2*((complexScale z).re-1)| ≤ shearBound M := by
  have hr : |(complexScale z).re-1| ≤ Real.exp (M/2)+1 := calc
    _ ≤ |(complexScale z).re|+|1| := abs_sub _ _
    _ ≤ ‖complexScale z‖+1 := by simpa using add_le_add_right (Complex.abs_re_le_norm _) 1
    _ ≤ Real.exp (M/2)+1 := by linarith [scale_bound M z hz]
  simpa only [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2),shearBound] using
    mul_le_mul_of_nonneg_left hr (by norm_num : (0:ℝ) ≤ 2)

theorem neutral_square_bound (M : ℝ) (z : ℂ) (hz : z.re ≤ M) (x : Charged) (r : ℝ) :
    r^2 ≤ 2*(r+shift z x)^2+4*(shearBound M)^2*squared x := by
  have hd := (sq_le_sq₀ (abs_nonneg (2*((complexScale z).re-1)))
    (by unfold shearBound; positivity)).mpr (shear_coefficient_bound M z hz)
  rw [sq_abs] at hd
  have hm := mul_le_mul hd (mix_square_bound x) (sq_nonneg (mix x)) (sq_nonneg (shearBound M))
  have hs := sq_nonneg (r+2*(shift z x))
  unfold shift at *
  nlinarith

theorem quadratic_isotropic_lower (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (z : ℂ) (hr : |z.re| ≤ M) (hi : |z.im| ≤ Real.pi/3)
    (x : Charged) (r : ℝ) :
    confinement α β M*(squared x+r^2) ≤ (quadratic α β z x r).re := by
  have hc := (confinement_positive α β M hα hβ).le
  have hc1 : confinement α β M*(1+4*(shearBound M)^2) ≤ (α/4)*Real.exp (-M) :=
    (le_div_iff₀ (by positivity : 0 < 1+4*(shearBound M)^2)).mp (min_le_left _ _)
  have hc2 : 2*confinement α β M ≤ β := by
    have hm : confinement α β M ≤ β/2 := min_le_right _ _
    linarith
  have hn := neutral_square_bound M z (abs_le.mp hr).2 x r
  have hn' := mul_le_mul_of_nonneg_left hn hc
  have ha := mul_le_mul_of_nonneg_right hc1 (squared_nonnegative x)
  have hb := mul_le_mul_of_nonneg_right hc2 (sq_nonneg (r+shift z x))
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (abs_le.mp hr).1)
      (show 0 ≤ α/4 by positivity)) (squared_nonnegative x)
  have hq := quadratic_re_lower α β hα.le hβ.le hw z hi x r
  nlinarith

theorem coherent_isotropic_bound (α β M : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hw : 32*β ≤ α) (b : Fin 5 → ℂ) (z : ℂ)
    (hr : |z.re| ≤ M) (hi : |z.im| ≤ Real.pi/3) (x : Grouped) :
    ‖coherentPacket α β b z x‖ ≤ Real.exp (sourceConstant α β b/2)*
      Real.exp (-(confinement α β M/2)*(squared x.1+x.2^2)) := by
  have hs := source_real_bound α β hα hβ hw b z hi x
  have hq := quadratic_isotropic_lower α β M hα hβ hw z hr hi x.1 x.2
  rw [coherentPacket,packet,norm_mul,Complex.norm_exp,Complex.norm_exp,Complex.neg_re,
    ← Real.exp_add,← Real.exp_add]
  exact Real.exp_le_exp.mpr (by linarith)

#print axioms confinement_positive
#print axioms scale_bound
#print axioms shear_coefficient_bound
#print axioms neutral_square_bound
#print axioms quadratic_isotropic_lower
#print axioms coherent_isotropic_bound
end
end UnifiedTheory.Audit.KFCausalUniformShearGaussian
