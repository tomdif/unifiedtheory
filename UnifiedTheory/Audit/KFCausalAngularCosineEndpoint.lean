/- The literal cosine-circle integral is transported to the actual
singular Gamma endpoint kernel, with its full Jacobian and normalization. -/
import UnifiedTheory.Audit.KFCausalAngularGammaMomentBounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Tactic

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalAngularCosineEndpoint
noncomputable section
open MeasureTheory Set
open KFCausalAngularGammaMomentBounds

theorem cosine_integral (f : ℝ → ℝ) (hf : Continuous f) :
    (∫ theta in 0..(2*Real.pi), f (Real.cos theta)) =
      2*(∫ x in (-1:ℝ)..1, f x*(Real.sqrt (1-x^2))⁻¹) := by
  have hi : ∀ a b : ℝ, IntervalIntegrable (fun theta => f (Real.cos theta)) volume a b :=
    fun a b => (hf.comp Real.continuous_cos).intervalIntegrable a b
  have hr := intervalIntegral.integral_comp_sub_left
    (a := (0:ℝ)) (b := Real.pi) (fun theta => f (Real.cos theta)) (2*Real.pi)
  have he : (∫ theta in Real.pi..(2*Real.pi), f (Real.cos theta)) =
      ∫ theta in 0..Real.pi, f (Real.cos theta) := by
    simpa only [show 2*Real.pi-Real.pi=Real.pi by ring, sub_zero,
      Real.cos_two_pi_sub] using hr.symm
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi 0 Real.pi)
    (hi Real.pi (2*Real.pi)),he]
  have ha := Polynomial.Chebyshev.integral_measureT_eq_integral_cos_of_continuous
    hf.continuousOn
  rw [← ha,Polynomial.Chebyshev.integral_measureT]
  simp only [Real.sqrt_inv]
  ring

private theorem sqrt_jacobian (z u : ℝ) (hz : 0<z) (hu : u∈Icc 0 (2*z)) :
    Real.sqrt (1-(u/z-1)^2) =
      Real.sqrt (2*z)*Real.sqrt u*Real.sqrt (1-u/(2*z))/z := by
  have hc : 0≤1-u/(2*z) := by
    have := (div_le_one (by positivity : 0<2*z)).mpr hu.2
    linarith
  have he : 1-(u/z-1)^2=(2*z)*(u*(1-u/(2*z)))/z^2 := by field_simp; ring
  rw [he,Real.sqrt_div (mul_nonneg (by positivity) (mul_nonneg hu.1 hc)),
    Real.sqrt_mul (by positivity),
    Real.sqrt_mul hu.1,Real.sqrt_sq_eq_abs,abs_of_pos hz]
  ring

theorem kernel_coordinate (z u : ℝ) (hz : 0<z) (hu : u∈Icc 0 (2*z)) :
    z⁻¹*(Real.exp (-z*(u/z-1))*(Real.sqrt (1-(u/z-1)^2))⁻¹) =
      (Real.exp z/Real.sqrt (2*z))*kernel 0 z u := by
  have hc : 0≤1-u/(2*z) := by
    have := (div_le_one (by positivity : 0<2*z)).mpr hu.2
    linarith
  have he : -z*(u/z-1)=z+(-u) := by field_simp; ring
  rw [sqrt_jacobian z u hz hu,he,Real.exp_add]
  simp only [kernel,density,correction,Nat.cast_zero,zero_sub,
    Real.rpow_neg hu.1,Real.rpow_neg hc,← Real.sqrt_eq_rpow]
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  field_simp

theorem endpoint_integrable (z : ℝ) (hz : 0<z) (g : ℝ→ℝ) (hg : Continuous g) :
    IntervalIntegrable (fun u => kernel 0 z u*g u) volume 0 (2*z) := by
  exact (kernel_integrable 0 z hz).mul_continuousOn hg.continuousOn

theorem integral_endpoint (z : ℝ) (hz : 0<z) (g : ℝ→ℝ) (hg : Continuous g) :
    (∫ theta in 0..(2*Real.pi),
      Real.exp (-z*Real.cos theta)*g (z*(1+Real.cos theta))) =
      (2*Real.exp z/Real.sqrt (2*z))*(∫ u in 0..(2*z), kernel 0 z u*g u) := by
  let f : ℝ→ℝ := fun x => Real.exp (-z*x)*g (z*(1+x))
  let h : ℝ→ℝ := fun x => f x*(Real.sqrt (1-x^2))⁻¹
  have hf : Continuous f := by dsimp [f]; fun_prop
  have ha := intervalIntegral.integral_comp_div_sub
    (a := (0:ℝ)) (b := 2*z) h hz.ne' 1
  have hu : 2*z/z-1=(1:ℝ) := by field_simp; ring
  simp only [zero_div,zero_sub,hu,smul_eq_mul] at ha
  have hb : (∫ x in (-1:ℝ)..1, h x)=z⁻¹*(∫ u in 0..(2*z), h (u/z-1)) := by
    rw [ha]
    simp [hz.ne']
  change (∫ theta in 0..(2*Real.pi), f (Real.cos theta)) = _
  rw [cosine_integral f hf]
  change 2*(∫ x in (-1:ℝ)..1, h x)=_
  rw [hb,← intervalIntegral.integral_const_mul]
  calc
    2*(∫ u in 0..(2*z), z⁻¹*h (u/z-1)) =
        2*(∫ u in 0..(2*z), (Real.exp z/Real.sqrt (2*z))*(kernel 0 z u*g u)) := by
      congr 1
      apply intervalIntegral.integral_congr
      intro u hu'
      have hu' : u∈Icc 0 (2*z) := by
        simpa only [uIcc_of_le (by positivity : (0:ℝ)≤2*z)] using hu'
      have he : z*(1+(u/z-1))=u := by field_simp; ring
      dsimp [h,f]
      rw [he]
      have hk := kernel_coordinate z u hz hu'
      calc
        _ = (z⁻¹*(Real.exp (-z*(u/z-1))*(Real.sqrt (1-(u/z-1)^2))⁻¹))*g u := by ring
        _ = _ := by rw [hk]; ring
    _ = _ := by rw [intervalIntegral.integral_const_mul]; ring

#print axioms cosine_integral
#print axioms kernel_coordinate
#print axioms endpoint_integrable
#print axioms integral_endpoint
end
end UnifiedTheory.Audit.KFCausalAngularCosineEndpoint
