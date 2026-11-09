/- Exact full-period charge averages and exponential lower bounds. The shear
is the actual transverse dilation/shear polynomial from ClassicalChargePhase;
the measure is the same normalized angle measure used by the quantum forms. -/
import UnifiedTheory.Audit.KFCausalClassicalChargePhase
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClassicalChargeMean
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def mean (f : ℝ → ℝ) : ℝ := (2*Real.pi)⁻¹ * ∫ θ in 0..2*Real.pi, f θ

theorem mean_eq_angle (f : ℝ → ℝ) :
    mean f = ∫ θ, f (2*Real.pi*θ) ∂angleMeasure := by
  change _ = ∫ θ in Set.Ioc 0 1, f (2*Real.pi*θ)
  rw [← intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_comp_mul_left f (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simp [mean]

theorem mean_const (a : ℝ) : mean (fun _ => a) = a := by
  simp [mean, mul_assoc, Real.pi_ne_zero]

theorem mean_add (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    mean (fun θ => f θ+g θ) = mean f+mean g := by
  rw [mean, intervalIntegral.integral_add (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  exact mul_add _ _ _

theorem mean_sub (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g) :
    mean (fun θ => f θ-g θ) = mean f-mean g := by
  rw [mean, intervalIntegral.integral_sub (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)]
  exact mul_sub _ _ _

theorem mean_mul_const (f : ℝ → ℝ) (a : ℝ) :
    mean (fun θ => f θ*a) = mean f*a := by
  simp only [mean, intervalIntegral.integral_mul_const]
  ring

theorem mean_mono (f g : ℝ → ℝ) (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ θ, f θ ≤ g θ) : mean f ≤ mean g := by
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (by positivity))
  exact intervalIntegral.integral_mono (by positivity) (hf.intervalIntegrable _ _)
    (hg.intervalIntegrable _ _) hfg

theorem mean_nonnegative (f : ℝ → ℝ) (hf : ∀ θ, 0 ≤ f θ) : 0 ≤ mean f := by
  exact mul_nonneg (by positivity)
    (intervalIntegral.integral_nonneg (by positivity) (fun θ _ => hf θ))

theorem mean_trig :
    mean Real.sin = 0 ∧ mean Real.cos = 0 ∧
    mean (fun θ => Real.sin θ^2) = 1/2 ∧
    mean (fun θ => Real.cos θ^2) = 1/2 ∧
    mean (fun θ => Real.sin θ*Real.cos θ) = 0 := by
  simp [mean, integral_sin, integral_cos, integral_sin_sq, integral_cos_sq,
    integral_sin_mul_cos₁, Real.sin_two_pi, Real.cos_two_pi]
  field_simp

theorem shear_continuous (z : Phase) : Continuous (fun θ => shear (rotate θ z)) := by
  simp_rw [shear_rotate]
  fun_prop

theorem shear_mean_zero (z : Phase) : mean (fun θ => shear (rotate θ z)) = 0 := by
  simp_rw [shear_rotate]
  rw [mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_mul_const]
  rw [mean_sub _ _ (by fun_prop) (by fun_prop), mean_trig.1, mean_trig.2.1,
    mean_trig.2.2.1, mean_trig.2.2.2.1, mean_trig.2.2.2.2]
  ring

theorem affine_square_mean (a b r : ℝ) :
    mean (fun θ => (Real.cos θ*a+Real.sin θ*b+r)^2) = (a^2+b^2)/2+r^2 := by
  have he : (fun θ => (Real.cos θ*a+Real.sin θ*b+r)^2) = fun θ =>
      Real.cos θ^2*a^2+Real.sin θ^2*b^2+(Real.sin θ*Real.cos θ)*(2*a*b)+
      Real.cos θ*(2*a*r)+Real.sin θ*(2*b*r)+r^2 := by funext θ; ring
  rw [he, mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop), mean_add _ _ (by fun_prop) (by fun_prop),
    mean_add _ _ (by fun_prop) (by fun_prop), mean_add _ _ (by fun_prop) (by fun_prop)]
  simp only [mean_mul_const, mean_const]
  rw [mean_trig.1, mean_trig.2.1, mean_trig.2.2.1, mean_trig.2.2.2.1, mean_trig.2.2.2.2]
  ring

def exponentialMean (C : ℝ) (z : Phase) : ℝ :=
  mean (fun θ => Real.exp (shear (rotate θ z)/C))

def tiltedShear (C : ℝ) (z : Phase) : ℝ :=
  mean (fun θ => shear (rotate θ z)/C * Real.exp (shear (rotate θ z)/C))

theorem exponentialMean_ge_one (C : ℝ) (z : Phase) : 1 ≤ exponentialMean C z := by
  have hm := mean_mono (fun θ => shear (rotate θ z)/C+1)
    (fun θ => Real.exp (shear (rotate θ z)/C))
    (((shear_continuous z).div_const C).add continuous_const)
    (Real.continuous_exp.comp ((shear_continuous z).div_const C))
    (fun θ => Real.add_one_le_exp _)
  rw [mean_add _ _ ((shear_continuous z).div_const C) continuous_const,
    mean_const] at hm
  simp only [div_eq_mul_inv, mean_mul_const, shear_mean_zero, zero_mul, zero_add] at hm
  exact hm

theorem tiltedShear_nonnegative (C : ℝ) (z : Phase) : 0 ≤ tiltedShear C z := by
  have hp (x : ℝ) : 0 ≤ x*(Real.exp x-1) := by
    by_cases hx : 0 ≤ x
    · exact mul_nonneg hx (sub_nonneg.mpr (Real.one_le_exp hx))
    · exact mul_nonneg_of_nonpos_of_nonpos (le_of_not_ge hx)
        (sub_nonpos.mpr (Real.exp_le_one_iff.mpr (le_of_not_ge hx)))
  have h := mean_nonnegative (fun θ => shear (rotate θ z)/C *
    (Real.exp (shear (rotate θ z)/C)-1)) (fun θ => hp _)
  have he : (fun θ => shear (rotate θ z)/C * (Real.exp (shear (rotate θ z)/C)-1)) =
      fun θ => shear (rotate θ z)/C * Real.exp (shear (rotate θ z)/C)-shear (rotate θ z)/C := by
    funext θ
    ring
  rw [he, mean_sub
    (fun θ => shear (rotate θ z)/C * Real.exp (shear (rotate θ z)/C))
    (fun θ => shear (rotate θ z)/C)
    (by have hc := shear_continuous z; fun_prop)
    ((shear_continuous z).div_const C)] at h
  simpa only [tiltedShear, div_eq_mul_inv, mean_mul_const, shear_mean_zero, zero_mul, sub_zero] using h

#print axioms mean_eq_angle
#print axioms mean_const
#print axioms mean_add
#print axioms mean_sub
#print axioms mean_mul_const
#print axioms mean_mono
#print axioms mean_nonnegative
#print axioms mean_trig
#print axioms shear_continuous
#print axioms shear_mean_zero
#print axioms affine_square_mean
#print axioms exponentialMean_ge_one
#print axioms tiltedShear_nonnegative

end
end UnifiedTheory.Audit.KFCausalClassicalChargeMean
