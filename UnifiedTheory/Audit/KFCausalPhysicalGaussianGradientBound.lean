/- Normalization-relative gradient bounds for the actual five-dimensional
Gaussian. The constants are deliberately coarse and independent of Planck's
parameter after multiplication by the physical kinetic coefficient. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
import UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial
import Mathlib.Algebra.Order.Chebyshev

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalPhysicalGaussianDerivative
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

def quadraticSize (α β : ℝ) (x : Transverse) : ℝ := ∑ i : Fin 5, widths α β i*(x i)^2

theorem norm_square_exp (α β : ℝ) (x : Transverse) :
    ‖physicalGaussian α β x‖^2 = Real.exp (-2*quadraticSize α β x) := by
  rw [physicalGaussian_square,← Real.exp_sum]
  congr 1
  simp only [quadraticSize,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem half_norm_square (α β : ℝ) (x : Transverse) :
    ‖physicalGaussian (α/2) (β/2) x‖^2 = Real.exp (-quadraticSize α β x) := by
  rw [norm_square_exp]
  congr 1
  simp only [quadraticSize,widths,Fin.sum_univ_succ,Fin.sum_univ_zero,
    Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  ring

theorem coordinate_absorption (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (i : Fin 5) (x : Transverse) :
    widths α β i*(x i)^2*‖physicalGaussian α β x‖^2 ≤
      ‖physicalGaussian (α/2) (β/2) x‖^2 := by
  have hx : widths α β i*(x i)^2 ≤ quadraticSize α β x :=
    Finset.single_le_sum (fun j _ => mul_nonneg (widths_positive α β hα hβ j).le
      (sq_nonneg _)) (Finset.mem_univ i)
  have he : widths α β i*(x i)^2 ≤ Real.exp (quadraticSize α β x) := by
    linarith only [hx,Real.add_one_le_exp (quadraticSize α β x)]
  rw [norm_square_exp,half_norm_square]
  calc
    _ ≤ Real.exp (quadraticSize α β x)*Real.exp (-2*quadraticSize α β x) :=
      mul_le_mul_of_nonneg_right he (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem gradient_pointwise_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hβα : β ≤ α) (v x : Transverse) :
    ‖gradient α β v x‖^2 ≤
      (20*α*(∑ i : Fin 5, (v i)^2))*‖physicalGaussian (α/2) (β/2) x‖^2 := by
  let f : Fin 5 → ℂ := fun i => (-2*widths α β i*v i:ℝ)*(x i:ℂ)*physicalGaussian α β x
  have hs : ‖∑ i, f i‖^2 ≤ 5*∑ i, ‖f i‖^2 := by
    calc
      _ ≤ (∑ i, ‖f i‖)^2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ _ := by simpa only [Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using
        (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => ‖f i‖))
  have hi (i : Fin 5) : ‖f i‖^2 ≤
      4*α*(v i)^2*‖physicalGaussian (α/2) (β/2) x‖^2 := by
    have hw : widths α β i ≤ α := by fin_cases i <;> simp [widths,hβα]
    have ha := mul_le_mul_of_nonneg_left (coordinate_absorption α β hα hβ i x)
      (show 0 ≤ 4*widths α β i*(v i)^2 by positivity [widths_positive α β hα hβ i])
    have hb := mul_le_mul_of_nonneg_right hw
      (show 0 ≤ 4*(v i)^2*‖physicalGaussian (α/2) (β/2) x‖^2 by positivity)
    have hn : ‖f i‖^2 =
        (4*widths α β i*(v i)^2)*(widths α β i*(x i)^2*‖physicalGaussian α β x‖^2) := by
      simp only [f,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
      ring
    exact hn.le.trans (ha.trans (by nlinarith only [hb]))
  calc
    _ ≤ 5*∑ i, ‖f i‖^2 := hs
    _ ≤ 5*∑ i, 4*α*(v i)^2*‖physicalGaussian (α/2) (β/2) x‖^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hi i)) (by norm_num)
    _ = _ := by rw [← Finset.sum_mul,← Finset.mul_sum]; ring

theorem gradient_mass_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hβα : β ≤ α) (v : Transverse) :
    (∫ x : Transverse, ‖gradient α β v x‖^2) ≤
      (160*α*(∑ i : Fin 5, (v i)^2))*gaussianMass α β := by
  have hm := gradient_memLp α β hα hβ v
  have hh := physicalGaussian_memLp (α/2) (β/2) (by positivity) (by positivity)
  have hc : 0 ≤ 20*α*(∑ i : Fin 5, (v i)^2) := by positivity
  calc
    _ ≤ ∫ x : Transverse, (20*α*(∑ i : Fin 5, (v i)^2))*‖physicalGaussian (α/2) (β/2) x‖^2 :=
      integral_mono ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)
        (((memLp_two_iff_integrable_sq_norm hh.1).mp hh).const_mul _)
        (gradient_pointwise_bound α β hα hβ hβα v)
    _ = (20*α*(∑ i : Fin 5, (v i)^2))*gaussianMass (α/2) (β/2) := by
      rw [integral_const_mul,physicalGaussian_mass _ _ (by positivity)]
    _ ≤ (20*α*(∑ i : Fin 5, (v i)^2))*(8*gaussianMass α β) :=
      mul_le_mul_of_nonneg_left (gaussianMass_half_bound α β hα hβ) hc
    _ = _ := by ring

theorem ground_gradient_mass_bound (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    hbar^2*(∫ x : Transverse, ‖gradient (groundWidth hbar) (neutralWidth hbar) v x‖^2) ≤
      (80*|hbar| *(∑ i : Fin 5, (v i)^2))*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hw : neutralWidth hbar ≤ groundWidth hbar := by
    have hp := groundWidth_positive hbar hh
    dsimp only [neutralWidth]
    linarith
  have hb := mul_le_mul_of_nonneg_left (gradient_mass_bound _ _
    (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) hw v) (sq_nonneg hbar)
  have he : hbar^2*(160*groundWidth hbar) = 80*|hbar| := by
    rw [groundWidth,← sq_abs hbar]
    field_simp
    ring
  calc
    _ ≤ hbar^2*((160*groundWidth hbar*(∑ i : Fin 5, (v i)^2))*
        gaussianMass (groundWidth hbar) (neutralWidth hbar)) := hb
    _ = _ := by rw [← mul_assoc,← mul_assoc,he]

#print axioms norm_square_exp
#print axioms half_norm_square
#print axioms coordinate_absorption
#print axioms gradient_pointwise_bound
#print axioms gradient_mass_bound
#print axioms ground_gradient_mass_bound

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
