/- Position moments and translated overlaps of the actual five-dimensional
Gaussian. These estimates identify the initial transverse phase-space limit. -/
import UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
import UnifiedTheory.Audit.KFCausalLpPhaseTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorShearBounds (physicalGaussian)
open UnifiedTheory.Audit.KFCausalPhysicalGaussianMoments
open UnifiedTheory.Audit.KFCausalPhysicalGaussianNormalization
open UnifiedTheory.Audit.KFCausalPhysicalGaussianGradientBound
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial

def dot (v x : Transverse) : ℝ := ∑ i : Fin 5, v i*x i
def directionSize (v : Transverse) : ℝ := ∑ i : Fin 5, (v i)^2

theorem dot_continuous (v : Transverse) : Continuous (dot v) := by unfold dot; fun_prop

theorem coordinate_point_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α)
    (i : Fin 5) (x : Transverse) :
    (x i)^2*‖physicalGaussian α β x‖^2 ≤ β⁻¹*‖physicalGaussian (α/2) (β/2) x‖^2 := by
  have hw : β ≤ widths α β i := by fin_cases i <;> simp [widths,hβα]
  have ha := coordinate_absorption α β hα hβ i x
  have hb := mul_le_mul_of_nonneg_right hw (mul_nonneg (sq_nonneg (x i)) (sq_nonneg ‖physicalGaussian α β x‖))
  have hc : β*((x i)^2*‖physicalGaussian α β x‖^2) ≤ ‖physicalGaussian (α/2) (β/2) x‖^2 := by
    nlinarith only [ha,hb]
  have hd := mul_le_mul_of_nonneg_left hc (inv_nonneg.mpr hβ.le)
  simpa only [← mul_assoc,inv_mul_cancel₀ hβ.ne',one_mul] using hd

theorem dot_point_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α)
    (v x : Transverse) :
    ‖(dot v x:ℂ)*physicalGaussian α β x‖^2 ≤
      (5*β⁻¹*directionSize v)*‖physicalGaussian (α/2) (β/2) x‖^2 := by
  have hs : (dot v x)^2 ≤ 5*∑ i : Fin 5, (v i*x i)^2 := by
    simpa only [dot,Finset.card_univ,Fintype.card_fin,Nat.cast_ofNat] using
      (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i => v i*x i))
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  calc
    _ ≤ (5*∑ i : Fin 5, (v i*x i)^2)*‖physicalGaussian α β x‖^2 :=
      mul_le_mul_of_nonneg_right hs (sq_nonneg _)
    _ = 5*∑ i : Fin 5, (v i)^2*((x i)^2*‖physicalGaussian α β x‖^2) := by
      simp only [mul_pow,Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ 5*∑ i : Fin 5, (v i)^2*(β⁻¹*‖physicalGaussian (α/2) (β/2) x‖^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_left (coordinate_point_bound α β hα hβ hβα i x) (sq_nonneg _))) (by norm_num)
    _ = _ := by rw [← Finset.sum_mul]; unfold directionSize; ring

theorem dot_gaussian_memLp (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (v : Transverse) :
    MemLp (fun x : Transverse => (dot v x:ℂ)*physicalGaussian α β x) 2 volume := by
  have hm := memLp_finset_sum (s := (Finset.univ : Finset (Fin 5)))
    (fun i _ => (physicalGaussian_coordinate_memLp α β hα hβ i).const_mul (v i:ℂ))
  convert hm using 1
  funext x
  simp only [dot,Complex.ofReal_sum,Complex.ofReal_mul,Finset.sum_mul,mul_assoc]

theorem dot_mass_bound (α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hβα : β ≤ α) (v : Transverse) :
    (∫ x : Transverse, ‖(dot v x:ℂ)*physicalGaussian α β x‖^2) ≤
      (40*β⁻¹*directionSize v)*gaussianMass α β := by
  have hm := dot_gaussian_memLp α β hα hβ v
  have hh := physicalGaussian_memLp (α/2) (β/2) (by positivity) (by positivity)
  have hc : 0 ≤ 5*β⁻¹*directionSize v := by unfold directionSize; positivity
  calc
    _ ≤ ∫ x : Transverse, (5*β⁻¹*directionSize v)*‖physicalGaussian (α/2) (β/2) x‖^2 :=
      integral_mono ((memLp_two_iff_integrable_sq_norm hm.1).mp hm)
        (((memLp_two_iff_integrable_sq_norm hh.1).mp hh).const_mul _)
        (dot_point_bound α β hα hβ hβα v)
    _ = (5*β⁻¹*directionSize v)*gaussianMass (α/2) (β/2) := by
      rw [integral_const_mul,physicalGaussian_mass _ _ (by positivity)]
    _ ≤ (5*β⁻¹*directionSize v)*(8*gaussianMass α β) :=
      mul_le_mul_of_nonneg_left (gaussianMass_half_bound α β hα hβ) hc
    _ = _ := by ring

theorem ground_dot_mass_bound (hbar : ℝ) (hh : hbar ≠ 0) (v : Transverse) :
    (∫ x : Transverse, ‖(dot v x:ℂ)*physicalGaussian (groundWidth hbar) (neutralWidth hbar) x‖^2) ≤
      (2560*|hbar| *directionSize v)*gaussianMass (groundWidth hbar) (neutralWidth hbar) := by
  have hw : neutralWidth hbar ≤ groundWidth hbar := by
    have hp := groundWidth_positive hbar hh
    dsimp only [neutralWidth]
    linarith
  have he : 40*(neutralWidth hbar)⁻¹ = 2560*|hbar| := by
    unfold neutralWidth groundWidth
    field_simp
    ring
  exact (dot_mass_bound _ _ (groundWidth_positive hbar hh) (neutralWidth_positive hbar hh) hw v).trans_eq
    (congrArg (fun c : ℝ => (c*directionSize v)*gaussianMass (groundWidth hbar) (neutralWidth hbar)) he)

theorem physicalGaussian_real (α β : ℝ) (x : Transverse) :
    physicalGaussian α β x = (Real.exp (-quadraticSize α β x):ℂ) := by
  rw [Complex.ofReal_exp]
  unfold physicalGaussian quadraticSize widths
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,add_zero]
  push_cast
  congr 1
  ring

theorem gaussian_overlap_point (α β : ℝ) (v x : Transverse) :
    starRingEnd ℂ (physicalGaussian α β x)*physicalGaussian α β (x+v) =
      (Real.exp (-quadraticSize α β v/2):ℂ)*(‖physicalGaussian α β (x+(1/2:ℝ) • v)‖^2:ℝ) := by
  have h : -quadraticSize α β x+-quadraticSize α β (x+v) =
      -quadraticSize α β v/2+(-2*quadraticSize α β (x+(1/2:ℝ) • v)) := by
    simp only [quadraticSize,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero,
      Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring
  calc
    _ = ((Real.exp (-quadraticSize α β x)*Real.exp (-quadraticSize α β (x+v)):ℝ):ℂ) := by
      rw [physicalGaussian_real,physicalGaussian_real,Complex.conj_ofReal,Complex.ofReal_mul]
    _ = ((Real.exp (-quadraticSize α β v/2)*Real.exp (-2*quadraticSize α β (x+(1/2:ℝ) • v)):ℝ):ℂ) := by
      rw [← Real.exp_add,← Real.exp_add,h]
    _ = _ := by rw [Complex.ofReal_mul,norm_square_exp]

theorem gaussian_overlap (α β : ℝ) (hα : 0 < α) (v : Transverse) :
    (∫ x : Transverse, starRingEnd ℂ (physicalGaussian α β x)*physicalGaussian α β (x+v)) =
      (Real.exp (-quadraticSize α β v/2)*gaussianMass α β:ℝ) := by
  simp_rw [gaussian_overlap_point]
  rw [integral_const_mul,integral_complex_ofReal,
    integral_add_right_eq_self (fun x : Transverse => ‖physicalGaussian α β x‖^2),
    physicalGaussian_mass α β hα,Complex.ofReal_mul]

#print axioms dot_continuous
#print axioms coordinate_point_bound
#print axioms dot_point_bound
#print axioms dot_gaussian_memLp
#print axioms dot_mass_bound
#print axioms ground_dot_mass_bound
#print axioms physicalGaussian_real
#print axioms gaussian_overlap_point
#print axioms gaussian_overlap

end
end UnifiedTheory.Audit.KFCausalPhysicalGaussianConcentration
