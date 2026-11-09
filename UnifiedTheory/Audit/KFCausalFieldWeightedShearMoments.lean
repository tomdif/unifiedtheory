/- Fourth physical-coordinate moments control the field-square weighted
shear differential. These are sufficient estimates; the next module
derives their hypotheses for the actual shifted Gaussian outputs. -/
import UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds
import UnifiedTheory.Audit.KFCausalPhysicalField

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldWeightedShearMoments
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalRelativeGaussianDifferential (profile profile_shear)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearDifferential (first first_smooth)
open UnifiedTheory.Audit.KFCausalGaussianSecondShearBounds (first_bound)
open UnifiedTheory.Audit.KFCausalGaussianShearSlopeBounds (slopeConstant slopeConstant_nonnegative)
open UnifiedTheory.Audit.KFCausalGaussianFourthMoments (radius_square_memLp)
open UnifiedTheory.Audit.KFCausalShearRadius
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalReconstruction (shearDerivative)

theorem field_square_bound (l : Transverse →L[ℝ] ℝ) (q : Transverse) :
    ‖(l q:ℂ)^2‖ ≤ ‖l‖^2*radius q := by
  have hn : ‖q‖ ≤ Real.sqrt (radius q) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    exact (Real.le_sqrt (abs_nonneg _) (radius_positive q).le).mpr
      (by simpa only [sq_abs] using coordinate_square_le q i)
  have hl := (l.le_opNorm q).trans (mul_le_mul_of_nonneg_left hn (norm_nonneg l))
  have hs := pow_le_pow_left₀ (norm_nonneg (l q)) hl 2
  simpa only [norm_pow,Complex.norm_real,mul_pow,Real.sq_sqrt (radius_positive q).le] using hs

theorem weighted_first_memLp (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s, ‖r s‖ ≤ M) (α β : ℝ) (b : Fin 5 → ℂ)
    (hp : MemLp (profile A r α β b) 2 volume)
    (h4 : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^4*profile A r α β b x) 2 volume)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l x.2:ℂ)^2*first A r α β b x) 2 volume := by
  let C := ‖l‖^2*(slopeConstant M α β b+1)
  have hs := slopeConstant_nonnegative M α β hM b
  have hC : 0 ≤ C := mul_nonneg (sq_nonneg _) (by linarith)
  have hc : Continuous (fun x : Configuration => (l x.2:ℂ)^2*first A r α β b x) :=
    ((Complex.continuous_ofReal.comp (l.continuous.comp continuous_snd)).pow 2).mul
      (first_smooth A r hA hr α β b).continuous
  apply ((radius_square_memLp _ hp h4).const_mul (C:ℂ)).of_le hc.aestronglyMeasurable
  filter_upwards [] with x
  have h := mul_le_mul (field_square_bound l x.2) (first_bound A r M hM hb α β b x)
    (norm_nonneg _) (mul_nonneg (sq_nonneg _) (radius_positive x.2).le)
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hC,
    abs_of_nonneg (sq_nonneg (radius x.2))]
  convert h using 1
  dsimp only [C]
  ring

theorem weighted_shear_memLp (A r : ℝ → ℂ) (hA : ContDiff ℝ 1 A) (hr : ContDiff ℝ 1 r)
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ s, ‖r s‖ ≤ M) (α β : ℝ) (b : Fin 5 → ℂ)
    (hp : MemLp (profile A r α β b) 2 volume)
    (h4 : ∀ i : Fin 5, MemLp (fun x => (x.2 i:ℂ)^4*profile A r α β b x) 2 volume)
    (l : Transverse →L[ℝ] ℝ) :
    MemLp (fun x : Configuration => (l x.2:ℂ)^2*shearDerivative (profile A r α β b) x) 2 volume := by
  have he : shearDerivative (profile A r α β b) = first A r α β b := by
    funext x
    rw [profile_shear A r hA hr α β b x]
    simp only [first,add_mul,one_mul]
  rw [he]
  exact weighted_first_memLp A r hA hr M hM hb α β b hp h4 l

#print axioms field_square_bound
#print axioms weighted_first_memLp
#print axioms weighted_shear_memLp
end
end UnifiedTheory.Audit.KFCausalFieldWeightedShearMoments
