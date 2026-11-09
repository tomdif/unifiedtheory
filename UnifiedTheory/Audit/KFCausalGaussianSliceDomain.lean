/- Exact L2 criterion for a complex Gaussian and its application to the
actual dilated gravity-coordinate Gaussian. Real clock slices are L2;
the explicit complex continuation has non-L2 slices arbitrarily near
the real axis, even with any nonzero scalar clock prefactor. This is
not a necessity theorem for the longitudinal spectral energy domain. -/
import UnifiedTheory.Audit.KFCausalComplexPhaseWinding
import UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
import UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalGaussianSliceDomain
noncomputable section
open MeasureTheory Set
open UnifiedTheory.Audit.KFCausalComplexClockChart
open UnifiedTheory.Audit.KFCausalComplexClockWeights
open UnifiedTheory.Audit.KFCausalComplexPhaseWinding
open UnifiedTheory.Audit.KFCausalFieldCoefficientTrials
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph

def gaussian (b : ℂ) (x : ℝ) : ℂ := Complex.exp (-b * (x:ℂ)^2)

theorem gaussian_continuous (b : ℂ) : Continuous (gaussian b) := by
  unfold gaussian
  fun_prop

theorem gaussian_norm_square (b : ℂ) (x : ℝ) :
    ‖gaussian b x‖^2 = Real.exp (-(2*b.re)*x^2) := by
  rw [gaussian, norm_cexp_neg_mul_sq, ← Real.exp_nat_mul]
  congr 1
  norm_num
  ring

theorem gaussian_memLp_iff (b : ℂ) : MemLp (gaussian b) 2 volume ↔ 0 < b.re := by
  rw [memLp_two_iff_integrable_sq_norm (gaussian_continuous b).aestronglyMeasurable]
  simp_rw [gaussian_norm_square]
  rw [integrable_exp_neg_mul_sq_iff]
  constructor <;> intro h <;> linarith

theorem scalar_gaussian_memLp_iff (c b : ℂ) (hc : c ≠ 0) :
    MemLp (fun x : ℝ => c * gaussian b x) 2 volume ↔ 0 < b.re := by
  constructor
  · intro h
    apply (gaussian_memLp_iff b).mp
    simpa only [← mul_assoc, inv_mul_cancel₀ hc, one_mul] using h.const_mul c⁻¹
  · intro h
    exact ((gaussian_memLp_iff b).mpr h).const_mul c

def dilationGaussian (ε α : ℝ) (q : ℂ) : ℝ → ℂ :=
  gaussian ((α:ℂ) * fieldCoefficient ε 2 q)

theorem fieldCoefficient_real_scale (ε : ℝ) (hε : 0 < ε) (q : ℝ) :
    fieldCoefficient ε 2 (q:ℂ) =
      ((scale (phase ε ((chartIso ε hε).symm q)))^2:ℝ) := by
  rw [fieldCoefficient_real ε 2 hε]
  apply congrArg Complex.ofReal
  rw [scale, ← Real.exp_nat_mul]
  congr 1
  ring

theorem dilationGaussian_real (ε α : ℝ) (hε : 0 < ε) (q x : ℝ) :
    dilationGaussian ε α (q:ℂ) x =
      gaussian (α:ℂ) (scale (phase ε ((chartIso ε hε).symm q)) * x) := by
  rw [dilationGaussian, fieldCoefficient_real_scale ε hε q]
  unfold gaussian
  push_cast
  congr 1
  ring

theorem dilationGaussian_inverse_coordinate (ε α : ℝ) (hε : 0 < ε)
    (q : ℝ) (x : Transverse) :
    dilationGaussian ε α (q:ℂ) (x 0) =
      gaussian (α:ℂ) (((coordinateHomeomorph ε hε).symm (q,x)).2 0) := by
  rw [dilationGaussian_real ε α hε, coordinateHomeomorph_symm_apply]
  rfl

theorem dilationGaussian_real_memLp (ε α : ℝ) (hε : 0 < ε) (hα : 0 < α) (q : ℝ) :
    MemLp (dilationGaussian ε α (q:ℂ)) 2 volume := by
  apply (gaussian_memLp_iff _).mpr
  rw [fieldCoefficient_real ε 2 hε]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_pos hα (Real.exp_pos _)

theorem dilationGaussian_not_memLp (ε α : ℝ) (hα : 0 < α) (q : ℂ)
    (hq : (fieldCoefficient ε 2 q).re ≤ 0) (c : ℂ) (hc : c ≠ 0) :
    ¬ MemLp (fun x : ℝ => c * dilationGaussian ε α q x) 2 volume := by
  rw [dilationGaussian, scalar_gaussian_memLp_iff c _ hc]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos hα.le hq)

theorem exists_nonL2_above (ε α δ : ℝ) (hε : 0 < ε) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ q : ℂ, q ∈ targetStrip ε ∧ 0 < q.im ∧ q.im < δ ∧
      ∀ c : ℂ, c ≠ 0 → ¬ MemLp (fun x : ℝ => c * dilationGaussian ε α q x) 2 volume := by
  obtain ⟨q,hq,hp,hb,hn⟩ := exists_negative_coefficient_above ε δ hε hδ
  exact ⟨q,hq,hp,hb,fun c hc => dilationGaussian_not_memLp ε α hα q hn.le c hc⟩

theorem exists_nonL2_below (ε α δ : ℝ) (hε : 0 < ε) (hα : 0 < α) (hδ : 0 < δ) :
    ∃ q : ℂ, q ∈ targetStrip ε ∧ -δ < q.im ∧ q.im < 0 ∧
      ∀ c : ℂ, c ≠ 0 → ¬ MemLp (fun x : ℝ => c * dilationGaussian ε α q x) 2 volume := by
  obtain ⟨q,hq,hb,hn,hr⟩ := exists_negative_coefficient_below ε δ hε hδ
  exact ⟨q,hq,hb,hn,fun c hc => dilationGaussian_not_memLp ε α hα q hr.le c hc⟩

#print axioms gaussian_continuous
#print axioms gaussian_norm_square
#print axioms gaussian_memLp_iff
#print axioms scalar_gaussian_memLp_iff
#print axioms fieldCoefficient_real_scale
#print axioms dilationGaussian_real
#print axioms dilationGaussian_inverse_coordinate
#print axioms dilationGaussian_real_memLp
#print axioms dilationGaussian_not_memLp
#print axioms exists_nonL2_above
#print axioms exists_nonL2_below

end
end UnifiedTheory.Audit.KFCausalGaussianSliceDomain
