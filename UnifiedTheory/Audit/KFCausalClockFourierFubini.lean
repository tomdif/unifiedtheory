/- For continuous jointly L1 functions, the full six-dimensional Fourier
integral is the transverse Fourier integral of the clock Fourier integral.
No product factorization of the input state is assumed. -/
import UnifiedTheory.Audit.KFCausalProductFourierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFourierFubini
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalProductFourierEnergy (phase_split)

def clockFourier (f : ℝ × TailSpace → ℂ) (w : ℝ × TailSpace) : ℂ :=
  (𝓕 (fun q : ℝ => f (q,w.2))) w.1

theorem clockFourier_aestronglyMeasurable (f : ℝ × TailSpace → ℂ) (hc : Continuous f) :
    AEStronglyMeasurable (clockFourier f) volume := by
  have hcont : Continuous (fun u : (ℝ × TailSpace) × ℝ =>
      (Real.fourierChar (-(u.2*u.1.1)):ℂ)*f (u.2,u.1.2)) := by
    fun_prop
  have hm : AEStronglyMeasurable (fun u : (ℝ × TailSpace) × ℝ =>
      (Real.fourierChar (-(u.2*u.1.1)):ℂ)*f (u.2,u.1.2))
      ((volume : Measure (ℝ × TailSpace)).prod (volume : Measure ℝ)) := hcont.aestronglyMeasurable
  convert hm.integral_prod_right' using 1
  funext w
  simp only [clockFourier,Real.fourier_eq,Circle.smul_def,smul_eq_mul,
    RCLike.inner_apply,conj_trivial,mul_comm]

theorem clock_kernel_integrable (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (k : ℝ) :
    Integrable (fun z : ℝ × TailSpace => (Real.fourierChar (-(z.1*k)):ℂ)*f z) := by
  apply hf.norm.mono' (show Continuous (fun z : ℝ × TailSpace =>
    (Real.fourierChar (-(z.1*k)):ℂ)*f z) by fun_prop).aestronglyMeasurable
  filter_upwards [] with z
  simp only [norm_mul,Circle.norm_coe,one_mul,le_refl]

theorem clockFourier_slice_integrable (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (k : ℝ) : Integrable (fun y => clockFourier f (k,y)) := by
  have hi := (clock_kernel_integrable f hc hf k).integral_prod_right
  convert hi using 1
  funext y
  simp only [clockFourier,Real.fourier_eq,Circle.smul_def,smul_eq_mul,
    RCLike.inner_apply,conj_trivial,mul_comm]

theorem fourier_iterated (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (k : Space) :
    (𝓕 (f ∘ euclideanSplit)) k = (𝓕 (fun y => clockFourier f (k 0,y))) (tail k) := by
  let H : ℝ × TailSpace → ℂ := fun z =>
    (Real.fourierChar (-(z.1*k 0)):ℂ)*(Real.fourierChar (-inner ℝ z.2 (tail k)):ℂ)*f z
  have hH : Integrable H := by
    apply hf.norm.mono' (show Continuous H by dsimp only [H]; fun_prop).aestronglyMeasurable
    filter_upwards [] with z
    simp only [H,norm_mul,Circle.norm_coe,one_mul,le_refl]
  rw [Real.fourier_eq]
  calc
    _ = ∫ x : Space, H (euclideanSplit x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [Circle.smul_def,smul_eq_mul,phase_split,Function.comp_apply,euclideanSplit_apply,H]
    _ = ∫ z : ℝ × TailSpace, H z := euclideanSplit_preserves_volume.integral_comp' H
    _ = ∫ y : TailSpace, ∫ q : ℝ, H (q,y) := integral_prod_symm H hH
    _ = ∫ y : TailSpace, (Real.fourierChar (-inner ℝ y (tail k)):ℂ)*clockFourier f (k 0,y) := by
      apply integral_congr_ae
      filter_upwards [] with y
      simp only [clockFourier,Real.fourier_eq,Circle.smul_def,smul_eq_mul,
        RCLike.inner_apply,conj_trivial,H]
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with q
      ring
    _ = _ := by simp only [Real.fourier_eq,Circle.smul_def,smul_eq_mul]

def fullFourier (f : ℝ × TailSpace → ℂ) (w : ℝ × TailSpace) : ℂ :=
  (𝓕 (f ∘ euclideanSplit)) (euclideanSplit.symm w)

theorem fullFourier_slice (f : ℝ × TailSpace → ℂ) (hc : Continuous f)
    (hf : Integrable f) (k : ℝ) (y : TailSpace) :
    fullFourier f (k,y) = (𝓕 (fun z => clockFourier f (k,z))) y := by
  have h := euclideanSplit_symm_apply k y
  rw [Prod.mk.injEq] at h
  rw [fullFourier,fourier_iterated f hc hf,h.1,h.2]

theorem fullFourier_measurable (f : ℝ × TailSpace → ℂ) (hf : Integrable f) :
    Measurable (fullFourier f) := by
  have hi := euclideanSplit_preserves_volume.integrable_comp_of_integrable hf
  have hc : Continuous (𝓕 (f ∘ euclideanSplit)) := VectorFourier.fourierIntegral_continuous
    (L := innerₗ Space) Real.continuous_fourierChar continuous_inner hi
  exact hc.measurable.comp euclideanSplit.symm.measurable

#print axioms clockFourier_aestronglyMeasurable
#print axioms clock_kernel_integrable
#print axioms clockFourier_slice_integrable
#print axioms fourier_iterated
#print axioms fullFourier_slice
#print axioms fullFourier_measurable

end
end UnifiedTheory.Audit.KFCausalClockFourierFubini
