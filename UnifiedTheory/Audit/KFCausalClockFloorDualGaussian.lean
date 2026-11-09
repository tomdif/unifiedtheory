/- The actual clock-floor trial under the five-dimensional transverse
Fourier coordinates has an everywhere nonzero anisotropic Gaussian
representative. The untouched clock factor and all Fourier constants are
retained; no density or multiplier-core conclusion is assumed. -/
import UnifiedTheory.Audit.KFCausalChargeTransverseSplit
import UnifiedTheory.Audit.KFCausalClockFloorCoherentStates
import UnifiedTheory.Audit.KFCausalReciprocalGaussianFourier

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClockFloorDualGaussian
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates
open KFCausalL2TensorEmbedding
open KFCausalChargeTransverseSplit
open KFCausalPhysicalCircleAction (chargeCoordinates)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalNormalizedChargeFlow (momentumScale momentumScale_ne_zero)
open KFCausalClockFloorInvariantTrial (trialState clockFunction clockFunction_continuous
  clockFunction_memLp clockFunction_ne_zero neutralWidth neutralWidth_positive)
open KFCausalGaussianSliceDomain (gaussian gaussian_continuous gaussian_memLp_iff)

def widths (h : ℝ) : Fin 5 → ℝ :=
  ![groundWidth h*(momentumScale h)^2,groundWidth h*(momentumScale h)^2,
    groundWidth h,groundWidth h,neutralWidth h]

theorem widths_positive (h : ℝ) (hh : h ≠ 0) (i : Fin 5) : 0 < widths h i := by
  have ha := groundWidth_positive h hh
  have hc := sq_pos_of_ne_zero (momentumScale_ne_zero h hh)
  fin_cases i <;> dsimp only [widths]
  · exact mul_pos ha hc
  · exact mul_pos ha hc
  · exact ha
  · exact ha
  · exact neutralWidth_positive h hh

def transverse (h : ℝ) (x : Block 5) : ℂ :=
  ∏ i, gaussian (widths h i:ℂ) (x i)

def clock (ε a h : ℝ) (x : Block 1) : ℂ :=
  ((Real.pi/groundWidth h:ℝ):ℂ)*clockFunction ε a (x 0)

def fourierTransverse (h : ℝ) (x : Block 5) : ℂ :=
  ∏ i, (Real.sqrt (Real.pi/widths h i):ℂ)*
    gaussian (Real.pi^2/widths h i:ℝ) (x i)

def weight (ε a h : ℝ) (x : Joint 5 1) : ℂ :=
  fourierTransverse h (split 5 1 x).1*clock ε a h (split 5 1 x).2

private theorem five_fourier (f : Fin 5 → ℝ → ℂ) (w : Block 5) :
    (𝓕 (fun u : Block 5 => ∏ i, f i (u i))) w = ∏ i, (𝓕 (f i)) (w i) := by
  let A : Fin 5 → ℝ → ℂ := fun i x => (Real.fourierChar (-(x*w i)):ℂ)*f i x
  calc
    _ = ∫ u : Block 5, ∏ i, A i (u i) := by
      rw [Real.fourier_eq]
      apply integral_congr_ae
      filter_upwards [] with u
      simp only [A,PiLp.inner_apply,Fin.sum_univ_succ,RCLike.inner_apply,
        conj_trivial,Fin.sum_univ_zero,add_zero,neg_add,AddChar.map_add_eq_mul,
        Circle.coe_mul,Circle.smul_def,smul_eq_mul,Fin.prod_univ_succ,
        Fin.prod_univ_zero,mul_one]
      simp only [mul_comm (w _) (u _)]
      ring_nf
    _ = ∫ u : Fin 5 → ℝ, ∏ i, A i (u i) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 5)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 5 → ℝ)).symm.measurableEmbedding
        (fun u : Fin 5 → ℝ => ∏ i, A i (u i))
    _ = ∏ i, ∫ x, A i x := integral_fintype_prod_volume_eq_prod A
    _ = _ := by
      apply Finset.prod_congr rfl
      intro i hi
      simp only [A,Real.fourier_eq,RCLike.inner_apply,conj_trivial,
        Circle.smul_def,smul_eq_mul]
      apply integral_congr_ae
      filter_upwards [] with x
      congr 2
      ring_nf

theorem transverse_integrable (h : ℝ) (hh : h ≠ 0) : Integrable (transverse h) := by
  have hi : ∀ i : Fin 5, Integrable (gaussian (widths h i:ℂ)) := by
    intro i
    have he : KFCausalGaussianQuadraticFourier.moment (widths h i) 0 =
        gaussian (widths h i:ℂ) := by
      funext x
      simp [KFCausalGaussianQuadraticFourier.moment]
    rw [← he]
    exact KFCausalGaussianQuadraticFourier.moment_integrable
      (widths h i) (widths_positive h hh i) 0
  exact (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 5)).integrable_comp_of_integrable
    (Integrable.fintype_prod hi)

theorem transverse_memLp (h : ℝ) (hh : h ≠ 0) : MemLp (transverse h) 2 :=
  KFCausalChargeGaussianProducts.block_product_memLp 5 _ (fun _ => gaussian_continuous _)
    (fun i => (gaussian_memLp_iff _).mpr (widths_positive h hh i))

theorem transverse_fourier (h : ℝ) (hh : h ≠ 0) : 𝓕 (transverse h) = fourierTransverse h := by
  funext x
  change (𝓕 (fun u : Block 5 => ∏ i, gaussian (widths h i:ℂ) (u i))) x = _
  rw [five_fourier]
  apply Finset.prod_congr rfl
  intro i hi
  exact KFCausalReciprocalGaussianFourier.scalar_fourier _ (widths_positive h hh i) _

private theorem clock_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) : MemLp (clock ε a h) 2 := by
  have hm := KFCausalChargeGaussianProducts.block_product_memLp 1
    (fun _ => clockFunction ε a) (fun _ => clockFunction_continuous ε a)
    (fun _ => clockFunction_memLp ε a hε ha)
  simpa only [Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one] using
    hm.const_mul ((Real.pi/groundWidth h:ℝ):ℂ)

private theorem charge_factor (ε a h : ℝ) (x : Joint 2 4) :
    transverse h (split 5 1 (repackIsometry x)).1 *
      clock ε a h (split 5 1 (repackIsometry x)).2 =
      KFCausalClockFloorCoherentStates.weight ε a h x := by
  change (∏ i, gaussian (widths h i:ℂ)
      (![x (.inl 0),x (.inl 1),x (.inr 1),x (.inr 2),x (.inr 3)] i)) *
      (((Real.pi/groundWidth h:ℝ):ℂ)*clockFunction ε a (x (.inr 0))) = _
  simp only [widths,Fin.prod_univ_succ,Fin.prod_univ_zero,mul_one,
    Matrix.cons_val_zero,Matrix.cons_val_succ,gaussian,
    KFCausalClockFloorCoherentStates.weight,KFCausalChargeGaussianGeometry.profile,
    KFCausalChargeGaussianGeometry.radius_coordinates]
  simp only [← Complex.exp_add]
  push_cast
  ring_nf

private theorem charge_product (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    chargeCoordinates (trialState ε a h hε ha hh) =
      repackPullback (coordinates 5 1 (productState volume volume
        ((transverse_memLp h hh).toLp (transverse h))
        ((clock_memLp ε a h hε ha).toLp (clock ε a h)))) := by
  apply Lp.ext
  filter_upwards [KFCausalClockFloorCoherentStates.weight_coe ε a h hε ha hh,
    repackPullback_coe (coordinates 5 1 (productState volume volume
      ((transverse_memLp h hh).toLp (transverse h))
      ((clock_memLp ε a h hε ha).toLp (clock ε a h)))),
    repack_preserves.quasiMeasurePreserving.ae (coordinates_product_coe 5 1
      (transverse h) (clock ε a h) (transverse_memLp h hh) (clock_memLp ε a h hε ha))] with x hx hy hz
  exact hx.trans ((charge_factor ε a h x).symm.trans (hz.symm.trans hy.symm))

theorem weight_coe (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    dualPhysical (trialState ε a h hε ha hh) =ᵐ[volume] weight ε a h := by
  have he : dualPhysical (trialState ε a h hε ha hh) =
      coordinates 5 1 (KFCausalPartialFourier.leftFourier 5 1
        (productState volume volume ((transverse_memLp h hh).toLp (transverse h))
          ((clock_memLp ε a h hε ha).toLp (clock ε a h)))) := by
    simp only [dualPhysical,dualMixed,transverseCoordinates,LinearIsometryEquiv.trans_apply,
      charge_product ε a h hε ha hh,LinearIsometryEquiv.symm_apply_apply]
  rw [he]
  filter_upwards [coordinates_coe 5 1 (KFCausalPartialFourier.leftFourier 5 1
      (productState volume volume ((transverse_memLp h hh).toLp (transverse h))
        ((clock_memLp ε a h hε ha).toLp (clock ε a h)))),
    (split_preserves_volume 5 1).quasiMeasurePreserving.ae
      (KFCausalPartialFourier.leftFourier_functions_coe 5 1 (transverse h) (clock ε a h)
        (transverse_integrable h hh) (transverse_memLp h hh) (clock_memLp ε a h hε ha))] with x hx hy
  simpa only [weight,transverse_fourier h hh] using hx.trans hy

theorem weight_continuous (ε a h : ℝ) : Continuous (weight ε a h) := by
  have hc := clockFunction_continuous ε a
  unfold weight fourierTransverse clock gaussian
  simp only [split_fst,split_snd]
  fun_prop

theorem weight_memLp (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) :
    MemLp (weight ε a h) 2 :=
  (Lp.memLp (dualPhysical (trialState ε a h hε ha hh))).ae_eq (weight_coe ε a h hε ha hh)

theorem weight_ne_zero (ε a h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (x : Joint 5 1) :
    weight ε a h x ≠ 0 := by
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos.mpr (div_pos Real.pi_pos (widths_positive h hh i))).ne')
      (Complex.exp_ne_zero _)
  · exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
      (div_ne_zero Real.pi_ne_zero (groundWidth_positive h hh).ne'))
      (clockFunction_ne_zero ε a hε.le _)

#print axioms widths_positive
#print axioms transverse_integrable
#print axioms transverse_memLp
#print axioms transverse_fourier
#print axioms weight_coe
#print axioms weight_continuous
#print axioms weight_memLp
#print axioms weight_ne_zero
end
end UnifiedTheory.Audit.KFCausalClockFloorDualGaussian
