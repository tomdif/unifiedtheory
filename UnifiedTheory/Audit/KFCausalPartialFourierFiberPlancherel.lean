/- Slice Plancherel derives the joint L2 bound required by the actual partial
Fourier fiber formula. Only measurability of the displayed slice transform
is required; no output L2 or operator identification is assumed. -/
import UnifiedTheory.Audit.KFCausalPartialFourierFiberFormula
import UnifiedTheory.Audit.KFCausalAveragedEnergyGraph

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalPartialFourierFiberPlancherel
noncomputable section
open MeasureTheory
open scoped FourierTransform
open KFCausalEuclideanProductCoordinates
open KFCausalPartialFourierFiberFormula
open KFCausalL2FourierIntegral
open KFCausalAveragedEnergyGraph (l2_norm_square)

variable (n m : ℕ)

theorem slice_norm_square (F : Block n → ℂ) (hF1 : Integrable F) (hF2 : MemLp F 2 volume) :
    (∫ x, ‖(𝓕 F) x‖^2) = ∫ x, ‖F x‖^2 := by
  have he := congrArg (fun r : ℝ => r^2)
    ((Lp.fourierTransformₗᵢ (Block n) ℂ).norm_map (hF2.toLp F))
  dsimp only at he
  rw [fourier_toLp_eq F hF1 hF2,l2_norm_square,l2_norm_square] at he
  have hleft : (∫ x, ‖((integralFourier_memLp F hF1 hF2).toLp (𝓕 F)) x‖^2) =
      ∫ x, ‖(𝓕 F) x‖^2 := by
    apply integral_congr_ae
    filter_upwards [(integralFourier_memLp F hF1 hF2).coeFn_toLp] with x hx
    rw [hx]
  have hright : (∫ x, ‖(hF2.toLp F) x‖^2) = ∫ x, ‖F x‖^2 := by
    apply integral_congr_ae
    filter_upwards [hF2.coeFn_toLp] with x hx
    rw [hx]
  exact hleft.symm.trans (he.trans hright)

theorem sliceFourier_memLp (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume)
    (hF1 : ∀ᵐ y ∂volume, Integrable (fun x => F (x,y)))
    (hGm : AEStronglyMeasurable (sliceFourier n m F) volume) :
    MemLp (sliceFourier n m F) 2 volume := by
  apply (memLp_two_iff_integrable_sq_norm hGm).mpr
  apply (integrable_prod_iff' (hGm.norm.pow 2)).mpr
  constructor
  · filter_upwards [hF1,slices_memLp n m F hF] with y hy hFy
    exact (memLp_two_iff_integrable_sq_norm
      (integralFourier_memLp (fun x => F (x,y)) hy hFy).aestronglyMeasurable).mp
        (integralFourier_memLp (fun x => F (x,y)) hy hFy)
  · have hi := (memLp_two_iff_integrable_sq_norm hF.aestronglyMeasurable).mp hF
    apply hi.integral_norm_prod_right.congr
    filter_upwards [hF1,slices_memLp n m F hF] with y hy hFy
    simpa only [Real.norm_eq_abs,Pi.pow_apply,abs_pow,abs_norm,sliceFourier] using
      (slice_norm_square n (fun x => F (x,y)) hy hFy).symm

theorem leftFourier_toLp_coe (F : Block n × Block m → ℂ) (hF : MemLp F 2 volume)
    (hF1 : ∀ᵐ y ∂volume, Integrable (fun x => F (x,y)))
    (hGm : AEStronglyMeasurable (sliceFourier n m F) volume) :
    KFCausalPartialFourier.leftFourier n m (hF.toLp F) =ᵐ[volume] sliceFourier n m F :=
  KFCausalPartialFourierFiberFormula.leftFourier_toLp_coe n m F hF hF1
    (sliceFourier_memLp n m F hF hF1 hGm)

#print axioms slice_norm_square
#print axioms sliceFourier_memLp
#print axioms leftFourier_toLp_coe
end
end UnifiedTheory.Audit.KFCausalPartialFourierFiberPlancherel
