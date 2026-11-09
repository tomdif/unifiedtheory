/- Identify the centered marginal with the existing charge-projected
weighted polynomial kernel, including its actual clock derivative. -/
import UnifiedTheory.Audit.KFCausalNeutralPlaneUniformGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalCenteredPolynomialKernel
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalPolynomialOrbitEnvelope (factor)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalPolynomialLocalGram
open UnifiedTheory.Audit.KFCausalNeutralPlaneMeasure (centeredEnergyDensity)
open UnifiedTheory.Audit.KFCausalNeutralPlaneIntegrability

private theorem parameters_zero (h : ℝ) :
    KFCausalClockFloorDisplacedSources.uParameter h 0 = 0 ∧
    KFCausalClockFloorDisplacedSources.vParameter h 0 = 0 ∧
    KFCausalClockFloorDisplacedSources.rParameter h 0 = 0 ∧
    KFCausalClockFloorDisplacedSources.wParameter h 0 = 0 := by
  refine ⟨?_,?_,?_,?_⟩ <;> ext i <;>
    simp [KFCausalClockFloorDisplacedSources.uParameter,
      KFCausalClockFloorDisplacedSources.vParameter,KFCausalClockFloorDisplacedSources.rParameter,
      KFCausalClockFloorDisplacedSources.wParameter,KFCausalEuclideanProductCoordinates.split_fst,
      KFCausalEuclideanProductCoordinates.split_snd,KFCausalNormalizedChargeFlow.dilate]

private theorem parameter_at_zero (θ : ℝ) :
    KFCausalChargeModulationFlow.parameter θ (0 : Joint 2 4) = 0 := by
  apply norm_eq_zero.mp
  rw [KFCausalChargeModulationFlow.parameter_norm]
  simp

theorem sourceCurve_zero (h θ : ℝ) : sourceCurve h 0 0 θ = 0 := by
  simp only [sourceCurve,parameter_at_zero,KFCausalClockFloorDisplacedSources.source,
    (parameters_zero h).1,(parameters_zero h).2.1,
    (parameters_zero h).2.2.1,(parameters_zero h).2.2.2]
  funext i
  fin_cases i <;> simp [KFCausalClockFloorDisplacedSources.coefficients]

theorem amplitudeCurve_zero (h θ : ℝ) : amplitudeCurve h 0 0 θ = 1 := by
  simp [amplitudeCurve,parameter_at_zero,KFCausalClockFloorDisplacedSources.amplitude,
    (parameters_zero h).1,(parameters_zero h).2.1,(parameters_zero h).2.2.2,
    KFCausalClockFloorDisplacedSources.constant,KFCausalFourierTranslation.phase]

theorem meanFactor_zero (ε h : ℝ) (P : Polynomial ℂ) (n : Fin 3) (s : ℝ) (x : Transverse) :
    meanFactor ε h 0 0 P n s x =
      factor ε (-h/2) (groundWidth h) (neutralWidth h) 0 1 P pointField n x s := by
  simp [meanFactor,angleFactor,sourceCurve_zero,amplitudeCurve_zero]

theorem localKernel_zero_re (ε h : ℝ) (P : Polynomial ℂ) (n : Fin 3)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    (localKernel ε h 0 0 P P n s).re =
      ∫ x : Transverse,
        ‖factor ε (-h/2) (groundWidth h) (neutralWidth h) 0 1 P pointField n x s‖^2 := by
  rw [localKernel_gram ε h 0 0 P P n hε hh hb]
  have he : (∫ x : Transverse,
      (star (meanFactor ε h 0 0 P n s x)*meanFactor ε h 0 0 P n s x).re) =
    (∫ x : Transverse,
      star (meanFactor ε h 0 0 P n s x)*meanFactor ε h 0 0 P n s x).re :=
    integral_re (gram_integrable ε h 0 0 P P n hε hh hb s)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [meanFactor_zero]
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring

def realKernel (ε h : ℝ) (P : Polynomial ℂ) (s : ℝ) : ℝ :=
  (KFCausalWeightedPolynomialLocalResponse.kernel ε h 0 0
    (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re

theorem realKernel_eq_centeredEnergy (ε h : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    realKernel ε h P s =
      ∫ q, centeredEnergyDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) s) P q := by
  have hi (n : ℕ) : Integrable (fun q : Transverse =>
      ‖factor ε (-h/2) (groundWidth h) (neutralWidth h) 0 1 P pointField n q s‖^2) volume := by
    have hm := centered_factor_memLp (groundWidth h) (neutralWidth h) ε (-h/2) s
      (groundWidth_positive h hh) (neutralWidth_positive h hh)
      (by unfold neutralWidth; linarith) hε (shift_bound ε h hb) P n
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  unfold realKernel
  rw [KFCausalWeightedPolynomialLocalResponse.physical_kernel]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,one_mul]
  rw [localKernel_zero_re ε h P 0 hε hh hb,localKernel_zero_re ε h P 1 hε hh hb,
    localKernel_zero_re ε h P 2 hε hh hb]
  simp_rw [centeredEnergy_sum]
  have hsum := integral_add ((hi 0).add ((hi 1).const_mul (1/2:ℝ)))
    ((hi 2).const_mul (1/4:ℝ))
  simp only [Pi.add_apply] at hsum
  rw [hsum,integral_add (hi 0) ((hi 1).const_mul (1/2:ℝ)),
    integral_const_mul,integral_const_mul]
  rfl

theorem realKernel_derivative (ε h : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (realKernel ε h P)
      (KFCausalWeightedPolynomialLocalResponse.kernelDerivative ε h 0 0
        (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re s :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (KFCausalWeightedPolynomialLocalResponse.kernel_derivative ε h 0 0 _ P P hε hh hb s)

theorem reducedResponse_zero_re (ε h : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    (KFCausalWeightedPolynomialLocalResponse.reducedResponse ε h 0 0
      (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re =
      KFCausalClockResponseTransport.coefficient ε (-h/2) s*realKernel ε h P s-
        deriv (realKernel ε h P) s/KFCausalClockResponseTransport.clock ε s := by
  rw [(realKernel_derivative ε h P hε hh hb s).deriv]
  simp only [KFCausalWeightedPolynomialLocalResponse.reducedResponse,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.div_ofReal_re,realKernel]

#print axioms sourceCurve_zero
#print axioms amplitudeCurve_zero
#print axioms meanFactor_zero
#print axioms localKernel_zero_re
#print axioms realKernel_eq_centeredEnergy
#print axioms realKernel_derivative
#print axioms reducedResponse_zero_re
end
end UnifiedTheory.Audit.KFCausalCenteredPolynomialKernel
