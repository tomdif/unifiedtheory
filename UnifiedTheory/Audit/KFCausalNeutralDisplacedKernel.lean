/- Identify the actual neutral-displaced projected weighted kernel with
the integrable neutral-profile energy, retaining its normalization and
the previously established kernel derivative. -/
import UnifiedTheory.Audit.KFCausalNeutralDisplacedSources

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

namespace UnifiedTheory.Audit.KFCausalNeutralDisplacedKernel
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorRelativeShift (scale)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalProjectedPolynomialLocalKernel
open UnifiedTheory.Audit.KFCausalPolynomialLocalGram
open UnifiedTheory.Audit.KFCausalNeutralProfileMarginal
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralDisplacedSources

theorem displacedProfile_factor_memLp (ε h Q K : ℝ) (P : Polynomial ℂ) (n : ℕ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    MemLp (profileFactor (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
      (displacedProfile h Q K P) n) 2 volume :=
  exponentialProfile_factor_memLp _ _ _ _ _ (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (by unfold neutralWidth; linarith)
    hε (shift_bound ε h hb) _ _ P n

theorem displacedProfile_integrable (ε h Q K : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    Integrable (profileEnergyDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
      (displacedProfile h Q K P)) volume :=
  profileEnergy_integrable_of_factors _ _ _ _ fun n =>
    displacedProfile_factor_memLp ε h Q K P n hε hh hb s

theorem localKernel_neutral_re (ε h Q K : ℝ) (P : Polynomial ℂ) (n : Fin 3)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    (localKernel ε h (neutralParameter Q) (neutralParameter K) P P n s).re =
      ∫ x : Transverse,
        ‖profileFactor (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
          (displacedProfile h Q K P) n x‖^2 := by
  rw [localKernel_gram ε h (neutralParameter Q) (neutralParameter K) P P n hε hh hb]
  have he : (∫ x : Transverse,
      (star (meanFactor ε h (neutralParameter Q) (neutralParameter K) P n s x)*
        meanFactor ε h (neutralParameter Q) (neutralParameter K) P n s x).re) =
    (∫ x : Transverse,
      star (meanFactor ε h (neutralParameter Q) (neutralParameter K) P n s x)*
        meanFactor ε h (neutralParameter Q) (neutralParameter K) P n s x).re :=
    integral_re (gram_integrable ε h (neutralParameter Q) (neutralParameter K) P P n hε hh hb s)
  rw [← he]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [meanFactor_neutral]
  simp only [Complex.star_def,Complex.mul_re,Complex.conj_re,Complex.conj_im,
    Complex.sq_norm,Complex.normSq_apply]
  ring

def realKernel (ε h Q K : ℝ) (P : Polynomial ℂ) (s : ℝ) : ℝ :=
  (KFCausalWeightedPolynomialLocalResponse.kernel ε h (neutralParameter Q) (neutralParameter K)
    (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re

theorem realKernel_eq_profileEnergy (ε h Q K : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    realKernel ε h Q K P s =
      ∫ q, profileEnergyDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
        (displacedProfile h Q K P) q := by
  have hi (n : ℕ) : Integrable (fun q : Transverse =>
      ‖profileFactor (groundWidth h) (neutralWidth h) (scale ε (-h/2) s)
        (displacedProfile h Q K P) n q‖^2) volume := by
    have hm := displacedProfile_factor_memLp ε h Q K P n hε hh hb s
    exact (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm
  unfold realKernel
  rw [KFCausalWeightedPolynomialLocalResponse.physical_kernel]
  simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero,one_mul]
  rw [localKernel_neutral_re ε h Q K P 0 hε hh hb,
    localKernel_neutral_re ε h Q K P 1 hε hh hb,
    localKernel_neutral_re ε h Q K P 2 hε hh hb]
  simp_rw [profileEnergy_sum]
  have hsum := integral_add ((hi 0).add ((hi 1).const_mul (1/2:ℝ)))
    ((hi 2).const_mul (1/4:ℝ))
  simp only [Pi.add_apply] at hsum
  rw [hsum,integral_add (hi 0) ((hi 1).const_mul (1/2:ℝ)),
    integral_const_mul,integral_const_mul]
  rfl

theorem realKernel_derivative (ε h Q K : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    HasDerivAt (realKernel ε h Q K P)
      (KFCausalWeightedPolynomialLocalResponse.kernelDerivative ε h
        (neutralParameter Q) (neutralParameter K)
        (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re s :=
  Complex.reCLM.hasFDerivAt.comp_hasDerivAt s
    (KFCausalWeightedPolynomialLocalResponse.kernel_derivative ε h
      (neutralParameter Q) (neutralParameter K) _ P P hε hh hb s)

theorem reducedResponse_neutral_re (ε h Q K : ℝ) (P : Polynomial ℂ)
    (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (s : ℝ) :
    (KFCausalWeightedPolynomialLocalResponse.reducedResponse ε h
      (neutralParameter Q) (neutralParameter K)
      (KFCausalWeightedPolynomialLocalResponse.physicalWeights 1 1 1) P P s).re =
      KFCausalClockResponseTransport.coefficient ε (-h/2) s*realKernel ε h Q K P s-
        deriv (realKernel ε h Q K P) s/KFCausalClockResponseTransport.clock ε s := by
  rw [(realKernel_derivative ε h Q K P hε hh hb s).deriv]
  simp only [KFCausalWeightedPolynomialLocalResponse.reducedResponse,Complex.sub_re,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,
    Complex.div_ofReal_re,realKernel]

#print axioms displacedProfile_factor_memLp
#print axioms displacedProfile_integrable
#print axioms localKernel_neutral_re
#print axioms realKernel_eq_profileEnergy
#print axioms realKernel_derivative
#print axioms reducedResponse_neutral_re
end
end UnifiedTheory.Audit.KFCausalNeutralDisplacedKernel
