/- An unconditional potential response bound for the actual shifted
centered/paired packets with independent positive clock widths and arbitrary
real frequencies. L1 hypotheses in the transport lemma are discharged
using the actual directional operator outputs. -/
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockTransport
import UnifiedTheory.Audit.KFCausalPairedSpanMixedClockDensities
import UnifiedTheory.Audit.KFCausalPairedSpanCrossKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPairedSpanMixedClockResponse
noncomputable section
open MeasureTheory
open scoped ComplexConjugate
open KFCausalCoupledLongitudinalFlow (Configuration)
open KFCausalTransverseDilationFlow (Transverse)
open KFCausalPairedSpanMoments (Coefficients)
open KFCausalPairedSpanMixedClockDensities
open KFCausalPairedSpanMixedClockTransport
  (clockCoefficients weakCoefficients energy geometry response)
open KFCausalPairedSpanCrossKernel (profile crossDensity)
open KFCausalPairedSpanKernel (physicalDensity)
open KFCausalClockFloorRelativeShift (scale)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open KFCausalMatterOrderedDomain (pointField)
open KFCausalClockFloorShiftedOutput (shift_bound)

theorem shifted_factorization (ε a b h p q : ℝ) (c : Coefficients) (n : Fin 3)
    (x : Configuration) :
    shifted ε a b h p q c n x =
      (pointField x.2:ℂ)^n.val*profile (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1)
        (clockCoefficients ε a b p q (-h/2) c x.1) x.2 := by
  simp only [shifted,centered,paired,profile,clockCoefficients,
    KFCausalGaussianResponseDensities.amplitude,KFCausalRelativeGaussianDifferential.profile]
  ring

theorem weakShifted_factorization (ε a b h p q : ℝ) (c : Coefficients) (n : Fin 3)
    (x : Configuration) :
    weakShifted ε a b h p q c n x =
      (pointField x.2:ℂ)^n.val*profile (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1)
        (weakCoefficients ε a b p q (-h/2) c x.1) x.2 := by
  simp only [weakShifted,centered,paired,profile,weakCoefficients,
    KFCausalGaussianResponseDensities.amplitude,KFCausalRelativeGaussianDifferential.profile]
  ring

theorem energy_factorization (ε a b h p q : ℝ) (c : Coefficients) (x : Configuration) :
    energyDensity ε a b h p q c x =
      physicalDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1)
        (clockCoefficients ε a b p q (-h/2) c x.1) x.2 := by
  simp only [energyDensity,shifted_factorization,physicalDensity,profile,
    KFCausalQuarticPlaneDomination.potential,Fin.val_zero,Fin.val_one,
    show (2:Fin 3).val=2 by rfl,norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    pow_zero,pow_one,one_mul,mul_pow,sq_abs]
  ring

theorem scalar_pair (t z w : ℂ) :
    (conj (t*z)*(t*w)).re = ‖t‖^2*(conj z*w).re := by
  have he : conj (t*z)*(t*w) = (conj t*t)*(conj z*w) := by rw [map_mul]; ring
  rw [he,Complex.conj_mul']
  simp only [← Complex.ofReal_pow,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,
    zero_mul,sub_zero]

theorem response_factorization (ε a b h p q : ℝ) (c : Coefficients) (x : Configuration) :
    potentialDensity ε a b h p q c x =
      crossDensity (groundWidth h) (neutralWidth h) (scale ε (-h/2) x.1)
        (clockCoefficients ε a b p q (-h/2) c x.1)
        (weakCoefficients ε a b p q (-h/2) c x.1) x.2 := by
  simp only [potentialDensity,responseDensity,shifted_factorization,weakShifted_factorization,
    scalar_pair,crossDensity,KFCausalQuarticPlaneDomination.potential,
    Fin.val_zero,Fin.val_one,show (2:Fin 3).val=2 by rfl,
    norm_pow,Complex.norm_real,Real.norm_eq_abs,pow_zero,pow_one,one_mul,sq_abs]
  ring

variable (ε a b h p q : ℝ) (c : Coefficients) (hε : 0 < ε) (ha : 0 < a) (hbw : 0 < b)
  (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)

include hε hh hb in
theorem energy_slice (s : ℝ) :
    (∫ x : Transverse, energyDensity ε a b h p q c (s,x)) =
      energy (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c s := by
  obtain ⟨hA,hB⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh) _
      (KFCausalChargedPairCompactGeometry.actual_mem_region _ _ ε (-h/2) s
        (groundWidth_positive h hh) (neutralWidth_positive h hh).le (neutralWidth_bound h)
        hε (shift_bound ε h hb))
  simp_rw [energy_factorization]
  exact KFCausalPairedSpanKernel.kernel_formula _ _ _ _ hA hB (neutralWidth_positive h hh)

include hε hh hb in
theorem response_slice (s : ℝ) :
    (∫ x : Transverse, potentialDensity ε a b h p q c (s,x)) =
      response (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c s := by
  obtain ⟨hA,hB⟩ := KFCausalChargedPairCompactGeometry.region_widths_positive
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh) _
      (KFCausalChargedPairCompactGeometry.actual_mem_region _ _ ε (-h/2) s
        (groundWidth_positive h hh) (neutralWidth_positive h hh).le (neutralWidth_bound h)
        hε (shift_bound ε h hb))
  simp_rw [response_factorization]
  exact KFCausalPairedSpanCrossKernel.crossDensity_integral _ _ _ _ _ hA hB
    (neutralWidth_positive h hh)

include hε ha hbw hh hb in
theorem clock_energy_integrable :
    Integrable (energy (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c) volume :=
  (energyDensity_integrable ε a h hε ha hh hb b p q hbw c).integral_prod_left.congr
    (Filter.Eventually.of_forall (energy_slice ε a b h p q c hε hh hb))

include hε ha hbw hh hb in
theorem clock_response_integrable :
    Integrable (response (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c) volume :=
  (potentialDensity_integrable ε a h hε ha hh hb b p q hbw c).integral_prod_left.congr
    (Filter.Eventually.of_forall (response_slice ε a b h p q c hε hh hb))

include hε ha hbw hh hb in
theorem energy_integral :
    (∫ x, energyDensity ε a b h p q c x) =
      ∫ s, energy (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c s := by
  change (∫ x : ℝ × Transverse, energyDensity ε a b h p q c x ∂volume.prod volume) = _
  rw [integral_prod _ (energyDensity_integrable ε a h hε ha hh hb b p q hbw c)]
  exact integral_congr_ae (Filter.Eventually.of_forall (energy_slice ε a b h p q c hε hh hb))

include hε ha hbw hh hb in
theorem response_integral :
    (∫ x, potentialDensity ε a b h p q c x) =
      ∫ s, response (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c s := by
  change (∫ x : ℝ × Transverse, potentialDensity ε a b h p q c x ∂volume.prod volume) = _
  rw [integral_prod _ (potentialDensity_integrable ε a h hε ha hh hb b p q hbw c)]
  exact integral_congr_ae (Filter.Eventually.of_forall (response_slice ε a b h p q c hε hh hb))

theorem exists_uniform_potential_response (h : ℝ) (hh : h ≠ 0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε a b p q : ℝ, 0 < ε → 0 < a → 0 < b →
      |h| ≤ 2*Real.pi*ε/3 → ∀ c : Coefficients,
        (∫ x, potentialDensity ε a b h p q c x) =
          ∫ s, KFCausalMovingKernelClockResponse.reduced ε (-h/2)
            (energy (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c)
            (geometry (groundWidth h) (neutralWidth h) ε a b p q (-h/2) c) s ∧
        -((C+2)/ε)*(∫ x, energyDensity ε a b h p q c x) ≤
          ∫ x, potentialDensity ε a b h p q c x := by
  obtain ⟨C,hC,hbound⟩ := KFCausalPairedSpanMixedClockTransport.exists_uniform_integrable_response_bound
    (groundWidth h) (neutralWidth h) (groundWidth_positive h hh) (neutralWidth_positive h hh)
    (neutralWidth_bound h)
  refine ⟨C,hC,?_⟩
  intro ε a b p q hε ha hbw hb c
  rw [energy_integral ε a b h p q c hε ha hbw hh hb,
    response_integral ε a b h p q c hε ha hbw hh hb]
  exact hbound ε a b p q (-h/2) hε (shift_bound ε h hb) c
    (clock_energy_integrable ε a b h p q c hε ha hbw hh hb)
    (clock_response_integrable ε a b h p q c hε ha hbw hh hb)

#print axioms shifted_factorization
#print axioms weakShifted_factorization
#print axioms energy_factorization
#print axioms scalar_pair
#print axioms response_factorization
#print axioms energy_slice
#print axioms response_slice
#print axioms clock_energy_integrable
#print axioms clock_response_integrable
#print axioms energy_integral
#print axioms response_integral
#print axioms exists_uniform_potential_response
end
end UnifiedTheory.Audit.KFCausalPairedSpanMixedClockResponse
