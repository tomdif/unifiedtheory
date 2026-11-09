/- Whole-clock integrals of neutral cross kernels are the pairings of
actual ordered outputs and pure-clock momentum outputs. Every source
pair is absolutely integrable before any finite sums are interchanged. -/
import UnifiedTheory.Audit.KFCausalNeutralCrossDensity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalNeutralCrossPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive neutralWidth_bound)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (pair)
open UnifiedTheory.Audit.KFCausalShiftedGaussianPhysicalProfile (clockAmplitude)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalNeutralExponentialProfiles
open UnifiedTheory.Audit.KFCausalNeutralCrossKernel
open UnifiedTheory.Audit.KFCausalNeutralCrossDensity
open UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
  (amplitude amplitude_density amplitude_memLp)

def clockWeight (ε a h s : ℝ) : ℝ := ‖clockAmplitude ε a 0 (-h/2) s‖^2

theorem clockWeight_nonnegative (ε a h s : ℝ) : 0 ≤ clockWeight ε a h s := sq_nonneg _

theorem pair_eq_clockWeight (ε a h s : ℝ) :
    pair ε a a 0 0 (-h/2) s = (clockWeight ε a h s:ℂ) := by
  apply Complex.ext <;>
    simp only [pair,clockWeight,Complex.star_def,Complex.mul_re,Complex.mul_im,
      Complex.conj_re,Complex.conj_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.sq_norm,Complex.normSq_apply] <;> ring

theorem amplitude_product (ε a h : ℝ) (b c C D : ℂ) (P Q : Polynomial ℂ)
    (n : Fin 3) (s : ℝ) (q : Transverse) :
    star (amplitude ε a h C 0 (neutralSource b) P pointField n (s,q))*
      amplitude ε a h D 0 (neutralSource c) Q pointField n (s,q) =
      pair ε a a 0 0 (-h/2) s*
        value ε (-h/2) (groundWidth h) (neutralWidth h) b c C D P Q n s q := by
  simp only [amplitude,value,KFCausalPolynomialOrbitEnvelope.factor,
    KFCausalPolynomialKernelResponse.transverse,KFCausalGaussianKernelResponse.transverse,
    KFCausalRelativeGaussianDifferential.profile,pair,one_mul,star_mul]
  ring

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

def packetOutput (b C : ℂ) (P : Polynomial ℂ) (n : Fin 3) : Hilbert :=
  KFCausalPolynomialGaussianDomain.output ε a h hε ha hh C 0 (neutralSource b) 4 hb P
    modelDirections pointField (index n)
def packetMomentumOutput (b C : ℂ) (P : Polynomial ℂ) (n : Fin 3) : Hilbert :=
  KFCausalPolynomialMomentumDomain.momentumFactor ε a h hε ha hh 0 (neutralSource b) 4 C hb P
    modelDirections pointField (index n)

variable (b c C D : ℂ) (P Q : Polynomial ℂ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "Ai" => amplitude ε a h C 0 (neutralSource b) P pointField n
local notation "Aj" => amplitude ε a h D 0 (neutralSource c) Q pointField n
local notation "K" => crossKernel ε (-h/2) α β b c C D P Q n
local notation "R" => reducedKernel ε (-h/2) α β b c C D P Q n
local notation "rho" => KFCausalPolynomialResponseIntegrability.reducedDensity ε a a h 0 0
  (neutralSource b) (neutralSource c) C D P Q pointField n

include hε hh hb in
theorem energy_slice (s : ℝ) :
    (∫ q : Transverse, star (Ai (s,q))*Aj (s,q)) = pair ε a a 0 0 (-h/2) s*K s := by
  simp_rw [amplitude_product]
  rw [integral_const_mul,value_integral α β ε (-h/2) s (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)]

include hε hh hb in
theorem response_slice (s : ℝ) :
    (∫ q : Transverse, rho (s,q)) = pair ε a a 0 0 (-h/2) s*R s := by
  simp_rw [physical_reducedDensity]
  rw [integral_const_mul,reducedValue_integral α β ε (-h/2) s (groundWidth_positive h hh)
    (neutralWidth_positive h hh) (neutralWidth_bound h) hε (shift_bound ε h hb)]

include hε ha hh hb in
theorem clockEnergy_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*K s) volume := by
  have hi := ((amplitude_memLp ε a h C 0 (neutralSource b) P pointField n hε ha hh hb).star.integrable_mul
    (amplitude_memLp ε a h D 0 (neutralSource c) Q pointField n hε ha hh hb)).integral_prod_left
  exact hi.congr (Filter.Eventually.of_forall (energy_slice ε a h hε hh hb b c C D P Q n))

include hε ha hh hb in
theorem clockResponse_integrable :
    Integrable (fun s => pair ε a a 0 0 (-h/2) s*R s) volume := by
  have hi := (KFCausalPolynomialResponseIntegrability.reducedDensity_integrable ε a a h 0 0
    (neutralSource b) (neutralSource c) C D P Q pointField n hε ha ha hh hb).integral_prod_left
  exact hi.congr (Filter.Eventually.of_forall (response_slice ε a h hε hh hb b c C D P Q n))

theorem clockEnergy_pairing :
    (∫ s, pair ε a a 0 0 (-h/2) s*K s) =
      inner ℂ (packetOutput ε a h hε ha hh hb b C P n)
        (packetOutput ε a h hε ha hh hb c D Q n) := by
  have hi := (amplitude_memLp ε a h C 0 (neutralSource b) P pointField n hε ha hh hb).star.integrable_mul
    (amplitude_memLp ε a h D 0 (neutralSource c) Q pointField n hε ha hh hb)
  calc
    _ = ∫ s : ℝ, ∫ q : Transverse, star (Ai (s,q))*Aj (s,q) := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun s => (energy_slice ε a h hε hh hb b c C D P Q n s).symm))
    _ = ∫ x : Configuration, star (Ai x)*Aj x := (integral_prod _ hi).symm
    _ = _ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [amplitude_density ε a h C 0 (neutralSource b) P pointField n hε ha hh hb,
        amplitude_density ε a h D 0 (neutralSource c) Q pointField n hε ha hh hb] with x hx hy
      simp only [packetOutput,hx,hy,RCLike.inner_apply,Complex.star_def]
      ring

theorem clockResponse_pairing :
    (∫ s, pair ε a a 0 0 (-h/2) s*R s) =
      (Complex.I/(h:ℂ))*
        (inner ℂ (packetOutput ε a h hε ha hh hb b C P n)
          (packetMomentumOutput ε a h hε ha hh hb c D Q n)-
        inner ℂ (packetMomentumOutput ε a h hε ha hh hb b C P n)
          (packetOutput ε a h hε ha hh hb c D Q n)) := by
  have hi := KFCausalPolynomialResponseIntegrability.reducedDensity_integrable ε a a h 0 0
    (neutralSource b) (neutralSource c) C D P Q pointField n hε ha ha hh hb
  calc
    _ = ∫ s : ℝ, ∫ q : Transverse, rho (s,q) := by
      exact integral_congr_ae (Filter.Eventually.of_forall
        (fun s => (response_slice ε a h hε hh hb b c C D P Q n s).symm))
    _ = ∫ x : Configuration, rho x := (integral_prod _ hi).symm
    _ = _ := KFCausalPolynomialResponsePairing.reduced_integral_pairing ε a a h 0 0
      (neutralSource b) (neutralSource c) C D P Q pointField n hε ha ha hh hb

#print axioms clockWeight_nonnegative
#print axioms pair_eq_clockWeight
#print axioms amplitude_product
#print axioms energy_slice
#print axioms response_slice
#print axioms clockEnergy_integrable
#print axioms clockResponse_integrable
#print axioms clockEnergy_pairing
#print axioms clockResponse_pairing
end
end UnifiedTheory.Audit.KFCausalNeutralCrossPairing
