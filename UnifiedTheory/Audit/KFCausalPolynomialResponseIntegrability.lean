/- Whole-configuration integrability of polynomial weak and reduced
ordered responses. The reduced kernel includes both differentiated
polynomials. No extra L2 or integration-by-parts premise is assumed. -/
import UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
import UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2400000

namespace UnifiedTheory.Audit.KFCausalPolynomialResponseIntegrability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockResponseTransport (clock coefficient pair weakPair reduced)
open UnifiedTheory.Audit.KFCausalPolynomialKernelResponse
  (weight weightDerivative transverse transverseDerivative kernel kernelDerivative)
open UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
  (amplitude momentum slopeWeight slopeDensity amplitude_memLp momentum_memLp slopeDensity_memLp)
open UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
  (relativeInverse relativeInverse_bound relativeInverse_continuous coefficient_bound coefficient_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput (shift_bound)
open UnifiedTheory.Audit.KFCausalClockFloorInvariantTrial (neutralWidth)
open UnifiedTheory.Audit.KFCausalChargeGaussianGeometry (groundWidth)

variable (ε a a' h p p' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
  (P Q : Polynomial ℂ) (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
local notation "α" => groundWidth h
local notation "β" => neutralWidth h
local notation "K" => kernel ε (-h/2) α β α β b c C D P Q
local notation "K'" => kernelDerivative ε (-h/2) α β α β b c C D P Q
local notation "Ai" => amplitude ε a h C p b P l n
local notation "Aj" => amplitude ε a' h D p' c Q l n
local notation "Si" => slopeDensity ε a h C p b P l n
local notation "Sj" => slopeDensity ε a' h D p' c Q l n

def weakDensity (x : Configuration) : ℂ :=
  (l x.2:ℂ)^(2*n.val)*K x.2 x.1*weakPair ε a a' p p' (-h/2) x.1

def reducedDensity (x : Configuration) : ℂ :=
  (l x.2:ℂ)^(2*n.val)*reduced ε a a' p p' (-h/2) (K x.2) (K' x.2) x.1

private theorem signed_pair_algebra (h : ℝ) (hh : h ≠ 0) (u v w z : ℂ) :
    (Complex.I/(h:ℂ))*(star u*((-Complex.I*(h:ℂ))*z*v)-
      star ((-Complex.I*(h:ℂ))*w*u)*v) = star u*v*(star w+z) := by
  simp only [star_mul,star_neg,Complex.star_def,Complex.conj_I,Complex.conj_ofReal]
  field_simp [Complex.ofReal_ne_zero.mpr hh]
  ring_nf
  simp [Complex.I_sq]

theorem weak_factorization (hh : h ≠ 0) (x : Configuration) :
    weakDensity ε a a' h p p' b c C D P Q l n x =
      (Complex.I/(h:ℂ))*(star (Ai x)*momentum ε a' h D p' c Q l n x-
        star (momentum ε a h C p b P l n x)*Aj x) := by
  rw [momentum,momentum,signed_pair_algebra h hh]
  simp only [weakDensity,weakPair,pair,kernel,transverse,
    KFCausalGaussianKernelResponse.transverse,amplitude,
    KFCausalRelativeGaussianDifferential.profile,one_mul,star_mul,star_pow,
    Complex.star_def,Complex.conj_ofReal]
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  ring

theorem reduced_factorization (hε : 0 < ε) (x : Configuration) :
    reducedDensity ε a a' h p p' b c C D P Q l n x =
      star (Ai x)*((coefficient ε (-h/2) x.1:ℂ)*Aj x-relativeInverse ε (-h/2) x.1*Sj x)-
        star (relativeInverse ε (-h/2) x.1*Si x)*Aj x := by
  have hc : (clock ε x.1:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by unfold clock; positivity)
  unfold reducedDensity reduced kernelDerivative transverseDerivative kernel transverse
    KFCausalGaussianKernelResponse.transverse KFCausalGaussianKernelResponse.transverseSlope
    weightDerivative pair amplitude slopeDensity slopeWeight relativeInverse
    KFCausalRelativeGaussianDifferential.profile
  rw [show 2*n.val=n.val+n.val by omega,pow_add]
  simp only [one_mul,star_mul,star_add,star_sub,star_pow,star_inv₀,star_one,
    Complex.star_def,Complex.conj_ofReal]
  field_simp
  ring

private theorem bounded_mul_memLp (f : Configuration → ℂ) (hf : MemLp f 2 volume)
    (g : ℝ → ℂ) (hg : Continuous g) (M : ℝ) (hM : ∀ s, ‖g s‖ ≤ M) :
    MemLp (fun x : Configuration => g x.1*f x) 2 volume :=
  hf.mul' (memLp_top_of_bound (hg.comp continuous_fst).aestronglyMeasurable M
    (Filter.Eventually.of_forall (fun x => hM x.1)))

variable (hε : 0 < ε) (ha : 0 < a) (ha' : 0 < a') (hh : h ≠ 0)
  (hb : |h| ≤ 2*Real.pi*ε/3)

include hε ha ha' hh hb in
theorem weakDensity_integrable :
    Integrable (weakDensity ε a a' h p p' b c C D P Q l n) volume := by
  have hi := amplitude_memLp ε a h C p b P l n hε ha hh hb
  have hj := amplitude_memLp ε a' h D p' c Q l n hε ha' hh hb
  have hmi := momentum_memLp ε a h C p b P l n hε ha hh hb
  have hmj := momentum_memLp ε a' h D p' c Q l n hε ha' hh hb
  apply (((hi.star.integrable_mul hmj).sub (hmi.star.integrable_mul hj)).const_mul
    (Complex.I/(h:ℂ))).congr
  exact Filter.Eventually.of_forall
    (fun x => (weak_factorization ε a a' h p p' b c C D P Q l n hh x).symm)

include hε ha ha' hh hb in
theorem reducedDensity_integrable :
    Integrable (reducedDensity ε a a' h p p' b c C D P Q l n) volume := by
  have hy := shift_bound ε h hb
  have hi := amplitude_memLp ε a h C p b P l n hε ha hh hb
  have hj := amplitude_memLp ε a' h D p' c Q l n hε ha' hh hb
  have hsi := slopeDensity_memLp ε a h C p b P l n hε ha hh hb
  have hsj := slopeDensity_memLp ε a' h D p' c Q l n hε ha' hh hb
  have hri := bounded_mul_memLp _ hsi (relativeInverse ε (-h/2))
    (relativeInverse_continuous ε (-h/2) hε hy) (2/ε)
    (fun s => relativeInverse_bound ε (-h/2) s hε hy)
  have hrj := bounded_mul_memLp _ hsj (relativeInverse ε (-h/2))
    (relativeInverse_continuous ε (-h/2) hε hy) (2/ε)
    (fun s => relativeInverse_bound ε (-h/2) s hε hy)
  have hcj := bounded_mul_memLp _ hj (fun s => (coefficient ε (-h/2) s:ℂ))
    (Complex.continuous_ofReal.comp (coefficient_continuous ε (-h/2) hε hy)) (4/ε)
    (fun s => coefficient_bound ε (-h/2) s hε hy)
  apply ((hi.star.integrable_mul (hcj.sub hrj)).sub (hri.star.integrable_mul hj)).congr
  exact Filter.Eventually.of_forall
    (fun x => (reduced_factorization ε a a' h p p' b c C D P Q l n hε x).symm)

#print axioms weak_factorization
#print axioms reduced_factorization
#print axioms weakDensity_integrable
#print axioms reducedDensity_integrable
end
end UnifiedTheory.Audit.KFCausalPolynomialResponseIntegrability
