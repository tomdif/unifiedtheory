/- The full reduced polynomial clock integral equals the signed
pairing of actual ordered operator outputs and their clock momenta.
Different complex polynomials, sources and frequencies retain interference. -/
import UnifiedTheory.Audit.KFCausalPolynomialWholeClockResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalPolynomialResponsePairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalPolynomialGaussianDomain (output)
open UnifiedTheory.Audit.KFCausalPolynomialMomentumDomain (momentumFactor)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (modelDirections)
open UnifiedTheory.Audit.KFCausalSourcedResponseFactorBridge (index)
open UnifiedTheory.Audit.KFCausalPolynomialResponseDensities
  (amplitude momentum amplitude_density momentum_density amplitude_memLp momentum_memLp)
open UnifiedTheory.Audit.KFCausalPolynomialResponseIntegrability
  (weakDensity reducedDensity weak_factorization)

private theorem inner_density (f g : Hilbert) (F G : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) (hg : g =ᵐ[volume] G) :
    inner ℂ f g = ∫ x : Configuration, star (F x)*G x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  simp only [hx,hy,RCLike.inner_apply,Complex.star_def]
  ring

variable (ε a a' h p p' : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ) (P Q : Polynomial ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
  (hε : 0 < ε) (ha : 0 < a) (ha' : 0 < a') (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "gi" => output ε a h hε ha hh C p b 4 hb P modelDirections l (index n)
local notation "gj" => output ε a' h hε ha' hh D p' c 4 hb Q modelDirections l (index n)
local notation "mi" => momentumFactor ε a h hε ha hh p b 4 C hb P modelDirections l (index n)
local notation "mj" => momentumFactor ε a' h hε ha' hh p' c 4 D hb Q modelDirections l (index n)
local notation "Ai" => amplitude ε a h C p b P l n
local notation "Aj" => amplitude ε a' h D p' c Q l n
local notation "Ti" => momentum ε a h C p b P l n
local notation "Tj" => momentum ε a' h D p' c Q l n

theorem weak_integral_pairing :
    (∫ x : Configuration, weakDensity ε a a' h p p' b c C D P Q l n x) =
      (Complex.I/(h:ℂ))*(inner ℂ gi mj-inner ℂ mi gj) := by
  have hgi := amplitude_density ε a h C p b P l n hε ha hh hb
  have hgj := amplitude_density ε a' h D p' c Q l n hε ha' hh hb
  have hmi := momentum_density ε a h C p b P l n hε ha hh hb
  have hmj := momentum_density ε a' h D p' c Q l n hε ha' hh hb
  have hi := (amplitude_memLp ε a h C p b P l n hε ha hh hb).star.integrable_mul
    (momentum_memLp ε a' h D p' c Q l n hε ha' hh hb)
  have hj := (momentum_memLp ε a h C p b P l n hε ha hh hb).star.integrable_mul
    (amplitude_memLp ε a' h D p' c Q l n hε ha' hh hb)
  simp_rw [weak_factorization ε a a' h p p' b c C D P Q l n hh]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => (Complex.I/(h:ℂ))*z)
    ((integral_sub hi hj).trans (congrArg₂ (fun z w : ℂ => z-w)
      (inner_density gi mj Ai Tj hgi hmj).symm (inner_density mi gj Ti Aj hmi hgj).symm))

theorem reduced_integral_pairing :
    (∫ x : Configuration, reducedDensity ε a a' h p p' b c C D P Q l n x) =
      (Complex.I/(h:ℂ))*(inner ℂ gi mj-inner ℂ mi gj) :=
  (KFCausalPolynomialWholeClockResponse.configuration_integrals_eq ε a a' h p p' b c C D P Q l n
    hε ha ha' hh hb).symm.trans
      (weak_integral_pairing ε a a' h p p' b c C D P Q l n hε ha ha' hh hb)

#print axioms weak_integral_pairing
#print axioms reduced_integral_pairing
end
end UnifiedTheory.Audit.KFCausalPolynomialResponsePairing
