/- Identify the full weak and reduced Gaussian integrals with actual
field-weighted Hilbert-space pairings. Powers one and two are the physical
field and field-square operator outputs, with their domains derived.
This is a fixed-packet identity, not an evolution or uniform energy bound. -/
import UnifiedTheory.Audit.KFCausalGaussianWholeClockResponse
import UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalGaussianResponsePairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseFieldSquare (fieldSquare)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower fieldPower_graph)
open UnifiedTheory.Audit.KFCausalGaussianResponseDensities
  (amplitude momentum field_power_memLp amplitude_density momentum_density amplitude_memLp momentum_memLp)
open UnifiedTheory.Audit.KFCausalGaussianResponseIntegrability
  (weakDensity reducedDensity weak_factorization)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedSpectral (shiftedOutput)
open UnifiedTheory.Audit.KFCausalCoherentMomentumOutputReduction (reducedOutput)
open UnifiedTheory.Audit.KFCausalClockFloorSourcedCommonDomain (shiftedOutput_fieldSquare_domain)
open UnifiedTheory.Audit.KFCausalSourcedMomentumOutput (reduced_square_domain)

def weighted (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (f : Hilbert)
    (hf : f ∈ (fieldSquare l).domain) : Hilbert :=
  (field_power_memLp l n f hf).toLp (fun x : Configuration => (l x.2:ℂ)^n.val*f x)

theorem weighted_density (l : Transverse →L[ℝ] ℝ) (n : Fin 3) (f : Hilbert)
    (hf : f ∈ (fieldSquare l).domain) :
    weighted l n f hf =ᵐ[volume] fun x : Configuration => (l x.2:ℂ)^n.val*f x :=
  (field_power_memLp l n f hf).coeFn_toLp

theorem weighted_zero (l : Transverse →L[ℝ] ℝ) (f : Hilbert)
    (hf : f ∈ (fieldSquare l).domain) : weighted l 0 f hf = f := by
  apply Lp.ext
  filter_upwards [weighted_density l 0 f hf] with x hx
  simpa using hx

theorem weighted_field_graph (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ (fieldSquare l).domain) :
    (f,weighted l ⟨i.val+1,by omega⟩ f hf) ∈ (fieldPower l i).graph :=
  (fieldPower_graph l i f _).mpr (weighted_density l ⟨i.val+1,by omega⟩ f hf)

private theorem inner_density (f g : Hilbert) (F G : Configuration → ℂ)
    (hf : f =ᵐ[volume] F) (hg : g =ᵐ[volume] G) :
    inner ℂ f g = ∫ x : Configuration, star (F x)*G x := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf,hg] with x hx hy
  simp only [hx,hy,RCLike.inner_apply,Complex.star_def]
  ring

variable (ε a a' p p' α β α' β' h : ℝ) (b c : Fin 5 → ℂ) (C D : ℂ)
  (l : Transverse →L[ℝ] ℝ) (n : Fin 3)
  (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
  (ha : 0 < a) (ha' : 0 < a') (hα : 0 < α) (hβ : 0 < β) (hw : 32*β ≤ α)
  (hα' : 0 < α') (hβ' : 0 < β') (hw' : 32*β' ≤ α')
local notation "Gi" => shiftedOutput ε a α β hε ha hα hβ hw C p b h hb
local notation "Gj" => shiftedOutput ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb
local notation "Hi" => shiftedOutput ε (a/2) α β hε (by positivity) hα hβ hw C p b h hb
local notation "Hj" => shiftedOutput ε (a'/2) α' β' hε (by positivity) hα' hβ' hw' D p' c h hb
local notation "Mi" => reducedOutput ε a h hε ha hb p Gi Hi
local notation "Mj" => reducedOutput ε a' h hε ha' hb p' Gj Hj
local notation "gi" => weighted l n Gi (shiftedOutput_fieldSquare_domain ε a α β hε ha hα hβ hw C p b h hb l)
local notation "gj" => weighted l n Gj (shiftedOutput_fieldSquare_domain ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l)
local notation "mi" => weighted l n Mi (reduced_square_domain ε a α β hε ha hα hβ hw C p b h hb l)
local notation "mj" => weighted l n Mj (reduced_square_domain ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l)
local notation "Ai" => amplitude ε a α β p (-h/2) b C l n
local notation "Aj" => amplitude ε a' α' β' p' (-h/2) c D l n
local notation "Ti" => momentum ε a α β p (-h/2) h b C l n
local notation "Tj" => momentum ε a' α' β' p' (-h/2) h c D l n

include hh in
theorem weak_integral_pairing :
    (∫ x : Configuration, weakDensity ε (-h/2) a a' p p' α β α' β' b c C D l n x) =
      (Complex.I/(h:ℂ))*(inner ℂ gi mj-inner ℂ mi gj) := by
  have hgi : gi =ᵐ[volume] Ai := (weighted_density l n Gi _).trans
    (amplitude_density ε a α β hε ha hα hβ hw C p b h hb l n)
  have hgj : gj =ᵐ[volume] Aj := (weighted_density l n Gj _).trans
    (amplitude_density ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n)
  have hmi : mi =ᵐ[volume] Ti := (weighted_density l n Mi _).trans
    (momentum_density ε a α β hε ha hα hβ hw C p b h hb l n)
  have hmj : mj =ᵐ[volume] Tj := (weighted_density l n Mj _).trans
    (momentum_density ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n)
  have hi := (amplitude_memLp ε a α β hε ha hα hβ hw C p b h hb l n).star.integrable_mul
    (momentum_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n)
  have hj := (momentum_memLp ε a α β hε ha hα hβ hw C p b h hb l n).star.integrable_mul
    (amplitude_memLp ε a' α' β' hε ha' hα' hβ' hw' D p' c h hb l n)
  simp_rw [weak_factorization ε (-h/2) a a' p p' α β α' β' b c C D l n h hh]
  rw [integral_const_mul]
  exact congrArg (fun z : ℂ => (Complex.I/(h:ℂ))*z)
    ((integral_sub hi hj).trans (congrArg₂ (fun z w : ℂ => z-w)
      (inner_density gi mj Ai Tj hgi hmj).symm (inner_density mi gj Ti Aj hmi hgj).symm))

include hh in
theorem reduced_integral_pairing :
    (∫ x : Configuration, reducedDensity ε (-h/2) a a' p p' α β α' β' b c C D l n x) =
      (Complex.I/(h:ℂ))*(inner ℂ gi mj-inner ℂ mi gj) :=
  (KFCausalGaussianWholeClockResponse.configuration_integrals_eq ε a a' p p' α β α' β' h b c C D l n
    hε hh hb ha ha' hα hβ hw hα' hβ' hw').symm.trans
      (weak_integral_pairing ε a a' p p' α β α' β' h b c C D l n
        hε hh hb ha ha' hα hβ hw hα' hβ' hw')

#print axioms weighted_density
#print axioms weighted_zero
#print axioms weighted_field_graph
#print axioms weak_integral_pairing
#print axioms reduced_integral_pairing
end
end UnifiedTheory.Audit.KFCausalGaussianResponsePairing
