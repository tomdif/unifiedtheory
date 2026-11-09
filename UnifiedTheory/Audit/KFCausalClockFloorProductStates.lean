/- Actual product states and their spectral exponential graphs under the
revised clock-floor coordinate unitary. Scalar Fourier identities transfer
to the full physical operator, retaining the exact composition domains. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedOutput
import UnifiedTheory.Audit.KFCausalProductFourierEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorProductStates
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorFourierMultiplier
open UnifiedTheory.Audit.KFCausalClockFloorExponential
open UnifiedTheory.Audit.KFCausalProductFourierEnergy
open UnifiedTheory.Audit.KFCausalL2FourierIntegral

def productState (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) : Hilbert :=
  coordinates ε hε ((configuration_memLp g ψ hg hψ).toLp (configurationProduct g ψ))

theorem productState_coe (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    productState ε hε g ψ hg hψ =ᵐ[volume] weightedFunction ε hε (configurationProduct g ψ) :=
  coordinates_toLp_coe ε hε _ _

theorem productState_fourier (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2) :
    coupledFourier ε hε (productState ε hε g ψ hg₂ hψ₂) =ᵐ[volume] 𝓕 (productFunction g ψ) := by
  let f := configurationProduct g ψ
  have hf : MemLp f 2 := configuration_memLp g ψ hg₂ hψ₂
  have hp : MemLp (f ∘ split) 2 := hf.comp_measurePreserving split_preserves_volume
  have he : euclideanPullback (hf.toLp f) = hp.toLp (f ∘ split) := by
    apply Lp.ext
    filter_upwards [euclideanPullback_coe (hf.toLp f),
      split_preserves_volume.quasiMeasurePreserving.ae hf.coeFn_toLp,hp.coeFn_toLp] with x hx hy hz
    exact (hx.trans hy).trans hz.symm
  change (Lp.fourierTransformₗᵢ Space ℂ)
    (euclideanPullback ((coordinates ε hε).symm (coordinates ε hε (hf.toLp f)))) =ᵐ[volume] _
  rw [LinearIsometryEquiv.symm_apply_apply,he]
  exact fourier_toLp_coe _ (split_preserves_volume.integrable_comp_of_integrable
    (configuration_integrable g ψ hg₁ hψ₁)) hp

theorem product_exponential_graph (ε hbar b : ℝ) (hε : 0 < ε)
    (g h : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg₁ : Integrable g) (hg₂ : MemLp g 2) (hh₁ : Integrable h) (hh₂ : MemLp h 2)
    (hψ₁ : Integrable ψ) (hψ₂ : MemLp ψ 2)
    (hF : ∀ k : ℝ, (𝓕 h) k=(Real.exp (b*(2*Real.pi*hbar*k)):ℂ)*(𝓕 g) k) :
    (productState ε hε g ψ hg₂ hψ₂,productState ε hε h ψ hh₂ hψ₂) ∈
      (longitudinalExponential ε hε hbar b).graph := by
  apply (longitudinal_exponential_graph ε hε hbar b _ _).mpr
  filter_upwards [productState_fourier ε hε g ψ hg₁ hg₂ hψ₁ hψ₂,
    productState_fourier ε hε h ψ hh₁ hh₂ hψ₁ hψ₂] with k hg hh
  rw [hh,hg,fourier_product,fourier_product,hF]
  simp only [symbol,mul_assoc]

def lift (ε : ℝ) (hε : 0 < ε) : FrequencyHilbert ≃ₗᵢ[ℂ] Hilbert :=
  euclideanPullback.symm.trans (coordinates ε hε)

theorem lift_product (ε : ℝ) (hε : 0 < ε) (g : ℝ → ℂ) (ψ : TailSpace → ℂ)
    (hg : MemLp g 2) (hψ : MemLp ψ 2) :
    lift ε hε ((product_memLp g ψ hg hψ).toLp (productFunction g ψ)) = productState ε hε g ψ hg hψ := by
  rfl

#print axioms productState_coe
#print axioms productState_fourier
#print axioms product_exponential_graph
#print axioms lift_product

end
end UnifiedTheory.Audit.KFCausalClockFloorProductStates
