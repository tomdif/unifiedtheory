/- Modulation becomes negative translation under the actual L2 Fourier
unitary. The proof starts with integrable Schwartz inputs and extends by
density, so no extra regularity assumption remains on the state. -/
import UnifiedTheory.Audit.KFCausalFourierPhasePackets
import UnifiedTheory.Audit.KFCausalPartialFourierTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalL2FourierModulation
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalFourierTranslation
open UnifiedTheory.Audit.KFCausalFourierPhasePackets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem phaseAction_schwartz (u : E) (f : SchwartzMap E ℂ) :
    phaseAction u (f.toLp 2) = (modulated_memLp u f (f.memLp 2)).toLp (modulated u f) := by
  apply Lp.ext
  filter_upwards [phaseAction_coe u (f.toLp 2),f.coeFn_toLp 2,
    (modulated_memLp u f (f.memLp 2)).coeFn_toLp] with x hp hf hm
  rw [hp,hf,hm]
  rfl

theorem fourier_phaseAction_schwartz (u : E) (f : SchwartzMap E ℂ) :
    (Lp.fourierTransformₗᵢ E ℂ) (phaseAction u (f.toLp 2)) =
      translation (-u) ((Lp.fourierTransformₗᵢ E ℂ) (f.toLp 2)) := by
  rw [phaseAction_schwartz]
  change 𝓕 ((modulated_memLp u f (f.memLp 2)).toLp (modulated u f)) =
    translation (-u) (𝓕 (f.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq]
  change (Lp.fourierTransformₗᵢ E ℂ) ((modulated_memLp u f (f.memLp 2)).toLp (modulated u f)) =
    translation (-u) ((𝓕 f : SchwartzMap E ℂ).toLp 2)
  apply Lp.ext
  filter_upwards [KFCausalL2FourierIntegral.fourier_toLp_coe (modulated u f)
      (modulated_integrable u f f.integrable) (modulated_memLp u f (f.memLp 2)),
    translation_coe (-u) ((𝓕 f : SchwartzMap E ℂ).toLp 2),
    (shift_preserves_volume (-u)).quasiMeasurePreserving.ae
      ((𝓕 f : SchwartzMap E ℂ).coeFn_toLp 2 (volume : Measure E))] with x hm ht hf
  change ((𝓕 f : SchwartzMap E ℂ).toLp 2) (x + -u) = (𝓕 f : SchwartzMap E ℂ) (x + -u) at hf
  rw [hm,ht,hf,fourier_modulated]
  simp only [SchwartzMap.fourier_coe,sub_eq_add_neg]

theorem fourier_phaseAction (u : E) (f : Hilbert (E := E)) :
    (Lp.fourierTransformₗᵢ E ℂ) (phaseAction u f) =
      translation (-u) ((Lp.fourierTransformₗᵢ E ℂ) f) := by
  have hh := (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := volume)
    (by norm_num)).equalizer
      ((Lp.fourierTransformₗᵢ E ℂ).continuous.comp (phaseAction u).continuous)
      ((translation (-u)).continuous.comp (Lp.fourierTransformₗᵢ E ℂ).continuous)
      (funext fun g => fourier_phaseAction_schwartz u g)
  exact congrFun hh f

open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates
open UnifiedTheory.Audit.KFCausalEuclideanTensorUnitary
open UnifiedTheory.Audit.KFCausalL2TensorEmbedding
open UnifiedTheory.Audit.KFCausalPartialFourier
open UnifiedTheory.Audit.KFCausalPartialFourierTranslation

theorem leftFourier_phase (n m : ℕ) (v : Block n) (f : ProductHilbert n m) :
    leftFourier n m (leftPhase n m v f) = leftTranslation n m (-v) (leftFourier n m f) := by
  have he := equal_on_products n m
    ((leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp (leftPhase n m v))
    ((leftTranslation n m (-v) : ProductHilbert n m →L[ℂ] ProductHilbert n m).comp
      (leftFourier n m : ProductHilbert n m →L[ℂ] ProductHilbert n m)) (by
      intro u w
      change leftFourier n m (leftPhase n m v (productState volume volume u w)) =
        leftTranslation n m (-v) (leftFourier n m (productState volume volume u w))
      rw [leftPhase_product,leftFourier_product,leftFourier_product,leftTranslation_product,
        fourier_phaseAction])
  exact congrArg (fun A : ProductHilbert n m →L[ℂ] ProductHilbert n m => A f) he

#print axioms phaseAction_schwartz
#print axioms fourier_phaseAction_schwartz
#print axioms fourier_phaseAction
#print axioms leftFourier_phase

end
end UnifiedTheory.Audit.KFCausalL2FourierModulation
