/- Fourier diagonalization of translations on all Euclidean L2 states.
The phase representative is proved from the Schwartz integral formula
and extended using actual L2 density and bounded unitary maps. -/
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback
import UnifiedTheory.Audit.KFCausalUnitModulusMultiplier
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.MeasureTheory.Group.Measure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFourierTranslation
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev Hilbert := Lp ℂ 2 (volume : Measure E)

def shift (v : E) : E ≃ᵐ E := (Homeomorph.addRight v).toMeasurableEquiv

theorem shift_preserves_volume (v : E) : MeasurePreserving (shift v) :=
  measurePreserving_add_right volume v

def translation (v : E) : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E) :=
  unitaryPullback (shift v) (shift_preserves_volume v)

theorem translation_coe (v : E) (f : Hilbert (E := E)) :
    translation v f =ᵐ[volume] fun x => f (x+v) :=
  unitaryPullback_coe (shift v) (shift_preserves_volume v) f

def phase (v k : E) : ℂ := Real.fourierChar (inner ℝ v k)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_continuous (v : E) : Continuous (phase v) := by
  unfold phase
  fun_prop

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem phase_norm (v k : E) : ‖phase v k‖ = 1 := Circle.norm_coe _

def phaseAction (v : E) : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E) :=
  KFCausalUnitModulusMultiplier.unitary (phase v) (phase_continuous v).measurable (phase_norm v)

theorem phaseAction_coe (v : E) (f : Hilbert (E := E)) :
    phaseAction v f =ᵐ[volume] fun k => phase v k*f k :=
  KFCausalUnitModulusMultiplier.unitary_coe _ _ _ f

def schwartzShift (v : E) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (by fun_prop : (fun x : E => x+v).HasTemperateGrowth) (isometry_add_right v).antilipschitz

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
theorem schwartzShift_apply (v : E) (f : SchwartzMap E ℂ) (x : E) :
    schwartzShift v f x = f (x+v) := rfl

theorem translation_schwartz (v : E) (f : SchwartzMap E ℂ) :
    translation v (f.toLp 2) = (schwartzShift v f).toLp 2 := by
  apply Lp.ext
  filter_upwards [translation_coe v (f.toLp 2),(schwartzShift v f).coeFn_toLp 2,
    (shift_preserves_volume v).quasiMeasurePreserving.ae (f.coeFn_toLp 2 (volume : Measure E))] with x hx hs hf
  rw [hx,hs]
  exact hf

theorem fourier_schwartzShift (v : E) (f : SchwartzMap E ℂ) (k : E) :
    (𝓕 (schwartzShift v f) : SchwartzMap E ℂ) k = phase v k*(𝓕 f : SchwartzMap E ℂ) k := by
  have hh := congrFun (VectorFourier.fourierIntegral_comp_add_right
    Real.fourierChar volume (innerₗ E) (f : E → ℂ) v) k
  simpa only [SchwartzMap.fourier_coe,schwartzShift_apply,phase,Circle.smul_def,smul_eq_mul,
    VectorFourier.fourierIntegral,Function.comp_apply,innerₗ_apply_apply] using hh

theorem fourier_translation_schwartz (v : E) (f : SchwartzMap E ℂ) :
    (Lp.fourierTransformₗᵢ E ℂ) (translation v (f.toLp 2)) =
      phaseAction v ((Lp.fourierTransformₗᵢ E ℂ) (f.toLp 2)) := by
  rw [translation_schwartz]
  change 𝓕 ((schwartzShift v f).toLp 2) = phaseAction v (𝓕 (f.toLp 2))
  rw [SchwartzMap.toLp_fourier_eq,SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (schwartzShift v f) : SchwartzMap E ℂ).coeFn_toLp 2,
    phaseAction_coe v ((𝓕 f : SchwartzMap E ℂ).toLp 2),
    (𝓕 f : SchwartzMap E ℂ).coeFn_toLp 2] with k hk hp hf
  rw [hk,hp,hf,fourier_schwartzShift]

theorem fourier_translation (v : E) (f : Hilbert (E := E)) :
    (Lp.fourierTransformₗᵢ E ℂ) (translation v f) =
      phaseAction v ((Lp.fourierTransformₗᵢ E ℂ) f) := by
  have hh := (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := volume)
    (by norm_num)).equalizer
      ((Lp.fourierTransformₗᵢ E ℂ).continuous.comp (translation v).continuous)
      ((phaseAction v).continuous.comp (Lp.fourierTransformₗᵢ E ℂ).continuous)
      (funext fun g => fourier_translation_schwartz v g)
  exact congrFun hh f

#print axioms translation
#print axioms phaseAction
#print axioms translation_schwartz
#print axioms fourier_schwartzShift
#print axioms fourier_translation_schwartz
#print axioms fourier_translation

end
end UnifiedTheory.Audit.KFCausalFourierTranslation
