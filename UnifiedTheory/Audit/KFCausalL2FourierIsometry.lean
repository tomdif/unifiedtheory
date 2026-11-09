/- The actual L2 Fourier unitary is equivariant under real orthogonal
coordinate changes. The Fourier integral identity is extended from L1/L2
states through a proved dense Schwartz class. -/
import UnifiedTheory.Audit.KFCausalL2FourierIntegral
import UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 400000

namespace UnifiedTheory.Audit.KFCausalL2FourierIsometry
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalL2FourierIntegral
open UnifiedTheory.Audit.KFCausalMeasureUnitaryPullback

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [MeasurableSpace F] [BorelSpace F]

def pullback (A : E ≃ₗᵢ[ℝ] F) : Lp ℂ 2 (volume : Measure F) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure E) :=
  unitaryPullback A.toMeasurableEquiv A.measurePreserving

theorem pullback_coe (A : E ≃ₗᵢ[ℝ] F) (f : Lp ℂ 2 (volume : Measure F)) :
    pullback A f =ᵐ[volume] f ∘ A := unitaryPullback_coe _ _ _

theorem pullback_toLp (A : E ≃ₗᵢ[ℝ] F) (f : F → ℂ) (hf : MemLp f 2) :
    pullback A (hf.toLp f) = (hf.comp_measurePreserving A.measurePreserving).toLp (f ∘ A) := by
  apply Lp.ext
  filter_upwards [pullback_coe A (hf.toLp f),A.measurePreserving.quasiMeasurePreserving.ae hf.coeFn_toLp,
    (hf.comp_measurePreserving A.measurePreserving).coeFn_toLp] with x hp hf' ht
  exact hp.trans (hf'.trans ht.symm)

theorem fourier_pullback_toLp (A : E ≃ₗᵢ[ℝ] F) (f : F → ℂ) (h1 : Integrable f) (h2 : MemLp f 2) :
    (Lp.fourierTransformₗᵢ E ℂ) (pullback A (h2.toLp f)) =
      pullback A ((Lp.fourierTransformₗᵢ F ℂ) (h2.toLp f)) := by
  rw [pullback_toLp]
  apply Lp.ext
  filter_upwards [fourier_toLp_coe (f ∘ A) (A.measurePreserving.integrable_comp_of_integrable h1)
      (h2.comp_measurePreserving A.measurePreserving),
    pullback_coe A ((Lp.fourierTransformₗᵢ F ℂ) (h2.toLp f)),
    A.measurePreserving.quasiMeasurePreserving.ae (fourier_toLp_coe f h1 h2)] with x hl hp hr
  rw [hl,hp,Function.comp_apply,hr]
  exact Real.fourier_comp_linearIsometry A f x

theorem fourier_pullback (A : E ≃ₗᵢ[ℝ] F) (f : Lp ℂ 2 (volume : Measure F)) :
    (Lp.fourierTransformₗᵢ E ℂ) (pullback A f) = pullback A ((Lp.fourierTransformₗᵢ F ℂ) f) := by
  have hc : IsClosed {g : Lp ℂ 2 (volume : Measure F) |
      (Lp.fourierTransformₗᵢ E ℂ) (pullback A g) = pullback A ((Lp.fourierTransformₗᵢ F ℂ) g)} :=
    isClosed_eq ((Lp.fourierTransformₗᵢ E ℂ).continuous.comp (pullback A).continuous)
      ((pullback A).continuous.comp (Lp.fourierTransformₗᵢ F ℂ).continuous)
  apply (closure_minimal (t := {g : Lp ℂ 2 (volume : Measure F) |
      (Lp.fourierTransformₗᵢ E ℂ) (pullback A g) = pullback A ((Lp.fourierTransformₗᵢ F ℂ) g)}) ?_ hc)
      (SchwartzMap.denseRange_toLpCLM (E := F) (F := ℂ) (p := 2) (by norm_num) f)
  rintro _ ⟨φ,rfl⟩
  exact fourier_pullback_toLp A φ φ.integrable (φ.memLp 2 volume)

#print axioms pullback_coe
#print axioms pullback_toLp
#print axioms fourier_pullback_toLp
#print axioms fourier_pullback

end
end UnifiedTheory.Audit.KFCausalL2FourierIsometry
