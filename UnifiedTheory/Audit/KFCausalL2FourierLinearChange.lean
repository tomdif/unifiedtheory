/- The determinant-weighted Fourier change of variables holds for actual
L2 unitaries and every state, by Schwartz density and null-set preservation. -/
import UnifiedTheory.Audit.KFCausalFourierLinearChange
import UnifiedTheory.Audit.KFCausalWeightedLpRepresentative
import UnifiedTheory.Audit.KFCausalL2FourierIntegral

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalL2FourierLinearChange
noncomputable section
open MeasureTheory
open scoped FourierTransform
open UnifiedTheory.Audit.KFCausalFourierLinearChange
open UnifiedTheory.Audit.KFCausalWeightedLpRepresentative

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

abbrev Hilbert := Lp ℂ 2 (volume : Measure E)

def composeSchwartz (A : E ≃L[ℝ] E) : SchwartzMap E ℂ →L[ℂ] SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ A

theorem unitary_schwartz (A : E ≃L[ℝ] E) (w : ℂ)
    (U : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E))
    (hu : ∀ f : Hilbert (E := E), U f =ᵐ[volume] fun x => w*f (A x))
    (φ : SchwartzMap E ℂ) : U (φ.toLp 2) = w • (composeSchwartz A φ).toLp 2 := by
  apply Lp.ext
  filter_upwards [hu (φ.toLp 2),Lp.coeFn_smul w ((composeSchwartz A φ).toLp 2),
    (composeSchwartz A φ).coeFn_toLp 2,
    (linear_quasiMeasurePreserving A).ae (φ.coeFn_toLp 2 (volume : Measure E))] with x hx hs hc hf
  rw [hx,hs]
  simp only [Pi.smul_apply,smul_eq_mul,hc,hf]
  rfl

theorem fourier_unitary_schwartz (A : E ≃L[ℝ] E) (w : ℂ)
    (U : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E))
    (hu : ∀ f : Hilbert (E := E), U f =ᵐ[volume] fun x => w*f (A x))
    (φ : SchwartzMap E ℂ) :
    (Lp.fourierTransformₗᵢ E ℂ) (U (φ.toLp 2)) =ᵐ[volume]
      fun k => (w*(jacobian A:ℂ))*((Lp.fourierTransformₗᵢ E ℂ) (φ.toLp 2)) (dualEquiv A k) := by
  let hm : MemLp (fun x => w*φ (A x)) 2 (volume : Measure E) :=
    by
    change MemLp (fun x => w*(composeSchwartz A φ) x) 2 volume
    exact ((composeSchwartz A φ).memLp 2 volume).const_mul w
  have hi : Integrable (fun x => w*φ (A x)) := (composeSchwartz A φ).integrable.const_mul w
  have he : U (φ.toLp 2) = hm.toLp (fun x => w*φ (A x)) := by
    apply Lp.ext
    filter_upwards [hu (φ.toLp 2),hm.coeFn_toLp,
      (linear_quasiMeasurePreserving A).ae (φ.coeFn_toLp 2 (volume : Measure E))] with x hx hy hz
    rw [hx,hy,hz]
  rw [he]
  filter_upwards [KFCausalL2FourierIntegral.fourier_toLp_coe _ hi hm,
    (dual_quasiMeasurePreserving A).ae
      (KFCausalL2FourierIntegral.fourier_toLp_coe (φ : E → ℂ) φ.integrable (φ.memLp 2 volume))]
    with k hx hy
  change ((Lp.fourierTransformₗᵢ E ℂ) (φ.toLp 2 volume)) (dualEquiv A k) = _ at hy
  rw [hx,hy]
  exact fourier_weighted_comp A w φ k

theorem conjugate_dense_representative {D : Type*} (j : D → Hilbert (E := E)) (hj : DenseRange j)
    (F U : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E))
    (e : E → E) (he : Measure.QuasiMeasurePreserving e volume volume) (w : E → ℂ)
    (hr : ∀ d, F (U (j d)) =ᵐ[volume] fun k => w k*(F (j d)) (e k))
    (f : Hilbert (E := E)) : F (U f) =ᵐ[volume] fun k => w k*(F f) (e k) := by
  let V : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E) := F.symm.trans (U.trans F)
  have hd : DenseRange (F ∘ j) := F.surjective.denseRange.comp hj F.continuous
  have hs (d : D) : V ((F ∘ j) d) =ᵐ[volume] fun k => w k*((F ∘ j) d) (e k) := by
    simpa only [V,Function.comp_apply,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply] using hr d
  have h := dense_weighted_representative (F ∘ j) hd V V.continuous e he w hs (F f)
  simpa only [V,LinearIsometryEquiv.trans_apply,LinearIsometryEquiv.symm_apply_apply] using h

theorem fourier_unitary_coe (A : E ≃L[ℝ] E) (w : ℂ)
    (U : Hilbert (E := E) ≃ₗᵢ[ℂ] Hilbert (E := E))
    (hu : ∀ f : Hilbert (E := E), U f =ᵐ[volume] fun x => w*f (A x))
    (f : Hilbert (E := E)) :
    (Lp.fourierTransformₗᵢ E ℂ) (U f) =ᵐ[volume]
      fun k => (w*(jacobian A:ℂ))*((Lp.fourierTransformₗᵢ E ℂ) f) (dualEquiv A k) := by
  exact conjugate_dense_representative (fun φ : SchwartzMap E ℂ => φ.toLp 2)
    (SchwartzMap.denseRange_toLpCLM (E := E) (F := ℂ) (p := 2) (μ := volume) (by norm_num))
    (Lp.fourierTransformₗᵢ E ℂ) U (dualEquiv A) (dual_quasiMeasurePreserving A)
    (fun _ => w*(jacobian A:ℂ)) (fourier_unitary_schwartz A w U hu) f

#print axioms unitary_schwartz
#print axioms fourier_unitary_schwartz
#print axioms fourier_unitary_coe
#print axioms conjugate_dense_representative
end
end UnifiedTheory.Audit.KFCausalL2FourierLinearChange
