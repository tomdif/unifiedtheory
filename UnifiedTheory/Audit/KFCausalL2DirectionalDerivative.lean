/- Classical directional derivatives in L2 satisfy the weak integration by
parts identity and the actual L2 Fourier multiplier identity. No L1 assumption
on the state or its derivative is made. -/
import UnifiedTheory.Audit.KFCausalL2FourierIntegral
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalL2DirectionalDerivative
noncomputable section
open MeasureTheory
open scoped FourierTransform ContDiff LineDeriv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem weak_derivative (f d : E → ℂ) (v : E) (hf : MemLp f 2) (hd : MemLp d 2)
    (hder : ∀ x, HasLineDerivAt ℝ f (d x) x v) (φ : SchwartzMap E ℂ) :
    (∫ x, φ x*d x) = -∫ x, (∂_{v} φ) x*f x := by
  apply integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.mul ℝ ℂ) (v := v)
    (μ := volume) (f := φ) (f' := ((∂_{v} φ : SchwartzMap E ℂ) : E → ℂ)) (g := f) (g' := d)
    (((∂_{v} φ).memLp 2).integrable_mul hf)
    ((φ.memLp 2).integrable_mul hd)
    ((φ.memLp 2).integrable_mul hf)
  · intro x
    exact (φ.hasFDerivAt x).hasLineDerivAt v
  · exact hder

theorem fourier_pairing (f : E → ℂ) (hf : MemLp f 2) (φ : SchwartzMap E ℂ) :
    (∫ x, φ x*((Lp.fourierTransformₗᵢ E ℂ) (hf.toLp f)) x) = ∫ x, (𝓕 φ) x*f x := by
  have h := congrArg (fun T : TemperedDistribution E ℂ => T φ)
    (Lp.fourier_toTemperedDistribution_eq (hf.toLp f))
  simp only [TemperedDistribution.fourier_apply,Lp.toTemperedDistribution_apply,smul_eq_mul] at h
  calc
    _ = ∫ x, (𝓕 φ) x*(hf.toLp f) x := h.symm
    _ = _ := ?_
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  rw [hx]

theorem continuous_mul_locallyIntegrable (w : E → ℂ) (hw : Continuous w)
    (f : E → ℂ) (hf : LocallyIntegrable f) : LocallyIntegrable (fun x => w x*f x) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  exact IntegrableOn.continuousOn_mul hw.continuousOn (hf.integrableOn_isCompact hK) hK

theorem derivative_fourier_pairing (f d : E → ℂ) (v : E)
    (hf : MemLp f 2) (hd : MemLp d 2)
    (hder : ∀ x, HasLineDerivAt ℝ f (d x) x v) (φ : SchwartzMap E ℂ) :
    (∫ x, φ x*((Lp.fourierTransformₗᵢ E ℂ) (hd.toLp d)) x) =
      ∫ x, φ x*((2*Real.pi*Complex.I)*(inner ℝ x v:ℂ)*
        ((Lp.fourierTransformₗᵢ E ℂ) (hf.toLp f)) x) := by
  have ht : (inner ℝ · v).HasTemperateGrowth := ((innerSL ℝ).flip v).hasTemperateGrowth
  let ψ : SchwartzMap E ℂ := -(2*Real.pi*Complex.I) •
    SchwartzMap.smulLeftCLM ℂ (inner ℝ · v) φ
  calc
    _ = ∫ x, (𝓕 φ) x*d x := fourier_pairing d hd φ
    _ = -∫ x, (∂_{v} (𝓕 φ)) x*f x := weak_derivative f d v hf hd hder (𝓕 φ)
    _ = -∫ x, (𝓕 ψ) x*f x := by rw [SchwartzMap.lineDerivOp_fourier_eq]
    _ = -∫ x, ψ x*((Lp.fourierTransformₗᵢ E ℂ) (hf.toLp f)) x :=
      congrArg Neg.neg (fourier_pairing f hf ψ).symm
    _ = _ := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [ψ,SchwartzMap.smul_apply,SchwartzMap.smulLeftCLM_apply_apply ht,
        Complex.real_smul,smul_eq_mul]
      ring

theorem derivative_fourier (f d : E → ℂ) (v : E)
    (hf : MemLp f 2) (hd : MemLp d 2)
    (hder : ∀ x, HasLineDerivAt ℝ f (d x) x v) :
    (Lp.fourierTransformₗᵢ E ℂ) (hd.toLp d) =ᵐ[volume]
      fun x => (2*Real.pi*Complex.I)*(inner ℝ x v:ℂ)*
        ((Lp.fourierTransformₗᵢ E ℂ) (hf.toLp f)) x := by
  have hw : Continuous (fun x : E => (2*Real.pi*Complex.I)*(inner ℝ x v:ℂ)) := by fun_prop
  apply ae_eq_of_integral_contDiff_smul_eq
    ((Lp.memLp ((Lp.fourierTransformₗᵢ E ℂ) (hd.toLp d))).locallyIntegrable (by norm_num))
    (continuous_mul_locallyIntegrable _ hw _
      ((Lp.memLp ((Lp.fourierTransformₗᵢ E ℂ) (hf.toLp f))).locallyIntegrable (by norm_num)))
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  have hg' : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let φ : SchwartzMap E ℂ := hs'.toSchwartzMap hg'
  simpa [φ,Complex.real_smul] using derivative_fourier_pairing f d v hf hd hder φ

#print axioms weak_derivative
#print axioms fourier_pairing
#print axioms continuous_mul_locallyIntegrable
#print axioms derivative_fourier_pairing
#print axioms derivative_fourier

end
end UnifiedTheory.Audit.KFCausalL2DirectionalDerivative
