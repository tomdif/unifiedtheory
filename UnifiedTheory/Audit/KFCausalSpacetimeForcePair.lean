/- Finite spacetime force pairs and their construction from the actual
positive output-time kernels. Interval slices recover the existing forces. -/
import UnifiedTheory.Audit.KFCausalFiniteKernelSpacetime
import UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalSpacetimeForcePair
noncomputable section
open MeasureTheory BoundedContinuousFunction Set
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure (FluxPair fromOutput)
open UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
open UnifiedTheory.Audit.KFCausalFiniteKernelSpacetime

structure Pair where
  positive : Measure (ℝ × ℝ)
  negative : Measure (ℝ × ℝ)
  positive_finite : IsFiniteMeasure positive
  negative_finite : IsFiniteMeasure negative

attribute [instance] Pair.positive_finite Pair.negative_finite

def Pair.mass (F : Pair) : ℝ := F.positive.real univ+F.negative.real univ

def Pair.evaluate (F : Pair) (q : (ℝ × ℝ) →ᵇ ℂ) : ℂ :=
  ((∫ z, q z ∂F.positive)-(∫ z, q z ∂F.negative))/2

def Pair.slice (F : Pair) (b c : ℝ) : FluxPair where
  positive := (F.positive.restrict (Icc b c ×ˢ univ)).map Prod.snd
  negative := (F.negative.restrict (Icc b c ×ˢ univ)).map Prod.snd
  positive_finite := inferInstance
  negative_finite := inferInstance

theorem evaluate_bound (F : Pair) (q : (ℝ × ℝ) →ᵇ ℂ) :
    ‖F.evaluate q‖ ≤ F.mass/2*‖q‖ := by
  have hp := q.norm_integral_le_mul_norm F.positive
  have hn := q.norm_integral_le_mul_norm F.negative
  have hs := norm_sub_le (∫ z, q z ∂F.positive) (∫ z, q z ∂F.negative)
  simp only [Pair.evaluate,norm_div,Complex.norm_ofNat]
  dsimp only [Pair.mass]
  nlinarith

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : ℝ) (w : Fin 8 → ℂ)
  (y : ℝ → Lp KFCausalNeutralTranslationOutput.Outputs 2 μ) (hy : Continuous y)

def fromCurve (b c : ℝ) : Pair where
  positive := spacetime (positiveKernel μ h w y hy) b c
  negative := spacetime (negativeKernel μ h w y hy) b c
  positive_finite := spacetime_finite _ (positive_mass_continuous μ h w y hy) b c
  negative_finite := spacetime_finite _ (negative_mass_continuous μ h w y hy) b c

theorem fromCurve_mass (b c : ℝ) :
    (fromCurve μ h w y hy b c).mass = (intervalPair μ h w y hy b c).mass := by
  simp only [Pair.mass,fromCurve,FluxPair.mass,intervalPair,Measure.real]
  rw [spacetime_mass _ (positive_mass_continuous μ h w y hy),
    spacetime_mass _ (negative_mass_continuous μ h w y hy)]

theorem fromCurve_slice (b c u v : ℝ) (hu : b ≤ u) (hv : v ≤ c) :
    ((fromCurve μ h w y hy b c).slice u v).positive = (intervalPair μ h w y hy u v).positive ∧
    ((fromCurve μ h w y hy b c).slice u v).negative = (intervalPair μ h w y hy u v).negative :=
  ⟨spacetime_slice _ (positive_mass_continuous μ h w y hy) b c u v hu hv,
    spacetime_slice _ (negative_mass_continuous μ h w y hy) b c u v hu hv⟩

theorem fromCurve_positive_test (b c : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) :
    (∫ z, q z ∂(fromCurve μ h w y hy b c).positive) =
      ∫ t in Icc b c, ∫ p, q (t,p) ∂(fromOutput μ h w (y t)).positive :=
  spacetime_test _ (positive_mass_continuous μ h w y hy) b c q

theorem fromCurve_negative_test (b c : ℝ) (q : (ℝ × ℝ) →ᵇ ℂ) :
    (∫ z, q z ∂(fromCurve μ h w y hy b c).negative) =
      ∫ t in Icc b c, ∫ p, q (t,p) ∂(fromOutput μ h w (y t)).negative :=
  spacetime_test _ (negative_mass_continuous μ h w y hy) b c q

theorem fromCurve_time_bound (b c C : ℝ)
    (hb : ∀ t ∈ Icc b c, (fromOutput μ h w (y t)).mass ≤ C)
    (A : Set ℝ) (hA : MeasurableSet A) :
    (fromCurve μ h w y hy b c).positive (A ×ˢ univ)+
      (fromCurve μ h w y hy b c).negative (A ×ˢ univ) ≤
      ENNReal.ofReal C * volume (A ∩ Icc b c) :=
  spacetime_time_sum_bound _ (positive_mass_continuous μ h w y hy) b c _
    (negative_mass_continuous μ h w y hy) C hb A hA

#print axioms evaluate_bound
#print axioms fromCurve_mass
#print axioms fromCurve_slice
#print axioms fromCurve_positive_test
#print axioms fromCurve_negative_test
#print axioms fromCurve_time_bound
end
end UnifiedTheory.Audit.KFCausalSpacetimeForcePair
