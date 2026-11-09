/- Positive force-output measures form measurable time kernels along
every continuous L2 output curve. Their time integrals are actual finite
measures, with derived mass and test identities. -/
import UnifiedTheory.Audit.KFCausalNeutralOutputSpectralCut
import UnifiedTheory.Audit.KFCausalNeutralForceMeasure
import UnifiedTheory.Audit.KFCausalFiniteKernelInterval

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
noncomputable section
open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput (Outputs)
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds (weightedLinear)
open UnifiedTheory.Audit.KFCausalNeutralOutputPolarization (plus minus)
open UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure (averagedLaw averagedLaw_mass)
open UnifiedTheory.Audit.KFCausalNeutralOutputSpectralCut (averaged_measurable)
open UnifiedTheory.Audit.KFCausalNeutralForceMeasure
open UnifiedTheory.Audit.KFCausalFiniteKernelInterval

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (h : ℝ) (w : Fin 8 → ℂ)
  (y : ℝ → Lp Outputs 2 μ) (hy : Continuous y)

def positiveKernel : Kernel ℝ ℝ :=
  ⟨fun t => (fromOutput μ h w (y t)).positive,
    (averaged_measurable μ h).comp
      (hy.add (((weightedLinear w).compLpL 2 μ).continuous.comp hy)).borel_measurable⟩

def negativeKernel : Kernel ℝ ℝ :=
  ⟨fun t => (fromOutput μ h w (y t)).negative,
    (averaged_measurable μ h).comp
      (hy.sub (((weightedLinear w).compLpL 2 μ).continuous.comp hy)).borel_measurable⟩

instance positiveKernel_finite (t : ℝ) : IsFiniteMeasure (positiveKernel μ h w y hy t) :=
  (fromOutput μ h w (y t)).positive_finite

instance negativeKernel_finite (t : ℝ) : IsFiniteMeasure (negativeKernel μ h w y hy t) :=
  (fromOutput μ h w (y t)).negative_finite

theorem positive_mass_continuous :
    Continuous (fun t => (positiveKernel μ h w y hy t).real Set.univ) := by
  change Continuous (fun t => (averagedLaw μ h (plus μ w (y t))).real Set.univ)
  simp only [Measure.real,averagedLaw_mass,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  exact (hy.add (((weightedLinear w).compLpL 2 μ).continuous.comp hy)).norm.pow 2

theorem negative_mass_continuous :
    Continuous (fun t => (negativeKernel μ h w y hy t).real Set.univ) := by
  change Continuous (fun t => (averagedLaw μ h (minus μ w (y t))).real Set.univ)
  simp only [Measure.real,averagedLaw_mass,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  exact (hy.sub (((weightedLinear w).compLpL 2 μ).continuous.comp hy)).norm.pow 2

def intervalPair (b c : ℝ) : FluxPair where
  positive := integrated (positiveKernel μ h w y hy) b c
  negative := integrated (negativeKernel μ h w y hy) b c
  positive_finite := integrated_finite _ (positive_mass_continuous μ h w y hy) b c
  negative_finite := integrated_finite _ (negative_mass_continuous μ h w y hy) b c

theorem intervalPair_mass (b c : ℝ) :
    (intervalPair μ h w y hy b c).mass = ∫ t in Set.Icc b c, (fromOutput μ h w (y t)).mass := by
  change (integrated (positiveKernel μ h w y hy) b c).real Set.univ+
    (integrated (negativeKernel μ h w y hy) b c).real Set.univ = _
  rw [integrated_real_mass _ (positive_mass_continuous μ h w y hy),
    integrated_real_mass _ (negative_mass_continuous μ h w y hy),
    ← integral_add (positive_mass_continuous μ h w y hy).integrableOn_Icc
      (negative_mass_continuous μ h w y hy).integrableOn_Icc]
  rfl

theorem intervalPair_evaluate (b c : ℝ) (q : ℝ →ᵇ ℂ) :
    (intervalPair μ h w y hy b c).evaluate q =
      ∫ t in Set.Icc b c, (fromOutput μ h w (y t)).evaluate q := by
  simp only [FluxPair.evaluate,intervalPair]
  rw [integrated_test _ (positive_mass_continuous μ h w y hy),
    integrated_test _ (negative_mass_continuous μ h w y hy),
    ← integral_sub (integrated_test_integrable _ (positive_mass_continuous μ h w y hy) b c q)
      (integrated_test_integrable _ (negative_mass_continuous μ h w y hy) b c q),
    ← integral_div]
  rfl

theorem intervalPair_fourier (b c v : ℝ) :
    (intervalPair μ h w y hy b c).fourier v =
      ∫ t in Set.Icc b c, (fromOutput μ h w (y t)).fourier v := by
  simpa only [fourier_evaluate] using intervalPair_evaluate μ h w y hy b c (innerProbChar v)

theorem intervalPair_mass_bound (b c C : ℝ) (hbc : b ≤ c)
    (hb : ∀ t ∈ Set.Icc b c, (fromOutput μ h w (y t)).mass ≤ C) :
    (intervalPair μ h w y hy b c).mass ≤ (c-b)*C := by
  rw [intervalPair_mass]
  have hm : Continuous (fun t => (fromOutput μ h w (y t)).mass) :=
    (positive_mass_continuous μ h w y hy).add (negative_mass_continuous μ h w y hy)
  calc
    _ ≤ ∫ _t in Set.Icc b c, C := by
      apply integral_mono_ae hm.integrableOn_Icc (integrable_const C)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      exact hb t ht
    _ = _ := by rw [setIntegral_const,Real.volume_real_Icc_of_le hbc,smul_eq_mul]

theorem intervalPair_rate (b c v : ℝ) (hbc : b ≤ c) :
    Complex.I*(v:ℂ)*(intervalPair μ h w y hy b c).fourier v =
      ∫ t in b..c, KFCausalNeutralOutputLinearResponse.linearRate μ w h v (y t) := by
  rw [intervalPair_fourier,← integral_const_mul,integral_Icc_eq_integral_Ioc,
    intervalIntegral.integral_of_le hbc]
  apply integral_congr_ae
  filter_upwards [] with t
  exact (linearRate_fourier μ h v w (y t)).symm

#print axioms positiveKernel
#print axioms negativeKernel
#print axioms positive_mass_continuous
#print axioms negative_mass_continuous
#print axioms intervalPair_mass
#print axioms intervalPair_evaluate
#print axioms intervalPair_fourier
#print axioms intervalPair_mass_bound
#print axioms intervalPair_rate
end
end UnifiedTheory.Audit.KFCausalNeutralOutputTimeKernel
