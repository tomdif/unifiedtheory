/- A concrete finite signed force response, represented by two positive
measures. Its action is half their difference. Both measures are constructed
from the actual output vectors; no classical force closure is a premise. -/
import UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralForceMeasure
noncomputable section
open MeasureTheory BoundedContinuousFunction
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
open UnifiedTheory.Audit.KFCausalNeutralOutputPolarization
open UnifiedTheory.Audit.KFCausalNeutralOutputBornMeasure

structure FluxPair where
  positive : Measure ℝ
  negative : Measure ℝ
  positive_finite : IsFiniteMeasure positive
  negative_finite : IsFiniteMeasure negative

attribute [instance] FluxPair.positive_finite FluxPair.negative_finite

def FluxPair.mass (F : FluxPair) : ℝ := F.positive.real Set.univ+F.negative.real Set.univ

def FluxPair.evaluate (F : FluxPair) (q : ℝ →ᵇ ℂ) : ℂ :=
  ((∫ x, q x ∂F.positive)-(∫ x, q x ∂F.negative))/2

def FluxPair.fourier (F : FluxPair) (v : ℝ) : ℂ :=
  (charFun F.positive v-charFun F.negative v)/2

theorem evaluate_bound (F : FluxPair) (q : ℝ →ᵇ ℂ) :
    ‖F.evaluate q‖ ≤ F.mass/2*‖q‖ := by
  have hp := q.norm_integral_le_mul_norm F.positive
  have hn := q.norm_integral_le_mul_norm F.negative
  have hs := norm_sub_le (∫ x, q x ∂F.positive) (∫ x, q x ∂F.negative)
  have htwo : ‖(2 : ℂ)‖ = (2 : ℝ) := by norm_num
  simp only [FluxPair.evaluate,norm_div,htwo]
  dsimp only [FluxPair.mass]
  nlinarith

theorem fourier_evaluate (F : FluxPair) (v : ℝ) :
    F.fourier v = F.evaluate (BoundedContinuousFunction.innerProbChar v) := by
  simp only [FluxPair.fourier,FluxPair.evaluate,charFun_eq_integral_innerProbChar]

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

def fromOutput (h : ℝ) (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) : FluxPair where
  positive := averagedLaw μ h (plus μ w y)
  negative := averagedLaw μ h (minus μ w y)
  positive_finite := averagedLaw_finite μ h _
  negative_finite := averagedLaw_finite μ h _

theorem fromOutput_mass (h : ℝ) (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) :
    (fromOutput μ h w y).mass = 2*‖y‖^2+2*‖(weightedLinear w).compLp y‖^2 := by
  simp only [FluxPair.mass,fromOutput,Measure.real,averagedLaw_mass,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  exact total_mass_identity μ w y

theorem fromOutput_mass_bound (h : ℝ) (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) :
    (fromOutput μ h w y).mass ≤ 2*(1+‖weightedLinear w‖^2)*‖y‖^2 := by
  simp only [FluxPair.mass,fromOutput,Measure.real,averagedLaw_mass,
    ENNReal.toReal_ofReal (sq_nonneg _)]
  exact total_mass_bound μ w y

theorem linearRate_fourier (h v : ℝ) (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) :
    KFCausalNeutralOutputLinearResponse.linearRate μ w h v y =
      Complex.I*(v:ℂ)*(fromOutput μ h w y).fourier v := by
  rw [linearRate_polarization]
  simp only [FluxPair.fourier,fromOutput,averagedLaw_characteristic]
  ring

theorem expectation_continuous (r : ℝ) : Continuous (expectation μ r) :=
  continuous_id.inner (𝕜 := ℂ) ((translateOutput r).compLpL 2 μ).continuous

theorem positive_characteristic_continuous (h v : ℝ) (w : Fin 8 → ℂ) :
    Continuous (fun y : Lp Outputs 2 μ => charFun (fromOutput μ h w y).positive v) := by
  simp only [fromOutput,averagedLaw_characteristic]
  exact (expectation_continuous μ (h*v)).comp
    (continuous_id.add ((weightedLinear w).compLpL 2 μ).continuous)

theorem negative_characteristic_continuous (h v : ℝ) (w : Fin 8 → ℂ) :
    Continuous (fun y : Lp Outputs 2 μ => charFun (fromOutput μ h w y).negative v) := by
  simp only [fromOutput,averagedLaw_characteristic]
  exact (expectation_continuous μ (h*v)).comp
    (continuous_id.sub ((weightedLinear w).compLpL 2 μ).continuous)

theorem fourier_continuous (h v : ℝ) (w : Fin 8 → ℂ) :
    Continuous (fun y : Lp Outputs 2 μ => (fromOutput μ h w y).fourier v) :=
  ((positive_characteristic_continuous μ h v w).sub
    (negative_characteristic_continuous μ h v w)).div_const 2

#print axioms evaluate_bound
#print axioms fourier_evaluate
#print axioms fromOutput_mass
#print axioms fromOutput_mass_bound
#print axioms linearRate_fourier
#print axioms expectation_continuous
#print axioms positive_characteristic_continuous
#print axioms negative_characteristic_continuous
#print axioms fourier_continuous
end
end UnifiedTheory.Audit.KFCausalNeutralForceMeasure
