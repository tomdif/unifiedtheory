/- Exact polarization of the neutral linear response. The two quadratic
expectations use the actual output vectors y + L y and y - L y. No commutation of
the output translation and the linear coefficient is assumed. -/
import UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 350000

namespace UnifiedTheory.Audit.KFCausalNeutralOutputPolarization
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
open UnifiedTheory.Audit.KFCausalNeutralOutputLinearResponse
open UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator (translateLp_dual)

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem translated_compLp (B : Outputs →L[ℂ] Outputs) (r : ℝ) (y : Lp Outputs 2 μ) :
    (translated B r).compLp y = (translateOutput r).compLp (B.compLp y) := by
  apply Lp.ext
  filter_upwards [(translated B r).coeFn_compLp y,
    (translateOutput r).coeFn_compLp (B.compLp y),B.coeFn_compLp y] with x h1 h2 h3
  rw [h1,h2,h3]
  rfl

def plus (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) : Lp Outputs 2 μ :=
  y+(weightedLinear w).compLp y

def minus (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) : Lp Outputs 2 μ :=
  y-(weightedLinear w).compLp y

def expectation (r : ℝ) (y : Lp Outputs 2 μ) : ℂ :=
  inner ℂ y ((translateOutput r).compLp y)

theorem linearPair_polarization (w : Fin 8 → ℂ) (r : ℝ) (y : Lp Outputs 2 μ) :
    linearPair μ w r y = (expectation μ r (plus μ w y)-expectation μ r (minus μ w y))/2 := by
  simp only [linearPair,translated_compLp,← translateLp_dual,expectation,plus,minus]
  change _ = (inner ℂ (y+(weightedLinear w).compLp y)
    (((translateOutput r).compLpL 2 μ) (y+(weightedLinear w).compLp y))-
    inner ℂ (y-(weightedLinear w).compLp y)
    (((translateOutput r).compLpL 2 μ) (y-(weightedLinear w).compLp y)))/2
  simp only [map_add,map_sub,inner_add_left,inner_add_right,inner_sub_left,inner_sub_right]
  have he (z : Lp Outputs 2 μ) :
      ((translateOutput r).compLpL 2 μ) z = (translateOutput r).compLp z := rfl
  simp only [he]
  ring

theorem linearRate_polarization (w : Fin 8 → ℂ) (h v : ℝ) (y : Lp Outputs 2 μ) :
    linearRate μ w h v y = Complex.I*(v:ℂ)/2*
      (expectation μ (h*v) (plus μ w y)-expectation μ (h*v) (minus μ w y)) := by
  rw [linearRate,linearPair_polarization]
  ring

theorem total_mass_identity (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) :
    ‖plus μ w y‖^2+‖minus μ w y‖^2 = 2*‖y‖^2+2*‖(weightedLinear w).compLp y‖^2 := by
  have he := parallelogram_law_with_norm ℝ y ((weightedLinear w).compLp y)
  dsimp only [plus,minus]
  nlinarith

theorem total_mass_bound (w : Fin 8 → ℂ) (y : Lp Outputs 2 μ) :
    ‖plus μ w y‖^2+‖minus μ w y‖^2 ≤ 2*(1+‖weightedLinear w‖^2)*‖y‖^2 := by
  rw [total_mass_identity]
  have he := (weightedLinear w).norm_compLp_le y
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) |>.mpr he
  nlinarith

#print axioms translated_compLp
#print axioms linearPair_polarization
#print axioms linearRate_polarization
#print axioms total_mass_identity
#print axioms total_mass_bound
end
end UnifiedTheory.Audit.KFCausalNeutralOutputPolarization
