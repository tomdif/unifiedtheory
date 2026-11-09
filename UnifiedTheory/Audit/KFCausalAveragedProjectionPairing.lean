/- Zero-period projection is symmetric for the actual averaged energy
pairing. This uses the adjoint of constant L2 functions and bounded
form-space averaging, without commuting an unbounded operator and an
integral. -/
import UnifiedTheory.Audit.KFCausalAveragedFormProjection

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAveragedProjectionPairing
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalProbabilityL2Mean
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
open UnifiedTheory.Audit.KFCausalAveragedFormSpace
open UnifiedTheory.Audit.KFCausalAveragedFormProjection
open UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage

theorem const_mean_pairing {Ω K : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K] (v w : Lp K 2 μ) :
    inner ℂ (Lp.const 2 μ (mean μ v)) w = inner ℂ v (Lp.const 2 μ (mean μ w)) := by
  calc
    _ = inner ℂ (mean μ v) (mean μ w) :=
      ((Lp.constL 2 μ ℂ : K →L[ℂ] Lp K 2 μ).adjoint_inner_right _ _).symm
    _ = _ := (Lp.constL 2 μ ℂ : K →L[ℂ] Lp K 2 μ).adjoint_inner_left _ _

variable {H E K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
  (U : StrongUnitaryGroup H) (T : ℝ) (hT : 0 < T)
  (hperiod : ∀ f, U.action T f = f) (J : E →L[ℂ] H) (A : E →L[ℂ] K)

theorem project_output_eq_const_mean (u : FormSpace U T J) :
    averagedOutput U T J A (project U T hT hperiod J u) =
      Lp.const 2 angleMeasure (mean angleMeasure (averagedOutput U T J A u)) := by
  rw [project_output]
  exact congrArg (Lp.const 2 angleMeasure) (mean_comp angleMeasure A (sectionMap U T J u)).symm

theorem project_energy_pairing (u v : FormSpace U T J) :
    inner ℂ (averagedOutput U T J A (project U T hT hperiod J u)) (averagedOutput U T J A v) =
      inner ℂ (averagedOutput U T J A u) (averagedOutput U T J A (project U T hT hperiod J v)) := by
  rw [project_output_eq_const_mean,project_output_eq_const_mean]
  exact const_mean_pairing angleMeasure _ _

#print axioms const_mean_pairing
#print axioms project_output_eq_const_mean
#print axioms project_energy_pairing

end
end UnifiedTheory.Audit.KFCausalAveragedProjectionPairing
