/- Integrating out neutral momentum does not cure the clock divergence.
The result concerns the explicit density prescription, not a heat-operator trace. -/
import UnifiedTheory.Audit.KFCausalFreeThermalDensity

set_option autoImplicit false
set_option Elab.async false

namespace UnifiedTheory.Audit.KFCausalThermalDensityClockObstruction
noncomputable section
open MeasureTheory
open KFCausalFreeThermalDensity KFCausalFreeClockThermalObstruction
open KFCausalFreeChargedPartition
open KFCausalClockFloorFlow (clock)

def lowerDensity (ε h t β : ℝ) : ℝ :=
  Real.exp (-β*groundBound ε h t 0)*
    Real.sqrt (Real.pi/(β*(2*Real.pi*h)^2/(2*ε)))

theorem lowerDensity_positive (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t β : ℝ) (hβ : 0 < β) : 0 < lowerDensity ε h t β := by
  unfold lowerDensity
  positivity

theorem density_lower_on_halfline (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : s ≤ 0) :
    lowerDensity ε h t β ≤ density ε h t s β := by
  have hc : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hr : gaussianRate ε h s β ≤ β*(2*Real.pi*h)^2/(2*ε) := by
    exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
  have hg := gaussianRate_positive ε hε h hh s β hβ
  have hsqrt := Real.sqrt_le_sqrt (div_le_div_of_nonneg_left Real.pi_pos.le hg hr)
  have hp := (ground_boltzmann_lower_bound ε hε h hh t 0 β hβ s hs).trans
    (ground_le_partition ε hε h hh t s 0 β hβ)
  rw [density_eq ε hε h hh t s β hβ]
  exact mul_le_mul hp hsqrt (Real.sqrt_nonneg _) ((Real.exp_pos _).le.trans hp)

theorem density_not_integrable_clock (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t β : ℝ) (hβ : 0 < β) : ¬ Integrable (fun s => density ε h t s β) volume :=
  not_integrable_of_positive_halfline_bound _ _
    (lowerDensity_positive ε hε h hh t β hβ)
    (density_lower_on_halfline ε hε h hh t β hβ)

#print axioms lowerDensity_positive
#print axioms density_lower_on_halfline
#print axioms density_not_integrable_clock
end
end UnifiedTheory.Audit.KFCausalThermalDensityClockObstruction
