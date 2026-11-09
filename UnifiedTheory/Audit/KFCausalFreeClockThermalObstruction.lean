/- The charged-fiber sum is finite, but its unregulated clock integral is not.
This is an integrability obstruction, not an asserted Hilbert-space trace formula. -/
import UnifiedTheory.Audit.KFCausalFreeChargedPartition
import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalFreeClockThermalObstruction
noncomputable section
open MeasureTheory
open KFCausalFreeChargedPartition
open KFCausalClockFloorFlow (clock)

def groundBound (ε h t ξ : ℝ) : ℝ :=
  (ε+1)/2+(2*Real.pi*h)^2*ξ^2/(2*ε)+2*h*Real.exp t/ε

theorem ground_le_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t ξ s : ℝ) (hs : s ≤ 0) : ground ε h t s ξ ≤ groundBound ε h t ξ := by
  have hc : ε ≤ clock ε s := by unfold clock; linarith [Real.exp_pos s]
  have hc' : clock ε s ≤ ε+1 := by
    unfold clock
    linarith [Real.exp_le_one_iff.mpr hs]
  have hp : 0 ≤ (2*Real.pi*h)^2*ξ^2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hq : 0 ≤ 2*h*Real.exp t := by positivity
  have hd := div_le_div_of_nonneg_left hp (by positivity : 0 < 2*ε)
    (show 2*ε ≤ 2*clock ε s by linarith)
  have hd' := div_le_div_of_nonneg_left hq hε hc
  unfold ground groundBound gap
  linarith

theorem ground_boltzmann_lower_bound (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t ξ β : ℝ) (hβ : 0 < β) (s : ℝ) (hs : s ≤ 0) :
    Real.exp (-β*groundBound ε h t ξ) ≤ Real.exp (-β*ground ε h t s ξ) := by
  apply Real.exp_le_exp.mpr
  exact mul_le_mul_of_nonpos_left (ground_le_bound ε hε h hh t ξ s hs) (by linarith)

theorem not_integrable_of_positive_halfline_bound (f : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hf : ∀ s ≤ 0, a ≤ f s) : ¬ Integrable f volume := by
  intro hi
  have hc : IntegrableOn (fun _ : ℝ => a) (Set.Iic 0) volume :=
    hi.integrableOn.mono' aestronglyMeasurable_const
      ((ae_restrict_mem measurableSet_Iic).mono fun s hs => by
        simpa only [Real.norm_eq_abs,abs_of_pos ha] using hf s hs)
  have he := (integrableOn_const_iff (C := a)).mp hc
  simpa [Real.volume_Iic,ha.ne'] using he

theorem ground_not_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t ξ β : ℝ) (hβ : 0 < β) :
    ¬ Integrable (fun s => Real.exp (-β*ground ε h t s ξ)) volume :=
  not_integrable_of_positive_halfline_bound _ _ (Real.exp_pos _)
    (ground_boltzmann_lower_bound ε hε h hh t ξ β hβ)

theorem ground_le_partition (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t s ξ β : ℝ) (hβ : 0 < β) :
    Real.exp (-β*ground ε h t s ξ) ≤ partition ε h t s ξ β := by
  have hs := (partition_hasSum ε hε h hh t s ξ β hβ).summable
  have he := hs.le_tsum 0 (fun p _ => by positivity)
  simpa [partition,KFCausalCircularZeroLevelCounting.level_card,levelEnergy] using he

theorem partition_not_integrable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hh : 0 < h)
    (t ξ β : ℝ) (hβ : 0 < β) :
    ¬ Integrable (fun s => partition ε h t s ξ β) volume := by
  apply not_integrable_of_positive_halfline_bound _ _ (Real.exp_pos (-β*groundBound ε h t ξ))
  intro s hs
  exact (ground_boltzmann_lower_bound ε hε h hh t ξ β hβ s hs).trans
    (ground_le_partition ε hε h hh t s ξ β hβ)

#print axioms ground_not_integrable
#print axioms partition_not_integrable
end
end UnifiedTheory.Audit.KFCausalFreeClockThermalObstruction
