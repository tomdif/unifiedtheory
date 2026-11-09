/- Complementary second moments weighted by the inverse clock and the
ordinary clock moment together control actual complementary-coordinate
tail probabilities, without unweighted second-moment assumptions. -/
import UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalClockFloorClockHalf (clockHalf)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (clock_positive)
open UnifiedTheory.Audit.KFCausalClockFloorDualClock (dualClock_integral dualClock_integrable)
open UnifiedTheory.Audit.KFCausalComplementaryChargeSymbol
open UnifiedTheory.Audit.KFCausalClockFloorAveragedComplementaryMoment (complementaryMoment)

theorem complementarySquare_continuous (h : ℝ) (i : Fin 2) : Continuous (complementarySquare h i) := by
  unfold complementarySquare complementaryMomentum complementaryPosition neutralTerm neutralMomentum
  fin_cases i <;> simp only [Matrix.cons_val_zero',Matrix.cons_val_succ'] <;> fun_prop

def complementaryTail (h R : ℝ) (i : Fin 2) (f : Hilbert) : ℝ :=
  ∫ x : Joint 5 1 in {x | R^2 ≤ complementarySquare h i x}, ‖(dualPhysical f) x‖^2

theorem complementaryTail_nonnegative (h R : ℝ) (i : Fin 2) (f : Hilbert) : 0 ≤ complementaryTail h R i f :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem complementaryTail_bound (ε : ℝ) (hε : 0 < ε) (h R : ℝ) (i : Fin 2) (f g : Hilbert)
    (hg : (f,g) ∈ (clockHalf ε).graph)
    (hi : Integrable (fun x => complementaryWeight ε h i x*‖(dualPhysical f) x‖^2)) :
    2*R*complementaryTail h R i f ≤ ‖g‖^2+complementaryMoment ε h i f := by
  have hs : MeasurableSet {x : Joint 5 1 | R^2 ≤ complementarySquare h i x} :=
    measurableSet_le measurable_const (complementarySquare_continuous h i).measurable
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable (dualPhysical f))).mp
    (Lp.memLp (dualPhysical f))
  rw [← dualClock_integral ε hε f g hg,complementaryMoment,complementaryTail,← integral_indicator hs,
    ← integral_const_mul,← integral_add (dualClock_integrable ε hε f g hg) hi]
  apply integral_mono_ae ((hf.indicator hs).const_mul _) ((dualClock_integrable ε hε f g hg).add hi)
  filter_upwards [] with x
  simp only [Pi.add_apply]
  by_cases hx : R^2 ≤ complementarySquare h i x
  · rw [Set.indicator_of_mem (show x ∈ {x : Joint 5 1 | R^2 ≤ complementarySquare h i x} from hx)]
    have hc := clock_positive ε (x (.inr 0)) hε.le
    have hw : clock ε (x (.inr 0))*complementaryWeight ε h i x = complementarySquare h i x := by
      unfold complementaryWeight
      exact mul_div_cancel₀ _ hc.ne'
    have hp : 2*R ≤ clock ε (x (.inr 0))+complementaryWeight ε h i x := by
      have hsq := sq_nonneg (clock ε (x (.inr 0))-R)
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg ‖(dualPhysical f) x‖)]
  · rw [Set.indicator_of_notMem (show x ∉ {x : Joint 5 1 | R^2 ≤ complementarySquare h i x} from hx),mul_zero]
    exact add_nonneg (mul_nonneg (clock_positive ε _ hε.le).le (sq_nonneg _))
      (mul_nonneg (complementaryWeight_nonnegative ε hε h i x) (sq_nonneg _))

#print axioms complementarySquare_continuous
#print axioms complementaryTail_nonnegative
#print axioms complementaryTail_bound

end
end UnifiedTheory.Audit.KFCausalClockFloorComplementaryTail
