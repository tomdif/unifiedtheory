/- Strong derivatives are constructed by averaging actual unitary orbits.
No differentiability of the original state is assumed. -/
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

variable (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]

structure StrongUnitaryGroup where
  action : ℝ → H ≃ₗᵢ[ℂ] H
  initial : ∀ x, action 0 x = x
  compose : ∀ t u x, action u (action t x) = action (t+u) x
  continuous_orbit : ∀ x, Continuous (fun t => action t x)

variable {H} [CompleteSpace H] (U : StrongUnitaryGroup H)

def primitive (x : H) (a : ℝ) : H := ∫ t in 0..a, U.action t x

def average (x : H) (a : ℝ) : H := a⁻¹ • primitive U x a

theorem primitive_derivative (x : H) (a : ℝ) :
    HasDerivAt (primitive U x) (U.action a x) a :=
  intervalIntegral.integral_hasDerivAt_right
    ((U.continuous_orbit x).intervalIntegrable _ _)
    (U.continuous_orbit x).stronglyMeasurable.stronglyMeasurableAtFilter
    (U.continuous_orbit x).continuousAt

theorem action_primitive (x : H) (a t : ℝ) :
    U.action t (primitive U x a) = primitive U x (a+t)-primitive U x t := by
  change (U.action t : H →L[ℂ] H) (∫ s in 0..a, U.action s x) = _
  rw [← ContinuousLinearMap.intervalIntegral_comp_comm
    (U.action t : H →L[ℂ] H) ((U.continuous_orbit x).intervalIntegrable _ _)]
  change (∫ s in 0..a, U.action t (U.action s x)) = _
  simp only [U.compose]
  rw [intervalIntegral.integral_comp_add_right (fun s => U.action s x) t,zero_add]
  exact (intervalIntegral.integral_interval_sub_left
    ((U.continuous_orbit x).intervalIntegrable 0 (a+t))
    ((U.continuous_orbit x).intervalIntegrable 0 t)).symm

theorem action_average (x : H) (a t : ℝ) :
    U.action t (average U x a) = a⁻¹ • (primitive U x (a+t)-primitive U x t) := by
  rw [average,map_real_smul (U.action t) (U.action t).continuous,action_primitive]

theorem average_derivative (x : H) (a : ℝ) :
    HasDerivAt (fun t => U.action t (average U x a))
      (a⁻¹ • (U.action a x-x)) 0 := by
  have hp : HasDerivAt (fun t : ℝ => primitive U x (a+t)) (U.action a x) 0 := by
    simpa only [add_zero,one_smul] using
      (primitive_derivative U x (a+0)).scomp 0 ((hasDerivAt_id 0).const_add a)
  have hq : HasDerivAt (primitive U x) x 0 := by
    simpa only [U.initial] using primitive_derivative U x 0
  simpa only [action_average] using (hp.sub hq).const_smul a⁻¹

theorem average_tendsto (x : H) :
    Tendsto (average U x) (𝓝[≠] 0) (𝓝 x) := by
  have hh := (primitive_derivative U x 0).tendsto_slope_zero
  simpa only [average,primitive,zero_add,intervalIntegral.integral_same,sub_zero,U.initial]
    using hh

theorem averages_dense : Dense (Set.range (fun p : H × ℝ => average U p.1 p.2)) := by
  intro x
  exact mem_closure_of_tendsto (average_tendsto U x)
    (Filter.Eventually.of_forall fun a => ⟨(x,a),rfl⟩)

#print axioms primitive_derivative
#print axioms action_primitive
#print axioms action_average
#print axioms average_derivative
#print axioms average_tendsto
#print axioms averages_dense

end
end UnifiedTheory.Audit.KFCausalUnitaryOrbitAverage
