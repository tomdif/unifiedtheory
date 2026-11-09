/- The actual shifted physical output lies in the inverse half-clock
domain, with a constructed L2 image and the exact multiplication graph. -/
import UnifiedTheory.Audit.KFCausalShiftedInverseClock
import UnifiedTheory.Audit.KFCausalShiftedProductAction
import UnifiedTheory.Audit.KFCausalPhysicalClockPowers

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalShiftedInverseClockAction
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalEuclideanClockSplit
open UnifiedTheory.Audit.KFCausalClockTransverseProducts
open UnifiedTheory.Audit.KFCausalCoupledProductDomain
open UnifiedTheory.Audit.KFCausalCoupledLpCoordinates
open UnifiedTheory.Audit.KFCausalCoupledCoordinateHomeomorph
open UnifiedTheory.Audit.KFCausalShiftedDampedScalar
open UnifiedTheory.Audit.KFCausalShiftedProductAction
open UnifiedTheory.Audit.KFCausalShiftedInverseClock
open UnifiedTheory.Audit.KFCausalPhysicalClockPowers

def inverseShiftedState (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) : Hilbert :=
  productState ε hε (inverseHalfShift ε a p y hε) ψ (inverseHalfShift_memLp ε a p y hε ha hy) hψ

theorem inverseShifted_function (ε a p y : ℝ) (hε : 0 < ε) (ψ : TailSpace → ℂ) :
    weightedFunction ε hε (configurationProduct (inverseHalfShift ε a p y hε) ψ) =
      fun z => (Real.exp (-(1/2)*z.1):ℂ)*shiftedFunction ε a p y hε ψ z := by
  funext z
  have hs : (chartIso ε hε).symm (chart ε z.1)=z.1 := (chartIso ε hε).symm_apply_apply _
  simp only [shiftedFunction,weightedFunction,configurationProduct,
    coordinateHomeomorph_apply,inverseHalfShift,hs]
  ring

theorem inverseShiftedState_coe (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    inverseShiftedState ε a p y hε ha hy ψ hψ =ᵐ[volume]
      fun z => (Real.exp (-(1/2)*z.1):ℂ)*shiftedFunction ε a p y hε ψ z := by
  rw [← inverseShifted_function]
  exact productState_coe ε hε _ ψ (inverseHalfShift_memLp ε a p y hε ha hy) hψ

theorem shifted_inverse_clock_graph (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    (shiftedState ε a p y hε ha hy ψ hψ,inverseShiftedState ε a p y hε ha hy ψ hψ) ∈
      (clockPower (-(1/2))).graph := by
  apply (clockPower_graph _ _ _).mpr
  filter_upwards [inverseShiftedState_coe ε a p y hε ha hy ψ hψ,
    shiftedState_coe ε a p y hε ha hy ψ hψ] with z hi hs
  rw [hi,hs]

theorem shifted_inverse_clock_domain (ε a p y : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (hy : |y| ≤ Real.pi*ε/2) (ψ : TailSpace → ℂ) (hψ : MemLp ψ 2) :
    shiftedState ε a p y hε ha hy ψ hψ ∈ (clockPower (-(1/2))).domain :=
  LinearPMap.mem_domain_of_mem_graph (shifted_inverse_clock_graph ε a p y hε ha hy ψ hψ)

#print axioms inverseShifted_function
#print axioms inverseShiftedState_coe
#print axioms shifted_inverse_clock_graph
#print axioms shifted_inverse_clock_domain

end
end UnifiedTheory.Audit.KFCausalShiftedInverseClockAction
