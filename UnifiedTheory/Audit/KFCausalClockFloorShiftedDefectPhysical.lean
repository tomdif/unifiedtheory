/- The existing shifted defect is physical multiplication by a bounded
clock function. The representative is derived through the actual weighted
coordinate unitary, so it can be used with unbounded physical field graphs. -/
import UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart
open UnifiedTheory.Audit.KFCausalClockFloorComplexDefect
open UnifiedTheory.Audit.KFCausalClockFloorLpCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorUnitaryCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectCoordinates
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator
open UnifiedTheory.Audit.KFCausalClockFloorFlow (coordinateHomeomorph)
open UnifiedTheory.Audit.KFCausalClockFloorShiftedDefect
open UnifiedTheory.Audit.KFCausalContractiveMultiplier

variable (ε : ℝ) (hε : 0 < ε) (hbar : ℝ) (hh : |hbar| ≤ 2*Real.pi*ε/3)

def physicalSymbol (x : Configuration) : ℂ :=
  complexDefect ε ((chart ε x.1:ℂ)+(-hbar/2:ℝ)*Complex.I)

include hε hh in
theorem physicalSymbol_continuous : Continuous (physicalSymbol ε hbar) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  have hc : Continuous (chart ε) := by unfold chart; fun_prop
  exact (complexDefect_analytic ε hε _
    (KFCausalClockFloorFullGaussian.third_strip_subset ε hε _
      (by simpa using shift_bound ε hbar hh))).continuousAt.comp
        (show ContinuousAt (fun x : Configuration => (chart ε x.1:ℂ)+(-hbar/2:ℝ)*Complex.I) x by fun_prop)

include hε hh in
theorem physicalSymbol_bound (x : Configuration) : ‖physicalSymbol ε hbar x‖ ≤ 2 :=
  complexDefect_norm_le_two ε hε _ (by simpa using shift_bound ε hbar hh)

theorem physicalSymbol_inverse (x : Configuration) :
    physicalSymbol ε hbar ((coordinateHomeomorph ε hε).symm x) =
      complexDefect ε ((x.1:ℂ)+(-hbar/2:ℝ)*Complex.I) := by
  have he : chart ε ((chartIso ε hε).symm x.1) = x.1 := (chartIso ε hε).apply_symm_apply x.1
  change complexDefect ε ((chart ε ((chartIso ε hε).symm x.1):ℂ)+(-hbar/2:ℝ)*Complex.I) = _
  rw [he]

def physicalOperator : Hilbert →L[ℂ] Hilbert :=
  (2:ℂ) • multiplyL (fun x => physicalSymbol ε hbar x/2)
    ((physicalSymbol_continuous ε hε hbar hh).div_const 2).measurable
    (fun x => by rw [norm_div]; norm_num; linarith [physicalSymbol_bound ε hε hbar hh x])

theorem physicalOperator_coe (f : Hilbert) :
    physicalOperator ε hε hbar hh f =ᵐ[volume] fun x => physicalSymbol ε hbar x*f x := by
  filter_upwards [Lp.coeFn_smul (2:ℂ) (multiplyL (fun x => physicalSymbol ε hbar x/2)
      ((physicalSymbol_continuous ε hε hbar hh).div_const 2).measurable _ f),
    multiplyL_coe (fun x => physicalSymbol ε hbar x/2)
      ((physicalSymbol_continuous ε hε hbar hh).div_const 2).measurable
      (fun x => by rw [norm_div]; norm_num; linarith [physicalSymbol_bound ε hε hbar hh x]) f] with x hs hm
  change ((2:ℂ) • multiplyL _ _ _ f) x = _
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,hm]
  ring

theorem inverse_coordinates_coe (f : Hilbert) :
    (coordinates ε hε).symm (physicalOperator ε hε hbar hh f) =ᵐ[volume]
      fun x => complexDefect ε ((x.1:ℂ)+(-hbar/2:ℝ)*Complex.I)*((coordinates ε hε).symm f) x := by
  filter_upwards [coordinates_inverse_coe ε hε (physicalOperator ε hε hbar hh f),
    coordinates_inverse_coe ε hε f,
    (coordinate_inverse_quasiMeasurePreserving ε hε).ae (physicalOperator_coe ε hε hbar hh f)] with x hx hy hd
  rw [hx,hy]
  unfold inverseFunction
  rw [hd,physicalSymbol_inverse]
  ring

theorem straightening_coe (f : Hilbert) :
    straightening ε hε (physicalOperator ε hε hbar hh f) =ᵐ[volume]
      fun x => symbol ε hbar x*(straightening ε hε f) x := by
  filter_upwards [euclideanPullback_coe ((coordinates ε hε).symm (physicalOperator ε hε hbar hh f)),
    euclideanPullback_coe ((coordinates ε hε).symm f),
    split_preserves_volume.quasiMeasurePreserving.ae (inverse_coordinates_coe ε hε hbar hh f)] with x hx hy hd
  change (euclideanPullback ((coordinates ε hε).symm (physicalOperator ε hε hbar hh f))) x = _
  rw [hx]
  change ((coordinates ε hε).symm (physicalOperator ε hε hbar hh f)) (split x) = _
  rw [hd]
  change _ = symbol ε hbar x*(euclideanPullback ((coordinates ε hε).symm f)) x
  rw [hy,split_apply]
  rfl

theorem physicalOperator_eq_shiftedDefect : physicalOperator ε hε hbar hh = shiftedDefect ε hε hbar hh := by
  apply ContinuousLinearMap.ext
  intro f
  apply (straightening ε hε).injective
  exact Lp.ext ((straightening_coe ε hε hbar hh f).trans (shiftedDefect_coe ε hε hbar hh f).symm)

theorem shiftedDefect_physical_coe (f : Hilbert) :
    shiftedDefect ε hε hbar hh f =ᵐ[volume] fun x => physicalSymbol ε hbar x*f x := by
  rw [← physicalOperator_eq_shiftedDefect]
  exact physicalOperator_coe ε hε hbar hh f

theorem shiftedDefect_norm_le_two (f : Hilbert) : ‖shiftedDefect ε hε hbar hh f‖ ≤ 2*‖f‖ :=
  (shiftedDefect_norm_bound ε hε hbar hh f).trans
    (mul_le_mul_of_nonneg_left (defectOperator_norm_le ε hε f) (by norm_num))

#print axioms physicalSymbol_continuous
#print axioms physicalSymbol_bound
#print axioms physicalSymbol_inverse
#print axioms physicalOperator_coe
#print axioms inverse_coordinates_coe
#print axioms straightening_coe
#print axioms physicalOperator_eq_shiftedDefect
#print axioms shiftedDefect_physical_coe
#print axioms shiftedDefect_norm_le_two

end
end UnifiedTheory.Audit.KFCausalClockFloorShiftedDefectPhysical
