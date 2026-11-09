/- The averaged field-slope correction is the actual maximal real
multiplier applied to the averaged path, with an a.e. representative. -/
import UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalProjectedFieldSlopeMultiplier
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalDisplacedStructuredResponse (StructuredState)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (fieldSlope powerSlope)
open UnifiedTheory.Audit.KFCausalPolynomialImaginaryShearCurve (Weight slopeWeight)
open UnifiedTheory.Audit.KFCausalImaginaryShearPathDomain (Interval)
open UnifiedTheory.Audit.KFCausalStructuredShearMean (meanInputAt)
open UnifiedTheory.Audit.KFCausalProjectedMatterShearGraphs (meanWeightedInput)
open UnifiedTheory.Audit.KFCausalUnitaryRealMultiplier (realPullback realPullback_graph)

def realSlope (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) : ℝ :=
  ((i.val+1:ℕ):ℝ)*(l x.2)^i.val*(fieldSlope l x.2)

theorem realSlope_coe (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (x : Configuration) :
    (realSlope l i x:ℂ) = powerSlope l i x := by
  unfold realSlope powerSlope
  push_cast
  rfl

theorem realSlope_continuous (l : Transverse →L[ℝ] ℝ) (i : Fin 2) : Continuous (realSlope l i) := by
  unfold realSlope
  fun_prop

variable (ε h : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3) (S : StructuredState)

theorem mean_real_multiplier_graph (P : Weight) (r : Configuration → ℝ) (hr : Measurable r)
    (hP : ∀ x, P.value x = (r x:ℂ)) (t : Interval) :
    (meanInputAt ε h hε hh hb S t,meanWeightedInput ε h hε hh hb S P t) ∈
      (realPullback (LinearIsometryEquiv.refl ℂ Hilbert) r hr).graph :=
  KFCausalProjectedKineticResponse.integral_closed_graph _
    (KFCausalRealMultiplierSelfAdjoint.realPullback_selfAdjoint _ _ _).isClosed _ _
    ((KFCausalStructuredShearMean.angle_continuous ε h hε hh hb S t).1.comp (continuous_const.mul continuous_id))
    ((KFCausalStructuredPolynomialShearOrbit.angle_continuous ε h hε hh hb S P t).1.comp
      (continuous_const.mul continuous_id))
    (fun θ => KFCausalStructuredPolynomialShearOrbit.real_multiplier_graph ε h hε hh hb S P r hr hP (2*Real.pi*θ) t)

theorem mean_slope_coe (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (t : Interval) :
    meanWeightedInput ε h hε hh hb S (slopeWeight l i) t =ᵐ[volume]
      fun x => powerSlope l i x*meanInputAt ε h hε hh hb S t x := by
  have he := mean_real_multiplier_graph ε h hε hh hb S (slopeWeight l i)
    (realSlope l i) (realSlope_continuous l i).measurable (fun x => (realSlope_coe l i x).symm) t
  simpa only [realSlope_coe] using
    (realPullback_graph (LinearIsometryEquiv.refl ℂ Hilbert) (realSlope l i)
      (realSlope_continuous l i).measurable _ _).mp he

#print axioms realSlope_coe
#print axioms realSlope_continuous
#print axioms mean_real_multiplier_graph
#print axioms mean_slope_coe
end
end UnifiedTheory.Audit.KFCausalProjectedFieldSlopeMultiplier
