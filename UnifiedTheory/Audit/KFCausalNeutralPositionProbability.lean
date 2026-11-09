/- The bare neutral-position characteristic is exactly the characteristic
of the actual Born position marginal. No limiting probability law is
postulated. Normalized evolved states give probability snapshots. -/
import UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic
import UnifiedTheory.Audit.KFCausalL2BornLaw
import UnifiedTheory.Audit.KFCausalCharacteristicRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalNeutralPositionProbability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalNeutralPositionCharge (coordinate action action_coe)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalNeutralPositionRadialCharacteristic (bare)

def law (f : Hilbert) : Measure ℝ := (KFCausalL2BornLaw.law volume f).map coordinate

theorem law_probability (f : Hilbert) (hf : ‖f‖ = 1) : IsProbabilityMeasure (law f) := by
  letI := KFCausalL2BornLaw.law_probability volume f hf
  exact Measure.isProbabilityMeasure_map coordinate.continuous.measurable.aemeasurable

theorem law_characteristic (v : ℝ) (f : Hilbert) :
    charFun (law f) v = inner ℂ f (action v f) := by
  rw [charFun_apply_real,law,integral_map coordinate.continuous.measurable.aemeasurable (by fun_prop)]
  calc
    _ = ∫ x, scalar (v*x.2 4) ∂KFCausalL2BornLaw.law volume f := by
      apply integral_congr_ae
      filter_upwards [] with x
      unfold scalar
      congr 1
      change (v:ℂ)*((x.2 4:ℝ):ℂ)*Complex.I = Complex.I*((v*x.2 4:ℝ):ℂ)
      push_cast
      ring
    _ = _ := KFCausalL2BornLaw.integral_eq_inner volume f (action v f)
      (fun x => scalar (v*x.2 4)) (action_coe v f)

def snapshot (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨law (evolvedState ε a h hε ha hne hh m g k s p t),
    law_probability _ (evolvedState_norm ε a h hε ha hne hh m g k s p t)⟩

theorem snapshot_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t v : ℝ) :
    charFun (snapshot ε a h hε ha hne hh m g k s p t : Measure ℝ) v =
      bare ε a h hε ha hne hh m g k s p v t := law_characteristic v _

#print axioms law_probability
#print axioms law_characteristic
#print axioms snapshot_characteristic

end
end UnifiedTheory.Audit.KFCausalNeutralPositionProbability
