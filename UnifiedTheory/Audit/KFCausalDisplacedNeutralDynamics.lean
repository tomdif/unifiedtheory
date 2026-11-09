/- Exact canonical neutral-momentum characteristic dynamics for the
actual evolved boosted states. The rate and energy are those of the
constructed quantum propagator, not an assumed classical law. -/
import UnifiedTheory.Audit.KFCausalNeutralEhrenfest
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalDisplacedNeutralDynamics
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedReferenceState
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency operator_action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationPhysicalCommutator (speedBound)
open UnifiedTheory.Audit.KFCausalPhysicalEnergyFactors (energyWeight)
open UnifiedTheory.Audit.KFCausalClockFloorAveragedTimeControl (timeEnergy)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
  (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration)
  (hm : 0 < m) (hg : 0 < g) (hk : 0 < k)
local notation "w" => referenceState ε a h hε ha hne hh m g k s p

def characteristic (v t : ℝ) : ℂ :=
  KFCausalCanonicalWeylAlgebra.characteristic volume h
    (evolvedState ε a h hε ha hne hh m g k s p t) (frequency v)

theorem characteristic_reference (v t : ℝ) :
    characteristic ε a h hε ha hne hh m g k s p v t =
      KFCausalNeutralEhrenfest.characteristic ε hε h hne hh m g k (h*v) s t w := by
  simp only [characteristic,KFCausalCanonicalWeylAlgebra.characteristic,operator_action,
    KFCausalNeutralEhrenfest.characteristic,referenceState_embedding,evolvedState]

def rate (v t : ℝ) : ℂ := KFCausalNeutralEhrenfest.exactRate ε hε h hne hh m g k hm hg hk (h*v) s t w

theorem characteristic_derivative (v t : ℝ) :
    HasDerivAt (characteristic ε a h hε ha hne hh m g k s p v)
      (rate ε a h hε ha hne hh m g k s p hm hg hk v t) t := by
  change HasDerivAt (fun z => characteristic ε a h hε ha hne hh m g k s p v z) _ t
  simpa only [characteristic_reference,rate] using
    KFCausalNeutralEhrenfest.expectation_derivative ε hε h hne hh m g k hm hg hk (h*v) s t w

include hm hg hk in
theorem characteristic_continuous (v : ℝ) :
    Continuous (characteristic ε a h hε ha hne hh m g k s p v) :=
  continuous_iff_continuousAt.mpr (fun t =>
    (characteristic_derivative ε a h hε ha hne hh m g k s p hm hg hk v t).continuousAt)

theorem rate_continuous (v : ℝ) : Continuous (rate ε a h hε ha hne hh m g k s p hm hg hk v) :=
  KFCausalNeutralEhrenfest.exactRate_continuous ε hε h hne hh m g k hm hg hk (h*v) s w

theorem characteristic_integral (v r t : ℝ) :
    (∫ z in r..t, rate ε a h hε ha hne hh m g k s p hm hg hk v z) =
      characteristic ε a h hε ha hne hh m g k s p v t-characteristic ε a h hε ha hne hh m g k s p v r := by
  simpa only [characteristic_reference,rate] using
    KFCausalNeutralEhrenfest.expectation_integral ε hε h hne hh m g k hm hg hk (h*v) s r t w

theorem characteristic_bound (v t : ℝ) : ‖characteristic ε a h hε ha hne hh m g k s p v t‖ ≤ 1 := by
  have hb := KFCausalCanonicalWeylAlgebra.characteristic_bound volume h
    (evolvedState ε a h hε ha hne hh m g k s p t) (frequency v)
  simpa only [characteristic,evolvedState_norm,one_pow] using hb

theorem rate_energy_bound (v H t : ℝ) (hH : |h| ≤ H) :
    ‖rate ε a h hε ha hne hh m g k s p hm hg hk v t‖ ≤
      speedBound (energyWeight m g k 0) H v*timeEnergy ε hε h hne hh m g k t
        (trajectory ε a h hε ha hne hh m g k s p t) :=
  KFCausalNeutralEhrenfest.canonical_rate_bound ε hε h hne hh m g k hm hg hk v H s t hH w

#print axioms characteristic_reference
#print axioms characteristic_derivative
#print axioms characteristic_continuous
#print axioms rate_continuous
#print axioms characteristic_integral
#print axioms characteristic_bound
#print axioms rate_energy_bound

end
end UnifiedTheory.Audit.KFCausalDisplacedNeutralDynamics
