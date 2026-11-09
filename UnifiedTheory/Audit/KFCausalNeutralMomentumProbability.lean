/- Exact Born probabilities for the canonical neutral momentum. Their
characteristic functions are the original quantum neutral tests. -/
import UnifiedTheory.Audit.KFCausalNeutralCharacteristicControl
import UnifiedTheory.Audit.KFCausalL2BornLaw
import UnifiedTheory.Audit.KFCausalCharacteristicRepresentation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 250000

namespace UnifiedTheory.Audit.KFCausalNeutralMomentumProbability
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Joint)
open UnifiedTheory.Audit.KFCausalChargeTransverseSplit (dualPhysical)
open UnifiedTheory.Audit.KFCausalComplementaryMomentumTests (momentumSymbol momentumTest momentumTest_dual_coe)
open UnifiedTheory.Audit.KFCausalNeutralCanonicalForm (frequency)
open UnifiedTheory.Audit.KFCausalNeutralCharacteristicControl (frequency_momentum)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (characteristic)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockRightTail (evolvedState evolvedState_norm)

local instance configurationHaar : Measure.IsAddHaarMeasure (volume : Measure Configuration) :=
  Measure.prod.instIsAddHaarMeasure _ _

theorem symbol_continuous (h : ℝ) : Continuous (momentumSymbol h 2) := by
  unfold momentumSymbol
  fun_prop

def law (h : ℝ) (f : Hilbert) : Measure ℝ :=
  (KFCausalL2BornLaw.law volume (dualPhysical f)).map (momentumSymbol h 2)

theorem law_probability (h : ℝ) (f : Hilbert) (hf : ‖f‖ = 1) : IsProbabilityMeasure (law h f) := by
  letI := KFCausalL2BornLaw.law_probability volume (dualPhysical f) ((dualPhysical.norm_map f).trans hf)
  exact Measure.isProbabilityMeasure_map (symbol_continuous h).measurable.aemeasurable

theorem law_characteristic (h v : ℝ) (f : Hilbert) :
    charFun (law h f) v = characteristic volume h f (frequency v) := by
  rw [charFun_apply_real,law,integral_map (symbol_continuous h).measurable.aemeasurable (by fun_prop)]
  calc
    _ = ∫ x, Complex.exp (Complex.I*((v*momentumSymbol h 2 x:ℝ):ℂ))
        ∂KFCausalL2BornLaw.law volume (dualPhysical f) := by
      apply integral_congr_ae
      filter_upwards [] with x
      congr 1
      push_cast
      ring
    _ = inner ℂ (dualPhysical f) (dualPhysical (momentumTest h v 2 f)) :=
      KFCausalL2BornLaw.integral_eq_inner volume (dualPhysical f) (dualPhysical (momentumTest h v 2 f))
        (fun x => Complex.exp (Complex.I*((v*momentumSymbol h 2 x:ℝ):ℂ))) (momentumTest_dual_coe h v 2 f)
    _ = _ := by
      simpa only [characteristic,frequency_momentum,momentumTest] using
        dualPhysical.inner_map_map f (momentumTest h v 2 f)

def snapshot (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t : ℝ) : ProbabilityMeasure ℝ :=
  ⟨law h (evolvedState ε a h hε ha hne hh m g k s p t),
    law_probability h _ (evolvedState_norm ε a h hε ha hne hh m g k s p t)⟩

theorem snapshot_characteristic (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hne : h ≠ 0)
    (hh : |h| ≤ 2*Real.pi*ε/3) (m g k s : ℝ) (p : Configuration) (t v : ℝ) :
    charFun (snapshot ε a h hε ha hne hh m g k s p t : Measure ℝ) v =
      KFCausalDisplacedNeutralDynamics.characteristic ε a h hε ha hne hh m g k s p v t :=
  law_characteristic h v _

#print axioms symbol_continuous
#print axioms law_probability
#print axioms law_characteristic
#print axioms snapshot_characteristic
end
end UnifiedTheory.Audit.KFCausalNeutralMomentumProbability
