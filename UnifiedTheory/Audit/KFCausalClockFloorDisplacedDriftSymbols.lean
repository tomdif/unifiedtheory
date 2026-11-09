/- The averaged drift limits equal physical clock-law expectations of
all three classical potential symbols. Fubini uses proved integrability. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedEnergyAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftSymbols
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)
open UnifiedTheory.Audit.KFCausalClockFloorInitialDriftPairing (drift_clock_continuous drift_clock_bound)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftAverage
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftLimit
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedExponentialSymbol (symbol symbol_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldSymbols (fieldSymbol fieldSymbol_integrable)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFieldIntegral (fieldIndex)
open UnifiedTheory.Audit.KFCausalClockFloorDisplacedFactorLimits
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw (clockLaw clockLaw_probability)
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)
open UnifiedTheory.Audit.KFCausalMatterOrderedDomain (pointField)

theorem drift_symbolMean_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (i : Fin 8) :
    Integrable (fun s => drift ε (defect ε s)*symbolMean ε p s i) (clockLaw ε a) :=
  (symbolMean_integrable ε a hε ha p i).bdd_mul (drift_clock_continuous ε hε).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun s => by simpa only [Real.norm_eq_abs] using drift_clock_bound ε hε s))

theorem drift_symbol_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    Integrable (fun x : ℝ × ℝ => drift ε (defect ε x.2)*symbol ε p x.1 x.2)
      (angleMeasure.prod (clockLaw ε a)) :=
  (symbol_integrable ε a hε ha p).bdd_mul
    ((drift_clock_continuous ε hε).comp continuous_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using drift_clock_bound ε hε x.2))

theorem drift_fieldSymbol_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) (j : Fin 2) :
    Integrable (fun x : ℝ × ℝ => drift ε (defect ε x.2)*fieldSymbol ε p pointField j x.1 x.2)
      (angleMeasure.prod (clockLaw ε a)) :=
  (fieldSymbol_integrable ε a hε ha p pointField j).bdd_mul
    ((drift_clock_continuous ε hε).comp continuous_snd).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun x => by simpa only [Real.norm_eq_abs] using drift_clock_bound ε hε x.2))

theorem averagedDriftLimit_symbolMean (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) (p : Configuration) :
    averagedDriftLimit ε a p = ∫ s, drift ε (defect ε s)*symbolMean ε p s 7 ∂clockLaw ε a := by
  letI := clockLaw_probability ε a hε ha
  change (∫ θ, (∫ s, drift ε (defect ε s)*symbol ε p θ s ∂clockLaw ε a) ∂angleMeasure) = _
  rw [integral_integral_swap (drift_symbol_integrable ε a hε ha p)]
  simp only [integral_const_mul,exponentialSymbol_mean]

theorem averagedFieldDriftLimit_symbolMean (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a)
    (p : Configuration) (j : Fin 2) :
    averagedFieldDriftLimit ε a p pointField j =
      ∫ s, drift ε (defect ε s)*symbolMean ε p s (fieldIndex j) ∂clockLaw ε a := by
  letI := clockLaw_probability ε a hε ha
  have he : averagedFieldDriftLimit ε a p pointField j =
      ∫ θ, (∫ s, drift ε (defect ε s)*fieldSymbol ε p pointField j θ s ∂clockLaw ε a) ∂angleMeasure := by
    simp only [averagedFieldDriftLimit,fieldDriftLimit,driftLimit,fieldSymbol,symbol,
      mul_left_comm (drift ε (defect ε _)),integral_const_mul]
  rw [he,integral_integral_swap (drift_fieldSymbol_integrable ε a hε ha p j)]
  simp only [integral_const_mul,fieldSymbol_mean]

#print axioms drift_symbolMean_integrable
#print axioms drift_symbol_integrable
#print axioms drift_fieldSymbol_integrable
#print axioms averagedDriftLimit_symbolMean
#print axioms averagedFieldDriftLimit_symbolMean

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedDriftSymbols
