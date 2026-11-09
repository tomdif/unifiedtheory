/- An explicit constant for the existing classical weighted-tilt bound,
and its application to the already constructed full classical evolution.
No quantum-domain propagation or quantum-to-classical identification follows. -/
import UnifiedTheory.Audit.KFCausalClassicalQuarterExponential
import UnifiedTheory.Audit.KFCausalClassicalMatterEvolution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096

namespace UnifiedTheory.Audit.KFCausalClassicalExplicitTiltControl
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHarmonics (first second)
open UnifiedTheory.Audit.KFCausalClassicalMatterCoercivity
open UnifiedTheory.Audit.KFCausalClassicalQuarterExponential
open UnifiedTheory.Audit.KFCausalClassicalMatterTiltControl (weightedTilt_lower)
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalMatterAdjustedDrift
open UnifiedTheory.Audit.KFCausalClassicalMatterEvolution
open UnifiedTheory.Audit.KFCausalClassicalMatterDefect (clock_derivative clockMomentum_derivative)
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth (TimePhase q p)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response)

theorem field_square_coercivity (C : ℝ) (z : Phase) :
    mean (fun θ => fieldValue (rotate θ z)^2) ≤
      32768*mean (fun θ => fieldValue (rotate θ z)^2*Real.exp (shear (rotate θ z)/C)) := by
  have he := square_coercivity ((fieldCoefficients z) 0) ((fieldCoefficients z) 1)
    ((fieldCoefficients z) 2) (shearCoefficients C z)
  change mean (fun θ => first (fieldCoefficients z) θ^2) ≤
    32768*mean (fun θ => first (fieldCoefficients z) θ^2*Real.exp (second (shearCoefficients C z) θ)) at he
  simpa only [fieldCoefficients_apply,shearCoefficients_apply] using he

theorem field_fourth_coercivity (C : ℝ) (z : Phase) :
    mean (fun θ => fieldValue (rotate θ z)^4) ≤
      65536*mean (fun θ => fieldValue (rotate θ z)^4*Real.exp (shear (rotate θ z)/C)) := by
  have he := fourth_coercivity ((fieldCoefficients z) 0) ((fieldCoefficients z) 1)
    ((fieldCoefficients z) 2) (shearCoefficients C z)
  change mean (fun θ => first (fieldCoefficients z) θ^4) ≤
    65536*mean (fun θ => first (fieldCoefficients z) θ^4*Real.exp (second (shearCoefficients C z) θ)) at he
  simpa only [fieldCoefficients_apply,shearCoefficients_apply] using he

theorem potential_coercivity (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (z : Phase) : mean (fun θ => potential m g κ (rotate θ z)) ≤ 65536*weightedMean m g κ C z := by
  have h2 := field_square_coercivity C z
  have hn2 : 0 ≤ mean (fun θ => fieldValue (rotate θ z)^2*Real.exp (shear (rotate θ z)/C)) :=
    mean_nonnegative _ (fun θ => by positivity)
  have h2' : mean (fun θ => fieldValue (rotate θ z)^2) ≤
      65536*mean (fun θ => fieldValue (rotate θ z)^2*Real.exp (shear (rotate θ z)/C)) := by
    linarith only [h2,hn2]
  have h4 := field_fourth_coercivity C z
  have hv := le_mul_of_one_le_right hκ (exponentialMean_ge_one C z)
  have hv' : κ ≤ 65536*(κ*exponentialMean C z) := by nlinarith only [hv,hκ]
  have hms := mul_le_mul_of_nonneg_left h2' (div_nonneg hm (by norm_num : (0:ℝ) ≤ 2))
  have hgs := mul_le_mul_of_nonneg_left h4 (div_nonneg hg (by norm_num : (0:ℝ) ≤ 4))
  rw [potential_mean_expansion,weightedMean_expansion]
  nlinarith only [hv',hms,hgs]

theorem tilt_control (m g κ C : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (z : Phase) : -65536*weightedMean m g κ C z ≤
      weightedMean m g κ C z+weightedTilt m g κ C z := by
  have hc := potential_coercivity m g κ C hm hg hκ z
  have ht := weightedTilt_lower m g κ C hm hg hκ z
  have hn := hκ.trans (weightedMean_lower m g κ C hm hg hκ z)
  linarith only [hc,ht,hn]

theorem explicit_correctedRate (ε m g κ t s r : ℝ) (hε : 0 < ε)
    (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ) (z : Phase) :
    0 ≤ longitudinalRate ε m g κ t z s r+
      65536*(response ε s*clockRate ε m g κ t z s r)+1/2 :=
  correctedRate_nonnegative ε m g κ 65536 t s r hε z
    (tilt_control m g κ (clock ε s) hm hg hκ z)

def adjusted (ε : ℝ) (z : Phase) : ℝ :=
  p (.inr 0) z/clock ε (q (.inr 0) z)+65536*Real.log (clock ε (q (.inr 0) z))

variable (ε m g κ : ℝ) (hε : 0 < ε) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 < κ)
local notation "Φ" => evolve ε m g κ hε hm hg hκ

theorem evolve_corrected_monotone (x : TimePhase) :
    Monotone (fun t => adjusted ε (Φ t x).2+t/2) := by
  have hs (t : ℝ) : HasDerivAt (fun u => q (.inr 0) (Φ u x).2)
      (clockRate ε m g κ (t+x.1) (Φ t x).2 (q (.inr 0) (Φ t x).2) (p (.inr 0) (Φ t x).2)) t := by
    have he := clock_derivative ε m g κ hε.le (fun u => Φ u x) t
      (evolve_derivative ε m g κ hε hm hg hκ x t)
    rw [evolve_time] at he
    exact he
  have hp (t : ℝ) : HasDerivAt (fun u => p (.inr 0) (Φ u x).2)
      (momentumRate ε m g κ (t+x.1) (Φ t x).2 (q (.inr 0) (Φ t x).2) (p (.inr 0) (Φ t x).2)) t := by
    have he := clockMomentum_derivative ε m g κ hε.le (fun u => Φ u x) t
      (evolve_derivative ε m g κ hε hm hg hκ x t)
    rw [evolve_time] at he
    exact he
  exact corrected_monotone ε m g κ x.1 hε (fun t => (Φ t x).2)
    (fun t => q (.inr 0) (Φ t x).2) (fun t => p (.inr 0) (Φ t x).2) hs hp 65536
    (fun C z => tilt_control m g κ C hm hg hκ.le z)

theorem evolve_interval_lower (x : TimePhase) (r t : ℝ) (hrt : r ≤ t) :
    adjusted ε (Φ r x).2-(t-r)/2 ≤ adjusted ε (Φ t x).2 := by
  have he := evolve_corrected_monotone ε m g κ hε hm hg hκ x hrt
  linarith only [he]

#print axioms field_square_coercivity
#print axioms field_fourth_coercivity
#print axioms potential_coercivity
#print axioms tilt_control
#print axioms explicit_correctedRate
#print axioms evolve_corrected_monotone
#print axioms evolve_interval_lower
end
end UnifiedTheory.Audit.KFCausalClassicalExplicitTiltControl
