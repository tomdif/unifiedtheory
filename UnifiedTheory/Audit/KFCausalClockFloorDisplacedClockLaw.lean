/- The clock and inverse-clock expectations of the actual initial law.
Their finiteness and values follow from the existing clock profiles. -/
import UnifiedTheory.Audit.KFCausalClockFloorDisplacedKineticEnergy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLaw
noncomputable section
open MeasureTheory Filter
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorInitialClassicalLaw
open UnifiedTheory.Audit.KFCausalClockFloorInitialEnergyIdentification (halfClock_square dampedClock_square)
open UnifiedTheory.Audit.KFCausalClockFloorTrialClockEnergy
open UnifiedTheory.Audit.KFCausalClockFloorTrialEnergyNorms (clockMass halfMass dampedMass)

theorem clock_density (ε a s : ℝ) (hε : 0 < ε) :
    clockDensity ε a s*clock ε s = ‖halfClockFunction ε a s‖^2/clockMass ε a := by
  rw [halfClock_square ε a s hε]
  unfold clockDensity
  ring

theorem inverseClock_density (ε a s : ℝ) (hε : 0 < ε) :
    clockDensity ε a s*(clock ε s)⁻¹ = ‖dampedClockFunction ε a s‖^2/clockMass ε a := by
  rw [dampedClock_square ε a s hε]
  unfold clockDensity
  ring

theorem clock_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (clock ε) (clockLaw ε a) := by
  rw [clockLaw,integrable_withDensity_iff_integrable_smul'
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hm := halfClockFunction_memLp ε a hε ha
  apply (((memLp_two_iff_integrable_sq_norm hm.1).mp hm).div_const (clockMass ε a)).congr
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,clock_density ε a s hε]

theorem inverseClock_integrable (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    Integrable (fun s => (clock ε s)⁻¹) (clockLaw ε a) := by
  rw [clockLaw,integrable_withDensity_iff_integrable_smul'
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have hm := dampedClockFunction_memLp ε a hε ha
  apply (((memLp_two_iff_integrable_sq_norm hm.1).mp hm).div_const (clockMass ε a)).congr
  filter_upwards [] with s
  rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,inverseClock_density ε a s hε]

theorem clock_integral (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ s, clock ε s ∂clockLaw ε a) = halfMass ε a/clockMass ε a := by
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ s, ‖halfClockFunction ε a s‖^2/clockMass ε a := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,clock_density ε a s hε]
    _ = _ := by rw [integral_div]; rfl

theorem inverseClock_integral (ε a : ℝ) (hε : 0 < ε) (ha : 0 < a) :
    (∫ s, (clock ε s)⁻¹ ∂clockLaw ε a) = dampedMass ε a/clockMass ε a := by
  rw [clockLaw,integral_withDensity_eq_integral_toReal_smul
    (clockDensity_continuous ε a).measurable.ennreal_ofReal
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  calc
    _ = ∫ s, ‖dampedClockFunction ε a s‖^2/clockMass ε a := by
      apply integral_congr_ae
      filter_upwards [] with s
      rw [ENNReal.toReal_ofReal (clockDensity_nonnegative ε a hε ha s),smul_eq_mul,inverseClock_density ε a s hε]
    _ = _ := by rw [integral_div]; rfl

#print axioms clock_density
#print axioms inverseClock_density
#print axioms clock_integrable
#print axioms inverseClock_integrable
#print axioms clock_integral
#print axioms inverseClock_integral

end
end UnifiedTheory.Audit.KFCausalClockFloorDisplacedClockLaw
