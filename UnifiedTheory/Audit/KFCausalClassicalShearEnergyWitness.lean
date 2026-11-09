/- An explicit charge-averaged classical family with quadratic energy and
quartic positive shear force. Matter fields vanish on its full charge orbit.
This is not a fixed-hbar quantum counterexample. -/
import UnifiedTheory.Audit.KFCausalClassicalShearTiltGrowth

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalClassicalShearEnergyWitness
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kineticMean_eq)
open UnifiedTheory.Audit.KFCausalClassicalShearTiltGrowth
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)

def phase (r : ℝ) : Phase :=
  (WithLp.toLp 2 (fun | .inl i => ![r,0] i | .inr _ => 0),
   WithLp.toLp 2 (fun | .inl i => ![r,0] i | .inr _ => 0))

theorem phase_shear (r θ : ℝ) : shear (rotate θ (phase r)) = r^2*profile θ := by
  simp [shear_rotate,diagonalPairing,crossPairing,phase,profile]
  ring

theorem phase_field (r θ : ℝ) : fieldValue (rotate θ (phase r)) = 0 := by
  simp [fieldValue_rotate,phase]

theorem phase_potential (m g r θ : ℝ) : potential m g 1 (rotate θ (phase r)) = 1 := by
  simp [potential,phase_field]

theorem phase_kinetic (r : ℝ) : kineticMean 0 (phase r) = r^2 := by
  simp [kineticMean_eq,phase]

theorem phase_mass (m g r : ℝ) : weightedMean m g 1 1 (phase r) = mass (r^2) := by
  simp only [weightedMean,phase_potential,phase_shear,div_one,one_mul,mass]

theorem phase_tilt (m g r : ℝ) : weightedTilt m g 1 1 (phase r) = r^2*moment (r^2) := by
  simp only [weightedTilt,phase_potential,phase_shear,div_one,one_mul]
  have he : (fun θ => r^2*profile θ*Real.exp (r^2*profile θ)) =
      fun θ => (profile θ*Real.exp (r^2*profile θ))*r^2 := by funext θ; ring
  rw [he,mean_mul_const]
  unfold moment
  ring

theorem mass_ge_one (r : ℝ) : 1 ≤ mass (r^2) := by
  have he := exponentialMean_ge_one 1 (phase r)
  simpa only [exponentialMean,phase_shear,div_one,mass] using he

def clockPoint : ℝ := Real.log (1/2:ℝ)
def clockMomentum (r : ℝ) : ℝ := Real.log (r^2/mass (r^2))
def shearRate (r : ℝ) : ℝ := (1/2:ℝ)*(r^2/mass (r^2))*(r^2*moment (r^2))

theorem clock_at_point : clock (1/2) clockPoint = 1 := by
  rw [clock,clockPoint,Real.exp_log (by norm_num : (0:ℝ)<1/2)]
  norm_num

theorem response_at_point : KFCausalClockFloorCanonicalDefect.response (1/2) clockPoint = 1/2 := by
  rw [KFCausalClockFloorCanonicalDefect.response,clock_at_point,clockPoint,
    Real.exp_log (by norm_num : (0:ℝ)<1/2)]
  norm_num

theorem amplitude_at_point (r : ℝ) (hr : r ≠ 0) :
    amplitude (1/2) 0 clockPoint (clockMomentum r) = r^2/mass (r^2) := by
  simp only [amplitude,clock_at_point,mul_zero,zero_add,div_one,clockMomentum]
  exact Real.exp_log (div_pos (sq_pos_of_ne_zero hr) (by linarith [mass_ge_one r]))

theorem witness_energy (m g r : ℝ) (hr : r ≠ 0) :
    hamiltonian (1/2) m g 1 0 (phase r) clockPoint (clockMomentum r) = 1/2+2*r^2 := by
  rw [hamiltonian,clock_at_point,phase_kinetic,amplitude_at_point r hr,phase_mass]
  have hm : mass (r^2) ≠ 0 := ne_of_gt (by linarith [mass_ge_one r])
  field_simp
  ring

theorem witness_rate (m g r : ℝ) (hr : r ≠ 0) :
    longitudinalRate (1/2) m g 1 0 (phase r) clockPoint (clockMomentum r) = -1/4+r^2+shearRate r := by
  rw [longitudinalRate,response_at_point,clock_at_point,phase_kinetic,
    amplitude_at_point r hr,phase_mass,phase_tilt]
  have hm : mass (r^2) ≠ 0 := ne_of_gt (by linarith [mass_ge_one r])
  unfold shearRate
  field_simp
  ring

theorem shearRate_lower (r : ℝ) (hr : 480 ≤ r^2) : r^4/16 ≤ shearRate r := by
  have hm : 0 < mass (r^2) := by linarith [mass_ge_one r]
  have ht : (1/8:ℝ) ≤ moment (r^2)/mass (r^2) :=
    (le_div_iff₀ hm).mpr (by linarith [moment_lower (r^2) hr])
  calc
    r^4/16 = (r^4/2)*(1/8:ℝ) := by ring
    _ ≤ (r^4/2)*(moment (r^2)/mass (r^2)) := mul_le_mul_of_nonneg_left ht (by positivity)
    _ = shearRate r := by unfold shearRate; ring

theorem witness_rate_lower (m g r : ℝ) (hr : 480 ≤ r^2) :
    r^4/16 ≤ longitudinalRate (1/2) m g 1 0 (phase r) clockPoint (clockMomentum r) := by
  have hn : r ≠ 0 := by intro hz; norm_num [hz] at hr
  rw [witness_rate m g r hn]
  linarith [shearRate_lower r hr]

#print axioms phase_shear
#print axioms phase_field
#print axioms phase_potential
#print axioms phase_kinetic
#print axioms phase_mass
#print axioms phase_tilt
#print axioms mass_ge_one
#print axioms clock_at_point
#print axioms response_at_point
#print axioms amplitude_at_point
#print axioms witness_energy
#print axioms witness_rate
#print axioms shearRate_lower
#print axioms witness_rate_lower
end
end UnifiedTheory.Audit.KFCausalClassicalShearEnergyWitness
