/- Exact clock Hamilton equations for the full mass/quartic classical
candidate, averaged using the same charge orbit and normalized measure. -/
import UnifiedTheory.Audit.KFCausalClassicalMatterSymbols

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalMatterSymbols
open UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum (kineticMean kinetic_continuous)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def amplitude (ε t s p : ℝ) : ℝ := Real.exp (2*t+p/clock ε s)

def hamiltonian (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  clock ε s/2+(kineticMean t z+amplitude ε t s p*weightedMean m g κ (clock ε s) z)/clock ε s

def clockRate (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  amplitude ε t s p*weightedMean m g κ (clock ε s) z/(clock ε s)^2

def momentumRate (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  -Real.exp s/2+Real.exp s/(clock ε s)^2*
    (kineticMean t z+amplitude ε t s p*
      ((1+p/clock ε s)*weightedMean m g κ (clock ε s) z+weightedTilt m g κ (clock ε s) z))

def longitudinalRate (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  response ε s*(-1/2+(kineticMean t z+amplitude ε t s p*
    (weightedMean m g κ (clock ε s) z+weightedTilt m g κ (clock ε s) z))/(clock ε s)^2)

theorem hamiltonian_eq_mean (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) :
    hamiltonian ε m g κ t z s p = mean (fun θ => clock ε s/2+
      (kinetic t (rotate θ z)+potential m g κ (rotate θ z)*Real.exp (2*t+(p+shear (rotate θ z))/clock ε s))/clock ε s) := by
  have he : (fun θ => clock ε s/2+
      (kinetic t (rotate θ z)+potential m g κ (rotate θ z)*Real.exp (2*t+(p+shear (rotate θ z))/clock ε s))/clock ε s) =
      fun θ => clock ε s/2+kinetic t (rotate θ z)/clock ε s+
        (potential m g κ (rotate θ z)*Real.exp (shear (rotate θ z)/clock ε s)*amplitude ε t s p)/clock ε s := by
    funext θ
    rw [show 2*t+(p+shear (rotate θ z))/clock ε s =
      (2*t+p/clock ε s)+shear (rotate θ z)/clock ε s by ring, Real.exp_add]
    unfold amplitude
    ring
  rw [he, mean_add _ _ (by have hk := kinetic_continuous t z; fun_prop)
    (by have hd := shear_continuous z; have hw := potential_continuous m g κ z; fun_prop),
    mean_add _ _ continuous_const ((kinetic_continuous t z).div_const _), mean_const]
  simp only [div_eq_mul_inv, mean_mul_const]
  unfold hamiltonian kineticMean weightedMean
  simp only [div_eq_mul_inv]
  ring

theorem hamiltonian_momentum_derivative (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) :
    HasDerivAt (hamiltonian ε m g κ t z s) (clockRate ε m g κ t z s p) p := by
  have h := (((((hasDerivAt_id p).div_const (clock ε s)).const_add (2*t)).exp).mul_const
    (weightedMean m g κ (clock ε s) z)).const_add (kineticMean t z)
  convert (h.div_const (clock ε s)).const_add (clock ε s/2) using 1
  simp only [id_eq]
  unfold clockRate amplitude
  ring

theorem hamiltonian_clock_derivative (ε m g κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    HasDerivAt (fun u => hamiltonian ε m g κ t z u p) (-momentumRate ε m g κ t z s p) s := by
  have hc := (clock_positive ε s hε).ne'
  have hd : HasDerivAt (clock ε) (Real.exp s) s := (Real.hasDerivAt_exp s).add_const ε
  have hp := (hasDerivAt_const s p).div hd hc
  have ha := (hp.const_add (2*t)).exp
  have he := (weightedMean_derivative m g κ (clock ε s) hc z).comp s hd
  have h := (hd.div_const 2).add (((ha.mul he).const_add (kineticMean t z)).div hd hc)
  convert h using 1
  simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  unfold momentumRate amplitude
  field_simp
  ring

theorem longitudinalRate_eq (ε m g κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    longitudinalRate ε m g κ t z s p =
      momentumRate ε m g κ t z s p/clock ε s-
      p*Real.exp s*clockRate ε m g κ t z s p/(clock ε s)^2 := by
  have hc := (clock_positive ε s hε).ne'
  unfold longitudinalRate momentumRate clockRate response
  field_simp
  ring

theorem longitudinalRate_is_bracket (ε m g κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    bracket (longitudinal ε) (hamiltonian ε m g κ t z) s p = longitudinalRate ε m g κ t z s p := by
  rw [bracket, (KFCausalClockFloorClassicalBackreaction.longitudinal_clock_derivative ε s p hε).deriv,
    (longitudinal_momentum_derivative ε s p).deriv,
    (hamiltonian_momentum_derivative ε m g κ t z s p).deriv,
    (hamiltonian_clock_derivative ε m g κ t hε z s p).deriv,
    longitudinalRate_eq ε m g κ t hε z s p]
  ring

theorem hamiltonian_vacuum (ε κ t : ℝ) (z : Phase) (s p : ℝ) :
    hamiltonian ε 0 0 κ t z s p = KFCausalClassicalAveragedVacuum.hamiltonian ε κ t z s p := by
  unfold hamiltonian KFCausalClassicalAveragedVacuum.hamiltonian
  rw [weightedMean_vacuum]
  unfold amplitude KFCausalClassicalAveragedVacuum.amplitude
  ring

theorem hamiltonian_eq_factor_mean (ε m g κ t : ℝ) (z : Phase) (s p : ℝ) :
    hamiltonian ε m g κ t z s p = mean (fun θ =>
      KFCausalClockFloorTrialUniformEnergy.energyPolynomial m g κ t
        (squaredSymbols (clock ε s) p (rotate θ z))) := by
  simp_rw [← rawHamiltonian_eq_energyPolynomial]
  exact hamiltonian_eq_mean ε m g κ t z s p

theorem clockRate_lower (ε m g κ t : ℝ) (hm : 0 ≤ m) (hg : 0 ≤ g) (hκ : 0 ≤ κ)
    (z : Phase) (s p : ℝ) : κ*amplitude ε t s p/(clock ε s)^2 ≤ clockRate ε m g κ t z s p := by
  have h := mul_le_mul_of_nonneg_left (weightedMean_lower m g κ (clock ε s) hm hg hκ z)
    (Real.exp_pos (2*t+p/clock ε s)).le
  apply div_le_div_of_nonneg_right _ (sq_nonneg _)
  simpa only [amplitude,mul_comm] using h

#print axioms hamiltonian_eq_mean
#print axioms hamiltonian_momentum_derivative
#print axioms hamiltonian_clock_derivative
#print axioms longitudinalRate_eq
#print axioms longitudinalRate_is_bracket
#print axioms hamiltonian_vacuum
#print axioms hamiltonian_eq_factor_mean
#print axioms clockRate_lower

end
end UnifiedTheory.Audit.KFCausalClassicalMatterHamiltonian
