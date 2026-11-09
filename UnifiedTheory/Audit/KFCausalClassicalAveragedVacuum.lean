/- Clock partial derivatives of the full charge-averaged classical vacuum
candidate, retaining all transverse phase coordinates and four kinetic factors.
This Hamiltonian is defined from those classical symbols. Its identification
as a controlled semiclassical limit of the ordered quantum forms is open. -/
import UnifiedTheory.Audit.KFCausalClassicalChargeLaplace
import UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalChargeMean
open UnifiedTheory.Audit.KFCausalClassicalChargeLaplace
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def kineticMean (t : ℝ) (z : Phase) : ℝ := mean (fun θ => kinetic t (rotate θ z))

def amplitude (ε κ t s p : ℝ) : ℝ := κ*Real.exp (2*t+p/clock ε s)

def hamiltonian (ε κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  clock ε s/2+(kineticMean t z+amplitude ε κ t s p*exponentialMean (clock ε s) z)/clock ε s

def clockRate (ε κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  amplitude ε κ t s p*exponentialMean (clock ε s) z/(clock ε s)^2

def momentumRate (ε κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  -Real.exp s/2+Real.exp s/(clock ε s)^2*
    (kineticMean t z+amplitude ε κ t s p*
      ((1+p/clock ε s)*exponentialMean (clock ε s) z+tiltedShear (clock ε s) z))

def longitudinalRate (ε κ t : ℝ) (z : Phase) (s p : ℝ) : ℝ :=
  response ε s*(-1/2+(kineticMean t z+amplitude ε κ t s p*
    (exponentialMean (clock ε s) z+tiltedShear (clock ε s) z))/(clock ε s)^2)

theorem kinetic_continuous (t : ℝ) (z : Phase) : Continuous (fun θ => kinetic t (rotate θ z)) := by
  simp_rw [kinetic_eq]
  simp [rotate]
  fun_prop

/-- Charge averaging fills the missing charged phase directions. The neutral
position remains absent in the vacuum Hamiltonian; its momentum is retained. -/
theorem kineticMean_eq (t : ℝ) (z : Phase) :
    kineticMean t z = (z.2 (.inr 1)^2+z.1 (.inl 0)^2+
      z.2 (.inr 2)^2+z.1 (.inl 1)^2+z.2 (.inr 3)^2)/2+
      Real.exp (2*t)*(z.2 (.inl 0)^2+z.1 (.inr 1)^2+
        z.2 (.inl 1)^2+z.1 (.inr 2)^2)/2 := by
  let c := KFCausalPairedModeCoordinates.scale
  let f := fun θ a b r : ℝ => (Real.cos θ*a+Real.sin θ*b+r)^2
  have he : (fun θ => kinetic t (rotate θ z)) = fun θ =>
      f θ (z.2 (.inr 1)) (-z.1 (.inl 0)) 0+
      f θ (2*c*z.2 (.inr 2)) (-2*c*z.1 (.inl 1)) (z.2 (.inr 3))*(1/2)+
      (f θ (z.2 (.inl 0)) (-z.1 (.inr 1)) 0+
        f θ (z.2 (.inl 1)) (-z.1 (.inr 2)) 0)*Real.exp (2*t) := by
    funext θ
    simp [kinetic_eq, rotate, f, c]
    ring
  rw [kineticMean, he, mean_add _ _ (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop),
    mean_add _ _ (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop), mean_mul_const,
    mean_mul_const, mean_add _ _ (by dsimp [f]; fun_prop) (by dsimp [f]; fun_prop)]
  simp only [f, affine_square_mean]
  dsimp [c]
  ring_nf
  rw [KFCausalPairedModeCoordinates.scale_square]
  ring

theorem hamiltonian_eq_mean (ε κ t : ℝ) (z : Phase) (s p : ℝ) :
    hamiltonian ε κ t z s p = mean (fun θ => clock ε s/2+
      (kinetic t (rotate θ z)+κ*Real.exp (2*t+(p+shear (rotate θ z))/clock ε s))/clock ε s) := by
  have he : (fun θ => clock ε s/2+
      (kinetic t (rotate θ z)+κ*Real.exp (2*t+(p+shear (rotate θ z))/clock ε s))/clock ε s) =
      fun θ => clock ε s/2+kinetic t (rotate θ z)/clock ε s+
        (Real.exp (shear (rotate θ z)/clock ε s)*amplitude ε κ t s p)/clock ε s := by
    funext θ
    rw [show 2*t+(p+shear (rotate θ z))/clock ε s =
      (2*t+p/clock ε s)+shear (rotate θ z)/clock ε s by ring, Real.exp_add]
    unfold amplitude
    ring
  rw [he, mean_add _ _ (by have hk := kinetic_continuous t z; fun_prop)
    (by have hd := shear_continuous z; fun_prop),
    mean_add _ _ continuous_const ((kinetic_continuous t z).div_const _), mean_const]
  simp only [div_eq_mul_inv, mean_mul_const]
  unfold hamiltonian kineticMean exponentialMean
  simp only [div_eq_mul_inv]
  ring

theorem hamiltonian_momentum_derivative (ε κ t : ℝ) (z : Phase) (s p : ℝ) :
    HasDerivAt (hamiltonian ε κ t z s) (clockRate ε κ t z s p) p := by
  have h := (((((hasDerivAt_id p).div_const (clock ε s)).const_add (2*t)).exp.const_mul κ).mul_const
    (exponentialMean (clock ε s) z)).const_add (kineticMean t z)
  convert (h.div_const (clock ε s)).const_add (clock ε s/2) using 1
  simp only [id_eq]
  unfold clockRate amplitude
  ring

theorem hamiltonian_clock_derivative (ε κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    HasDerivAt (fun u => hamiltonian ε κ t z u p) (-momentumRate ε κ t z s p) s := by
  have hc := (clock_positive ε s hε).ne'
  have hd : HasDerivAt (clock ε) (Real.exp s) s := (Real.hasDerivAt_exp s).add_const ε
  have hp := (hasDerivAt_const s p).div hd hc
  have ha := (hp.const_add (2*t)).exp.const_mul κ
  have he := (exponentialMean_derivative (clock ε s) hc z).comp s hd
  have h := (hd.div_const 2).add (((ha.mul he).const_add (kineticMean t z)).div hd hc)
  convert h using 1
  simp only [Pi.div_apply, Pi.mul_apply, Function.comp_apply]
  unfold momentumRate amplitude
  field_simp
  ring

theorem longitudinalRate_eq (ε κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    longitudinalRate ε κ t z s p =
      momentumRate ε κ t z s p/clock ε s-
      p*Real.exp s*clockRate ε κ t z s p/(clock ε s)^2 := by
  have hc := (clock_positive ε s hε).ne'
  unfold longitudinalRate momentumRate clockRate response
  field_simp
  ring

theorem longitudinalRate_is_bracket (ε κ t : ℝ) (hε : 0 ≤ ε) (z : Phase) (s p : ℝ) :
    bracket (longitudinal ε) (hamiltonian ε κ t z) s p = longitudinalRate ε κ t z s p := by
  rw [bracket, (KFCausalClockFloorClassicalBackreaction.longitudinal_clock_derivative ε s p hε).deriv,
    (longitudinal_momentum_derivative ε s p).deriv,
    (hamiltonian_momentum_derivative ε κ t z s p).deriv,
    (hamiltonian_clock_derivative ε κ t hε z s p).deriv,
    longitudinalRate_eq ε κ t hε z s p]
  ring

theorem kineticMean_nonnegative (t : ℝ) (z : Phase) : 0 ≤ kineticMean t z :=
  mean_nonnegative _ (fun θ => kinetic_nonnegative t (rotate θ z))

theorem clockRate_lower (ε κ t : ℝ) (hκ : 0 ≤ κ) (z : Phase) (s p : ℝ) :
    amplitude ε κ t s p/(clock ε s)^2 ≤ clockRate ε κ t z s p := by
  have ha : 0 ≤ amplitude ε κ t s p := mul_nonneg hκ (Real.exp_pos _).le
  exact div_le_div_of_nonneg_right
    (le_mul_of_one_le_right ha (exponentialMean_ge_one _ z)) (sq_nonneg _)

theorem longitudinalRate_lower (ε κ t : ℝ) (hε : 0 < ε) (hκ : 0 ≤ κ)
    (z : Phase) (s p : ℝ) : -1/2 ≤ longitudinalRate ε κ t z s p := by
  have hr := response_bounds ε s hε
  have hF : 0 ≤ exponentialMean (clock ε s) z := le_trans (by norm_num) (exponentialMean_ge_one _ z)
  have hT := tiltedShear_nonnegative (clock ε s) z
  have hK := kineticMean_nonnegative t z
  have ha : 0 ≤ amplitude ε κ t s p := mul_nonneg hκ (Real.exp_pos _).le
  have hn : 0 ≤ (kineticMean t z+amplitude ε κ t s p*
      (exponentialMean (clock ε s) z+tiltedShear (clock ε s) z))/(clock ε s)^2 := by positivity
  unfold longitudinalRate
  nlinarith [mul_nonneg hr.1.le hn]

#print axioms hamiltonian_momentum_derivative
#print axioms kinetic_continuous
#print axioms kineticMean_eq
#print axioms hamiltonian_eq_mean
#print axioms hamiltonian_clock_derivative
#print axioms longitudinalRate_eq
#print axioms longitudinalRate_is_bracket
#print axioms kineticMean_nonnegative
#print axioms clockRate_lower
#print axioms longitudinalRate_lower

end
end UnifiedTheory.Audit.KFCausalClassicalAveragedVacuum
