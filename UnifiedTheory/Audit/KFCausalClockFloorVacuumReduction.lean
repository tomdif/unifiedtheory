/- Exact reduction of the revised vacuum clock Hamiltonian. The variables
are canonical s,p and L=p/(exp(s)+epsilon); the time parameter is physical
Hamiltonian time. The relation to the full quantum semiclassical dynamics
is not assumed by these classical identities. -/
import UnifiedTheory.Audit.KFCausalClockFloorReducedODE

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart (chart chart_derivative)
open UnifiedTheory.Audit.KFCausalClockFloorReducedODE (rate)

def amplitude (ε κ t s L : ℝ) : ℝ := κ*Real.exp (2*t+L)/clock ε s
def energy (ε κ t s L : ℝ) : ℝ := clock ε s/2+amplitude ε κ t s L
def invariant (ε κ t s L : ℝ) : ℝ := energy ε κ t s L-2*chart ε s

def canonicalHamiltonian (ε κ t s p : ℝ) : ℝ := hamiltonian ε 0 (κ*Real.exp (2*t)) s p

theorem energy_canonical (ε κ t s L : ℝ) (hε : 0 < ε) :
    canonicalHamiltonian ε κ t s (clock ε s*L) = energy ε κ t s L := by
  have hc := (clock_positive ε s hε.le).ne'
  unfold canonicalHamiltonian hamiltonian potential longitudinal energy amplitude
  rw [mul_div_cancel_left₀ L hc,Real.exp_add]
  ring

theorem rate_identity (ε κ t s L : ℝ) (hε : 0 < ε) :
    rate ε (invariant ε κ t s L) s = amplitude ε κ t s L/clock ε s := by
  have hc := (clock_positive ε s hε.le).ne'
  unfold rate invariant energy chart
  field_simp
  unfold clock
  ring

variable (ε κ : ℝ) (hε : 0 < ε) (s L : ℝ → ℝ)
include hε

theorem amplitude_derivative (t : ℝ)
    (hs : HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) :
    HasDerivAt (fun u => amplitude ε κ u (s u) (L u))
      ((2-response ε (s t)/2)*amplitude ε κ t (s t) (L t)) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have hd := (((((hasDerivAt_id t).const_mul 2).add hL).exp).const_mul κ).div
    ((hs.exp).add_const ε) hc
  convert hd using 1
  dsimp only [Pi.add_apply,id_eq]
  unfold amplitude response clock
  dsimp only [clock] at hc
  field_simp
  ring

theorem energy_derivative (t : ℝ)
    (hs : HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) :
    HasDerivAt (fun u => energy ε κ u (s u) (L u)) (2*amplitude ε κ t (s t) (L t)) t := by
  have hd := (((hs.exp).add_const ε).div_const 2).add (amplitude_derivative ε κ hε s L t hs hL)
  convert hd using 1
  unfold response
  ring

theorem invariant_derivative (t : ℝ)
    (hs : HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) :
    HasDerivAt (fun u => invariant ε κ u (s u) (L u)) 0 t := by
  have hd := (energy_derivative ε κ hε s L t hs hL).sub
    (((chart_derivative ε (s t)).comp t hs).const_mul 2)
  convert hd using 1
  have hc := (clock_positive ε (s t) hε.le).ne'
  change 0 = 2*amplitude ε κ t (s t) (L t)-2*(clock ε (s t)*(amplitude ε κ t (s t) (L t)/clock ε (s t)))
  field_simp
  ring

theorem invariant_constant
    (hs : ∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : ∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t)
    (t : ℝ) : invariant ε κ t (s t) (L t) = invariant ε κ 0 (s 0) (L 0) :=
  is_const_of_deriv_eq_zero
    (fun u => (invariant_derivative ε κ hε s L u (hs u) (hL u)).differentiableAt)
    (fun u => (invariant_derivative ε κ hε s L u (hs u) (hL u)).deriv) t 0

theorem clock_reduction
    (hs : ∀ t, HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : ∀ t, HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t)
    (t : ℝ) : HasDerivAt s (rate ε (invariant ε κ 0 (s 0) (L 0)) (s t)) t := by
  rw [← invariant_constant ε κ hε s L hs hL t,rate_identity ε κ t (s t) (L t) hε]
  exact hs t

theorem canonical_equations (t : ℝ)
    (hs : HasDerivAt s (amplitude ε κ t (s t) (L t)/clock ε (s t)) t)
    (hL : HasDerivAt L (response ε (s t)*(-1/2+amplitude ε κ t (s t) (L t)/clock ε (s t))) t) :
    HasDerivAt s (deriv (canonicalHamiltonian ε κ t (s t)) (clock ε (s t)*L t)) t ∧
    HasDerivAt (fun u => clock ε (s u)*L u)
      (-deriv (fun x => canonicalHamiltonian ε κ t x (clock ε (s t)*L t)) (s t)) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have he : longitudinal ε (s t) (clock ε (s t)*L t) = L t := by
    unfold longitudinal
    exact mul_div_cancel_left₀ _ hc
  constructor
  · change HasDerivAt s (deriv (hamiltonian ε 0 (κ*Real.exp (2*t)) (s t)) _) t
    rw [(hamiltonian_momentum_derivative ε 0 (κ*Real.exp (2*t)) (s t) _).deriv,potential,he]
    convert hs using 1
    unfold amplitude
    rw [Real.exp_add]
    field_simp
  · have hd := ((hs.exp).add_const ε).mul hL
    change HasDerivAt _ (-deriv (fun x => hamiltonian ε 0 (κ*Real.exp (2*t)) x _) _) t
    rw [(hamiltonian_clock_derivative ε 0 (κ*Real.exp (2*t)) (s t) _ hε.le).deriv,
      potential,he]
    convert hd using 1
    unfold amplitude response
    rw [Real.exp_add]
    field_simp
    unfold clock
    ring

omit s L in
theorem longitudinal_equations (s p : ℝ → ℝ) (t : ℝ)
    (hs : HasDerivAt s (deriv (canonicalHamiltonian ε κ t (s t)) (p t)) t)
    (hp : HasDerivAt p (-deriv (fun x => canonicalHamiltonian ε κ t x (p t)) (s t)) t) :
    HasDerivAt s (amplitude ε κ t (s t) (p t/clock ε (s t))/clock ε (s t)) t ∧
    HasDerivAt (fun u => p u/clock ε (s u))
      (response ε (s t)*(-1/2+amplitude ε κ t (s t) (p t/clock ε (s t))/clock ε (s t))) t := by
  have hc := (clock_positive ε (s t) hε.le).ne'
  have hs' := hs
  have hp' := hp
  change HasDerivAt s (deriv (hamiltonian ε 0 (κ*Real.exp (2*t)) (s t)) (p t)) t at hs'
  rw [(hamiltonian_momentum_derivative ε 0 (κ*Real.exp (2*t)) (s t) (p t)).deriv] at hs'
  change HasDerivAt p (-deriv (fun x => hamiltonian ε 0 (κ*Real.exp (2*t)) x (p t)) (s t)) t at hp'
  rw [(hamiltonian_clock_derivative ε 0 (κ*Real.exp (2*t)) (s t) (p t) hε.le).deriv] at hp'
  constructor
  · convert hs' using 1
    unfold amplitude potential longitudinal
    rw [Real.exp_add]
    field_simp
  · have hd := hp'.div ((hs'.exp).add_const ε) hc
    convert hd using 1
    unfold amplitude potential longitudinal response clock
    dsimp only [clock] at hc
    rw [Real.exp_add]
    field_simp
    ring

#print axioms energy_canonical
#print axioms rate_identity
#print axioms amplitude_derivative
#print axioms energy_derivative
#print axioms invariant_derivative
#print axioms invariant_constant
#print axioms clock_reduction
#print axioms canonical_equations
#print axioms longitudinal_equations

end
end UnifiedTheory.Audit.KFCausalClockFloorVacuumReduction
