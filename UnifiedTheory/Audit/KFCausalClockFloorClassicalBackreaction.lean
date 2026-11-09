/- Exact canonical Hamilton equations of the revised homogeneous symbol.
E and kappa are held fixed in the clock partial derivatives; W=kappa*exp(L).
The positive clock and longitudinal equations both acquire exp(s)/C.
This establishes a classical model difference, not a semiclassical theorem
for the ordered or charge-averaged quantum Hamiltonian. -/
import UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect

def potential (ε κ s p : ℝ) : ℝ := κ * Real.exp (longitudinal ε s p)
def hamiltonian (ε E κ s p : ℝ) : ℝ :=
  clock ε s / 2 + (E/2 + potential ε κ s p) / clock ε s

theorem longitudinal_clock_derivative (ε s p : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun s => longitudinal ε s p)
      (-(p * Real.exp s) / (clock ε s)^2) s := by
  have h := (hasDerivAt_const s p).div ((Real.hasDerivAt_exp s).add_const ε)
    (clock_positive ε s hε).ne'
  simpa only [longitudinal, clock, zero_mul, zero_sub] using h

theorem hamiltonian_momentum_derivative (ε E κ s p : ℝ) :
    HasDerivAt (hamiltonian ε E κ s)
      (potential ε κ s p / (clock ε s)^2) p := by
  have hw := ((longitudinal_momentum_derivative ε s p).exp.const_mul κ).const_add (E/2)
  have h := (hw.div_const (clock ε s)).const_add (clock ε s / 2)
  convert h using 1
  unfold potential
  ring

theorem hamiltonian_clock_derivative (ε E κ s p : ℝ) (hε : 0 ≤ ε) :
    HasDerivAt (fun s => hamiltonian ε E κ s p)
      (Real.exp s / 2 - Real.exp s *
        (E/2 + (1 + longitudinal ε s p)*potential ε κ s p) / (clock ε s)^2) s := by
  have hc := (clock_positive ε s hε).ne'
  have hd : HasDerivAt (clock ε) (Real.exp s) s := (Real.hasDerivAt_exp s).add_const ε
  have hw := ((longitudinal_clock_derivative ε s p hε).exp.const_mul κ).const_add (E/2)
  have h := (hd.div_const 2).add (hw.div hd hc)
  convert h using 1
  unfold potential longitudinal
  field_simp
  ring

theorem clock_backreaction (ε E κ s p : ℝ) :
    bracket (fun s _ => clock ε s) (hamiltonian ε E κ) s p =
      response ε s * (potential ε κ s p / clock ε s) := by
  have hd : deriv (clock ε) s = Real.exp s := ((Real.hasDerivAt_exp s).add_const ε).deriv
  simp only [bracket, hd, deriv_const, zero_mul, sub_zero,
    (hamiltonian_momentum_derivative ε E κ s p).deriv, response]
  ring

theorem longitudinal_backreaction (ε E κ s p : ℝ) (hε : 0 ≤ ε) :
    bracket (longitudinal ε) (hamiltonian ε E κ) s p =
      response ε s * (-1/2 + (E + 2*potential ε κ s p)/(2*(clock ε s)^2)) := by
  have hc := (clock_positive ε s hε).ne'
  rw [bracket, (longitudinal_clock_derivative ε s p hε).deriv,
    (longitudinal_momentum_derivative ε s p).deriv,
    (hamiltonian_momentum_derivative ε E κ s p).deriv,
    (hamiltonian_clock_derivative ε E κ s p hε).deriv]
  unfold response longitudinal
  field_simp
  ring

/-- The clock error is strictly nonzero on the positive potential branch. -/
theorem positive_potential_clock_error (ε E κ s p : ℝ) (hε : 0 < ε) (hκ : 0 < κ) :
    potential ε κ s p / clock ε s -
      bracket (fun s _ => clock ε s) (hamiltonian ε E κ) s p =
        defect ε s * (potential ε κ s p / clock ε s) ∧
    0 < defect ε s * (potential ε κ s p / clock ε s) := by
  rw [clock_backreaction ε E κ s p]
  constructor
  · have h := response_add_defect ε s hε.le
    linear_combination -(potential ε κ s p / clock ε s) * h
  · exact mul_pos (defect_positive ε s hε)
      (div_pos (mul_pos hκ (Real.exp_pos _)) (clock_positive ε s hε.le))

/-- Add one free canonical matter momentum: E=pi^2 and kappa=0.
Its conjugate position velocity retains pi/C, without the clock factor. -/
theorem free_matter_velocity (ε s p π : ℝ) :
    HasDerivAt (fun π => hamiltonian ε (π^2) 0 s p) (π / clock ε s) π := by
  have h := (((hasDerivAt_id π).pow 2).div_const 2).div_const (clock ε s)
  have he : (fun π => hamiltonian ε (π^2) 0 s p) =
      fun π => clock ε s / 2 + (π^2/2)/clock ε s := by
    funext π
    simp [hamiltonian, potential]
  rw [he]
  convert h.const_add (clock ε s / 2) using 1
  simp only [id_eq]
  ring

/-- At pi=C/2 the free matter position velocity is 1/2, while the
longitudinal velocity is -3*response/8 instead of the old -3/8. -/
theorem free_matter_witness (ε s p : ℝ) (hε : 0 ≤ ε) :
    deriv (fun π => hamiltonian ε (π^2) 0 s p) (clock ε s / 2) = 1/2 ∧
    bracket (longitudinal ε) (hamiltonian ε ((clock ε s / 2)^2) 0) s p =
      -(3/8) * response ε s := by
  have hc := (clock_positive ε s hε).ne'
  constructor
  · rw [(free_matter_velocity ε s p (clock ε s / 2)).deriv]
    field_simp
  · rw [longitudinal_backreaction ε _ 0 s p hε]
    simp only [potential, zero_mul, mul_zero, add_zero]
    field_simp
    ring

/-- A common scalar change of evolution time cannot repair these two
components simultaneously, keeping the same clock and matter observables.
This does not rule out more general changes of variables or model. -/
theorem no_common_time_rescaling (ε s p rate : ℝ) (hε : 0 < ε) :
    ¬(rate * deriv (fun π => hamiltonian ε (π^2) 0 s p) (clock ε s / 2) = 1/2 ∧
      rate * bracket (longitudinal ε) (hamiltonian ε ((clock ε s / 2)^2) 0) s p = -(3/8)) := by
  rw [(free_matter_witness ε s p hε.le).1, (free_matter_witness ε s p hε.le).2]
  rintro ⟨hm, hc⟩
  have hr : rate = 1 := by linarith
  rw [hr, one_mul] at hc
  linarith [(response_bounds ε s hε).2]

#print axioms longitudinal_clock_derivative
#print axioms hamiltonian_momentum_derivative
#print axioms hamiltonian_clock_derivative
#print axioms clock_backreaction
#print axioms longitudinal_backreaction
#print axioms positive_potential_clock_error
#print axioms free_matter_velocity
#print axioms free_matter_witness
#print axioms no_common_time_rescaling

end
end UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
