/- Classical symbol audit of the optional clock-floor model. The actual
positive clock exp(s)+epsilon and homogeneous longitudinal symbol p/C do
not form the original canonical pair at positive epsilon. The complete
transport coordinate exp(s)+epsilon*s does. This is a classical statement;
no semiclassical limit of the quantum Hamiltonian is assumed or proved. -/
import UnifiedTheory.Audit.KFCausalClockFloorFlow
import UnifiedTheory.Audit.KFCausalLongitudinalDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock mobility)
open UnifiedTheory.Audit.KFCausalRegularizedLongitudinalChart

/-- Standard canonical bracket in the chart (s,p), with {s,p}=1. -/
def bracket (F G : ℝ → ℝ → ℝ) (s p : ℝ) : ℝ :=
  deriv (fun u => F u p) s * deriv (G s) p -
    deriv (F s) p * deriv (fun u => G u p) s

def longitudinal (ε s p : ℝ) : ℝ := p / clock ε s
def defect (ε s : ℝ) : ℝ := ε / clock ε s
def response (ε s : ℝ) : ℝ := Real.exp s / clock ε s

theorem clock_positive (ε s : ℝ) (hε : 0 ≤ ε) : 0 < clock ε s := by
  unfold clock
  positivity

theorem longitudinal_momentum_derivative (ε s p : ℝ) :
    HasDerivAt (longitudinal ε s) (clock ε s)⁻¹ p := by
  simpa only [longitudinal, div_eq_mul_inv, one_mul] using
    (hasDerivAt_id p).mul_const (clock ε s)⁻¹

theorem bracket_clock (ε s p : ℝ) :
    bracket (longitudinal ε) (fun s _ => clock ε s) s p = -response ε s := by
  simp only [bracket, deriv_const, mul_zero, zero_sub,
    (longitudinal_momentum_derivative ε s p).deriv, response]
  rw [show deriv (clock ε) s = Real.exp s from ((Real.hasDerivAt_exp s).add_const ε).deriv]
  ring

theorem response_add_defect (ε s : ℝ) (hε : 0 ≤ ε) :
    response ε s + defect ε s = 1 := by
  have hc := (clock_positive ε s hε).ne'
  unfold response defect
  rw [← add_div]
  exact div_self hc

theorem defect_positive (ε s : ℝ) (hε : 0 < ε) : 0 < defect ε s :=
  div_pos hε (clock_positive ε s hε.le)

theorem response_bounds (ε s : ℝ) (hε : 0 < ε) :
    0 < response ε s ∧ response ε s < 1 := by
  constructor
  · exact div_pos (Real.exp_pos s) (clock_positive ε s hε.le)
  · have h := response_add_defect ε s hε.le
    linarith [defect_positive ε s hε]

theorem bracket_clock_error (ε s p : ℝ) (hε : 0 ≤ ε) :
    bracket (longitudinal ε) (fun s _ => clock ε s) s p + 1 = defect ε s := by
  rw [bracket_clock]
  linarith [response_add_defect ε s hε]

theorem bracket_clock_ne_canonical (ε s p : ℝ) (hε : 0 < ε) :
    bracket (longitudinal ε) (fun s _ => clock ε s) s p ≠ -1 := by
  have h := bracket_clock_error ε s p hε.le
  have hd := defect_positive ε s hε
  intro he
  linarith

/-- The exact conjugate of p/C is the straightening coordinate, not C. -/
theorem bracket_chart (ε s p : ℝ) (hε : 0 ≤ ε) :
    bracket (longitudinal ε) (fun s _ => chart ε s) s p = -1 := by
  have hc := (clock_positive ε s hε).ne'
  simp only [bracket, deriv_const, mul_zero, zero_sub,
    (longitudinal_momentum_derivative ε s p).deriv, (chart_derivative ε s).deriv]
  exact congrArg Neg.neg (inv_mul_cancel₀ hc)

/-- This is longitudinal transport time, not Hamiltonian evolution time. -/
theorem positive_clock_transport_derivative (ε : ℝ) (hε : 0 < ε) (s t : ℝ) :
    HasDerivAt (fun u => clock ε (logFlow ε hε s u))
      (response ε (logFlow ε hε s t)) t := by
  simpa only [clock, response, clockFlow] using
    (clockFlow_derivative ε hε s t).add_const ε

/-- Clock-only homogeneous energy, the classical symbol of the F*F/2 term. -/
def clockEnergy (ε s : ℝ) (_p : ℝ) : ℝ := clock ε s / 2

theorem clock_energy_longitudinal_velocity (ε s p : ℝ) :
    bracket (longitudinal ε) (clockEnergy ε) s p = -response ε s / 2 := by
  have hd : deriv (fun s => clockEnergy ε s p) s = Real.exp s / 2 :=
    (((Real.hasDerivAt_exp s).add_const ε).div_const 2).deriv
  have hp : deriv (clockEnergy ε s) p = 0 := deriv_const p _
  unfold bracket
  rw [hd, hp, (longitudinal_momentum_derivative ε s p).deriv]
  simp only [mul_zero, zero_sub, response]
  ring

/-- Even the clock-only classical energy has a nonzero velocity defect. -/
theorem clock_energy_velocity_error (ε s p : ℝ) (hε : 0 < ε) :
    bracket (longitudinal ε) (clockEnergy ε) s p + 1/2 = defect ε s / 2 ∧
      0 < defect ε s / 2 := by
  rw [clock_energy_longitudinal_velocity]
  constructor
  · linarith [response_add_defect ε s hε.le]
  · exact div_pos (defect_positive ε s hε) (by norm_num)

/-- Restoring the original clock bracket forces the old, unbounded mobility. -/
theorem canonical_mobility_forced (ε s v : ℝ)
    (h : bracket (fun _ p => v*p) (fun s _ => clock ε s) s 0 = -1) :
    v = Real.exp (-s) := by
  have hd : deriv (fun p : ℝ => v*p) 0 = v := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul v).deriv
  simp only [bracket, deriv_const, mul_zero, zero_sub, hd] at h
  rw [show deriv (clock ε) s = Real.exp s from
    ((Real.hasDerivAt_exp s).add_const ε).deriv] at h
  rw [Real.exp_neg]
  apply mul_right_cancel₀ (Real.exp_ne_zero s)
  rw [inv_mul_cancel₀ (Real.exp_ne_zero s)]
  linarith

/-- The existing global-translation obstruction applies to this positive clock.
It does not rule out a commutator on a noninvariant quantum core. -/
theorem no_complete_unit_clock_rate (ε : ℝ) (hε : 0 ≤ ε) (s : ℝ → ℝ)
    (h : ∀ t, HasDerivAt (fun u => clock ε (s u)) 1 t) : False :=
  UnifiedTheory.Audit.KFCausalLongitudinalDomain.no_global_positive_translation
    (fun t => clock ε (s t)) (fun t => (clock_positive ε (s t) hε).le) h

#print axioms longitudinal_momentum_derivative
#print axioms bracket_clock
#print axioms response_add_defect
#print axioms defect_positive
#print axioms response_bounds
#print axioms bracket_clock_error
#print axioms bracket_clock_ne_canonical
#print axioms bracket_chart
#print axioms positive_clock_transport_derivative
#print axioms clock_energy_longitudinal_velocity
#print axioms clock_energy_velocity_error
#print axioms canonical_mobility_forced
#print axioms no_complete_unit_clock_rate

end
end UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
