/- Identification of the drift coefficient with the defect equation of
the actual revised homogeneous classical Hamiltonian symbol. -/
import UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
import UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityScalar

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical
noncomputable section
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect
open UnifiedTheory.Audit.KFCausalClockFloorClassicalBackreaction
open UnifiedTheory.Audit.KFCausalClockFloorDefectTransportScalar (drift)

theorem defect_clock_derivative (ε s : ℝ) (hε : 0 < ε) :
    HasDerivAt (defect ε) (-(ε*Real.exp s)/(clock ε s)^2) s := by
  have hd := ((((Real.hasDerivAt_exp s).add_const ε).inv
    (clock_positive ε s hε.le).ne').const_mul ε)
  convert hd using 1
  unfold clock
  ring

theorem classical_defect_velocity (ε E κ s p : ℝ) (hε : 0 < ε) :
    bracket (fun s _ => defect ε s) (hamiltonian ε E κ) s p =
      drift ε (defect ε s)*(potential ε κ s p/clock ε s) := by
  rw [bracket,(defect_clock_derivative ε s hε).deriv,deriv_const,
    zero_mul,sub_zero,(hamiltonian_momentum_derivative ε E κ s p).deriv]
  have hc := (clock_positive ε s hε.le).ne'
  unfold drift defect
  field_simp
  unfold clock
  ring

#print axioms defect_clock_derivative
#print axioms classical_defect_velocity

end
end UnifiedTheory.Audit.KFCausalClockFloorQuantumVelocityClassical
