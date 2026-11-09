/- Charge invariance of the actual singleton Gaussian input. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSingleGaussianCharge
noncomputable section
open KFCausalSingleGaussianSecondInput (state family)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredPhysicalClockLimit (lift)
open KFCausalStandingChargeOperator (zeroSector)
open KFCausalPhysicalCircleAction (action)

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)

theorem state_zeroSector : state ε h a hε hh ha ∈ zeroSector h hh := by
  rw [state,KFCausalCorrelatedClusteredInputProfiles.finiteState,dif_pos (by norm_num : (0:ℝ)<1)]
  exact KFCausalReciprocalNeutralSuperposition.state_zeroSector (count family) ε h
    (lift family (fun _ => a)) (widths family 1) (lift family (fun _ => 0))
    (coefficients family 1) (sources family) (polynomials family) hε
    (fun _ => ha) hh (widths_admissible family 1 (by norm_num))

theorem action_state (θ : ℝ) : action h hh θ (state ε h a hε hh ha)=state ε h a hε hh ha :=
  state_zeroSector ε h a hε hh ha θ

#print axioms state_zeroSector
#print axioms action_state
end
end UnifiedTheory.Audit.KFCausalSingleGaussianCharge
