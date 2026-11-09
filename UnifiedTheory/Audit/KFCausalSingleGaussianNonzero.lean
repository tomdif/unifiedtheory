/- The singleton used in the mixed and averaged vacuum graphs is the
nonzero physical reciprocal Gaussian, rather than a zero witness. -/
import UnifiedTheory.Audit.KFCausalSingleGaussianSecondInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalSingleGaussianNonzero
noncomputable section
open MeasureTheory
open KFCausalSingleGaussianSecondInput (family state family_width family_coefficient)
open KFCausalCorrelatedClusteredProfiles
open KFCausalCorrelatedClusteredInputProfiles (finiteState_coe represented_sum)
open KFCausalChargeGaussianGeometry (groundWidth groundWidth_positive)
open KFCausalClockFloorInvariantTrial (neutralWidth neutralWidth_positive clockFunction
  clockFunction_continuous clockFunction_memLp clockFunction_ne_zero)

variable (ε h a : ℝ) (hε : 0 < ε) (hh : h ≠ 0) (ha : 0 < a)

theorem state_eq_gaussian : state ε h a hε hh ha=
    KFCausalReciprocalGaussianStates.state (groundWidth h) (neutralWidth h) 1
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (by norm_num)
      (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha) := by
  apply Lp.ext
  filter_upwards [finiteState_coe family ε h (fun _ => a) (fun _ => 0)
      hε hh (fun _ => ha) 1 (by norm_num),
    KFCausalReciprocalGaussianStates.state_configuration_coe (groundWidth h) (neutralWidth h) 1
      (groundWidth_positive h hh) (neutralWidth_positive h hh) (by norm_num)
      (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)] with x hx hg
  change (KFCausalCorrelatedClusteredInputProfiles.finiteState family ε h (fun _ => a) (fun _ => 0)
      hε hh (fun _ => ha) 1) x = _
  rw [hx,hg,represented_sum]
  simp only [family_width,family_coefficient]
  simp [sources,polynomials,family,count,Index,KFCausalCorrelatedClusteredPhysicalClockLimit.lift,
    KFCausalReciprocalNeutralPackets.profile,KFCausalClockFloorCoherentStrip.clockPhase]

theorem state_ne_zero : state ε h a hε hh ha ≠ 0 := by
  rw [state_eq_gaussian ε h a hε hh ha]
  exact KFCausalReciprocalGaussianStates.state_ne_zero (groundWidth h) (neutralWidth h) 1
    (groundWidth_positive h hh) (neutralWidth_positive h hh) (by norm_num)
    (clockFunction ε a) (clockFunction_continuous ε a) (clockFunction_memLp ε a hε ha)
    (clockFunction_ne_zero ε a hε.le 0)

#print axioms state_eq_gaussian
#print axioms state_ne_zero
end
end UnifiedTheory.Audit.KFCausalSingleGaussianNonzero
