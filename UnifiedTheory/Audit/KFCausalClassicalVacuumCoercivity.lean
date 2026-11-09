/- Removing the cyclic neutral position leaves a phase norm controlled by
energy variables and the two clock coordinates. -/
import UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
import UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity
noncomputable section
open UnifiedTheory.Audit.KFCausalClassicalChargePhase
open UnifiedTheory.Audit.KFCausalClassicalVacuumSmooth
open UnifiedTheory.Audit.KFCausalCanonicalPhaseODE
open UnifiedTheory.Audit.KFCausalClassicalVacuumNeutral
open UnifiedTheory.Audit.KFCausalClassicalVacuumTranslation
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergy
open UnifiedTheory.Audit.KFCausalClassicalVacuumEnergyBounds
open UnifiedTheory.Audit.KFCausalClassicalVacuumShearBounds

theorem erased_norm_squares (z : Phase) :
    ‖(eraseNeutral z).1‖^2+‖(eraseNeutral z).2‖^2 =
      (q (.inr 0) z)^2+(p (.inr 0) z)^2+phaseSize z := by
  simp [EuclideanSpace.norm_sq_eq,eraseNeutral_apply,neutralShift,positionBasis,
    PiLp.basisFun_apply,Fin.sum_univ_succ,phaseSize,staticKinetic,growingKinetic,
    q_apply,p_apply,Real.norm_eq_abs,sq_abs]
  ring

theorem erased_norm_bound (z : Phase) :
    ‖eraseNeutral z‖ ≤ |q (.inr 0) z|+|p (.inr 0) z|+phaseSize z+1 := by
  have he := erased_norm_squares z
  have hp := phaseSize_nonnegative z
  have hq := abs_nonneg (q (.inr 0) z)
  have hr := abs_nonneg (p (.inr 0) z)
  have hqp := mul_nonneg hq hr
  have hqP := mul_nonneg hq hp
  have hrP := mul_nonneg hr hp
  rw [Prod.norm_def]
  apply max_le
  · nlinarith [sq_nonneg ‖(eraseNeutral z).2‖,sq_abs (q (.inr 0) z),
      sq_abs (p (.inr 0) z),sq_nonneg (phaseSize z)]
  · nlinarith [sq_nonneg ‖(eraseNeutral z).1‖,sq_abs (q (.inr 0) z),
      sq_abs (p (.inr 0) z),sq_nonneg (phaseSize z)]

theorem phase_reconstruct (z : Phase) :
    z = eraseNeutral z+q (.inr 3) z • positionBasis (.inr 3) := by
  simp [eraseNeutral,sub_add_cancel]

theorem phase_norm_bound (z : Phase) :
    ‖z‖ ≤ |q (.inr 0) z|+|p (.inr 0) z|+phaseSize z+1+
      |q (.inr 3) z| *‖positionBasis (.inr 3)‖ := by
  calc
    _ = ‖eraseNeutral z+q (.inr 3) z • positionBasis (.inr 3)‖ := congrArg norm (phase_reconstruct z)
    _ ≤ ‖eraseNeutral z‖+‖q (.inr 3) z • positionBasis (.inr 3)‖ := norm_add_le _ _
    _ ≤ _ := by
      simpa only [norm_smul,Real.norm_eq_abs,add_comm] using
        add_le_add_right (erased_norm_bound z) ‖q (.inr 3) z • positionBasis (.inr 3)‖

#print axioms erased_norm_squares
#print axioms erased_norm_bound
#print axioms phase_reconstruct
#print axioms phase_norm_bound

end
end UnifiedTheory.Audit.KFCausalClassicalVacuumCoercivity
