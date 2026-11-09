/- The complex shear is an entire one-parameter group. These identities
factor a real reference clock out of the direct holomorphic multiplier;
they do not commute distinct charge-conjugated shears. -/
import UnifiedTheory.Audit.KFCausalComplexShearPerturbation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalComplexShearGroup
noncomputable section
open KFCausalComplexShearPerturbation (Space flow rotatedFlow)

theorem flow_zero (σ : ℝ) (x : Space) : flow σ 0 x=x := by
  ext i
  fin_cases i <;> simp [flow]

theorem flow_compose (σ : ℝ) (z t : ℂ) (x : Space) :
    flow σ z (flow σ t x)=flow σ (z+t) x := by
  have hp : Complex.exp ((z+t)/2)=Complex.exp (z/2)*Complex.exp (t/2) := by
    rw [add_div,Complex.exp_add]
  have hm : Complex.exp (-(z+t)/2)=Complex.exp (-z/2)*Complex.exp (-t/2) := by
    rw [neg_add,add_div,Complex.exp_add]
  ext i
  fin_cases i <;> dsimp [flow]
  all_goals simp only [hp,hm]
  all_goals ring

theorem rotated_zero (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (x : Space) :
    rotatedFlow U σ 0 x=x := by
  rw [rotatedFlow,flow_zero,U.symm_apply_apply]

theorem rotated_compose (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (z t : ℂ) (x : Space) :
    rotatedFlow U σ z (rotatedFlow U σ t x)=rotatedFlow U σ (z+t) x := by
  simp only [rotatedFlow,U.apply_symm_apply,flow_compose]

theorem rotated_reference (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (z t : ℂ) (x : Space) :
    rotatedFlow U σ (z-t) (rotatedFlow U σ t x)=rotatedFlow U σ z x := by
  rw [rotated_compose,sub_add_cancel]

theorem flow_real (σ t : ℝ) (x : Space) (hx : ∀ i, (x i).im=0) :
    ∀ i, (flow σ (t:ℂ) x i).im=0 := by
  intro i
  fin_cases i <;> simp [flow,Complex.mul_im,Complex.add_im,Complex.exp_im,hx]

theorem flow_analytic (σ : ℝ) (x : Space) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => flow σ t x) z := by
  apply ((PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 5 => ℂ)).symm.toContinuousLinearMap.analyticAt _).comp
  apply analyticAt_pi_iff.mpr
  intro i
  fin_cases i <;> dsimp
  all_goals fun_prop

theorem rotated_analytic (U : Space ≃ₗᵢ[ℂ] Space) (σ : ℝ) (x : Space) (z : ℂ) :
    AnalyticAt ℂ (fun t : ℂ => rotatedFlow U σ t x) z := by
  exact (U.symm.toContinuousLinearEquiv.toContinuousLinearMap.analyticAt _).comp (flow_analytic σ (U x) z)

#print axioms flow_zero
#print axioms flow_compose
#print axioms rotated_zero
#print axioms rotated_compose
#print axioms rotated_reference
#print axioms flow_real
#print axioms flow_analytic
#print axioms rotated_analytic
end
end UnifiedTheory.Audit.KFCausalComplexShearGroup
