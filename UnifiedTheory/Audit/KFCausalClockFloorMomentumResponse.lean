/- The response and commutator remainder are bounded physical operators.
Response multiplication preserves the full maximal longitudinal graph,
using the existing exact defect commutator. -/
import UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients
import UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalClockFloorFlow (clock mobility)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (response defect response_bounds response_add_defect)
open UnifiedTheory.Audit.KFCausalClockFloorMomentumCoefficients (remainderRate remainder_bounds)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe)
open UnifiedTheory.Audit.KFCausalClockFloorDefectMomentum (defect_momentum_graph)
open UnifiedTheory.Audit.KFCausalClockFloorLongitudinalMomentum (longitudinalMomentum)

def responseOperator (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  ContinuousLinearMap.id ℂ Hilbert-defectOperator ε hε

def remainderOperator (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  (1/(2*(ε:ℂ))) • (defectOperator ε hε).comp
    ((defectOperator ε hε).comp (responseOperator ε hε))

theorem responseOperator_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    responseOperator ε hε f =ᵐ[volume] fun x => (response ε x.1:ℂ)*f x := by
  change f-defectOperator ε hε f =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub f (defectOperator ε hε f),defectOperator_coe ε hε f] with x hx hd
  rw [hx]
  simp only [Pi.sub_apply,hd]
  have he : (response ε x.1:ℂ)+(defect ε x.1:ℂ) = 1 := by
    exact_mod_cast response_add_defect ε x.1 hε.le
  linear_combination -(f x)*he

theorem remainder_coefficient (ε s : ℝ) (hε : 0 < ε) :
    (1/(2*ε))*(defect ε s)^2*response ε s = remainderRate ε s := by
  have hc : Real.exp s+ε ≠ 0 := by positivity
  have he : ε ≠ 0 := hε.ne'
  unfold remainderRate mobility response defect clock
  field_simp [hc,he]
  ring

theorem remainderOperator_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    remainderOperator ε hε f =ᵐ[volume] fun x => (remainderRate ε x.1:ℂ)*f x := by
  let D := defectOperator ε hε
  let R := responseOperator ε hε
  change (1/(2*(ε:ℂ))) • D (D (R f)) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul (1/(2*(ε:ℂ))) (D (D (R f))),
    defectOperator_coe ε hε (D (R f)),defectOperator_coe ε hε (R f),responseOperator_coe ε hε f]
    with x hs h1 h2 hR
  change D (D (R f)) x = _ at h1
  change D (R f) x = _ at h2
  change R f x = _ at hR
  rw [hs]
  simp only [Pi.smul_apply,smul_eq_mul,h1,h2,hR]
  have he : (1/(2*(ε:ℂ)))*(defect ε x.1:ℂ)^2*(response ε x.1:ℂ) = (remainderRate ε x.1:ℂ) := by
    exact_mod_cast remainder_coefficient ε x.1 hε
  linear_combination (f x)*he

theorem responseOperator_norm (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ‖responseOperator ε hε f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [responseOperator_coe ε hε f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (response_bounds ε x.1 hε).1]
  exact mul_le_of_le_one_left (norm_nonneg _) (response_bounds ε x.1 hε).2.le

theorem remainderOperator_norm (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    ‖remainderOperator ε hε f‖ ≤ (1/(8*ε))*‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [remainderOperator_coe ε hε f] with x hx
  rw [hx,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (remainder_bounds ε x.1 hε).1]
  exact mul_le_mul_of_nonneg_right (remainder_bounds ε x.1 hε).2 (norm_nonneg _)

theorem response_graph (ε : ℝ) (hε : 0 < ε) (h : ℝ) (f g : Hilbert)
    (hg : (f,g) ∈ (longitudinalMomentum ε hε h).graph) :
    (responseOperator ε hε f,responseOperator ε hε g-
      (2*Complex.I*(h:ℂ)) • remainderOperator ε hε f) ∈ (longitudinalMomentum ε hε h).graph := by
  have hd := (longitudinalMomentum ε hε h).graph.sub_mem hg (defect_momentum_graph ε hε h f g hg)
  have he : (2*Complex.I*(h:ℂ))*(1/(2*(ε:ℂ))) = Complex.I*(h:ℂ)/(ε:ℂ) := by ring
  simpa only [responseOperator,remainderOperator,ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.id_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.comp_apply,
    Prod.sub_def,smul_smul,he,sub_add_eq_sub_sub] using hd

#print axioms responseOperator_coe
#print axioms remainder_coefficient
#print axioms remainderOperator_coe
#print axioms responseOperator_norm
#print axioms remainderOperator_norm
#print axioms response_graph

end
end UnifiedTheory.Audit.KFCausalClockFloorMomentumResponse
