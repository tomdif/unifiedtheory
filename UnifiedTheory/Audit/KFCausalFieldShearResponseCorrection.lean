/- The signed two-vector matter response becomes a genuine weighted
shear expectation plus an explicit field-derivative correction. The
correction is bounded in a lower-degree moment, not in energy alone. -/
import UnifiedTheory.Audit.KFCausalCoherentFieldShearGraph
import UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection
noncomputable section
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumCommutator (shearCorrection shearCorrection_bound)
open UnifiedTheory.Audit.KFCausalClockFloorPureClockVacuumResponse (response response_split)
open UnifiedTheory.Audit.KFCausalClockFloorSignedShearResponse (response_weighted_shear)
open UnifiedTheory.Audit.KFCausalClockFloorShearWeight (root)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator)

variable (ε : ℝ) (hε : 0 < ε) (h : ℝ) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "C" => shearCorrection ε hε h hb
local notation "D" => defectOperator ε hε
local notation "responseL" => KFCausalClockFloorVacuumMomentumResponse.response ε hε h hb

def derivativeCorrection (u d : Hilbert) : ℝ := 2*(inner ℂ u (C d)).re

theorem derivativeCorrection_bound (u d : Hilbert) :
    |derivativeCorrection ε hε h hb u d| ≤ (4*|h|/ε^2)*‖u‖*‖D (D d)‖ := by
  unfold derivativeCorrection
  rw [abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  calc
    _ ≤ 2*(‖u‖*‖C d‖) := mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (norm_inner_le_norm (𝕜 := ℂ) _ _)) (by norm_num)
    _ ≤ 2*(‖u‖*((2*|h|/ε^2)*‖D (D d)‖)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (shearCorrection_bound ε hε h hb d) (norm_nonneg u)) (by norm_num)
    _ = _ := by ring

variable (hh : h ≠ 0)
local notation "W" => root ε hε h hb hh

theorem corrected_response (u j d : Hilbert)
    (hj : (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph) :
    response ε hε h hb u j = responseL u+
      (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re-
      derivativeCorrection ε hε h hb u d := by
  have he : (inner ℂ u (C (j+(-Complex.I*(h:ℂ)) • d))).im =
      (inner ℂ u (C j)).im-h*(inner ℂ u (C d)).re := by
    simp only [map_add,map_smul,inner_add_right,inner_smul_right,Complex.add_im,
      Complex.mul_im,Complex.mul_re,Complex.neg_re,Complex.neg_im,Complex.I_re,Complex.I_im,
      Complex.ofReal_re,Complex.ofReal_im,neg_zero,mul_zero,zero_mul,sub_zero]
    ring
  have hr := response_weighted_shear ε hε h hb hh u (j+(-Complex.I*(h:ℂ)) • d) hj
  rw [response_split ε hε h hb hh,he] at hr
  rw [response_split ε hε h hb hh]
  unfold derivativeCorrection
  have hc : (2/h)*h = 2 := by field_simp
  rw [mul_sub,← mul_assoc,hc] at hr
  linarith

theorem corrected_response_error (u j d : Hilbert)
    (hj : (u,j+(-Complex.I*(h:ℂ)) • d) ∈ (shearMomentum h).graph) :
    |response ε hε h hb u j-(responseL u+
      (4/ε^2)*(inner ℂ (W u) (W (j+(-Complex.I*(h:ℂ)) • d))).re)| ≤
      (4*|h|/ε^2)*‖u‖*‖D (D d)‖ := by
  rw [corrected_response ε hε h hb hh u j d hj,sub_sub_cancel_left,abs_neg]
  exact derivativeCorrection_bound ε hε h hb u d

#print axioms derivativeCorrection_bound
#print axioms corrected_response
#print axioms corrected_response_error
end
end UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection
