/- The actual real matter correction is controlled by the same field
state and its defect-weighted shear graph, with explicit coefficients.
The shear graph norm still needs a sufficient Hamiltonian comparison. -/
import UnifiedTheory.Audit.KFCausalFieldShearHardy
import UnifiedTheory.Audit.KFCausalFieldCorrectionRealPairing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1200000

namespace UnifiedTheory.Audit.KFCausalFieldShearHardyCorrection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalConfigurationTestSpace (Hilbert)
open UnifiedTheory.Audit.KFCausalTransverseDilationFlow (Transverse)
open UnifiedTheory.Audit.KFCausalClockFloorCoherentCommonDomain (coherentSpan)
open UnifiedTheory.Audit.KFCausalClockFloorTrialSpectralDomain (orderedExponential)
open UnifiedTheory.Audit.KFCausalTransverseShearMomentum (shearMomentum)
open UnifiedTheory.Audit.KFCausalFieldWeightedClockCommutator (fieldPower)
open UnifiedTheory.Audit.KFCausalFieldShearDifferential (powerSlope)
open UnifiedTheory.Audit.KFCausalClockFloorDefectOperator (defectOperator defectOperator_coe defectOperator_norm_le)
open UnifiedTheory.Audit.KFCausalClockFloorCanonicalDefect (defect)
open UnifiedTheory.Audit.KFCausalFieldShearResponseCorrection (derivativeCorrection)

def cube (ε : ℝ) (hε : 0 < ε) : Hilbert →L[ℂ] Hilbert :=
  (defectOperator ε hε).comp ((defectOperator ε hε).comp (defectOperator ε hε))

theorem cube_coe (ε : ℝ) (hε : 0 < ε) (f : Hilbert) :
    cube ε hε f =ᵐ[volume] fun x => ((defect ε x.1:ℂ)^3)*f x := by
  filter_upwards [defectOperator_coe ε hε (defectOperator ε hε (defectOperator ε hε f)),
    defectOperator_coe ε hε (defectOperator ε hε f),defectOperator_coe ε hε f] with x h0 h1 h2
  change cube ε hε f x = _ at h0
  rw [h0,h1,h2]
  ring

theorem cube_norm_le (ε : ℝ) (hε : 0 < ε) (f : Hilbert) : ‖cube ε hε f‖ ≤ ‖f‖ :=
  (defectOperator_norm_le ε hε (defectOperator ε hε (defectOperator ε hε f))).trans
    ((defectOperator_norm_le ε hε (defectOperator ε hε f)).trans (defectOperator_norm_le ε hε f))

theorem coefficient_expand (ε h p u k v : ℝ) (hε : 0 < ε) (hh : h ≠ 0) :
    (20*h^2/ε^3)*u*((2*p/|h|)*k+(p/2)*v) =
      (40*p*|h|/ε^3)*u*k+(10*p*h^2/ε^3)*u*v := by
  have he : h^2=|h|^2 := (sq_abs h).symm
  rw [he]
  field_simp [hε.ne',abs_ne_zero.mpr hh]
  ring

theorem scalar_young (A B η u k v : ℝ) (hB : 0 ≤ B) (hη : 0 < η)
    (hu : 0 ≤ u) (hv : v ≤ u) :
    A*u*k+B*u*v ≤ η*k^2+(A^2/(4*η)+B)*u^2 := by
  have hy : A*u*k ≤ η*k^2+(A^2/(4*η))*u^2 := by
    apply (mul_le_mul_iff_right₀ (show 0 < 4*η by positivity)).mp
    have he : (4*η)*(A^2/(4*η)) = A^2 := mul_div_cancel₀ _ (by positivity)
    have he' := congrArg (fun z : ℝ => z*u^2) he
    nlinarith only [sq_nonneg (2*η*k-A*u),he']
  have hb := mul_le_mul_of_nonneg_left hv (mul_nonneg hB hu)
  nlinarith only [hy,hb]

variable (ε a h : ℝ) (hε : 0 < ε) (ha : 0 < a) (hh : h ≠ 0) (hb : |h| ≤ 2*Real.pi*ε/3)
local notation "D3" => cube ε hε

theorem actual_correction_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (g jg u j d : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x) :
    |derivativeCorrection ε hε h hb u d| ≤
      (40*((i.val:ℝ)+1)*|h|/ε^3)*‖u‖*‖D3 (j+(-Complex.I*(h:ℂ)) • d)‖+
        (10*((i.val:ℝ)+1)*h^2/ε^3)*‖u‖*‖D3 u‖ := by
  obtain ⟨d',hd',_,hbound⟩ := KFCausalFieldShearHardy.actual_weighted_bound
    ε a h hε ha hh hb l i f hf g jg u j hg hjg hu hj D3
      (fun s => (defect ε s:ℂ)^3) (cube_coe ε hε)
  have ed : d'=d := Lp.ext (hd'.trans hd.symm)
  rw [ed] at hbound
  have hc := KFCausalFieldCorrectionRealPairing.field_correction_bound ε hε h hb l i g u d hu hd
  change |derivativeCorrection ε hε h hb u d| ≤ ((20*h^2/ε^3)*‖u‖)*‖D3 d‖ at hc
  have hs := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (20*h^2/ε^3)*‖u‖ by positivity)
  exact hc.trans (hs.trans_eq (coefficient_expand ε h ((i.val:ℝ)+1) ‖u‖
    ‖D3 (j+(-Complex.I*(h:ℂ)) • d)‖ ‖D3 u‖ hε hh))

theorem actual_infinitesimal_bound (l : Transverse →L[ℝ] ℝ) (i : Fin 2) (f : Hilbert)
    (hf : f ∈ coherentSpan ε a h hε ha hh) (g jg u j d : Hilbert)
    (hg : (f,g) ∈ (orderedExponential ε hε h).graph) (hjg : (g,jg) ∈ (shearMomentum h).graph)
    (hu : (g,u) ∈ (fieldPower l i).graph) (hj : (jg,j) ∈ (fieldPower l i).graph)
    (hd : d =ᵐ[volume] fun x => powerSlope l i x*g x) (η : ℝ) (hη : 0 < η) :
    |derivativeCorrection ε hε h hb u d| ≤
      η*‖D3 (j+(-Complex.I*(h:ℂ)) • d)‖^2+
        ((40*((i.val:ℝ)+1)*|h|/ε^3)^2/(4*η)+10*((i.val:ℝ)+1)*h^2/ε^3)*‖u‖^2 := by
  exact (actual_correction_bound ε a h hε ha hh hb l i f hf g jg u j d hg hjg hu hj hd).trans
    (scalar_young _ _ η ‖u‖ ‖D3 (j+(-Complex.I*(h:ℂ)) • d)‖ ‖D3 u‖
      (by positivity) hη (norm_nonneg _) (cube_norm_le ε hε u))

#print axioms cube_coe
#print axioms cube_norm_le
#print axioms coefficient_expand
#print axioms scalar_young
#print axioms actual_correction_bound
#print axioms actual_infinitesimal_bound
end
end UnifiedTheory.Audit.KFCausalFieldShearHardyCorrection
