import UnifiedTheory.Audit.KFCausalConformal4DRadialInverseOrigin

/- At a critical point, composition with the actual inverse chart preserves
the Hessian because its first derivative is the identity. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalConformal4DCriticalHessian
noncomputable section
open Filter Topology
open scoped ContDiff
open KFCausalConformal4DRadialInverse KFCausalConformal4DRadialInverseOrigin

theorem critical_hessian_comp (F : Point → ℝ) (g : Point → Point)
    (hF : ContDiffAt ℝ 2 F 0) (hg : ContDiffAt ℝ 2 g 0)
    (hg0 : g 0=0) (hg1 : fderiv ℝ g 0=ContinuousLinearMap.id ℝ Point)
    (hF1 : fderiv ℝ F 0=0) :
    fderiv ℝ (fderiv ℝ (F ∘ g)) 0=fderiv ℝ (fderiv ℝ F) 0 := by
  have heF0 := hF.eventually (by decide : (2:WithTop ℕ∞)≠∞)
  have heF : ∀ᶠ p in 𝓝 (0:Point), ContDiffAt ℝ 2 F (g p) :=
    hg.continuousAt.eventually (by simpa only [hg0] using heF0)
  have heG := hg.eventually (by decide : (2:WithTop ℕ∞)≠∞)
  have he : fderiv ℝ (F ∘ g) =ᶠ[𝓝 (0:Point)]
      (fun p => (fderiv ℝ F (g p)).comp (fderiv ℝ g p)) := by
    filter_upwards [heF,heG] with p hpF hpG
    exact fderiv_comp p (hpF.differentiableAt (by norm_num))
      (hpG.differentiableAt (by norm_num))
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (show (1:WithTop ℕ∞)+1≤2 by norm_num)).differentiableAt (by norm_num)
  have hDG : DifferentiableAt ℝ (fderiv ℝ g) 0 :=
    (hg.fderiv_right (show (1:WithTop ℕ∞)+1≤2 by norm_num)).differentiableAt (by norm_num)
  have hDFg : DifferentiableAt ℝ (fderiv ℝ F) (g 0) := by
    simpa only [hg0] using hDF
  have hG := hg.differentiableAt (by norm_num)
  rw [he.fderiv_eq]
  change fderiv ℝ (fun p => ((fderiv ℝ F ∘ g) p).comp (fderiv ℝ g p)) 0=_
  rw [fderiv_clm_comp (hDFg.comp 0 hG) hDG]
  simp only [Function.comp_apply,hg0,hF1,hg1]
  rw [fderiv_comp 0 hDFg hG,hg0,hg1]
  apply ContinuousLinearMap.ext
  intro p
  apply ContinuousLinearMap.ext
  intro q
  simp

theorem inverse_critical_hessian (c : ℝ) (hc : |c|≤1/54) (F : Point → ℝ)
    (hF : ContDiffAt ℝ 2 F 0) (hF1 : fderiv ℝ F 0=0) :
    fderiv ℝ (fderiv ℝ (F ∘ inverse c hc)) 0=fderiv ℝ (fderiv ℝ F) 0 := by
  apply critical_hessian_comp F (inverse c hc) hF
    ((inverse_smoothAt c hc 0 (by norm_num [targetBox])).of_le
      (show (2:WithTop ℕ∞)≤∞ from WithTop.coe_le_coe.mpr le_top))
    (inverse_origin c hc) (inverse_origin_fderiv c hc) hF1

theorem ray_second_hasDerivAt (F : Point → ℝ) (hF : ContDiffAt ℝ 2 F 0) (d : Point) :
    HasDerivAt (deriv (fun l : ℝ => F (l • d)))
      (fderiv ℝ (fderiv ℝ F) 0 d d) 0 := by
  have hDF : DifferentiableAt ℝ (fderiv ℝ F) 0 :=
    (hF.fderiv_right (show (1:WithTop ℕ∞)+1≤2 by norm_num)).differentiableAt (by norm_num)
  have hline : ContinuousAt (fun l : ℝ => l • d) 0 := by fun_prop
  have heF : ∀ᶠ l in 𝓝 (0:ℝ), ContDiffAt ℝ 2 F (l • d) :=
    hline.eventually (by simpa only [zero_smul] using
      (hF.eventually (by decide : (2:WithTop ℕ∞)≠∞)))
  have he : deriv (fun l : ℝ => F (l • d)) =ᶠ[𝓝 (0:ℝ)]
      (fun l => fderiv ℝ F (l • d) d) := by
    filter_upwards [heF] with l hl
    have hd := (hl.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt l
      ((hasDerivAt_id l).smul_const d)
    simpa only [Function.comp_apply,id_eq,one_smul] using hd.deriv
  have hDF' : HasFDerivAt (fderiv ℝ F) (fderiv ℝ (fderiv ℝ F) 0) ((0:ℝ) • d) := by
    simpa only [zero_smul] using hDF.hasFDerivAt
  have h1 : HasDerivAt (fun l : ℝ => fderiv ℝ F (l • d))
      (fderiv ℝ (fderiv ℝ F) 0 d) 0 := by
    simpa only [Function.comp_apply,id_eq,one_smul] using
      hDF'.comp_hasDerivAt 0 ((hasDerivAt_id (0:ℝ)).smul_const d)
  have h2 : HasDerivAt (fun l : ℝ => fderiv ℝ F (l • d) d)
      (fderiv ℝ (fderiv ℝ F) 0 d d) 0 := by
    simpa only [map_zero,zero_add,add_zero] using h1.clm_apply (hasDerivAt_const (0:ℝ) d)
  exact h2.congr_of_eventuallyEq he

#print axioms critical_hessian_comp
#print axioms inverse_critical_hessian
#print axioms ray_second_hasDerivAt
end
end UnifiedTheory.Audit.KFCausalConformal4DCriticalHessian
