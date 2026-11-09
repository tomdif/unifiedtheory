import UnifiedTheory.Audit.KFCausalBDG4DCompactSymmetricTensor
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/- Actual directional derivatives of smooth compact two-variable profiles.
No derivative or support certificate is an additional input. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactPartials
noncomputable section
open Set
open scoped ContDiff

abbrev Point := ℝ × ℝ
def directional (F : Point → ℝ) (d : Point) (p : Point) : ℝ := fderiv ℝ F p d
def du (F : Point → ℝ) : Point → ℝ := directional F (1,0)
def dv (F : Point → ℝ) : Point → ℝ := directional F (0,1)

theorem directional_smooth (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (d : Point) :
    ContDiff ℝ ∞ (directional F d) := by
  exact (contDiff_infty_iff_fderiv.mp hF).2.clm_apply contDiff_const

theorem directional_support (F : Point → ℝ) (d : Point) :
    tsupport (directional F d) ⊆ tsupport F := tsupport_fderiv_apply_subset ℝ d

theorem directional_compact (F : Point → ℝ) (hF : HasCompactSupport F) (d : Point) :
    HasCompactSupport (directional F d) := hF.fderiv_apply ℝ d

theorem derivative_u (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (u v : ℝ) :
    HasDerivAt (fun x => F (x,v)) (du F (u,v)) u := by
  have h := (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt u
    ((hasDerivAt_id u).prodMk (hasDerivAt_const u v))
  simpa only [du,directional] using h

theorem derivative_v (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (u v : ℝ) :
    HasDerivAt (fun x => F (u,x)) (dv F (u,v)) v := by
  have h := (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt.comp_hasDerivAt v
    ((hasDerivAt_const v u).prodMk (hasDerivAt_id v))
  simpa only [dv,directional] using h

private theorem directional_directional (F : Point → ℝ) (hF : ContDiff ℝ ∞ F)
    (d e p : Point) : directional (directional F d) e p = fderiv ℝ (fderiv ℝ F) p e d := by
  have hf := (contDiff_infty_iff_fderiv.mp hF).2.differentiable (by norm_num)
  unfold directional
  rw [fderiv_clm_apply hf.differentiableAt (differentiableAt_const d)]
  simp

theorem directional_commute (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) (d e : Point) :
    directional (directional F d) e = directional (directional F e) d := by
  funext p
  rw [directional_directional F hF d e p,directional_directional F hF e d p]
  exact hF.contDiffAt.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    exact WithTop.coe_le_coe.mpr le_top) e d

theorem du_dv (F : Point → ℝ) (hF : ContDiff ℝ ∞ F) : du (dv F) = dv (du F) :=
  directional_commute F hF (0,1) (1,0)

theorem compact_radius (F : Point → ℝ) (hF : HasCompactSupport F) :
    ∃ R > 0, ∀ p ∈ tsupport F, |p.1| < R ∧ |p.2| < R := by
  obtain ⟨R,hR,h⟩ := hF.isBounded.exists_pos_norm_lt
  refine ⟨R,hR,fun p hp => ?_⟩
  have hn := h p hp
  rw [Prod.norm_def] at hn
  exact ⟨(le_max_left _ _).trans_lt hn,(le_max_right _ _).trans_lt hn⟩

theorem outside_radius (F G : Point → ℝ) (R : ℝ)
    (hR : ∀ p ∈ tsupport F, |p.1| < R ∧ |p.2| < R)
    (hG : tsupport G ⊆ tsupport F) (u v : ℝ) (h : R ≤ |u| ∨ R ≤ |v|) :
    G (u,v)=0 := by
  apply image_eq_zero_of_notMem_tsupport
  intro hp
  have hh := hR (u,v) (hG hp)
  rcases h with hu | hv
  · exact (not_lt_of_ge hu) hh.1
  · exact (not_lt_of_ge hv) hh.2

theorem compact_bound (F : Point → ℝ) (hF : HasCompactSupport F) (hc : Continuous F) :
    ∃ C ≥ 0, ∀ p, |F p| ≤ C := by
  obtain ⟨C,hC⟩ := hF.exists_bound_of_continuous hc
  refine ⟨max C 0,le_max_right _ _,fun p => ?_⟩
  exact (hC p).trans (le_max_left _ _)

#print axioms directional_smooth
#print axioms directional_support
#print axioms directional_compact
#print axioms derivative_u
#print axioms derivative_v
#print axioms directional_commute
#print axioms du_dv
#print axioms compact_radius
#print axioms outside_radius
#print axioms compact_bound
end
end UnifiedTheory.Audit.KFCausalBDG4DSmoothCompactPartials
