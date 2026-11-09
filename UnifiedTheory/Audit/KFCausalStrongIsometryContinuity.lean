/- Strong continuity of inverse isometries and joint evaluation.
No operator-norm continuity of the family is required. -/
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStrongIsometryContinuity
noncomputable section
open Filter
open scoped Topology

variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [NormedSpace ℂ H]

theorem inverse_strong_continuous (U : X → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ f, Continuous (fun x => U x f)) (f : H) :
    Continuous (fun x => (U x).symm f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_dist_tendsto_zero.mpr
  have he (y : X) : dist ((U y).symm f) ((U x).symm f) = dist f (U y ((U x).symm f)) := by
    rw [← (U y).isometry.dist_eq,LinearIsometryEquiv.apply_symm_apply]
  simpa only [he,LinearIsometryEquiv.apply_symm_apply,dist_self] using
    ((continuous_const (y := f)).dist (hc ((U x).symm f))).tendsto x

theorem strong_joint_apply (U : X → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ f, Continuous (fun x => U x f)) :
    Continuous (fun p : X × H => U p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb (q : X × H) : dist (U q.1 q.2) (U p.1 p.2) ≤
      dist q.2 p.2 + dist (U q.1 p.2) (U p.1 p.2) := by
    have h := dist_triangle (U q.1 q.2) (U q.1 p.2) (U p.1 p.2)
    simpa only [(U q.1).isometry.dist_eq] using h
  have hl : Tendsto (fun q : X × H => dist q.2 p.2 + dist (U q.1 p.2) (U p.1 p.2))
      (𝓝 p) (𝓝 0) := by
    have h₁ := ((continuous_snd : Continuous (fun q : X × H => q.2)).dist
      (continuous_const (y := p.2))).tendsto p
    have h₂ := (((hc p.2).comp (continuous_fst : Continuous (fun q : X × H => q.1))).dist
      (continuous_const (y := U p.1 p.2))).tendsto p
    simpa only [Function.comp_apply,dist_self,zero_add] using h₁.add h₂
  exact squeeze_zero (fun _ => dist_nonneg) hb hl

#print axioms inverse_strong_continuous
#print axioms strong_joint_apply

end
end UnifiedTheory.Audit.KFCausalStrongIsometryContinuity
