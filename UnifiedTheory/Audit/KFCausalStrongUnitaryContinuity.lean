/- Strong continuity of unitary inverses and joint evaluation. The estimates
use isometry, so no operator-norm continuity of an unbounded evolution is
required or asserted. -/
import UnifiedTheory.Audit.KFCausalDenseUnitaryExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity
noncomputable section
open Filter
open scoped Topology

variable {H X : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [TopologicalSpace X]

theorem inverse_strong_continuous (F : X → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => F t x)) (x : H) :
    Continuous (fun t => (F t).symm x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  change Tendsto (fun z => (F z).symm x) (𝓝 t) (𝓝 ((F t).symm x))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hh := ((tendsto_const_nhds (x := x)).sub ((hc ((F t).symm x)).tendsto t)).norm
  have he (z : X) : ‖(F z).symm x-(F t).symm x‖ = ‖x-F z ((F t).symm x)‖ := by
    rw [← (F z).norm_map ((F z).symm x-(F t).symm x),map_sub,LinearIsometryEquiv.apply_symm_apply]
  simpa only [he,LinearIsometryEquiv.apply_symm_apply,sub_self,norm_zero] using hh

theorem joint_evaluation_continuous (F : X → H ≃ₗᵢ[ℂ] H)
    (hc : ∀ x, Continuous (fun t => F t x)) : Continuous (fun p : X×H => F p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q : X×H => F q.1 q.2) (𝓝 p) (𝓝 (F p.1 p.2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := ((continuous_snd.tendsto p).sub (tendsto_const_nhds (x := p.2))).norm
  have h2 := (((hc p.2).comp continuous_fst).tendsto p |>.sub (tendsto_const_nhds (x := F p.1 p.2))).norm
  have hb (q : X×H) : ‖F q.1 q.2-F p.1 p.2‖ ≤ ‖q.2-p.2‖+‖F q.1 p.2-F p.1 p.2‖ := by
    have hh := norm_sub_le_norm_sub_add_norm_sub (F q.1 q.2) (F q.1 p.2) (F p.1 p.2)
    simpa only [← map_sub,(F q.1).norm_map] using hh
  apply squeeze_zero (fun q => norm_nonneg _) hb
  simpa only [Function.comp_apply,sub_self,norm_zero,zero_add] using h1.add h2

#print axioms inverse_strong_continuous
#print axioms joint_evaluation_continuous

end
end UnifiedTheory.Audit.KFCausalStrongUnitaryContinuity
