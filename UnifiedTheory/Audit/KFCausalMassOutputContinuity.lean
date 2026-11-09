/- Uniform form-norm bounds and continuity after the mass map imply
continuity in physical norm. Uniform operator bounds extend it from dense data. -/
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalMassOutputContinuity
noncomputable section
open Set Filter Topology
variable {V H X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [TopologicalSpace X]

theorem difference_bound (J : V →L[ℂ] H) (M : V →L[ℂ] V)
    (hm : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y)) (C : ℝ)
    (x y : V) (hx : ‖x‖ ≤ C) (hy : ‖y‖ ≤ C) :
    ‖J x-J y‖^2 ≤ (2*C)*‖M x-M y‖ := by
  have he : ‖J (x-y)‖^2 = (inner ℂ (M (x-y)) (x-y)).re :=
    (norm_sq_eq_re_inner (𝕜 := ℂ) _).trans (congrArg Complex.re (hm (x-y) (x-y))).symm
  have hb : ‖x-y‖ ≤ 2*C := (norm_sub_le x y).trans (by linarith)
  rw [← map_sub,he]
  have hn := (re_inner_le_norm (𝕜 := ℂ) (M (x-y)) (x-y)).trans
    (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  simpa only [map_sub,mul_comm] using hn

theorem continuous_embedding (J : V →L[ℂ] H) (M : V →L[ℂ] V)
    (hm : ∀ x y, inner ℂ (M x) y = inner ℂ (J x) (J y))
    (u : X → V) (C : ℝ) (hu : ∀ x, ‖u x‖ ≤ C)
    (hc : Continuous (fun x => M (u x))) : Continuous (fun x => J (u x)) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hmass : Tendsto (fun y => ‖M (u y)-M (u x)‖) (𝓝 x) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp (hc.tendsto x)
  have hsq : Tendsto (fun y => ‖J (u y)-J (u x)‖^2) (𝓝 x) (𝓝 0) :=
    squeeze_zero (fun y => sq_nonneg _) (fun y => difference_bound J M hm C (u y) (u x) (hu y) (hu x))
      (by simpa only [mul_zero] using hmass.const_mul (2*C))
  have hsqrt := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using hsqrt

theorem continuous_of_dense (J : V →L[ℂ] H) (hJ : DenseRange J) (E : X → H →L[ℂ] H)
    (C : ℝ) (hC : 0 ≤ C) (hE : ∀ t, ‖E t‖ ≤ C)
    (hc : ∀ v, Continuous (fun t => E t (J v))) (f : H) : Continuous (fun t => E t f) := by
  obtain ⟨v,hv,hlim⟩ := mem_closure_iff_seq_limit.mp (hJ f)
  choose w hw using hv
  have hn : Tendsto (fun n => ‖f-v n‖) atTop (𝓝 0) := by
    simpa only [sub_self,norm_zero] using (tendsto_const_nhds (x := f)).sub hlim |>.norm
  have hu : TendstoUniformly (fun n t => E t (v n)) (fun t => E t f) atTop := by
    apply Metric.tendstoUniformly_iff.mpr
    intro δ hδ
    have hp : 0 < C+1 := by linarith
    filter_upwards [hn.eventually (gt_mem_nhds (div_pos hδ hp))] with n hn t
    rw [dist_eq_norm,← map_sub]
    have hb := ((E t).le_opNorm (f-v n)).trans
      (mul_le_mul_of_nonneg_right (hE t) (norm_nonneg _))
    have hh : ‖f-v n‖*(C+1) < δ := (lt_div_iff₀ hp).mp hn
    nlinarith [norm_nonneg (f-v n)]
  apply hu.continuous
  apply Frequently.of_forall
  intro n
  rw [← hw n]
  exact hc (w n)

#print axioms difference_bound
#print axioms continuous_embedding
#print axioms continuous_of_dense
end
end UnifiedTheory.Audit.KFCausalMassOutputContinuity
