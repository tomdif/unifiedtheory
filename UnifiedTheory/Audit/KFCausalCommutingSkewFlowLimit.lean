/- A strongly continuous unitary group is constructed from commuting
bounded skew-adjoint approximants, using convergence on a dense set. -/
import UnifiedTheory.Audit.KFCausalCommutingSkewFlows
import Mathlib.Topology.UniformSpace.UniformApproximation

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCommutingSkewFlowLimit
noncomputable section
open Set Filter
open scoped Topology
open KFCausalCommutingSkewFlows
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
local notation "M" => H →L[ℂ] H

structure Data (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  generator : ℕ → H →L[ℂ] H
  skew : ∀ n, star (generator n) = -generator n
  commute : ∀ n m, generator n*generator m=generator m*generator n
  core : Set H
  dense : Dense core
  cauchy : ∀ x ∈ core, CauchySeq (fun n => generator n x)

variable (D : Data H)
local notation "U" => fun n t => flow (D.generator n) (D.skew n) t

theorem uniform_cauchy (x : H) (T : ℝ) (hT : 0 ≤ T) :
    UniformCauchySeqOn (fun n t => U n t x) atTop (Icc (-T) T) := by
  apply Metric.uniformCauchySeqOn_iff.mpr
  intro δ hδ
  obtain ⟨y,hy,hxy⟩ := D.dense.exists_dist_lt x (show 0 < δ/8 by positivity)
  obtain ⟨N,hN⟩ := Metric.cauchySeq_iff.mp (D.cauchy y hy) (δ/(2*(T+1))) (by positivity)
  refine ⟨N,?_⟩
  intro n hn m hm t ht
  have hb := dense_comparison (D.generator n) (D.generator m) (D.skew n) (D.skew m)
    (D.commute n m) t x y
  have hd := hN m hm n hn
  rw [dist_eq_norm] at hd hxy ⊢
  have ht' : |t| ≤ T := abs_le.mpr ht
  have he : ‖(D.generator m-D.generator n) y‖*|t| < δ/2 := by
    change ‖D.generator m y-D.generator n y‖*|t| < δ/2
    have hdiv : δ/(2*(T+1))*(T+1)=δ/2 := by field_simp
    have hmul := mul_lt_mul_of_pos_right hd (show 0 < T+1 by positivity)
    have hle := mul_le_mul_of_nonneg_left (ht'.trans (by linarith : T ≤ T+1))
      (norm_nonneg (D.generator m y-D.generator n y))
    exact hle.trans_lt (hmul.trans_eq hdiv)
  linarith

theorem cauchy (t : ℝ) (x : H) : CauchySeq (fun n => U n t x) :=
  (uniform_cauchy D x |t| (abs_nonneg t)).cauchySeq ⟨neg_abs_le t,le_abs_self t⟩

def value (t : ℝ) (x : H) : H := (cauchySeq_tendsto_of_complete (cauchy D t x)).choose

theorem tendsto_value (t : ℝ) (x : H) :
    Tendsto (fun n => U n t x) atTop (𝓝 (value D t x)) :=
  (cauchySeq_tendsto_of_complete (cauchy D t x)).choose_spec

theorem uniform_limit (x : H) (T : ℝ) (hT : 0 ≤ T) :
    TendstoUniformlyOn (fun n t => U n t x) (fun t => value D t x) atTop (Icc (-T) T) :=
  (uniform_cauchy D x T hT).tendstoUniformlyOn_of_tendsto (fun t _ => tendsto_value D t x)

theorem value_add (t : ℝ) (x y : H) : value D t (x+y)=value D t x+value D t y := by
  apply tendsto_nhds_unique (tendsto_value D t (x+y))
  simpa only [map_add] using (tendsto_value D t x).add (tendsto_value D t y)

theorem value_smul (t : ℝ) (c : ℂ) (x : H) : value D t (c • x)=c • value D t x := by
  apply tendsto_nhds_unique (tendsto_value D t (c • x))
  simpa only [map_smul] using (tendsto_value D t x).const_smul c

theorem value_norm (t : ℝ) (x : H) : ‖value D t x‖=‖x‖ := by
  apply tendsto_nhds_unique (tendsto_value D t x).norm
  simpa only [flow_norm] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => ‖x‖) atTop (𝓝 ‖x‖))

def isometry (t : ℝ) : H →ₗᵢ[ℂ] H where
  toFun := value D t
  map_add' := value_add D t
  map_smul' := value_smul D t
  norm_map' := value_norm D t

theorem value_initial (x : H) : value D 0 x=x := by
  apply tendsto_nhds_unique (tendsto_value D 0 x)
  simpa only [flow_initial,ContinuousLinearMap.one_apply] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => x) atTop (𝓝 x))

theorem moving_input (t : ℝ) (x : ℕ → H) (y : H) (hx : Tendsto x atTop (𝓝 y)) :
    Tendsto (fun n => U n t (x n)) atTop (𝓝 (value D t y)) := by
  have he : Tendsto (fun n => U n t (x n)-U n t y) atTop (𝓝 0) := by
    apply tendsto_zero_iff_norm_tendsto_zero.mpr
    simpa only [← map_sub,flow_norm] using (tendsto_zero_iff_norm_tendsto_zero.mp
      (show Tendsto (fun n => x n-y) atTop (𝓝 0) by simpa only [sub_self] using hx.sub_const y))
  have ht := he.add (tendsto_value D t y)
  simpa only [sub_add_cancel,zero_add] using ht

theorem value_compose (s t : ℝ) (x : H) : value D (s+t) x=value D t (value D s x) := by
  apply tendsto_nhds_unique (tendsto_value D (s+t) x)
  simpa only [flow_add] using moving_input D t (fun n => U n s x) (value D s x) (tendsto_value D s x)

theorem value_reverse (t : ℝ) (x : H) : value D (-t) (value D t x)=x := by
  rw [← value_compose,add_neg_cancel,value_initial]

def group (t : ℝ) : H ≃ₗᵢ[ℂ] H := LinearIsometryEquiv.ofSurjective (isometry D t)
  (fun x => ⟨value D (-t) x,by
    change value D t (value D (-t) x)=x
    simpa only [neg_neg] using value_reverse D (-t) x⟩)

theorem group_apply (t : ℝ) (x : H) : group D t x=value D t x := rfl

theorem value_continuous (x : H) : Continuous (fun t => value D t x) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  have hc := (uniform_limit D x (|t|+1) (by positivity)).continuousOn
    (Eventually.of_forall (fun n => (continuous_iff_continuousAt.mpr
      (fun u => (flow_derivative (D.generator n) (D.skew n) u x).continuousAt)).continuousOn)).frequently
  exact hc.continuousAt (Icc_mem_nhds (by linarith [neg_abs_le t]) (by linarith [le_abs_self t]))

#print axioms uniform_cauchy
#print axioms cauchy
#print axioms tendsto_value
#print axioms uniform_limit
#print axioms value_add
#print axioms value_smul
#print axioms value_norm
#print axioms value_initial
#print axioms moving_input
#print axioms value_compose
#print axioms value_reverse
#print axioms group_apply
#print axioms value_continuous
end
end UnifiedTheory.Audit.KFCausalCommutingSkewFlowLimit
