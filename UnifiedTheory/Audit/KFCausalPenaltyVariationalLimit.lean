/- A vanishing nonnegative quadratic penalty selects the Riesz vector
in the completion of a dense form inclusion. The convergence follows
from a variational identity and proved density, not an assumed limit. -/
import UnifiedTheory.Audit.KFCausalFormResolventError

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalPenaltyVariationalLimit
noncomputable section
open Filter
open scoped Topology
variable {V W K : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  (I : V →L[ℂ] W) (A : V →L[ℂ] K)

def cost (w : W) (a : ℝ) (v : V) : ℝ := ‖I v-w‖^2+a*‖A v‖^2

theorem variational_identity (w : W) (a : ℝ) (r v : V)
    (hp : ∀ z, inner ℂ (I r) (I z)+(a:ℂ)*inner ℂ (A r) (A z) = inner ℂ w (I z)) :
    cost I A w a v = cost I A w a r+‖I (v-r)‖^2+a*‖A (v-r)‖^2 := by
  have hz : (inner ℂ (I r-w) (I (v-r))).re+a*(inner ℂ (A r) (A (v-r))).re = 0 := by
    have he := congrArg Complex.re (hp (v-r))
    simp only [inner_sub_left,Complex.sub_re,Complex.add_re,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero] at he ⊢
    linarith only [he]
  have hi : I v-w = (I r-w)+I (v-r) := by rw [map_sub]; abel
  have ha : A v = A r+A (v-r) := by rw [map_sub]; abel
  unfold cost
  rw [hi,ha,norm_add_sq (𝕜 := ℂ),norm_add_sq (𝕜 := ℂ)]
  simp only [RCLike.re_eq_complex_re]
  nlinarith only [hz]

theorem variational_minimum (w : W) (a : ℝ) (ha : 0 ≤ a) (r v : V)
    (hp : ∀ z, inner ℂ (I r) (I z)+(a:ℂ)*inner ℂ (A r) (A z) = inner ℂ w (I z)) :
    cost I A w a r ≤ cost I A w a v := by
  rw [variational_identity I A w a r v hp]
  linarith only [sq_nonneg ‖I (v-r)‖,mul_nonneg ha (sq_nonneg ‖A (v-r)‖)]

theorem cost_tendsto_zero (hd : DenseRange I) (w : W) (r : ℝ → V)
    (hp : ∀ u, 0 < u → ∀ z,
      inner ℂ (I (r u)) (I z)+((1/u:ℝ):ℂ)*inner ℂ (A (r u)) (A z) = inner ℂ w (I z)) :
    Tendsto (fun u => cost I A w (1/u) (r u)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact ha.trans_le (add_nonneg (sq_nonneg _) (mul_nonneg (one_div_pos.mpr hu).le (sq_nonneg _)))
  · intro δ hδ
    obtain ⟨v,hv⟩ := hd.exists_dist_lt w (Real.sqrt_pos.mpr (show 0 < δ/2 by positivity))
    rw [dist_eq_norm,norm_sub_rev] at hv
    have hv2 : ‖I v-w‖^2 < δ/2 := by
      nlinarith [Real.sq_sqrt (show 0 ≤ δ/2 by positivity),norm_nonneg (I v-w),Real.sqrt_nonneg (δ/2)]
    have ht : Tendsto (fun u : ℝ => ‖A v‖^2/u) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    filter_upwards [eventually_gt_atTop (0:ℝ),ht.eventually (gt_mem_nhds (show 0 < δ/2 by positivity))] with u hu huδ
    have hm := variational_minimum I A w (1/u) (one_div_pos.mpr hu).le (r u) v (hp u hu)
    have hvδ : cost I A w (1/u) v < δ := by
      unfold cost
      have he : (1/u)*‖A v‖^2 = ‖A v‖^2/u := by ring
      rw [he]
      linarith only [hv2,huδ]
    exact hm.trans_lt hvδ

theorem strong_limit (hd : DenseRange I) (w : W) (r : ℝ → V)
    (hp : ∀ u, 0 < u → ∀ z,
      inner ℂ (I (r u)) (I z)+((1/u:ℝ):ℂ)*inner ℂ (A (r u)) (A z) = inner ℂ w (I z)) :
    Tendsto (fun u => I (r u)) atTop (𝓝 w) := by
  have ht := cost_tendsto_zero I A hd w r hp
  have hb : ∀ᶠ u : ℝ in atTop, ‖I (r u)-w‖^2 ≤ cost I A w (1/u) (r u) := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact le_add_of_nonneg_right (mul_nonneg (one_div_pos.mpr hu).le (sq_nonneg _))
  have hs := squeeze_zero' (Eventually.of_forall (fun u => sq_nonneg ‖I (r u)-w‖)) hb ht
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [Function.comp_def,Real.sqrt_sq_eq_abs,abs_norm,Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp hs

theorem penalty_limit (hd : DenseRange I) (w : W) (r : ℝ → V)
    (hp : ∀ u, 0 < u → ∀ z,
      inner ℂ (I (r u)) (I z)+((1/u:ℝ):ℂ)*inner ℂ (A (r u)) (A z) = inner ℂ w (I z)) :
    Tendsto (fun u => (1/u)*‖A (r u)‖^2) atTop (𝓝 0) := by
  have hn : ∀ᶠ u : ℝ in atTop, 0 ≤ (1/u)*‖A (r u)‖^2 := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with u hu
    exact mul_nonneg (one_div_pos.mpr hu).le (sq_nonneg _)
  exact squeeze_zero' hn (Eventually.of_forall (fun u => le_add_of_nonneg_left (sq_nonneg ‖I (r u)-w‖)))
    (cost_tendsto_zero I A hd w r hp)

#print axioms variational_identity
#print axioms variational_minimum
#print axioms cost_tendsto_zero
#print axioms strong_limit
#print axioms penalty_limit
end
end UnifiedTheory.Audit.KFCausalPenaltyVariationalLimit
