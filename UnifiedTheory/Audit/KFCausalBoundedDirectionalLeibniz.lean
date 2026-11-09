/- A bounded multiplier with a bounded classical directional derivative
preserves the entire maximal translation-momentum domain. The strong L2
product rule is derived by domination, not assumed on a packet subspace. -/
import UnifiedTheory.Audit.KFCausalDirectionalTranslationMomentum
import UnifiedTheory.Audit.KFCausalBoundedLpMultiplier
import UnifiedTheory.Audit.KFCausalDominatedL2Derivative
import Mathlib.Analysis.Calculus.MeanValue

set_option Elab.async false
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalBoundedDirectionalLeibniz
noncomputable section
open MeasureTheory Filter Set
open scoped Topology
open KFCausalFourierTranslation (translation translation_coe shift_preserves_volume)
open KFCausalDirectionalTranslationMomentum
  (spectralMomentum spectralMomentum_graph_derivative translation_initial translation_continuous)
open KFCausalBoundedLpMultiplier (operator operator_coe operator_norm)

private theorem bounded_joint_continuous
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℝ → H →L[ℂ] H) (B : ℝ)
    (hb : ∀ t x, ‖A t x‖ ≤ B*‖x‖)
    (hc : ∀ x, Continuous (fun t => A t x)) :
    Continuous (fun p : ℝ × H => A p.1 p.2) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  change Tendsto (fun q : ℝ × H => A q.1 q.2) (𝓝 p) (𝓝 (A p.1 p.2))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have h1 := (((continuous_snd.tendsto p).sub
    (tendsto_const_nhds (x := p.2))).norm).const_mul B
  have h2 := ((((hc p.2).comp continuous_fst).tendsto p).sub
    (tendsto_const_nhds (x := A p.1 p.2))).norm
  have hb' (q : ℝ × H) : ‖A q.1 q.2-A p.1 p.2‖ ≤
      B*‖q.2-p.2‖+‖A q.1 p.2-A p.1 p.2‖ := by
    apply (norm_sub_le_norm_sub_add_norm_sub (A q.1 q.2) (A q.1 p.2)
      (A p.1 p.2)).trans
    refine add_le_add ?_ le_rfl
    rw [← map_sub]
    exact hb q.1 (q.2-p.2)
  apply squeeze_zero (fun q : ℝ × H => norm_nonneg (A q.1 q.2-A p.1 p.2)) hb'
  simpa only [Function.comp_apply,sub_self,norm_zero,mul_zero,zero_add] using h1.add h2

private theorem strong_product_derivative
    {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]
    (A : ℝ → H →L[ℂ] H)
    (hc : Continuous (fun p : ℝ × H => A p.1 p.2))
    (v : ℝ → H) (a b : H)
    (ha : HasDerivAt (fun t => A t (v 0)) a 0)
    (hv : HasDerivAt v b 0) :
    HasDerivAt (fun t => A t (v t)) (A 0 b+a) 0 := by
  have hs : Tendsto (fun t : ℝ => t⁻¹ • (v t-v 0)) (𝓝[≠] 0) (𝓝 b) := by
    simpa only [zero_add] using hv.tendsto_slope_zero
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hj := hc.continuousAt.tendsto.comp (ht.prodMk_nhds hs)
  have hh := hj.add ha.tendsto_slope_zero
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  convert hh using 1
  funext t
  simp only [Function.comp_apply,zero_add,map_real_smul (A t) (A t).continuous,
    map_sub,smul_sub]
  abel

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

variable (v : E) (m d : E → ℂ) (hm : Measurable m) (hdm : Measurable d)
  (B D : ℝ) (hB : 0 ≤ B) (hD : 0 ≤ D)
  (hb : ∀ x, ‖m x‖ ≤ B) (hdb : ∀ x, ‖d x‖ ≤ D)
  (hd : ∀ x t, HasDerivAt (fun s : ℝ => m (x+s • v)) (d (x+t • v)) t)

def shifted (t : ℝ) : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E) :=
  operator (fun x => m (x+t • v)) (hm.comp (by fun_prop)) B hB (fun x => hb (x+t • v))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
include hdb hd in
theorem increment_bound (x : E) (t s : ℝ) :
    ‖m (x+t • v)-m (x+s • v)‖ ≤ D*‖t-s‖ := by
  exact Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun t => m (x+t • v)) (f' := fun t => d (x+t • v))
    (fun t _ => (hd x t).hasDerivWithinAt) (fun t _ => hdb _)
    (convex_univ : Convex ℝ (Set.univ : Set ℝ)) (mem_univ s) (mem_univ t)

private theorem shifted_coe (t : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    shifted v m hm B hB hb t f =ᵐ[volume] fun x => m (x+t • v)*f x :=
  operator_coe _ _ _ _ _ f

private theorem shifted_zero : shifted v m hm B hB hb 0 = operator m hm B hB hb := by
  apply ContinuousLinearMap.ext
  intro f
  apply Lp.ext
  filter_upwards [shifted_coe v m hm B hB hb 0 f,operator_coe m hm B hB hb f] with x hx hy
  simp only [zero_smul,add_zero] at hx
  exact hx.trans hy.symm

include hd in
private theorem shifted_continuous (f : Lp ℂ 2 (volume : Measure E)) :
    Continuous (fun t => shifted v m hm B hB hb t f) := by
  let F : ℝ → E → ℂ := fun t x => m (x+t • v)*f x
  have hF (t : ℝ) : MemLp (F t) 2 volume :=
    (Lp.memLp (shifted v m hm B hB hb t f)).ae_eq (shifted_coe v m hm B hB hb t f)
  let g : E → ℂ := fun x => (B:ℂ)*f x
  have hg : MemLp g 2 volume := (Lp.memLp f).const_mul (B:ℂ)
  have hc := KFCausalDominatedL2Continuity.continuous_toLp F hF g hg
    (fun t => Eventually.of_forall (fun x => by
      dsimp only [F,g]
      rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hB]
      exact mul_le_mul_of_nonneg_right (hb _) (norm_nonneg _)))
    (Eventually.of_forall (fun x =>
      (continuous_iff_continuousAt.mpr (fun t => (hd x t).continuousAt)).mul continuous_const))
  have he : (fun t => (hF t).toLp (F t)) = fun t => shifted v m hm B hB hb t f := by
    funext t
    exact Lp.ext ((hF t).coeFn_toLp.trans (shifted_coe v m hm B hB hb t f).symm)
  rwa [he] at hc

include hd in
theorem shifted_derivative (f : Lp ℂ 2 (volume : Measure E)) :
    HasDerivAt (fun t => shifted v m hm B hB hb t f)
      (operator d hdm D hD hdb f) 0 := by
  let g : E → ℂ := fun x => d x*f x
  have hg : MemLp g 2 volume :=
    (Lp.memLp (operator d hdm D hD hdb f)).ae_eq (operator_coe d hdm D hD hdb f)
  have he : hg.toLp g=operator d hdm D hD hdb f :=
    Lp.ext (hg.coeFn_toLp.trans (operator_coe d hdm D hD hdb f).symm)
  rw [← he]
  apply KFCausalDominatedL2Derivative.hasDerivAt_represented
    (fun t => shifted v m hm B hB hb t f) (fun t x => m (x+t • v)*f x)
    (fun t => shifted_coe v m hm B hB hb t f) g hg (fun x => D*‖f x‖)
  · simpa only [mul_pow] using
      ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable f)).mp (Lp.memLp f)).const_mul (D^2)
  · exact Eventually.of_forall (fun t => Eventually.of_forall (fun x => by
      by_cases ht : t=0
      · simp only [ht,inv_zero,zero_smul,norm_zero]
        exact mul_nonneg hD (norm_nonneg _)
      · have hs := increment_bound v m d D hdb hd x t 0
        simp only [zero_smul,add_zero,sub_zero] at hs ⊢
        rw [← sub_mul,norm_smul,norm_mul,Real.norm_eq_abs,abs_inv]
        have hh := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hs (norm_nonneg (f x))) (inv_nonneg.mpr (abs_nonneg t))
        apply hh.trans_eq
        rw [Real.norm_eq_abs]
        field_simp [abs_ne_zero.mpr ht]))
  · exact Eventually.of_forall (fun x => by
      simpa only [g,zero_smul,add_zero] using (hd x 0).mul_const (f x))

private theorem translation_product (t : ℝ) (f : Lp ℂ 2 (volume : Measure E)) :
    translation (t • v) (operator m hm B hB hb f) =
      shifted v m hm B hB hb t (translation (t • v) f) := by
  apply Lp.ext
  filter_upwards [translation_coe (t • v) (operator m hm B hB hb f),
    (shift_preserves_volume (t • v)).quasiMeasurePreserving.ae (operator_coe m hm B hB hb f),
    shifted_coe v m hm B hB hb t (translation (t • v) f),translation_coe (t • v) f]
    with x hx hy hz hw
  change (operator m hm B hB hb f) (x+t • v)=m (x+t • v)*f (x+t • v) at hy
  rw [hx,hy,hz,hw]

include hd in
theorem spectral_graph (h : ℝ) (hh : h ≠ 0)
    (f g : Lp ℂ 2 (volume : Measure E)) (hfg : (f,g) ∈ (spectralMomentum h v).graph) :
    (operator m hm B hB hb f,
      operator m hm B hB hb g+(-Complex.I*(h:ℂ)) • operator d hdm D hD hdb f) ∈
      (spectralMomentum h v).graph := by
  have ha : HasDerivAt (fun t => shifted v m hm B hB hb t (translation ((0:ℝ) • v) f))
      (operator d hdm D hD hdb f) 0 := by
    simpa only [zero_smul,translation_initial] using shifted_derivative v m d hm hdm B D hB hD hb hdb hd f
  have hc := bounded_joint_continuous (shifted v m hm B hB hb) B
    (fun t x => operator_norm _ _ _ _ _ x) (shifted_continuous v m d hm B hB hb hd)
  have hp := strong_product_derivative (shifted v m hm B hB hb) hc
    (fun t => translation (t • v) f) _ _ ha
    ((spectralMomentum_graph_derivative h hh v f g).mp hfg)
  apply (spectralMomentum_graph_derivative h hh v _ _).mpr
  simp only [← translation_product v m hm B hB hb,shifted_zero,map_smul] at hp
  convert hp using 1
  rw [smul_add,smul_smul]
  congr 1
  have hi : (Complex.I/(h:ℂ))*(-Complex.I*(h:ℂ))=1 := by
    field_simp [Complex.ofReal_ne_zero.mpr hh]
    simp [Complex.I_sq]
  rw [hi,one_smul]

#print axioms increment_bound
#print axioms shifted_derivative
#print axioms spectral_graph
end
end UnifiedTheory.Audit.KFCausalBoundedDirectionalLeibniz
