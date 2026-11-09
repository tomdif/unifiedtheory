/- A conserved physical norm, dense weak derivatives and a vanishing
form residual imply the strong initial derivative. -/
import UnifiedTheory.Audit.KFCausalDifferentialNormBound
import UnifiedTheory.Audit.KFCausalDenseWeakDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1500000

namespace UnifiedTheory.Audit.KFCausalWeakInitialStrongDerivative
noncomputable section
open Filter Asymptotics
open scoped Topology
variable {H V : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem increment_bigO (u : ℝ → H) (v : H) (d q : ℝ → ℝ) (s : ℝ)
    (hu : Continuous u) (hn : ∀ t, ‖u t‖ = ‖u s‖)
    (hd : ∀ t, HasDerivAt (fun z => (inner ℂ (u z) (u s)).re) (d t) t)
    (hq0 : q s = 0) (hq : HasDerivAt q 0 s)
    (he : ∀ t, d t = -(inner ℂ (u t-u s) v).re+q t) :
    (fun t => u t-u s) =O[𝓝 s] fun t => t-s := by
  have hqo : q =o[𝓝 s] fun t => t-s := by
    simpa only [hq0,sub_zero,smul_zero] using hasDerivAt_iff_isLittleO.mp hq
  obtain ⟨δ,hδ,hb⟩ := Metric.eventually_nhds_iff.mp hqo.eventuallyLE
  have hb' (t : ℝ) (ht : |t-s| < δ) : |q t| ≤ |t-s| := by
    exact hb (by simpa only [Real.dist_eq] using ht)
  have hnorm (t : ℝ) : ‖u t-u s‖^2 = -2*((inner ℂ (u t) (u s)).re-‖u s‖^2) := by
    rw [norm_sub_sq (𝕜 := ℂ),hn]
    change ‖u s‖^2-2*(inner ℂ (u t) (u s)).re+‖u s‖^2 = _
    ring
  have hnd (t : ℝ) : HasDerivAt (fun z => ‖u z-u s‖^2) (-2*d t) t := by
    have hp := ((hd t).sub_const (‖u s‖^2)).const_mul (-2)
    exact (congrArg (fun f : ℝ → ℝ => HasDerivAt f (-2*d t) t) (funext hnorm)).mpr hp
  have hdb (t : ℝ) (ht : |t-s| < δ) :
      |-2*d t| ≤ (2*‖v‖)*‖u t-u s‖+2*|t-s| := by
    have hp : |(inner ℂ (u t-u s) v).re| ≤ ‖u t-u s‖*‖v‖ :=
      (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have ha := abs_add_le (-(inner ℂ (u t-u s) v).re) (q t)
    rw [← he,abs_neg] at ha
    rw [abs_mul]
    norm_num only [abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    nlinarith [hb' t ht]
  apply IsBigO.of_bound (2*‖v‖+Real.sqrt 2)
  filter_upwards [Metric.ball_mem_nhds s hδ] with t ht
  rw [Real.norm_eq_abs]
  exact KFCausalDifferentialNormBound.increment_bound (fun z => u z-u s) _ s δ
    (2*‖v‖) 2 (hu.sub continuous_const) (by positivity) (by norm_num)
    (sub_self _) hnd hdb t (by simpa only [Metric.mem_ball,Real.dist_eq] using ht)

theorem strong_derivative (J : V → H) (hJ : DenseRange J)
    (u : ℝ → H) (v : H) (d q : ℝ → ℝ) (s : ℝ)
    (hu : Continuous u) (hn : ∀ t, ‖u t‖ = ‖u s‖)
    (hd : ∀ t, HasDerivAt (fun z => (inner ℂ (u z) (u s)).re) (d t) t)
    (hq0 : q s = 0) (hq : HasDerivAt q 0 s)
    (he : ∀ t, d t = -(inner ℂ (u t-u s) v).re+q t)
    (hw : ∀ w, HasDerivAt (fun t => (inner ℂ (u t) (J w)).re)
      (inner ℂ v (J w)).re s) : HasDerivAt u v s := by
  have hb := increment_bigO u v d q s hu hn hd hq0 hq he
  have hv := KFCausalDenseWeakDerivative.pairing_derivative J hJ u v s hb hw v
  have hself : (inner ℂ v v).re = ‖v‖^2 := inner_self_eq_norm_sq (𝕜 := ℂ) v
  rw [hself] at hv
  have he' : d = fun t => -((inner ℂ (u t) v).re-(inner ℂ (u s) v).re)+q t := by
    funext t
    simpa only [inner_sub_left,Complex.sub_re] using he t
  apply KFCausalInitialStrongDerivativeCalculus.initial_derivative_of_scalar_jets u v s d hn hd
  · simp only [he s,sub_self,inner_zero_left,Complex.zero_re,neg_zero,hq0,add_zero]
  · rw [he']
    simpa only [add_zero] using ((hv.sub_const (inner ℂ (u s) v).re).neg.add hq)
  · exact hv

#print axioms increment_bigO
#print axioms strong_derivative
end
end UnifiedTheory.Audit.KFCausalWeakInitialStrongDerivative
