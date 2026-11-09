/- A continuous weak Hilbert derivative is a strong derivative. A
strong approximate solution of a unitary equation has an error bounded
by its actual residual, with no exponential loss. -/
import UnifiedTheory.Audit.KFCausalHilbertEvolutionStability
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace UnifiedTheory.Audit.KFCausalStrongResidualCalculus
noncomputable section
open Set
open UnifiedTheory.Audit.KFCausalHilbertIntervalPropagator (constant_on_interval)
open UnifiedTheory.Audit.KFCausalHilbertEvolution
open UnifiedTheory.Audit.KFCausalHilbertStateEvolution
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem strong_of_continuous_weak_derivative (u v : ℝ → H) (hv : Continuous v)
    (hd : ∀ t y, HasDerivAt (fun z => inner ℂ (u z) y) (inner ℂ (v t) y) t)
    (t : ℝ) : HasDerivAt u (v t) t := by
  let p := fun z => ∫ r in (0:ℝ)..z, v r
  have hp (z : ℝ) : HasDerivAt p (v z) z :=
    intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 z)
      (hv.stronglyMeasurableAtFilter _ _) hv.continuousAt
  have he : u = fun z => p z+u 0 := by
    funext z
    apply ext_inner_right ℂ
    intro y
    have hzero (r : ℝ) : HasDerivAt
        (fun x => inner ℂ (u x) y-inner ℂ (p x) y) 0 r := by
      simpa only [inner_zero_right,zero_add,sub_self] using
        (hd r y).sub ((hp r).inner ℂ (hasDerivAt_const r y))
    have hz := constant_on_interval (fun x => inner ℂ (u x) y-inner ℂ (p x) y)
      (min 0 z) (max 0 z) (fun r _ => (hzero r).hasDerivWithinAt)
      0 z ⟨min_le_left _ _,le_max_left _ _⟩ ⟨min_le_right _ _,le_max_right _ _⟩
    simp only [p,intervalIntegral.integral_same,inner_zero_left,sub_zero] at hz
    rw [inner_add_left]
    exact sub_eq_iff_eq_add.mp hz |>.trans (add_comm _ _)
  rw [he]
  exact (hp t).add_const (u 0)

theorem residual_interaction_derivative (A : ℝ → H →L[ℂ] H) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (v r : ℝ → H) (s t : ℝ)
    (hv : HasDerivAt v (A t (v t)+r t) t) :
    HasDerivAt (fun z => star (evolution A hA hskew s z) (v z))
      (star (evolution A hA hskew s t) (r t)) t := by
  have hd := operator_apply_derivative (fun z => star (evolution A hA hskew s z)) v
    (star (A t*evolution A hA hskew s t)) (A t (v t)+r t) t
    (evolution_derivative A hA hskew s t).star hv
  convert hd using 1
  simp only [star_mul,hskew,ContinuousLinearMap.mul_apply,ContinuousLinearMap.neg_apply,
    map_neg,map_add,neg_add_cancel_left]

theorem residual_error_bound (A : ℝ → H →L[ℂ] H) (hA : Continuous A)
    (hskew : ∀ t, star (A t) = -A t) (v r : ℝ → H)
    (hv : ∀ t, HasDerivAt v (A t (v t)+r t) t) (s t C : ℝ) (f : H)
    (hr : ∀ z ∈ uIcc s t, ‖r z‖ ≤ C) :
    ‖evolution A hA hskew s t f-v t‖ ≤ ‖f-v s‖+C*|t-s| := by
  let w := fun z => star (evolution A hA hskew s z) (v z)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun z (_ : z ∈ uIcc s t) =>
      (residual_interaction_derivative A hA hskew v r s z (hv z)).hasDerivWithinAt)
    (fun z (hz : z ∈ uIcc s t) => by
      rw [evolution_reverse,evolution_norm]
      exact hr z hz)
    (convex_uIcc s t) (left_mem_uIcc : s ∈ uIcc s t) (right_mem_uIcc : t ∈ uIcc s t)
  have hi : w s = v s := by simp only [w,evolution_initial,star_one,ContinuousLinearMap.one_apply]
  have hb0 : ‖w t-w s‖ ≤ C*|t-s| := by simpa only [Real.norm_eq_abs] using hb
  have hb' : ‖w t-v s‖ ≤ C*|t-s| := by simpa only [hi] using hb0
  have he : ‖evolution A hA hskew s t f-v t‖ = ‖f-w t‖ := by
    have hn := evolution_norm A hA hskew t s (evolution A hA hskew s t f-v t)
    rw [map_sub,← ContinuousLinearMap.mul_apply,evolution_compose,evolution_initial,
      ContinuousLinearMap.one_apply] at hn
    exact hn.symm.trans (congrArg norm (congrArg (fun x : H => f-x)
      (congrArg (fun B : H →L[ℂ] H => B (v t)) (evolution_reverse A hA hskew s t)).symm))
  rw [he]
  have hn := norm_add_le (f-v s) (v s-w t)
  have hc : f-v s+(v s-w t) = f-w t := by abel
  rw [hc,norm_sub_rev (v s) (w t)] at hn
  linarith only [hn,hb']

#print axioms strong_of_continuous_weak_derivative
#print axioms residual_interaction_derivative
#print axioms residual_error_bound
end
end UnifiedTheory.Audit.KFCausalStrongResidualCalculus
