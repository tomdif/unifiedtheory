/- An initial characteristic limit and uniform low-frequency time
increments imply uniform tails on a time window. The initial limit is
used under a finite frequency integral; no initial uniform convergence
or time-window tightness is assumed. -/
import UnifiedTheory.Audit.KFCausalCharacteristicTightness
import UnifiedTheory.Audit.KFCausalNeutralPositionMovingProbability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 600000

namespace UnifiedTheory.Audit.KFCausalUniformCharacteristicTail
noncomputable section
open MeasureTheory Filter
open scoped Topology
open UnifiedTheory.Audit.KFCausalNeutralPositionMovingProbability (probability_characteristic_continuous)

theorem initial_integral_zero (μ : ℕ → ProbabilityMeasure ℝ)
    (hμ : ∀ v, Tendsto (fun n => charFun (μ n : Measure ℝ) v) atTop (𝓝 (1:ℂ))) (l r : ℝ) :
    Tendsto (fun n => ∫ v in l..r, 1-charFun (μ n : Measure ℝ) v) atTop (𝓝 (0:ℂ)) := by
  simpa only [smul_eq_mul,mul_one,sub_self,intervalIntegral.integral_zero] using
    KFCausalCharacteristicTailControl.integral_defect_limit μ (fun _ => (1:ℂ)) hμ (1:ℝ) l r

theorem uniform_tail (μ : ℕ → ℝ → ProbabilityMeasure ℝ) (s T : ℝ)
    (hinit : ∀ v, Tendsto (fun n => charFun (μ n s : Measure ℝ) v) atTop (𝓝 (1:ℂ)))
    (hmove : ∀ η : ℝ, 0 < η → ∃ V : ℝ, 0 < V ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ v t : ℝ,
      |v| ≤ V → |t-s| ≤ T → ‖charFun (μ n t : Measure ℝ) v-charFun (μ n s : Measure ℝ) v‖ < η)
    (η : ℝ) (hη : 0 < η) :
    ∃ R : ℝ, 0 < R ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ, |t-s| ≤ T →
      (μ n t : Measure ℝ).real {x | R < |x|} < η := by
  obtain ⟨V,hV,N,hN⟩ := hmove (η/4) (by positivity)
  let R := 4/V
  have hR : 0 < R := by dsimp [R]; positivity
  have hend : 2*R⁻¹ = V/2 := by dsimp [R]; field_simp; ring
  have hlen : |2*R⁻¹-(-2*R⁻¹)| = V := by
    rw [neg_mul,hend,abs_of_pos (by linarith : 0 < V/2-(-(V/2)))]
    ring
  have hi := (initial_integral_zero (fun n => μ n s) hinit (-2*R⁻¹) (2*R⁻¹)).norm.const_mul (2⁻¹*R)
  have hi' : ∀ᶠ n in atTop, 2⁻¹*R*‖∫ v in (-2*R⁻¹)..(2*R⁻¹),
      1-charFun (μ n s : Measure ℝ) v‖ < η/2 := by
    exact hi.eventually (gt_mem_nhds (show 2⁻¹*R*‖(0:ℂ)‖ < η/2 by
      simpa only [norm_zero,mul_zero] using (show (0:ℝ) < η/2 by positivity)))
  obtain ⟨M,hM⟩ := eventually_atTop.mp hi'
  refine ⟨R,hR,max N M,?_⟩
  intro n hn t ht
  have hm := hM n ((le_max_right N M).trans hn)
  have hd : ‖∫ v in (-2*R⁻¹)..(2*R⁻¹),
      charFun (μ n s : Measure ℝ) v-charFun (μ n t : Measure ℝ) v‖ ≤ (η/4)*V := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const (C := η/4) ?_).trans_eq
    · rw [hlen]
    · intro v hv
      rw [neg_mul,hend,Set.uIoc_of_le (by linarith)] at hv
      have hb : |v| ≤ V := abs_le.mpr ⟨by linarith [hv.1],by linarith [hv.2]⟩
      simpa only [norm_sub_rev] using (hN n ((le_max_left N M).trans hn) v t hb ht).le
  have hsplit : (∫ v in (-2*R⁻¹)..(2*R⁻¹), 1-charFun (μ n t : Measure ℝ) v) =
      (∫ v in (-2*R⁻¹)..(2*R⁻¹), 1-charFun (μ n s : Measure ℝ) v)+
        ∫ v in (-2*R⁻¹)..(2*R⁻¹), charFun (μ n s : Measure ℝ) v-charFun (μ n t : Measure ℝ) v := by
    rw [← intervalIntegral.integral_add
      ((continuous_const.sub (probability_characteristic_continuous (μ n s))).intervalIntegrable _ _)
      (((probability_characteristic_continuous (μ n s)).sub
        (probability_characteristic_continuous (μ n t))).intervalIntegrable _ _)]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  have hbound : 2⁻¹*R*‖∫ v in (-2*R⁻¹)..(2*R⁻¹), 1-charFun (μ n t : Measure ℝ) v‖ < η := by
    have hnorm := (congrArg norm hsplit).le.trans (norm_add_le _ _)
    have hp := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 2⁻¹*R)
    have hpd := mul_le_mul_of_nonneg_left hd (by positivity : 0 ≤ 2⁻¹*R)
    have he : 2⁻¹*R*((η/4)*V) = η/2 := by dsimp [R]; field_simp
    rw [he] at hpd
    nlinarith
  exact (measureReal_abs_gt_le_integral_charFun (μ := (μ n t : Measure ℝ)) hR).trans_lt hbound

theorem tight_of_eventual_real_tail (μ : ℕ → ProbabilityMeasure ℝ)
    (ht : ∀ η : ℝ, 0 < η → ∃ R : ℝ, 0 < R ∧ ∀ᶠ n in atTop,
      (μ n : Measure ℝ).real {x | R < |x|} ≤ η) :
    IsTightMeasureSet (Set.range (fun n => (μ n : Measure ℝ))) := by
  apply isTightMeasureSet_of_tendsto_measure_norm_gt
  have hproj := KFCausalCharacteristicTightness.projection_tail_tendsto μ (1:ℝ) (by
    intro η hη
    simpa [RCLike.inner_apply] using ht η hη)
  simpa only [iSup_range,RCLike.inner_apply,map_one,mul_one,Real.norm_eq_abs] using hproj

#print axioms initial_integral_zero
#print axioms uniform_tail
#print axioms tight_of_eventual_real_tail

end
end UnifiedTheory.Audit.KFCausalUniformCharacteristicTail
