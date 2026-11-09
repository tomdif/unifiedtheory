/- Pointwise characteristic convergence to a function continuous at zero
prevents eventual escape along every fixed projection. The proof uses the
actual positive measures and the library's integrated characteristic tail
bound; no tightness hypothesis is supplied. -/
import Mathlib.MeasureTheory.Measure.IntegralCharFun
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace UnifiedTheory.Audit.KFCausalCharacteristicTailControl
noncomputable section
open MeasureTheory Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

 theorem integral_defect_limit (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z)))
    (a : E) (l r : ℝ) :
    Tendsto (fun n => ∫ t in l..r, 1-charFun (μ n : Measure E) (t • a))
      atTop (𝓝 (∫ t in l..r, 1-f (t • a))) := by
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => (2:ℝ))
  · exact Eventually.of_forall (fun n =>
      (stronglyMeasurable_const.sub (stronglyMeasurable_charFun.comp_measurable
        (by fun_prop : Measurable (fun t : ℝ => t • a)))).aestronglyMeasurable)
  · exact Eventually.of_forall (fun n => ae_of_all _ (fun _ _ => norm_one_sub_charFun_le_two))
  · exact intervalIntegrable_const
  · exact ae_of_all _ (fun t _ => tendsto_const_nhds.sub (hc (t • a)))

 theorem eventual_projection_tail (μ : ℕ → ProbabilityMeasure E) (f : E → ℂ)
    (hf : Continuous f) (hf0 : f 0 = 1)
    (hc : ∀ z, Tendsto (fun n => charFun (μ n : Measure E) z) atTop (𝓝 (f z)))
    (a : E) (η : ℝ) (hη : 0 < η) :
    ∃ r : ℝ, 0 < r ∧ ∀ᶠ n in atTop,
      (μ n : Measure E).real {x | r < |inner ℝ a x|} ≤ η := by
  have hcont : Continuous (fun t : ℝ => f (t • a)) := hf.comp (by fun_prop)
  obtain ⟨δ,hδ,hD⟩ := Metric.continuous_iff.mp hcont 0 (η/4) (by positivity)
  let r : ℝ := 4/δ
  have hr : 0 < r := by dsimp [r]; positivity
  have hed : 2*r⁻¹ = δ/2 := by dsimp [r]; field_simp; ring
  have hn : ‖∫ t in (-2*r⁻¹)..(2*r⁻¹), 1-f (t • a)‖ ≤ (η/4)*δ := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := -2*r⁻¹) (b := 2*r⁻¹) (C := η/4) (f := fun t => (1:ℂ)-f (t • a)) (by
        intro t ht
        rw [neg_mul,hed,Set.uIoc_of_le (by linarith)] at ht
        have htd : dist t 0 < δ := by
          rw [dist_zero_right,Real.norm_eq_abs,abs_lt]
          exact ⟨by linarith [ht.1],by linarith [ht.2]⟩
        have h := hD t htd
        simpa only [zero_smul,hf0,dist_eq_norm,norm_sub_rev] using h.le)
    have he : |2*r⁻¹-(-2*r⁻¹)| = δ := by rw [neg_mul,hed]; rw [abs_of_pos (by linarith)]; ring
    simpa only [he] using hbound
  have hs : 2⁻¹*r*‖∫ t in (-2*r⁻¹)..(2*r⁻¹), 1-f (t • a)‖ ≤ η/2 := by
    calc
      _ ≤ 2⁻¹*r*((η/4)*δ) := mul_le_mul_of_nonneg_left hn (by positivity)
      _ = η/2 := by dsimp [r]; field_simp
  have hl := (integral_defect_limit μ f hc a (-2*r⁻¹) (2*r⁻¹)).norm.const_mul (2⁻¹*r)
  refine ⟨r,hr,?_⟩
  have hsmall : (η:ℝ)/2 < η := by linarith
  filter_upwards [hl.eventually (gt_mem_nhds (hs.trans_lt hsmall))] with n hn
  exact (measureReal_abs_inner_gt_le_integral_charFun (μ := (μ n : Measure E)) (a := a) hr).trans hn.le

#print axioms integral_defect_limit
#print axioms eventual_projection_tail

end
end UnifiedTheory.Audit.KFCausalCharacteristicTailControl
