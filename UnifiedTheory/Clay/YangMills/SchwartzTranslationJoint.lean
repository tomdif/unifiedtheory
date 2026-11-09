/- Joint continuity of translation and test-function variation in the full
Schwartz topology, using locally uniform bounds for every Schwartz seminorm. -/
import UnifiedTheory.Clay.YangMills.SchwartzTranslationContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SchwartzTranslationJoint
noncomputable section
open LocalFields PoincareKinematics PoincareTestAction SchwartzTranslationContinuity
open scoped Topology

def translationBound (k n : ℕ) (f : TestFunction) : ℝ :=
  2 ^ k * ∑ i ∈ Finset.Iic (k, n), SchwartzMap.seminorm ℂ i.1 i.2 f

theorem translationBound_nonneg (k n : ℕ) (f : TestFunction) : 0 ≤ translationBound k n f := by
  unfold translationBound
  positivity

theorem continuous_translationBound (k n : ℕ) : Continuous (translationBound k n) := by
  apply continuous_const.mul
  apply continuous_finset_sum
  intro i hi
  exact (schwartz_withSeminorms ℂ Spacetime ℂ).continuous_seminorm i

@[simp] theorem translationBound_zero (k n : ℕ) : translationBound k n 0 = 0 := by
  simp [translationBound]

theorem seminorm_translation_bound (k n : ℕ) (f : TestFunction) (a : Spacetime)
    (ha : ‖a‖ ≤ 1) :
    SchwartzMap.seminorm ℂ k n (testPullback (translation a) f) ≤ translationBound k n f := by
  apply SchwartzMap.seminorm_le_bound ℂ k n _ (translationBound_nonneg k n f)
  intro x
  rw [iteratedFDeriv_translation]
  have hx : ‖x‖ ≤ 1 + ‖x - a‖ := by
    have h := norm_le_norm_sub_add x a
    linarith
  calc
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n f (x - a)‖ ≤
        (1 + ‖x - a‖) ^ k * ‖iteratedFDeriv ℝ n f (x - a)‖ := by gcongr
    _ ≤ 2 ^ k * (Finset.Iic (k, n)).sup
        (fun i => SchwartzMap.seminorm ℂ i.1 i.2) f :=
      SchwartzMap.one_add_le_sup_seminorm_apply (m := (k, n)) le_rfl le_rfl f (x - a)
    _ ≤ translationBound k n f := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Seminorm.finset_sup_apply_le (by positivity)
      intro i hi
      exact Finset.single_le_sum (fun j _ => apply_nonneg (SchwartzMap.seminorm ℂ j.1 j.2) f) hi

theorem seminorm_translation_pair_difference (k n : ℕ) (f u : TestFunction) (a : Spacetime)
    (ha : ‖a‖ ≤ 1) :
    SchwartzMap.seminorm ℂ k n (testPullback (translation a) u - f) ≤
      translationBound k n (u - f) + derivativeBound f k n * ‖a‖ := by
  have heq : testPullback (translation a) u - f =
      testPullback (translation a) (u - f) + (testPullback (translation a) f - f) := by
    rw [map_sub]
    abel
  rw [heq]
  exact (map_add_le_add (SchwartzMap.seminorm ℂ k n) _ _).trans
    (add_le_add (seminorm_translation_bound k n (u - f) a ha)
      (seminorm_translation_difference f k n a ha))

theorem tendsto_translation_pair_zero (f : TestFunction) :
    Filter.Tendsto (fun p : Spacetime × TestFunction => testPullback (translation p.1) p.2)
      (𝓝 (0, f)) (𝓝 f) := by
  apply ((schwartz_withSeminorms ℂ Spacetime ℂ).tendsto_nhds _ f).mpr
  rintro ⟨k, n⟩ ε hε
  have hsmall : ∀ᶠ p : Spacetime × TestFunction in 𝓝 (0, f), ‖p.1‖ ≤ 1 := by
    have hb := (continuous_fst.tendsto (0, f)).eventually
      (Metric.closedBall_mem_nhds (0 : Spacetime) (by norm_num : (0 : ℝ) < 1))
    simpa only [Metric.mem_closedBall, dist_zero_right] using hb
  have hc : Continuous (fun p : Spacetime × TestFunction =>
      translationBound k n (p.2 - f) + derivativeBound f k n * ‖p.1‖) :=
    ((continuous_translationBound k n).comp (continuous_snd.sub continuous_const)).add
      (continuous_const.mul continuous_fst.norm)
  have hlim : Filter.Tendsto (fun p : Spacetime × TestFunction =>
      translationBound k n (p.2 - f) + derivativeBound f k n * ‖p.1‖)
      (𝓝 (0, f)) (𝓝 0) := by simpa using hc.tendsto (0, f)
  filter_upwards [hsmall, hlim.eventually (gt_mem_nhds hε)] with p hp hεp
  exact (seminorm_translation_pair_difference k n f p.2 p.1 hp).trans_lt hεp

/-- Joint continuity, including variation of the Schwartz test itself. -/
theorem continuous_translation_test_pair :
    Continuous (fun p : Spacetime × TestFunction => testPullback (translation p.1) p.2) := by
  apply continuous_iff_continuousAt.mpr
  rintro ⟨b, f⟩
  have hc : Continuous (fun p : Spacetime × TestFunction => (p.1 - b, p.2)) :=
    (continuous_fst.sub continuous_const).prodMk continuous_snd
  have hlim : Filter.Tendsto (fun p : Spacetime × TestFunction => (p.1 - b, p.2))
      (𝓝 (b, f)) (𝓝 (0, f)) := by simpa using hc.tendsto (b, f)
  have ht := ((testPullback (translation b)).continuous.tendsto f).comp
    ((tendsto_translation_pair_zero f).comp hlim)
  have hcancel (a : Spacetime) : b + (a - b) = a := by abel
  simpa only [Function.comp_def, ← testPullback_mul, ← translation_add,
    hcancel] using ht

end
end UnifiedTheory.Clay.YangMills.SchwartzTranslationJoint
