/- A genuine form commutator estimate, including L2 families of outputs.
Its size is O(|c|+|c|^2), uniform over all energy-output vectors. -/
import UnifiedTheory.Audit.KFCausalNeutralTranslationBounds
import UnifiedTheory.Audit.KFCausalNeutralTranslationFactors
import Mathlib.MeasureTheory.Function.L2Space

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1400000

namespace UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalNeutralTranslationCoordinates (action)
open UnifiedTheory.Audit.KFCausalNeutralTranslationFactors (action_inverse)
open UnifiedTheory.Audit.KFCausalNeutralTranslationOutput
open UnifiedTheory.Audit.KFCausalNeutralTranslationBounds

theorem translateOutput_inverse (r : ℝ) (y : Outputs) :
    translateOutput (-r) (translateOutput r y) = y := by
  apply PiLp.ext
  intro i
  exact action_inverse r (y i)

theorem translateOutput_inner (r : ℝ) (x y : Outputs) :
    inner ℂ (translateOutput r x) (translateOutput r y) = inner ℂ x y := by
  simp only [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  exact (action r).inner_map_map (x i) (y i)

theorem translateOutput_dual (r : ℝ) (x y : Outputs) :
    inner ℂ x (translateOutput r y) = inner ℂ (translateOutput (-r) x) y := by
  have he := translateOutput_inner r (translateOutput (-r) x) y
  have hi : translateOutput r (translateOutput (-r) x) = x := by
    simpa only [neg_neg] using translateOutput_inverse (-r) x
  rwa [hi] at he

theorem commutator_bound {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (R S T V : K →L[ℂ] K) (d : ℝ)
    (hdual : ∀ x y, inner ℂ x (T y) = inner ℂ (V x) y)
    (hR : ∀ y, ‖R y-T y‖ ≤ d*‖y‖) (hS : ∀ x, ‖S x-V x‖ ≤ d*‖x‖) (x y : K) :
    ‖inner ℂ x (R y)-inner ℂ (S x) y‖ ≤ (2*d)*‖x‖*‖y‖ := by
  have he : inner ℂ x (R y)-inner ℂ (S x) y =
      inner ℂ x (R y-T y)-inner ℂ (S x-V x) y := by
    rw [inner_sub_right,inner_sub_left,hdual]
    ring
  rw [he]
  calc
    _ ≤ ‖inner ℂ x (R y-T y)‖+‖inner ℂ (S x-V x) y‖ := norm_sub_le _ _
    _ ≤ ‖x‖*‖R y-T y‖+‖S x-V x‖*‖y‖ :=
      add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
    _ ≤ ‖x‖*(d*‖y‖)+(d*‖x‖)*‖y‖ :=
      add_le_add (mul_le_mul_of_nonneg_left (hR y) (norm_nonneg _))
        (mul_le_mul_of_nonneg_right (hS x) (norm_nonneg _))
    _ = _ := by ring

theorem output_commutator (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (r : ℝ) (x y : Outputs) :
    ‖inner ℂ x (outputAction w c r y)-inner ℂ (outputAction w (-c) (-r) x) y‖ ≤
      (2*errorBound w c)*‖x‖*‖y‖ :=
  commutator_bound _ _ (translateOutput r) (translateOutput (-r)) _ (translateOutput_dual r)
    (outputAction_error w hw c r)
    (by simpa only [errorBound_neg] using outputAction_error w hw (-c) (-r)) x y

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)

theorem compLp_error (R T : Outputs →L[ℂ] Outputs) (d : ℝ) (hd : 0 ≤ d)
    (hb : ∀ y, ‖R y-T y‖ ≤ d*‖y‖) (y : Lp Outputs 2 μ) :
    ‖R.compLp y-T.compLp y‖ ≤ d*‖y‖ := by
  have he : (R-T).compLp y = R.compLp y-T.compLp y := by
    apply Lp.ext
    filter_upwards [(R-T).coeFn_compLp y,R.coeFn_compLp y,T.coeFn_compLp y,
      Lp.coeFn_sub (R.compLp y) (T.compLp y)] with z h1 h2 h3 h4
    simp only [h1,h2,h3,h4,Pi.sub_apply,ContinuousLinearMap.sub_apply]
  rw [← he]
  apply ((R-T).norm_compLp_le y).trans
  exact mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_le_bound _ hd hb) (norm_nonneg y)

theorem translateLp_dual (r : ℝ) (x y : Lp Outputs 2 μ) :
    inner ℂ x ((translateOutput r).compLp y) = inner ℂ ((translateOutput (-r)).compLp x) y := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(translateOutput r).coeFn_compLp y,(translateOutput (-r)).coeFn_compLp x] with z h1 h2
  rw [h1,h2,translateOutput_dual]

theorem outputLp_commutator (w : Fin 8 → ℂ) (hw : ∀ i, w i ≠ 0) (c : ℂ) (r : ℝ)
    (x y : Lp Outputs 2 μ) :
    ‖inner ℂ x ((outputAction w c r).compLp y)-inner ℂ ((outputAction w (-c) (-r)).compLp x) y‖ ≤
      (2*errorBound w c)*‖x‖*‖y‖ :=
  commutator_bound ((outputAction w c r).compLpL 2 μ) ((outputAction w (-c) (-r)).compLpL 2 μ)
    ((translateOutput r).compLpL 2 μ) ((translateOutput (-r)).compLpL 2 μ) _
    (translateLp_dual μ r)
    (compLp_error μ _ _ _ (errorBound_nonneg w c) (outputAction_error w hw c r))
    (by simpa only [errorBound_neg] using
      compLp_error μ _ _ _ (errorBound_nonneg w (-c)) (outputAction_error w hw (-c) (-r))) x y

#print axioms translateOutput_inverse
#print axioms translateOutput_inner
#print axioms translateOutput_dual
#print axioms commutator_bound
#print axioms output_commutator
#print axioms compLp_error
#print axioms translateLp_dual
#print axioms outputLp_commutator

end
end UnifiedTheory.Audit.KFCausalNeutralTranslationCommutator
