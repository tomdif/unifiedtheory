/- Strong continuity in the full Schwartz topology of genuine Poincare
pullbacks. This discharges the test-action continuity interface using the real
coefficient topology. It does not construct a physical unitary field theory. -/
import UnifiedTheory.Clay.YangMills.SchwartzTranslationJoint
import UnifiedTheory.Clay.YangMills.SchwartzLinearContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PoincareStrongTestContinuity
noncomputable section
open LocalFields PoincareKinematics PoincareTestAction PoincareTopology
open SchwartzTranslationJoint SchwartzLinearContinuity
open scoped Topology

theorem inverse_affine_formula (g : Poincare) (x : Spacetime) :
    transform g⁻¹ x = linearOperator g⁻¹ (x - offset g) := by
  have h := affine_difference (transform g⁻¹) x (transform g 0)
  rw [transform_apply_inv, sub_zero] at h
  exact h

/-- Separate translation from the inverse linear part without changing the
geometric pullback convention. -/
theorem testPullback_eq_translation_linear (g : Poincare) (f : TestFunction) :
    testPullback g f = testPullback (translation (offset g)) (linearPullback g⁻¹ f) := by
  ext x
  rw [testPullback_apply, testPullback_translation, linearPullback_apply,
    inverse_affine_formula]

theorem tendsto_testPullback_one (f : TestFunction) :
    Filter.Tendsto (fun g : Poincare => testPullback g f) (𝓝 1) (𝓝 f) := by
  have hinv : Filter.Tendsto (fun g : Poincare => g⁻¹) (𝓝 1) (𝓝 1) := by
    simpa using (continuous_inv : Continuous (fun g : Poincare => g⁻¹)).tendsto 1
  have hlinear := (tendsto_linearPullback_one f).comp hinv
  have hoffset : Filter.Tendsto offset (𝓝 (1 : Poincare)) (𝓝 0) := by
    simpa [offset] using continuous_offset.tendsto 1
  have hpair := hoffset.prodMk_nhds hlinear
  have ht := (continuous_translation_test_pair.tendsto (0, f)).comp hpair
  simpa only [Function.comp_def, translation_zero, testPullback_one,
    ← testPullback_eq_translation_linear] using ht

/-- Unconditional strong continuity of the actual full affine Minkowski group
on Schwartz tests, including Lorentz transformations and translations. -/
theorem continuous_testPullback (f : TestFunction) :
    Continuous (fun g : Poincare => testPullback g f) := by
  apply continuous_iff_continuousAt.mpr
  intro h
  have hc : Continuous (fun g : Poincare => h⁻¹ * g) := continuous_const.mul continuous_id
  have hlim : Filter.Tendsto (fun g : Poincare => h⁻¹ * g) (𝓝 h) (𝓝 1) := by
    simpa using hc.tendsto h
  have ht := ((testPullback h).continuous.tendsto f).comp
    ((tendsto_testPullback_one f).comp hlim)
  simpa only [Function.comp_def, ← testPullback_mul, ← mul_assoc,
    mul_inv_cancel, one_mul] using ht

/-- The previously stated proper-orthochronous test-continuity target is now
proved, with no assumed physical representation or continuity premise. -/
theorem stronglyContinuousTestAction : StronglyContinuousTestAction := by
  intro f
  exact (continuous_testPullback f).comp continuous_subtype_val

/-- Every continuous functional of a transformed test inherits the actual
group-parameter continuity. Physical covariance is a separate requirement. -/
theorem continuous_transformed_functional {V : Type*} [TopologicalSpace V]
    (L : TestFunction → V) (hL : Continuous L) (f : TestFunction) :
    Continuous (fun g : ProperPoincare => L (properTestAction g f)) :=
  hL.comp (stronglyContinuousTestAction f)

theorem continuous_transformed_matrix_element {Label H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : FieldSystem Label H)
    (htemp : WeakTempered S) (a : Label) (u v : S.domain) (f : TestFunction) :
    Continuous (fun g : ProperPoincare =>
      inner ℂ (u : H) (S.field a (properTestAction g f) v : H)) :=
  (htemp a u v).comp (stronglyContinuousTestAction f)

end
end UnifiedTheory.Clay.YangMills.PoincareStrongTestContinuity
