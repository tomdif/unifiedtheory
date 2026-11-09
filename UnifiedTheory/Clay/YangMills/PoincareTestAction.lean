/- Schwartz-test pullbacks by genuine four-dimensional Poincare transformations.
Continuity here is in the test argument for each fixed transformation. Strong
continuity in the group parameter and a physical unitary representation are
separate obligations, not conclusions of this module. -/
import UnifiedTheory.Clay.YangMills.PoincareKinematics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PoincareTestAction
noncomputable section
open LocalFields PoincareKinematics

/-- Scalar pullback with the inverse convention, so multiplication gives a left
action. Schwartz decay is preserved by the affine inverse's coercivity. -/
def testPullback (g : Poincare) : TestFunction →L[ℂ] TestFunction :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (affine_temperateGrowth (transform g⁻¹)) (affine_antilipschitz (transform g⁻¹))

@[simp] theorem testPullback_apply (g : Poincare) (f : TestFunction) (x : Spacetime) :
    testPullback g f x = f (transform g⁻¹ x) := rfl

@[simp] theorem testPullback_one (f : TestFunction) : testPullback 1 f = f := by
  ext x
  simp

theorem testPullback_mul (g h : Poincare) (f : TestFunction) :
    testPullback (g * h) f = testPullback g (testPullback h f) := by
  ext x
  simp only [testPullback_apply, mul_inv_rev, transform_mul]

@[simp] theorem testPullback_inv (g : Poincare) (f : TestFunction) :
    testPullback g⁻¹ (testPullback g f) = f := by
  rw [← testPullback_mul, inv_mul_cancel, testPullback_one]

@[simp] theorem testPullback_inv_right (g : Poincare) (f : TestFunction) :
    testPullback g (testPullback g⁻¹ f) = f := by
  rw [← testPullback_mul, mul_inv_cancel, testPullback_one]

/-- Every geometric pullback is a continuous linear automorphism of the actual
Schwartz test space on R^4. -/
def testEquiv (g : Poincare) : TestFunction ≃L[ℂ] TestFunction :=
  ContinuousLinearEquiv.equivOfInverse (testPullback g) (testPullback g⁻¹)
    (testPullback_inv g) (testPullback_inv_right g)

@[simp] theorem testEquiv_apply (g : Poincare) (f : TestFunction) :
    testEquiv g f = testPullback g f := rfl

/-- The full affine Poincare group acts algebraically on the Schwartz space. -/
def testAction : Poincare →* (TestFunction ≃L[ℂ] TestFunction) where
  toFun := testEquiv
  map_one' := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact testPullback_one f
  map_mul' g h := by
    apply ContinuousLinearEquiv.ext
    funext f
    exact testPullback_mul g h f

/-- Restriction to the group appropriate for unitary physical covariance. -/
def properTestAction : ProperPoincare →* (TestFunction ≃L[ℂ] TestFunction) :=
  testAction.comp properOrthochronous.subtype

theorem continuous_testPullback (g : Poincare) : Continuous (testPullback g) :=
  (testPullback g).continuous

@[simp] theorem testPullback_translation (a : Spacetime) (f : TestFunction) (x : Spacetime) :
    testPullback (translation a) f x = f (x - a) := by
  simp only [testPullback_apply, translation_inv, translation_apply]
  congr 1
  abel

/-- Exact topological-support transport, not a permutation of insertion indices. -/
theorem tsupport_testPullback (g : Poincare) (f : TestFunction) :
    tsupport (testPullback g f) = (transform g⁻¹) ⁻¹' tsupport f := by
  exact tsupport_comp_eq_preimage f (spacetimeHomeomorph g⁻¹)

theorem mem_tsupport_testPullback_iff (g : Poincare) (f : TestFunction) (x : Spacetime) :
    x ∈ tsupport (testPullback g f) ↔ transform g⁻¹ x ∈ tsupport f := by
  rw [tsupport_testPullback]
  rfl

/-- Genuine causal separation is invariant under the geometric action. -/
theorem spacelikeSeparated_testPullback (g : Poincare) (f h : TestFunction)
    (hsep : SpacelikeSeparated f h) :
    SpacelikeSeparated (testPullback g f) (testPullback g h) := by
  intro x hx y hy
  have hx' := (mem_tsupport_testPullback_iff g f x).mp hx
  have hy' := (mem_tsupport_testPullback_iff g h y).mp hy
  have hxy := hsep (transform g⁻¹ x) hx' (transform g⁻¹ y) hy'
  rwa [preserves_interval] at hxy

theorem spacelikeSeparated_testPullback_iff (g : Poincare) (f h : TestFunction) :
    SpacelikeSeparated (testPullback g f) (testPullback g h) ↔ SpacelikeSeparated f h := by
  constructor
  · intro hsep
    simpa using spacelikeSeparated_testPullback g⁻¹ _ _ hsep
  · exact spacelikeSeparated_testPullback g f h

/-- Every already-local candidate remains local on the transformed tests. This
is a consequence of locality and geometry, not a construction of local fields. -/
theorem locality_on_transformed_tests {Label H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (S : FieldSystem Label H)
    (hlocal : Locality S) (g : Poincare) (a b : Label) (f h : TestFunction)
    (hsep : SpacelikeSeparated f h) (u : S.domain) :
    S.field a (testPullback g f) (S.field b (testPullback g h) u) =
      S.field b (testPullback g h) (S.field a (testPullback g f) u) :=
  hlocal a b _ _ (spacelikeSeparated_testPullback g f h hsep) u

end
end UnifiedTheory.Clay.YangMills.PoincareTestAction
