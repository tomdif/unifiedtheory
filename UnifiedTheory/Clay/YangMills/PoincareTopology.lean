/- Coefficient topology and jointly continuous spacetime evaluation for the
actual affine Poincare group. The topology is pulled back from the invertible
continuous linear operator and translation-vector coordinates, not declared
discrete to make a continuity requirement vacuous. -/
import UnifiedTheory.Clay.YangMills.PoincareTestAction
import Mathlib.Topology.Algebra.Group.Units

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.PoincareTopology
noncomputable section
open LocalFields PoincareKinematics PoincareTestAction

/-- The invertible continuous linear part in operator-norm coordinates. -/
def linearUnit : Poincare →* (Spacetime →L[ℝ] Spacetime)ˣ where
  toFun g := (transform g).linear.toContinuousLinearEquiv.toUnit
  map_one' := by
    apply Units.ext
    ext x
    rfl
  map_mul' g h := by
    apply Units.ext
    ext x
    rfl

@[simp] theorem linearUnit_apply (g : Poincare) (x : Spacetime) :
    (linearUnit g : Spacetime →L[ℝ] Spacetime) x = (transform g).linear x := rfl

def offset (g : Poincare) : Spacetime := transform g 0

def coordinates (g : Poincare) : (Spacetime →L[ℝ] Spacetime)ˣ × Spacetime :=
  (linearUnit g, offset g)

instance poincareTopologicalSpace : TopologicalSpace Poincare :=
  TopologicalSpace.induced coordinates inferInstance

theorem continuous_coordinates : Continuous coordinates := continuous_induced_dom

theorem continuous_linearUnit : Continuous linearUnit := continuous_coordinates.fst

theorem continuous_offset : Continuous offset := continuous_coordinates.snd

theorem coordinates_injective : Function.Injective coordinates := by
  intro g h hgh
  apply Subtype.ext
  apply AffineEquiv.ext
  intro x
  have hl := congrArg Prod.fst hgh
  have ht := congrArg Prod.snd hgh
  have hx := congrArg (fun u : (Spacetime →L[ℝ] Spacetime)ˣ => (u : Spacetime →L[ℝ] Spacetime) x) hl
  change (transform g).linear x = (transform h).linear x at hx
  change offset g = offset h at ht
  change transform g x = transform h x
  rw [affine_decomposition (transform g) x, affine_decomposition (transform h) x, hx]
  exact congrArg ((transform h).linear x + ·) ht

theorem offset_mul (g h : Poincare) :
    offset (g * h) = (linearUnit g : Spacetime →L[ℝ] Spacetime) (offset h) + offset g := by
  exact affine_decomposition (transform g) (transform h 0)

theorem offset_inv (g : Poincare) :
    offset g⁻¹ = -((linearUnit g)⁻¹).val (offset g) := by
  have h := affine_decomposition (transform g⁻¹) (transform g 0)
  rw [transform_apply_inv] at h
  change 0 = ((linearUnit g)⁻¹).val (offset g) + offset g⁻¹ at h
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using h.symm

instance poincareTopologicalGroup : IsTopologicalGroup Poincare where
  continuous_mul := by
    apply continuous_induced_rng.mpr
    have hlin : Continuous (fun p : Poincare × Poincare => linearUnit p.1 * linearUnit p.2) :=
      (continuous_linearUnit.comp continuous_fst).mul
        (continuous_linearUnit.comp continuous_snd)
    have hoff : Continuous (fun p : Poincare × Poincare =>
        (linearUnit p.1 : Spacetime →L[ℝ] Spacetime) (offset p.2) + offset p.1) :=
      ((Units.continuous_val.comp (continuous_linearUnit.comp continuous_fst)).clm_apply
        (continuous_offset.comp continuous_snd)).add
        (continuous_offset.comp continuous_fst)
    simpa only [Function.comp_def, coordinates, map_mul, offset_mul] using hlin.prodMk hoff
  continuous_inv := by
    apply continuous_induced_rng.mpr
    have hlin : Continuous (fun g : Poincare => (linearUnit g)⁻¹) := continuous_linearUnit.inv
    have hoff : Continuous (fun g : Poincare =>
        -((linearUnit g)⁻¹).val (offset g)) :=
      ((Units.continuous_val.comp hlin).clm_apply continuous_offset).neg
    simpa only [Function.comp_def, coordinates, map_inv, offset_inv] using hlin.prodMk hoff

/-- The genuine action on spacetime is jointly continuous in transformation and
spacetime point. This is weaker than continuity of its action on Schwartz tests. -/
theorem continuous_spacetime_action :
    Continuous (fun p : Poincare × Spacetime => transform p.1 p.2) := by
  have h : Continuous (fun p : Poincare × Spacetime =>
      (linearUnit p.1 : Spacetime →L[ℝ] Spacetime) p.2 + offset p.1) :=
    ((Units.continuous_val.comp (continuous_linearUnit.comp continuous_fst)).clm_apply
      continuous_snd).add (continuous_offset.comp continuous_fst)
  simpa only [linearUnit_apply, offset, ← affine_decomposition] using h

@[simp] theorem linearUnit_translation (a : Spacetime) : linearUnit (translation a) = 1 := by
  apply Units.ext
  ext x
  rfl

@[simp] theorem offset_translation (a : Spacetime) : offset (translation a) = a := by
  simp [offset]

theorem continuous_translation : Continuous translation := by
  apply continuous_induced_rng.mpr
  simpa only [Function.comp_def, coordinates, linearUnit_translation, offset_translation] using
    (continuous_const.prodMk continuous_id :
      Continuous (fun a : Spacetime => ((1 : (Spacetime →L[ℝ] Spacetime)ˣ), a)))

theorem continuous_properTranslation : Continuous properTranslation :=
  continuous_translation.subtype_mk _

/-- Group-parameter continuity of the test action is recorded as its own
analytic target. Fixed-transform continuity was proved in PoincareTestAction. -/
def StronglyContinuousTestAction : Prop :=
  ∀ f : TestFunction, Continuous (fun g : ProperPoincare => properTestAction g f)

/-- Although Schwartz-topology continuity remains separate, every point
evaluation of a transformed test is already continuous in the full spacetime
group and the evaluation point. -/
theorem continuous_pullback_evaluation (f : TestFunction) :
    Continuous (fun p : Poincare × Spacetime => testPullback p.1 f p.2) := by
  have hinv : Continuous (fun p : Poincare × Spacetime => (p.1⁻¹, p.2)) :=
    continuous_fst.inv.prodMk continuous_snd
  exact f.continuous.comp (continuous_spacetime_action.comp hinv)

end
end UnifiedTheory.Clay.YangMills.PoincareTopology
