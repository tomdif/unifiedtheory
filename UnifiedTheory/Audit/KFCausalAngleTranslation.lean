/- Translation of the normalized angle interval modulo one. The map
preserves the actual angle measure, so its pullback is an L2 isometry.
This construction applies to arbitrary L2 sections, not just continuous
orbit representatives. -/
import UnifiedTheory.Audit.KFCausalUnitIntervalOrbit
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 800000

namespace UnifiedTheory.Audit.KFCausalAngleTranslation
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalUnitIntervalOrbit (angleMeasure)

def representative (x : UnitAddCircle) : ℝ := (AddCircle.equivIoc 1 0 x).val

def shift (a θ : ℝ) : ℝ := representative ((θ : UnitAddCircle)+(a : UnitAddCircle))

theorem representative_preserving :
    MeasurePreserving representative volume angleMeasure := by
  simpa only [representative, angleMeasure, zero_add] using
    (measurePreserving_subtype_coe measurableSet_Ioc).comp
      (AddCircle.measurePreserving_equivIoc 1 (a := 0))

theorem shift_preserving (a : ℝ) : MeasurePreserving (shift a) angleMeasure angleMeasure := by
  exact representative_preserving.comp
    ((measurePreserving_add_right (volume : Measure UnitAddCircle) (a : UnitAddCircle)).comp
      (show MeasurePreserving ((↑) : ℝ → UnitAddCircle) angleMeasure volume by
        simpa only [angleMeasure, zero_add] using UnitAddCircle.measurePreserving_mk 0))

theorem representative_coe (x : UnitAddCircle) : (representative x : UnitAddCircle) = x :=
  (AddCircle.equivIoc 1 0).symm_apply_apply x

theorem periodic_shift {E : Type*} (f : ℝ → E) (hf : Function.Periodic f 1) (a θ : ℝ) :
    f (shift a θ) = f (θ+a) := by
  have he : (shift a θ : UnitAddCircle) = (θ+a : ℝ) := by
    rw [shift, representative_coe]
    rfl
  exact congrArg hf.lift he

variable {E K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

def pullback (a : ℝ) : Lp E 2 angleMeasure →ₗᵢ[ℂ] Lp E 2 angleMeasure :=
  Lp.compMeasurePreservingₗᵢ ℂ (shift a) (shift_preserving a)

theorem pullback_coe (a : ℝ) (v : Lp E 2 angleMeasure) :
    pullback a v =ᵐ[angleMeasure] fun θ => v (shift a θ) :=
  Lp.coeFn_compMeasurePreserving v (shift_preserving a)

theorem pullback_compLp (a : ℝ) (A : E →L[ℂ] K) (v : Lp E 2 angleMeasure) :
    A.compLp (pullback a v) = pullback a (A.compLp v) := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLp (pullback a v), pullback_coe a v,
    pullback_coe a (A.compLp v),
    (shift_preserving a).quasiMeasurePreserving.ae (A.coeFn_compLp v)] with θ hA hv hP hAv
  exact hA.trans ((congrArg A hv).trans (hAv.symm.trans hP.symm))

#print axioms representative_preserving
#print axioms shift_preserving
#print axioms representative_coe
#print axioms periodic_shift
#print axioms pullback_coe
#print axioms pullback_compLp

end
end UnifiedTheory.Audit.KFCausalAngleTranslation
