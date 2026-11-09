/- A concrete ten-dimensional phase-space projection is dual to the
already proved canonical frequency encoding. Pushforward characteristics
are exactly the ten physical phase tests, without coordinate assumptions. -/
import UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
import UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalTenPhaseProjection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space split)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalTenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates (coordinateMap)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (phase)

abbrev TenSpace := EuclideanSpace ℝ (Fin 5 ⊕ Fin 5)
abbrev FullSpace := Block 6 × Block 6

def coefficients : TenSpace →L[ℝ] Coefficients where
  toFun z := (fun i => z (Sum.inl i),fun j => z (Sum.inr j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def coefficientVector (z : Coefficients) : TenSpace := WithLp.toLp 2 (Sum.elim z.1 z.2)

theorem coefficients_vector (z : Coefficients) : coefficients (coefficientVector z) = z := rfl

def inverseLinear : Configuration →ₗ[ℝ] Space where
  toFun := split.symm
  map_add' x y := by
    apply split.injective
    change coordinateMap (split.symm (x+y)) = coordinateMap (split.symm x+split.symm y)
    rw [coordinateMap.map_add]
    change split (split.symm (x+y)) = split (split.symm x)+split (split.symm y)
    simp only [split.apply_symm_apply]
  map_smul' c x := by
    apply split.injective
    change coordinateMap (split.symm (c • x)) = coordinateMap (c • split.symm x)
    rw [coordinateMap.map_smul]
    change split (split.symm (c • x)) = c • split (split.symm x)
    simp only [split.apply_symm_apply]

def functionalLinear (x : FullSpace) : TenSpace →ₗ[ℝ] ℝ where
  toFun z := (encode (coefficients z)).1 (coordinateMap x.1)+
    inner ℝ (inverseLinear (encode (coefficients z)).2) x.2
  map_add' z w := by simp [map_add,inner_add_left]; ring
  map_smul' c z := by simp [map_smul,inner_smul_left]; ring

def functional (x : FullSpace) : TenSpace →L[ℝ] ℝ := (functionalLinear x).toContinuousLinearMap

def functionalsLinear : FullSpace →ₗ[ℝ] (TenSpace →L[ℝ] ℝ) where
  toFun := functional
  map_add' x y := by
    apply ContinuousLinearMap.ext
    intro z
    change functionalLinear (x+y) z = functionalLinear x z+functionalLinear y z
    simp [functionalLinear,map_add,inner_add_right]
    ring
  map_smul' c x := by
    apply ContinuousLinearMap.ext
    intro z
    change functionalLinear (c • x) z = c*functionalLinear x z
    simp [functionalLinear,map_smul,inner_smul_right]
    ring

def project : FullSpace →L[ℝ] TenSpace :=
  (InnerProductSpace.toDual ℝ TenSpace).symm.toContinuousLinearMap.comp
    functionalsLinear.toContinuousLinearMap

theorem project_inner (x : FullSpace) (z : TenSpace) :
    inner ℝ (project x) z = (encode (coefficients z)).1 (coordinateMap x.1)+
      inner ℝ (inverseLinear (encode (coefficients z)).2) x.2 := by
  exact InnerProductSpace.toDual_symm_apply

theorem phase_project (x : FullSpace) (z : TenSpace) :
    Complex.exp ((inner ℝ (project x) z : ℂ)*Complex.I) = phase (encode (coefficients z)) x := by
  rw [project_inner]
  change Complex.exp (_*Complex.I) = Complex.exp (Complex.I*_)
  congr 1
  exact mul_comm _ _

theorem projected_characteristic (μ : Measure FullSpace) (z : TenSpace) :
    charFun (μ.map project) z = ∫ x, phase (encode (coefficients z)) x ∂μ := by
  rw [charFun_apply,integral_map project.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [phase_project]

#print axioms coefficients_vector
#print axioms project_inner
#print axioms phase_project
#print axioms projected_characteristic

end
end UnifiedTheory.Audit.KFCausalTenPhaseProjection
