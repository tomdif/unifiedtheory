/- A concrete eleven-dimensional phase-space projection is dual to the
already proved canonical frequency encoding. Pushforward characteristics
are exactly the eleven physical phase tests, without coordinate assumptions. -/
import UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw
import UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates
import UnifiedTheory.Audit.KFCausalTenPhaseProjection
import Mathlib.MeasureTheory.Measure.CharacteristicFunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1800000

namespace UnifiedTheory.Audit.KFCausalElevenPhaseProjection
noncomputable section
open MeasureTheory
open UnifiedTheory.Audit.KFCausalEuclideanProductCoordinates (Block)
open UnifiedTheory.Audit.KFCausalEuclideanConfiguration (Space split)
open UnifiedTheory.Audit.KFCausalCoupledLongitudinalFlow (Configuration)
open UnifiedTheory.Audit.KFCausalCanonicalElevenCoordinates (Coefficients encode)
open UnifiedTheory.Audit.KFCausalPhysicalCanonicalCoordinates (coordinateMap)
open UnifiedTheory.Audit.KFCausalCanonicalWeylAlgebra (scalar)
open UnifiedTheory.Audit.KFCausalPhysicalWindowedLaw (phase)

abbrev ElevenSpace := EuclideanSpace ℝ ((Fin 5 ⊕ Fin 5) ⊕ Unit)
abbrev FullSpace := Block 6 × Block 6

def coefficients : ElevenSpace →L[ℝ] Coefficients where
  toFun z := ((fun i => z (.inl (.inl i)),fun j => z (.inl (.inr j))),z (.inr ()))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  cont := by fun_prop

def coefficientVector (z : Coefficients) : ElevenSpace := WithLp.toLp 2 (Sum.elim (Sum.elim z.1.1 z.1.2) (fun _ => z.2))

theorem coefficients_vector (z : Coefficients) : coefficients (coefficientVector z) = z := rfl

theorem vector_coefficients (z : ElevenSpace) : coefficientVector (coefficients z) = z := by
  apply PiLp.ext
  intro i
  rcases i with ((i|i)|⟨⟩) <;> rfl

open UnifiedTheory.Audit.KFCausalTenPhaseProjection (inverseLinear)

def functionalLinear (x : FullSpace) : ElevenSpace →ₗ[ℝ] ℝ where
  toFun z := (encode (coefficients z)).1 (coordinateMap x.1)+
    inner ℝ (inverseLinear (encode (coefficients z)).2) x.2
  map_add' z w := by simp [map_add,inner_add_left]; ring
  map_smul' c z := by simp [map_smul,inner_smul_left]; ring

def functional (x : FullSpace) : ElevenSpace →L[ℝ] ℝ := (functionalLinear x).toContinuousLinearMap

def functionalsLinear : FullSpace →ₗ[ℝ] (ElevenSpace →L[ℝ] ℝ) where
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

def project : FullSpace →L[ℝ] ElevenSpace :=
  (InnerProductSpace.toDual ℝ ElevenSpace).symm.toContinuousLinearMap.comp
    functionalsLinear.toContinuousLinearMap

theorem project_inner (x : FullSpace) (z : ElevenSpace) :
    inner ℝ (project x) z = (encode (coefficients z)).1 (coordinateMap x.1)+
      inner ℝ (inverseLinear (encode (coefficients z)).2) x.2 := by
  exact InnerProductSpace.toDual_symm_apply

theorem phase_project (x : FullSpace) (z : ElevenSpace) :
    Complex.exp ((inner ℝ (project x) z : ℂ)*Complex.I) = phase (encode (coefficients z)) x := by
  rw [project_inner]
  change Complex.exp (_*Complex.I) = Complex.exp (Complex.I*_)
  congr 1
  exact mul_comm _ _

theorem projected_characteristic (μ : Measure FullSpace) (z : ElevenSpace) :
    charFun (μ.map project) z = ∫ x, phase (encode (coefficients z)) x ∂μ := by
  rw [charFun_apply,integral_map project.continuous.measurable.aemeasurable (by fun_prop)]
  simp only [phase_project]

#print axioms coefficients_vector
#print axioms vector_coefficients
#print axioms project_inner
#print axioms phase_project
#print axioms projected_characteristic

end
end UnifiedTheory.Audit.KFCausalElevenPhaseProjection
