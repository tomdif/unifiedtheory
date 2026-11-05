/- A constructed topological group equivalence between unit quaternions and
the actual determinant-one 2 by 2 complex unitary matrices. Its inverse reads
the first row, and both normalized compact Haar measures are transported.
No sphere-coordinate density, Wilson staple identity, or continuum theorem is
assumed or claimed. -/
import UnifiedTheory.Clay.YangMills.SU2QuaternionCoordinates
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.Star.Unitary
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import UnifiedTheory.Clay.YangMills.RegulatedGaugeMeasure
import Mathlib.MeasureTheory.Measure.Haar.Unique

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence
noncomputable section
open Matrix SU2QuaternionCoordinates MeasureTheory RegulatedGauge

abbrev SU2 := Matrix.specialUnitaryGroup (Fin 2) ℂ
abbrev UnitQuaternion := unitary (Quaternion ℝ)

/-- Determinant one and unitarity identify the algebraic adjugate explicitly. -/
theorem adjugate_eq_star (A : SU2) : Matrix.adjugate (A : TwoMatrix) = star (A : TwoMatrix) := by
  have hd : Matrix.det (A : TwoMatrix) = 1 := A.property.2
  calc
    Matrix.adjugate (A : TwoMatrix) = 1 * Matrix.adjugate (A : TwoMatrix) := by simp
    _ = (star (A : TwoMatrix) * A) * Matrix.adjugate (A : TwoMatrix) := by rw [A.property.1.1]
    _ = star (A : TwoMatrix) * ((A : TwoMatrix) * Matrix.adjugate (A : TwoMatrix)) :=
      mul_assoc _ _ _
    _ = star (A : TwoMatrix) := by rw [Matrix.mul_adjugate, hd, one_smul, mul_one]

theorem entry11 (A : SU2) : (A : TwoMatrix) 1 1 = star ((A : TwoMatrix) 0 0) := by
  have h := congrArg (fun M : TwoMatrix => M 0 0) (adjugate_eq_star A)
  simpa [Matrix.adjugate_fin_two, Matrix.star_apply] using h

theorem entry10 (A : SU2) : (A : TwoMatrix) 1 0 = -star ((A : TwoMatrix) 0 1) := by
  have h := congrArg (fun M : TwoMatrix => M 1 0) (adjugate_eq_star A)
  have he : -(A : TwoMatrix) 1 0 = star ((A : TwoMatrix) 0 1) := by
    simpa [Matrix.adjugate_fin_two, Matrix.star_apply] using h
  linear_combination -he

/-- The inverse coordinates are read from the first row, without a choice. -/
def fromMatrix (A : TwoMatrix) : Quaternion ℝ :=
  ⟨(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im⟩

theorem fromMatrix_toMatrix (q : Quaternion ℝ) : fromMatrix (toMatrix q) = q := by
  apply Quaternion.ext <;> simp [fromMatrix, toMatrix]

/-- The determinant-one equations reconstruct the second row as well. -/
theorem toMatrix_fromMatrix (A : SU2) : toMatrix (fromMatrix A) = (A : TwoMatrix) := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> apply Complex.ext <;>
    simp [toMatrix, fromMatrix, entry10, entry11]

theorem fromMatrix_normSq (A : SU2) : Quaternion.normSq (fromMatrix A) = 1 := by
  have hd : Matrix.det (A : TwoMatrix) = 1 := A.property.2
  have h := congrArg Matrix.det (toMatrix_fromMatrix A)
  rw [det_toMatrix, hd] at h
  have hr := congrArg Complex.re h
  simpa using hr

def fromSpecialUnitary (A : SU2) : UnitQuaternion :=
  ⟨fromMatrix A, by
    constructor
    · rw [Quaternion.star_mul_self, fromMatrix_normSq]
      rfl
    · rw [Quaternion.self_mul_star, fromMatrix_normSq]
      rfl⟩

theorem fromSpecialUnitary_left (q : UnitQuaternion) :
    fromSpecialUnitary (unitaryToSpecialUnitary q) = q := by
  apply Subtype.ext
  exact fromMatrix_toMatrix q

theorem fromSpecialUnitary_right (A : SU2) :
    unitaryToSpecialUnitary (fromSpecialUnitary A) = A := by
  apply Subtype.ext
  exact toMatrix_fromMatrix A

/-- Surjectivity is proved from the explicit inverse, not postulated. -/
theorem unitaryToSpecialUnitary_surjective : Function.Surjective unitaryToSpecialUnitary :=
  fun A => ⟨fromSpecialUnitary A, fromSpecialUnitary_right A⟩

theorem fromMatrix_continuous : Continuous fromMatrix := by
  have hc (i j : Fin 2) : Continuous (fun A : TwoMatrix => A i j) :=
    (continuous_apply j).comp (continuous_apply i)
  have hv : Continuous (fun A : TwoMatrix =>
      ![(A 0 0).re, (A 0 0).im, (A 0 1).re, (A 0 1).im]) := by
    apply continuous_pi
    intro i
    fin_cases i
    · exact Complex.continuous_re.comp (hc 0 0)
    · exact Complex.continuous_im.comp (hc 0 0)
    · exact Complex.continuous_re.comp (hc 0 1)
    · exact Complex.continuous_im.comp (hc 0 1)
  exact Quaternion.linearIsometryEquivTuple.symm.continuous.comp
    ((PiLp.continuous_toLp 2 _).comp hv)

theorem fromSpecialUnitary_continuous : Continuous fromSpecialUnitary :=
  (fromMatrix_continuous.comp continuous_subtype_val).subtype_mk
    (fun A => (fromSpecialUnitary A).property)

/-- The actual continuous group isomorphism in both directions. -/
def equivalence : UnitQuaternion ≃ₜ* SU2 where
  toFun := unitaryToSpecialUnitary
  invFun := fromSpecialUnitary
  left_inv := fromSpecialUnitary_left
  right_inv := fromSpecialUnitary_right
  map_mul' := unitaryToSpecialUnitary.map_mul
  continuous_toFun := unitaryToSpecialUnitary_continuous
  continuous_invFun := fromSpecialUnitary_continuous

/-- Compactness follows from the closed unit sphere in four real dimensions. -/
instance quaternionCompactSpace : CompactSpace UnitQuaternion := by
  apply isCompact_iff_compactSpace.mp
  apply (isCompact_closedBall (0 : Quaternion ℝ) 1).of_isClosed_subset isClosed_unitary
  intro q hq
  simp only [Metric.mem_closedBall, dist_zero_right]
  exact (CStarRing.norm_of_mem_unitary hq).le

instance quaternionSecondCountable : SecondCountableTopology UnitQuaternion := by
  infer_instance

instance su2CompactSpace : CompactSpace SU2 := equivalence.toHomeomorph.compactSpace

instance su2SecondCountable : SecondCountableTopology SU2 :=
  equivalence.symm.toHomeomorph.secondCountableTopology

instance su2TopologicalGroup : IsTopologicalGroup SU2 :=
  Topology.IsInducing.topologicalGroup equivalence.symm.toMonoidHom
    equivalence.symm.toHomeomorph.isInducing

instance quaternionMeasurableSpace : MeasurableSpace UnitQuaternion := borel UnitQuaternion
instance quaternionBorelSpace : BorelSpace UnitQuaternion := ⟨rfl⟩
instance su2MeasurableSpace : MeasurableSpace SU2 := borel SU2
instance su2BorelSpace : BorelSpace SU2 := ⟨rfl⟩

def measurableEquivalence : UnitQuaternion ≃ᵐ SU2 := equivalence.toHomeomorph.toMeasurableEquiv

/-- Both measures are the repository's constructed, normalized compact Haar measures. -/
theorem compactHaar_preserving :
    MeasurePreserving measurableEquivalence (compactHaar UnitQuaternion) (compactHaar SU2) := by
  letI : (compactHaar UnitQuaternion).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  letI : (compactHaar SU2).IsHaarMeasure := by
    unfold compactHaar
    infer_instance
  exact MonoidHom.measurePreserving (f := unitaryToSpecialUnitary)
    unitaryToSpecialUnitary_continuous unitaryToSpecialUnitary_surjective (by simp)

theorem compactHaar_preserving_symm :
    MeasurePreserving measurableEquivalence.symm (compactHaar SU2) (compactHaar UnitQuaternion) :=
  compactHaar_preserving.symm

/-- Actual Haar integrals can now be rewritten in quaternion coordinates. -/
theorem compactHaar_integral (f : SU2 → ℝ) :
    (∫ q, f (unitaryToSpecialUnitary q) ∂compactHaar UnitQuaternion) =
      ∫ A, f A ∂compactHaar SU2 :=
  compactHaar_preserving.integral_comp measurableEquivalence.measurableEmbedding f


end
end UnifiedTheory.Clay.YangMills.SU2QuaternionEquivalence

