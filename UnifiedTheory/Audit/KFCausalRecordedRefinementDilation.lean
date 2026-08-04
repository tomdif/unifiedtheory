/-
  Audit/KFCausalRecordedRefinementDilation.lean

  RECORDED REFINEMENT DILATION OF THE DOUBLE-CONSERVATION LAW

  The preceding double-conservation theorem characterizes the local equations

      sum_e K_e = I,            sum_e K_e^dagger K_e = I.

  This module derives both equations from a deeper finite recorded-refinement
  architecture.

  Stack the birth operators into the canonical recorded dilation

      V : H -> H x Outcome,       V[(i,e),j] = K_e[i,j].

  The first dynamical demand is reversible refinement on the image:

      V^dagger V = I.

  It is equivalent to Born/Kraus completeness.  The second demand uses the
  canonical coherent record counit E that forgets the outcome label by adding
  all record slots:

      E[i,(j,e)] = delta_ij,      E V = I.

  It is equivalent to coherent exhaustivity.  Hence a recorded refinement is
  simultaneously isometric and counital iff its operators obey the causal
  double-conservation law.

  This supplies a finite microscopic realization of the two conservation
  demands and a left inverse for both resolved and unresolved refinement.  It
  does not prove that causal order must provide the record factor, nor does it
  select the operators.  The existing rank-one and harmonic causal-holonomy
  laws instantiate the architecture without further fitted coefficients.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalDoubleConservationLaw
import UnifiedTheory.LayerB.StinespringDilation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalRecordedRefinementDilation

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw
open UnifiedTheory.Audit.KFCausalDoubleConservationLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

/-! ## 1. The canonical coherent record counit -/

/-- Forget a finite record label coherently by adding its carrier slots.  This
is the finite codiagonal/counit on the outcome-indexed record carrier. -/
def coherentRecordCounit (dimension outcomes : ℕ) :
    Matrix (Fin dimension) (Fin dimension × Fin outcomes) ℂ :=
  fun row indexed => if row = indexed.1 then 1 else 0

/-- Multiplying the canonical counit by the stacked recorded refinement gives
the coherent sum of its birth operators. -/
theorem coherentRecordCounit_mul_krausToStinespring
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    coherentRecordCounit dimension outcomes *
        krausToStinespring operator =
      ∑ outcome, operator outcome := by
  ext row column
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  change (∑ carrier : Fin dimension, ∑ outcome : Fin outcomes,
      (if row = carrier then 1 else 0) * operator outcome carrier column) = _
  rw [Finset.sum_eq_single row]
  · simp only [ite_true, one_mul]
    symm
    rw [Finset.sum_apply]
    rw [Finset.sum_apply]
  · intro carrier _ hCarrier
    simp [Ne.symm hCarrier]
  · simp

/-- Counital recovery is exactly coherent operator exhaustivity. -/
theorem coherentRecordRecovery_iff_sum_eq_one
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    coherentRecordCounit dimension outcomes *
          krausToStinespring operator =
        (1 : SquareMatrix dimension) ↔
      ∑ outcome, operator outcome = (1 : SquareMatrix dimension) := by
  rw [coherentRecordCounit_mul_krausToStinespring]

/-! ## 2. Isometric refinement is exactly Born completeness -/

/-- The converse missing from the generic Stinespring API: the canonical
stacked refinement is an isometry only if its birth operators are complete. -/
theorem krausToStinespring_isIsometry_iff_complete
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    IsIsometry (krausToStinespring operator) ↔
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension) := by
  constructor
  · intro hIsometry
    unfold IsIsometry at hIsometry
    ext row column
    rw [Finset.sum_apply]
    rw [Finset.sum_apply]
    calc
      (∑ outcome,
          ((operator outcome)ᴴ * operator outcome) row column) =
          ((krausToStinespring operator)ᴴ *
            krausToStinespring operator) row column :=
        (krausToStinespring_dagger_self_apply
          operator row column).symm
      _ = (1 : SquareMatrix dimension) row column := by
        rw [hIsometry]
  · intro hComplete
    exact krausToStinespring_isIsometry hComplete

/-! ## 3. Recorded causal refinement -/

/-- A finite causal refinement whose resolved record dilation is reversible on
its image and whose unresolved coherent record sum recovers the parent. -/
structure RecordedCausalRefinement (dimension outcomes : ℕ) where
  operator : Fin outcomes → SquareMatrix dimension
  isometric : IsIsometry (krausToStinespring operator)
  counital : coherentRecordCounit dimension outcomes *
      krausToStinespring operator = (1 : SquareMatrix dimension)

/-- A recorded refinement is precisely a realization of the operator
double-conservation equations. -/
theorem recordedRefinement_iff_doubleConservation
    {dimension outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix dimension) :
    (IsIsometry (krausToStinespring operator) ∧
      coherentRecordCounit dimension outcomes *
          krausToStinespring operator = (1 : SquareMatrix dimension)) ↔
    ((∑ outcome, operator outcome) = (1 : SquareMatrix dimension) ∧
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)) := by
  rw [krausToStinespring_isIsometry_iff_complete,
    coherentRecordRecovery_iff_sum_eq_one]
  constructor
  · rintro ⟨hBorn, hCoherent⟩
    exact ⟨hCoherent, hBorn⟩
  · rintro ⟨hCoherent, hBorn⟩
    exact ⟨hBorn, hCoherent⟩

/-- Every projective Born operator law canonically yields an isometric,
counital recorded refinement. -/
def recordedRefinementOfProjectiveBorn
    {dimension outcomes : ℕ}
    (law : ProjectiveBornOperatorLaw dimension outcomes) :
    RecordedCausalRefinement dimension outcomes where
  operator := law.operator
  isometric := krausToStinespring_isIsometry law.bornComplete
  counital := by
    rw [coherentRecordCounit_mul_krausToStinespring,
      law.coherentlyExhaustive]

/-- Conversely, the recorded-refinement structure canonically produces the
double-normalized operator law. -/
def RecordedCausalRefinement.toProjectiveBorn
    {dimension outcomes : ℕ}
    (refinement : RecordedCausalRefinement dimension outcomes) :
    ProjectiveBornOperatorLaw dimension outcomes where
  operator := refinement.operator
  bornComplete :=
    (krausToStinespring_isIsometry_iff_complete
      refinement.operator).1 refinement.isometric
  coherentlyExhaustive :=
    (coherentRecordRecovery_iff_sum_eq_one
      refinement.operator).1 refinement.counital

/-! ## 4. Two exact recovery maps -/

/-- Resolved refinement is reversible on its image: the adjoint of the
recorded dilation recovers every incoming carrier amplitude. -/
theorem RecordedCausalRefinement.adjoint_recovers
    {dimension outcomes : ℕ}
    (refinement : RecordedCausalRefinement dimension outcomes)
    (incoming : SquareMatrix dimension) :
    (krausToStinespring refinement.operator)ᴴ *
        (krausToStinespring refinement.operator * incoming) = incoming := by
  rw [← Matrix.mul_assoc]
  have hIsometry := refinement.isometric
  unfold IsIsometry at hIsometry
  rw [hIsometry, Matrix.one_mul]

/-- Unresolved coherent refinement is also exactly recoverable: first stack
the birth records, then apply the codiagonal record counit. -/
theorem RecordedCausalRefinement.counit_recovers
    {dimension outcomes : ℕ}
    (refinement : RecordedCausalRefinement dimension outcomes)
    (incoming : SquareMatrix dimension) :
    coherentRecordCounit dimension outcomes *
        (krausToStinespring refinement.operator * incoming) = incoming := by
  rw [← Matrix.mul_assoc, refinement.counital, Matrix.one_mul]

/-- The same finite microscopic object therefore supplies both the matched
Born refinement and the exhaustive coherent refinement laws. -/
theorem RecordedCausalRefinement.preserves_both
    {dimension outcomes : ℕ}
    (refinement : RecordedCausalRefinement dimension outcomes) :
    PreservesEveryCoherentCarrier refinement.operator ∧
      PreservesEveryBornCarrier refinement.operator :=
  projectiveBornOperatorLaw_preservesEveryParent
    refinement.toProjectiveBorn

/-! ## 5. The two dynamical demands are independent -/

/-- Embed scalar branch amplitudes as one-dimensional carrier operators. -/
def scalarRecordedOperator {outcomes : ℕ}
    (amplitude : Fin outcomes → ℂ) (outcome : Fin outcomes) :
    SquareMatrix 1 :=
  fun _ _ => amplitude outcome

theorem scalarRecordedOperator_sum_eq_one_iff {outcomes : ℕ}
    (amplitude : Fin outcomes → ℂ) :
    (∑ outcome, scalarRecordedOperator amplitude outcome) =
        (1 : SquareMatrix 1) ↔
      ∑ outcome, amplitude outcome = 1 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h (0 : Fin 1)) (0 : Fin 1)
    rw [Finset.sum_apply] at h00
    rw [Finset.sum_apply] at h00
    simpa [scalarRecordedOperator] using h00
  · intro h
    ext row column
    fin_cases row
    fin_cases column
    rw [Finset.sum_apply]
    rw [Finset.sum_apply]
    simpa [scalarRecordedOperator] using h

theorem scalarRecordedOperator_complete_iff {outcomes : ℕ}
    (amplitude : Fin outcomes → ℂ) :
    (∑ outcome,
        (scalarRecordedOperator amplitude outcome)ᴴ *
          scalarRecordedOperator amplitude outcome) =
        (1 : SquareMatrix 1) ↔
      finiteComplexBornMass amplitude = 1 := by
  constructor
  · intro h
    have h00 := congr_fun (congr_fun h (0 : Fin 1)) (0 : Fin 1)
    rw [Finset.sum_apply] at h00
    rw [Finset.sum_apply] at h00
    simpa [scalarRecordedOperator, Matrix.mul_apply,
      finiteComplexBornMass] using h00
  · intro h
    ext row column
    fin_cases row
    fin_cases column
    rw [Finset.sum_apply]
    rw [Finset.sum_apply]
    simpa [scalarRecordedOperator, Matrix.mul_apply,
      finiteComplexBornMass] using h

/-- Isometric record creation does not imply coherent record recovery. -/
theorem isometric_recording_does_not_imply_counital_recovery :
    ∃ operator : Fin 2 → SquareMatrix 1,
      IsIsometry (krausToStinespring operator) ∧
      coherentRecordCounit 1 2 * krausToStinespring operator ≠
        (1 : SquareMatrix 1) := by
  refine ⟨scalarRecordedOperator bornOnlyBinaryAmplitude, ?_, ?_⟩
  · apply (krausToStinespring_isIsometry_iff_complete _).2
    exact (scalarRecordedOperator_complete_iff _).2
      (by
        rw [← ofReal_finiteComplexBornMass,
          bornOnlyBinaryAmplitude_bornNormalized]
        norm_num)
  · rw [coherentRecordCounit_mul_krausToStinespring]
    intro hCoherent
    exact bornNormalization_does_not_imply_coherentNormalization.2
      ((scalarRecordedOperator_sum_eq_one_iff _).1 hCoherent)

/-- Coherent record recovery does not imply isometric record creation. -/
theorem counital_recovery_does_not_imply_isometric_recording :
    ∃ operator : Fin 2 → SquareMatrix 1,
      coherentRecordCounit 1 2 * krausToStinespring operator =
        (1 : SquareMatrix 1) ∧
      ¬IsIsometry (krausToStinespring operator) := by
  refine ⟨scalarRecordedOperator coherentOnlyBinaryAmplitude, ?_, ?_⟩
  · rw [coherentRecordCounit_mul_krausToStinespring]
    exact (scalarRecordedOperator_sum_eq_one_iff _).2
      coherentOnlyBinaryAmplitude_coherentNormalized
  · intro hIsometric
    have hComplete :=
      (krausToStinespring_isIsometry_iff_complete _).1 hIsometric
    exact coherentNormalization_does_not_imply_bornNormalization.2
      (by
        apply Complex.ofReal_injective
        rw [ofReal_finiteComplexBornMass,
          (scalarRecordedOperator_complete_iff _).1 hComplete]
        norm_num)

/-! ## 6. Existing causal realizations -/

/-- The first two causal births have a canonical recorded dilation with no
additional phase or normalization. -/
def rankOneCausalRecordedRefinement (chirality : Fin 2) :
    RecordedCausalRefinement 3 2 :=
  recordedRefinementOfProjectiveBorn
    (rankOneCausalProjectiveBornLaw chirality)

/-- The corrected six-outcome harmonic causal/holonomy process has the same
recorded-refinement realization. -/
def harmonicCausalRecordedRefinement (chirality : Fin 2) :
    RecordedCausalRefinement 3 6 :=
  recordedRefinementOfProjectiveBorn
    (harmonicCausalProjectiveBornLaw chirality)

theorem rankOneCausalRecordedRefinement_recoveries
    (chirality : Fin 2) (incoming : SquareMatrix 3) :
    ((krausToStinespring
          (rankOneCausalRecordedRefinement chirality).operator)ᴴ *
        (krausToStinespring
          (rankOneCausalRecordedRefinement chirality).operator * incoming) =
        incoming) ∧
    (coherentRecordCounit 3 2 *
        (krausToStinespring
          (rankOneCausalRecordedRefinement chirality).operator * incoming) =
        incoming) := by
  exact ⟨(rankOneCausalRecordedRefinement chirality).adjoint_recovers incoming,
    (rankOneCausalRecordedRefinement chirality).counit_recovers incoming⟩

theorem harmonicCausalRecordedRefinement_recoveries
    (chirality : Fin 2) (incoming : SquareMatrix 3) :
    ((krausToStinespring
          (harmonicCausalRecordedRefinement chirality).operator)ᴴ *
        (krausToStinespring
          (harmonicCausalRecordedRefinement chirality).operator * incoming) =
        incoming) ∧
    (coherentRecordCounit 3 6 *
        (krausToStinespring
          (harmonicCausalRecordedRefinement chirality).operator * incoming) =
        incoming) := by
  exact ⟨(harmonicCausalRecordedRefinement chirality).adjoint_recovers incoming,
    (harmonicCausalRecordedRefinement chirality).counit_recovers incoming⟩

/-! ## 7. Capstone and axiom audit -/

/-- **Recorded-refinement derivation.**  The causal double-conservation law is
equivalent to the conjunction of isometric record creation and exact coherent
record recombination.  Both established causal operator laws realize both
parts of the structure.  The remaining physical bridge is whether causal
growth uniquely supplies this record factor and selects its operators. -/
theorem causalRecordedRefinementDilation_capstone :
    (∀ (dimension outcomes : ℕ)
        (operator : Fin outcomes → SquareMatrix dimension),
      (IsIsometry (krausToStinespring operator) ∧
        coherentRecordCounit dimension outcomes *
            krausToStinespring operator = (1 : SquareMatrix dimension)) ↔
      ((∑ outcome, operator outcome) = (1 : SquareMatrix dimension) ∧
        (∑ outcome, (operator outcome)ᴴ * operator outcome) =
          (1 : SquareMatrix dimension))) ∧
    (∀ chirality : Fin 2,
      IsIsometry (krausToStinespring
          (rankOneCausalRecordedRefinement chirality).operator) ∧
        coherentRecordCounit 3 2 * krausToStinespring
            (rankOneCausalRecordedRefinement chirality).operator =
          (1 : SquareMatrix 3)) ∧
    (∀ chirality : Fin 2,
      IsIsometry (krausToStinespring
          (harmonicCausalRecordedRefinement chirality).operator) ∧
        coherentRecordCounit 3 6 * krausToStinespring
            (harmonicCausalRecordedRefinement chirality).operator =
          (1 : SquareMatrix 3)) := by
  constructor
  · intro dimension outcomes operator
    exact recordedRefinement_iff_doubleConservation operator
  · constructor
    · intro chirality
      exact ⟨(rankOneCausalRecordedRefinement chirality).isometric,
        (rankOneCausalRecordedRefinement chirality).counital⟩
    · intro chirality
      exact ⟨(harmonicCausalRecordedRefinement chirality).isometric,
        (harmonicCausalRecordedRefinement chirality).counital⟩

#print axioms coherentRecordCounit_mul_krausToStinespring
#print axioms coherentRecordRecovery_iff_sum_eq_one
#print axioms krausToStinespring_isIsometry_iff_complete
#print axioms recordedRefinement_iff_doubleConservation
#print axioms RecordedCausalRefinement.adjoint_recovers
#print axioms RecordedCausalRefinement.counit_recovers
#print axioms isometric_recording_does_not_imply_counital_recovery
#print axioms counital_recovery_does_not_imply_isometric_recording
#print axioms rankOneCausalRecordedRefinement_recoveries
#print axioms harmonicCausalRecordedRefinement_recoveries
#print axioms causalRecordedRefinementDilation_capstone

end

end UnifiedTheory.Audit.KFCausalRecordedRefinementDilation
