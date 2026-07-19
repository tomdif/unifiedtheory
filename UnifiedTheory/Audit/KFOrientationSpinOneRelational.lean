/-
  Audit/KFOrientationSpinOneRelational.lean

  RELATIONAL GEOMETRY AND A CUBIC ORIENTATION OBSERVABLE

  The spin-one effective-field description admits an exact hierarchy of
  basis-independent matrix observables.  A trace of two Hamiltonians is twice
  the Euclidean dot product of their effective fields.  A Hamiltonian traced
  against the commutator of two others is twice i times their scalar triple
  product.

  Simultaneous outer-fiber reflection preserves every pairwise trace overlap
  but reverses the cubic trace.  Thus spectra and pairwise Gram data remain
  orientation-blind, while a three-operator pseudoscalar detects handedness.
  An explicit profile triple has cubic value 8i and reflected value -8i.
  Every triple of uniform profiles has zero chirality.

  These are exact finite relational observables.  They do not yet define a
  quantum measure, a continuum volume form, or physical parity violation.
-/

import UnifiedTheory.Audit.KFOrientationSpinOne

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationSpinOneRelational

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationQuantumProjectors
open UnifiedTheory.Audit.KFOrientationSpinOne

/-! ## 1. Effective-field vector algebra -/

def spinOneFieldHamiltonian (x y z : ℝ) : SpinOneMatrix :=
  (x : ℂ) • spinOneJ1 + (y : ℂ) • spinOneJ2 + (z : ℂ) • spinOneJ3

def fieldDot
    (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  a1 * b1 + a2 * b2 + a3 * b3

def fieldCross1 (_a1 a2 a3 _b1 b2 b3 : ℝ) : ℝ :=
  a2 * b3 - a3 * b2

def fieldCross2 (a1 _a2 a3 b1 _b2 b3 : ℝ) : ℝ :=
  a3 * b1 - a1 * b3

def fieldCross3 (a1 a2 _a3 b1 b2 _b3 : ℝ) : ℝ :=
  a1 * b2 - a2 * b1

def fieldTriple
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) : ℝ :=
  a1 * fieldCross1 b1 b2 b3 c1 c2 c3 +
    a2 * fieldCross2 b1 b2 b3 c1 c2 c3 +
      a3 * fieldCross3 b1 b2 b3 c1 c2 c3

/-! ## 2. Trace geometry of the spin-one sector -/

theorem spinOneField_trace_product
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    Matrix.trace
        (spinOneFieldHamiltonian a1 a2 a3 *
          spinOneFieldHamiltonian b1 b2 b3) =
      ((2 * fieldDot a1 a2 a3 b1 b2 b3 : ℝ) : ℂ) := by
  norm_num [spinOneFieldHamiltonian, fieldDot, spinOneJ1, spinOneJ2,
    spinOneJ3, skewHamiltonian, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_three, Fin.ext_iff]
  field_simp [spinOneSqrtTwo_ne_zero]
  ring_nf
  simp [spinOneSqrtTwo_sq_complex]
  ring

theorem spinOneField_commutator
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    complexMatrixCommutator
        (spinOneFieldHamiltonian a1 a2 a3)
        (spinOneFieldHamiltonian b1 b2 b3) =
      Complex.I •
        spinOneFieldHamiltonian
          (fieldCross1 a1 a2 a3 b1 b2 b3)
          (fieldCross2 a1 a2 a3 b1 b2 b3)
          (fieldCross3 a1 a2 a3 b1 b2 b3) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [complexMatrixCommutator, spinOneFieldHamiltonian,
      fieldCross1, fieldCross2, fieldCross3, spinOneJ1, spinOneJ2,
      spinOneJ3, skewHamiltonian, Matrix.mul_apply, Fin.sum_univ_three,
      Fin.ext_iff] <;>
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    try simp [Complex.I_sq, spinOneSqrtTwo_sq_complex]
    ring

theorem spinOneField_trace_commutator
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    Matrix.trace
        (spinOneFieldHamiltonian a1 a2 a3 *
          complexMatrixCommutator
            (spinOneFieldHamiltonian b1 b2 b3)
            (spinOneFieldHamiltonian c1 c2 c3)) =
      (2 * Complex.I) *
        (fieldTriple a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℂ) := by
  rw [spinOneField_commutator]
  simp only [Matrix.mul_smul, Matrix.trace_smul]
  rw [spinOneField_trace_product]
  unfold fieldTriple fieldDot
  push_cast
  simp only [smul_eq_mul]
  ring

/-! ## 3. Relational observables for fiber profiles -/

theorem fieldDot_reflection
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    fieldDot a1 a2 (-a3) b1 b2 (-b3) =
      fieldDot a1 a2 a3 b1 b2 b3 := by
  unfold fieldDot
  ring

theorem fieldTriple_reflection
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    fieldTriple a1 a2 (-a3) b1 b2 (-b3) c1 c2 (-c3) =
      -fieldTriple a1 a2 a3 b1 b2 b3 c1 c2 c3 := by
  unfold fieldTriple fieldCross1 fieldCross2 fieldCross3
  ring

theorem orientationHamiltonian_eq_spinOneField (p q r : ℕ) :
    orientationHamiltonian p q r =
      spinOneFieldHamiltonian
        (effectiveField1 p q r)
        (effectiveField2 p q r)
        (effectiveField3 p q r) := by
  exact orientationHamiltonian_spinOne_effectiveField p q r

def orientationPairOverlap
    (p q r p' q' r' : ℕ) : ℂ :=
  Matrix.trace
    (orientationHamiltonian p q r * orientationHamiltonian p' q' r')

theorem orientationPairOverlap_formula
    (p q r p' q' r' : ℕ) :
    orientationPairOverlap p q r p' q' r' =
      ((2 * fieldDot
        (effectiveField1 p q r)
        (effectiveField2 p q r)
        (effectiveField3 p q r)
        (effectiveField1 p' q' r')
        (effectiveField2 p' q' r')
        (effectiveField3 p' q' r') : ℝ) : ℂ) := by
  unfold orientationPairOverlap
  rw [orientationHamiltonian_eq_spinOneField,
    orientationHamiltonian_eq_spinOneField]
  exact spinOneField_trace_product _ _ _ _ _ _

theorem orientationPairOverlap_simultaneous_reflection
    (p q r p' q' r' : ℕ) :
    orientationPairOverlap r q p r' q' p' =
      orientationPairOverlap p q r p' q' r' := by
  rw [orientationPairOverlap_formula, orientationPairOverlap_formula]
  rcases effectiveField_outer_reflection p q r with ⟨h1, h2, h3⟩
  rcases effectiveField_outer_reflection p' q' r' with ⟨h1', h2', h3'⟩
  rw [h1, h2, h3, h1', h2', h3']
  rw [fieldDot_reflection]

def orientationChirality
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) : ℂ :=
  Matrix.trace
    (orientationHamiltonian p1 q1 r1 *
      complexMatrixCommutator
        (orientationHamiltonian p2 q2 r2)
        (orientationHamiltonian p3 q3 r3))

theorem orientationChirality_formula
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 =
      (2 * Complex.I) *
        (fieldTriple
          (effectiveField1 p1 q1 r1)
          (effectiveField2 p1 q1 r1)
          (effectiveField3 p1 q1 r1)
          (effectiveField1 p2 q2 r2)
          (effectiveField2 p2 q2 r2)
          (effectiveField3 p2 q2 r2)
          (effectiveField1 p3 q3 r3)
          (effectiveField2 p3 q3 r3)
          (effectiveField3 p3 q3 r3) : ℂ) := by
  unfold orientationChirality
  rw [orientationHamiltonian_eq_spinOneField,
    orientationHamiltonian_eq_spinOneField,
    orientationHamiltonian_eq_spinOneField]
  exact spinOneField_trace_commutator _ _ _ _ _ _ _ _ _

/-! ## 4. Channel volume and reflection parity -/

def orientationChannelVolume
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) : ℝ :=
  fieldTriple
    (nativeCoefficient p1 q1 r1 : ℝ)
    (longCoefficient p1 q1 r1 : ℝ)
    (imbalanceCoefficient p1 q1 r1 : ℝ)
    (nativeCoefficient p2 q2 r2 : ℝ)
    (longCoefficient p2 q2 r2 : ℝ)
    (imbalanceCoefficient p2 q2 r2 : ℝ)
    (nativeCoefficient p3 q3 r3 : ℝ)
    (longCoefficient p3 q3 r3 : ℝ)
    (imbalanceCoefficient p3 q3 r3 : ℝ)

theorem effectiveField_triple_eq_two_mul_channelVolume
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    fieldTriple
        (effectiveField1 p1 q1 r1)
        (effectiveField2 p1 q1 r1)
        (effectiveField3 p1 q1 r1)
        (effectiveField1 p2 q2 r2)
        (effectiveField2 p2 q2 r2)
        (effectiveField3 p2 q2 r2)
        (effectiveField1 p3 q3 r3)
        (effectiveField2 p3 q3 r3)
        (effectiveField3 p3 q3 r3) =
      2 * orientationChannelVolume
        p1 q1 r1 p2 q2 r2 p3 q3 r3 := by
  unfold effectiveField1 effectiveField2 effectiveField3
    orientationChannelVolume fieldTriple fieldCross1 fieldCross2 fieldCross3
  ring_nf
  rw [spinOneSqrtTwo_sq]
  ring

theorem orientationChirality_channelVolume_formula
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 =
      (4 * Complex.I) *
        (orientationChannelVolume p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℂ) := by
  rw [orientationChirality_formula,
    effectiveField_triple_eq_two_mul_channelVolume]
  push_cast
  ring

theorem orientationChirality_simultaneous_reflection
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    orientationChirality r1 q1 p1 r2 q2 p2 r3 q3 p3 =
      -orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 := by
  rw [orientationChirality_formula, orientationChirality_formula]
  rcases effectiveField_outer_reflection p1 q1 r1 with ⟨h11, h12, h13⟩
  rcases effectiveField_outer_reflection p2 q2 r2 with ⟨h21, h22, h23⟩
  rcases effectiveField_outer_reflection p3 q3 r3 with ⟨h31, h32, h33⟩
  rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  rw [fieldTriple_reflection]
  push_cast
  ring

/-! ## 5. Uniform no-go and an asymmetric chirality witness -/

theorem uniform_orientationChirality_zero (s t u : ℕ) :
    orientationChirality s s s t t t u u u = 0 := by
  rw [orientationChirality_formula]
  rcases uniform_effectiveField s with ⟨_, _, hs⟩
  rcases uniform_effectiveField t with ⟨_, _, ht⟩
  rcases uniform_effectiveField u with ⟨_, _, hu⟩
  rw [hs, ht, hu]
  unfold fieldTriple fieldCross1 fieldCross2 fieldCross3
  push_cast
  ring

theorem profile_chirality_witness_fieldTriple :
    fieldTriple
      (effectiveField1 1 1 1) (effectiveField2 1 1 1) (effectiveField3 1 1 1)
      (effectiveField1 2 2 2) (effectiveField2 2 2 2) (effectiveField3 2 2 2)
      (effectiveField1 2 1 1) (effectiveField2 2 1 1) (effectiveField3 2 1 1) =
        4 := by
  unfold effectiveField1 effectiveField2 effectiveField3
    nativeCoefficient longCoefficient imbalanceCoefficient
    fieldTriple fieldCross1 fieldCross2 fieldCross3
  norm_num
  nlinarith [spinOneSqrtTwo_sq]

theorem profile_chirality_witness :
    orientationChirality 1 1 1 2 2 2 2 1 1 = 8 * Complex.I := by
  rw [orientationChirality_formula, profile_chirality_witness_fieldTriple]
  change 2 * Complex.I * (4 : ℂ) = (8 : ℂ) * Complex.I
  ring

theorem reflected_profile_chirality_witness :
    orientationChirality 1 1 1 2 2 2 1 1 2 = -(8 * Complex.I) := by
  rw [orientationChirality_simultaneous_reflection]
  exact congrArg Neg.neg profile_chirality_witness

theorem profile_chirality_witness_ne_reflection :
    orientationChirality 1 1 1 2 2 2 2 1 1 ≠
      orientationChirality 1 1 1 2 2 2 1 1 2 := by
  rw [profile_chirality_witness, reflected_profile_chirality_witness]
  intro h
  have him := congrArg Complex.im h
  norm_num at him

def WitnessPairwiseOverlapsReflectionInvariant : Prop :=
    orientationPairOverlap 1 1 1 1 1 1 =
        orientationPairOverlap 1 1 1 1 1 1
    ∧ orientationPairOverlap 2 2 2 2 2 2 =
        orientationPairOverlap 2 2 2 2 2 2
    ∧ orientationPairOverlap 1 1 2 1 1 2 =
        orientationPairOverlap 2 1 1 2 1 1
    ∧ orientationPairOverlap 1 1 1 2 2 2 =
        orientationPairOverlap 1 1 1 2 2 2
    ∧ orientationPairOverlap 1 1 1 1 1 2 =
        orientationPairOverlap 1 1 1 2 1 1
    ∧ orientationPairOverlap 2 2 2 1 1 2 =
        orientationPairOverlap 2 2 2 2 1 1

theorem witness_pairwise_overlaps_reflection_invariant :
    WitnessPairwiseOverlapsReflectionInvariant := by
  unfold WitnessPairwiseOverlapsReflectionInvariant
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · exact orientationPairOverlap_simultaneous_reflection 2 1 1 2 1 1
      · constructor
        · rfl
        · constructor
          · exact orientationPairOverlap_simultaneous_reflection 1 1 1 2 1 1
          · exact orientationPairOverlap_simultaneous_reflection 2 2 2 2 1 1

theorem pairwise_data_blind_but_cubic_chirality_detects :
    WitnessPairwiseOverlapsReflectionInvariant
    ∧ orientationChirality 1 1 1 2 2 2 2 1 1 ≠
        orientationChirality 1 1 1 2 2 2 1 1 2 :=
  ⟨witness_pairwise_overlaps_reflection_invariant,
    profile_chirality_witness_ne_reflection⟩

#print axioms spinOneField_trace_product
#print axioms spinOneField_commutator
#print axioms spinOneField_trace_commutator
#print axioms orientationPairOverlap_formula
#print axioms orientationPairOverlap_simultaneous_reflection
#print axioms orientationChirality_channelVolume_formula
#print axioms orientationChirality_simultaneous_reflection
#print axioms uniform_orientationChirality_zero
#print axioms profile_chirality_witness
#print axioms pairwise_data_blind_but_cubic_chirality_detects

end

end UnifiedTheory.Audit.KFOrientationSpinOneRelational
