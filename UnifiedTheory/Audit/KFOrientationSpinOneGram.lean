/-
  Audit/KFOrientationSpinOneGram.lean

  LENGTH, AREA, VOLUME, AND THE EXACT Z2 ORIENTATION AMBIGUITY

  The relational spin-one observables form an exact metric hierarchy.  A single
  Hamiltonian trace measures effective-field length.  The squared trace of a
  commutator is minus twice the squared cross-product area.  The cubic chirality
  is twice i times oriented volume.

  The square of the scalar triple product equals the determinant of the pairwise
  Gram matrix.  Consequently, complete pairwise trace data already determine the
  magnitude of cubic chirality, but only up to sign.  The missing information is
  exactly a Z2 choice of orientation for nondegenerate triples, rather than an
  additional continuous degree of freedom.

  These are finite matrix identities.  They do not establish a continuum metric,
  area or volume operator, quantum geometry dynamics, or physical parity sector.
-/

import UnifiedTheory.Audit.KFOrientationSpinOneRelational

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationSpinOneGram

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationSpinOneRelational

/-! ## 1. Effective-field metric invariants -/

def fieldNormSq (a1 a2 a3 : ℝ) : ℝ :=
  fieldDot a1 a2 a3 a1 a2 a3

def fieldCrossNormSq (a1 a2 a3 b1 b2 b3 : ℝ) : ℝ :=
  fieldCross1 a1 a2 a3 b1 b2 b3 ^ 2 +
    fieldCross2 a1 a2 a3 b1 b2 b3 ^ 2 +
      fieldCross3 a1 a2 a3 b1 b2 b3 ^ 2

def fieldGramDet
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) : ℝ :=
  fieldNormSq a1 a2 a3 * fieldNormSq b1 b2 b3 * fieldNormSq c1 c2 c3 +
    2 * fieldDot a1 a2 a3 b1 b2 b3 *
      fieldDot b1 b2 b3 c1 c2 c3 * fieldDot c1 c2 c3 a1 a2 a3 -
    fieldNormSq a1 a2 a3 * fieldDot b1 b2 b3 c1 c2 c3 ^ 2 -
    fieldNormSq b1 b2 b3 * fieldDot c1 c2 c3 a1 a2 a3 ^ 2 -
    fieldNormSq c1 c2 c3 * fieldDot a1 a2 a3 b1 b2 b3 ^ 2

theorem fieldCrossNormSq_lagrange
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    fieldCrossNormSq a1 a2 a3 b1 b2 b3 =
      fieldNormSq a1 a2 a3 * fieldNormSq b1 b2 b3 -
        fieldDot a1 a2 a3 b1 b2 b3 ^ 2 := by
  unfold fieldCrossNormSq fieldNormSq fieldDot
    fieldCross1 fieldCross2 fieldCross3
  ring

theorem fieldTriple_sq_eq_gramDet
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    fieldTriple a1 a2 a3 b1 b2 b3 c1 c2 c3 ^ 2 =
      fieldGramDet a1 a2 a3 b1 b2 b3 c1 c2 c3 := by
  unfold fieldTriple fieldGramDet fieldNormSq fieldDot
    fieldCross1 fieldCross2 fieldCross3
  ring

theorem fieldGramDet_nonneg
    (a1 a2 a3 b1 b2 b3 c1 c2 c3 : ℝ) :
    0 ≤ fieldGramDet a1 a2 a3 b1 b2 b3 c1 c2 c3 := by
  rw [← fieldTriple_sq_eq_gramDet]
  positivity

/-! ## 2. Quantum commutator area -/

theorem spinOneField_trace_commutator_sq
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    Matrix.trace
        (complexMatrixCommutator
            (spinOneFieldHamiltonian a1 a2 a3)
            (spinOneFieldHamiltonian b1 b2 b3) *
          complexMatrixCommutator
            (spinOneFieldHamiltonian a1 a2 a3)
            (spinOneFieldHamiltonian b1 b2 b3)) =
      ((-2 * fieldCrossNormSq a1 a2 a3 b1 b2 b3 : ℝ) : ℂ) := by
  rw [spinOneField_commutator]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    Matrix.trace_smul]
  rw [spinOneField_trace_product]
  unfold fieldCrossNormSq fieldDot
  push_cast
  rw [Complex.I_mul_I]
  simp only [neg_smul, one_smul]
  ring

theorem spinOneField_commutator_eq_zero_iff_crossNormSq_eq_zero
    (a1 a2 a3 b1 b2 b3 : ℝ) :
    complexMatrixCommutator
        (spinOneFieldHamiltonian a1 a2 a3)
        (spinOneFieldHamiltonian b1 b2 b3) = 0 ↔
      fieldCrossNormSq a1 a2 a3 b1 b2 b3 = 0 := by
  constructor
  · intro h
    have htrace :
        Matrix.trace
            (complexMatrixCommutator
                (spinOneFieldHamiltonian a1 a2 a3)
                (spinOneFieldHamiltonian b1 b2 b3) *
              complexMatrixCommutator
                (spinOneFieldHamiltonian a1 a2 a3)
                (spinOneFieldHamiltonian b1 b2 b3)) = 0 := by
      rw [h]
      simp
    rw [spinOneField_trace_commutator_sq] at htrace
    have hr : -2 * fieldCrossNormSq a1 a2 a3 b1 b2 b3 = 0 := by
      exact_mod_cast htrace
    linarith
  · intro h
    have h1 : fieldCross1 a1 a2 a3 b1 b2 b3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross2 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross3 a1 a2 a3 b1 b2 b3)]
    have h2 : fieldCross2 a1 a2 a3 b1 b2 b3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross2 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross3 a1 a2 a3 b1 b2 b3)]
    have h3 : fieldCross3 a1 a2 a3 b1 b2 b3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross2 a1 a2 a3 b1 b2 b3),
        sq_nonneg (fieldCross3 a1 a2 a3 b1 b2 b3)]
    rw [spinOneField_commutator, h1, h2, h3]
    simp [spinOneFieldHamiltonian]

/-! ## 3. Pairwise Gram data leave only a sign -/

theorem fieldTriple_eq_or_eq_neg_of_pairwiseDot_eq
    (a1 a2 a3 b1 b2 b3 c1 c2 c3
      d1 d2 d3 e1 e2 e3 f1 f2 f3 : ℝ)
    (hAA : fieldDot a1 a2 a3 a1 a2 a3 = fieldDot d1 d2 d3 d1 d2 d3)
    (hBB : fieldDot b1 b2 b3 b1 b2 b3 = fieldDot e1 e2 e3 e1 e2 e3)
    (hCC : fieldDot c1 c2 c3 c1 c2 c3 = fieldDot f1 f2 f3 f1 f2 f3)
    (hAB : fieldDot a1 a2 a3 b1 b2 b3 = fieldDot d1 d2 d3 e1 e2 e3)
    (hBC : fieldDot b1 b2 b3 c1 c2 c3 = fieldDot e1 e2 e3 f1 f2 f3)
    (hCA : fieldDot c1 c2 c3 a1 a2 a3 = fieldDot f1 f2 f3 d1 d2 d3) :
    fieldTriple a1 a2 a3 b1 b2 b3 c1 c2 c3 =
        fieldTriple d1 d2 d3 e1 e2 e3 f1 f2 f3
    ∨ fieldTriple a1 a2 a3 b1 b2 b3 c1 c2 c3 =
        -fieldTriple d1 d2 d3 e1 e2 e3 f1 f2 f3 := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [fieldTriple_sq_eq_gramDet, fieldTriple_sq_eq_gramDet]
  unfold fieldGramDet fieldNormSq
  rw [hAA, hBB, hCC, hAB, hBC, hCA]

/-! ## 4. Profile Gram determinant and chirality square -/

def orientationGramDet
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) : ℝ :=
  fieldGramDet
    (effectiveField1 p1 q1 r1)
    (effectiveField2 p1 q1 r1)
    (effectiveField3 p1 q1 r1)
    (effectiveField1 p2 q2 r2)
    (effectiveField2 p2 q2 r2)
    (effectiveField3 p2 q2 r2)
    (effectiveField1 p3 q3 r3)
    (effectiveField2 p3 q3 r3)
    (effectiveField3 p3 q3 r3)

theorem orientationGramDet_nonneg
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    0 ≤ orientationGramDet p1 q1 r1 p2 q2 r2 p3 q3 r3 := by
  unfold orientationGramDet
  exact fieldGramDet_nonneg _ _ _ _ _ _ _ _ _

theorem orientationChirality_sq_eq_neg_four_mul_gramDet
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 ^ 2 =
      (-4 : ℂ) *
        (orientationGramDet p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℂ) := by
  rw [orientationChirality_formula]
  unfold orientationGramDet
  rw [← fieldTriple_sq_eq_gramDet]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem orientationChirality_eq_or_eq_neg_of_gramDet_eq
    (p1 q1 r1 p2 q2 r2 p3 q3 r3
      p1' q1' r1' p2' q2' r2' p3' q3' r3' : ℕ)
    (hGram :
      orientationGramDet p1 q1 r1 p2 q2 r2 p3 q3 r3 =
        orientationGramDet p1' q1' r1' p2' q2' r2' p3' q3' r3') :
    orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 =
        orientationChirality p1' q1' r1' p2' q2' r2' p3' q3' r3'
    ∨ orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3 =
        -orientationChirality p1' q1' r1' p2' q2' r2' p3' q3' r3' := by
  apply eq_or_eq_neg_of_sq_eq_sq
  rw [orientationChirality_sq_eq_neg_four_mul_gramDet,
    orientationChirality_sq_eq_neg_four_mul_gramDet, hGram]

theorem orientationGramDet_simultaneous_reflection
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    orientationGramDet r1 q1 p1 r2 q2 p2 r3 q3 p3 =
      orientationGramDet p1 q1 r1 p2 q2 r2 p3 q3 r3 := by
  unfold orientationGramDet fieldGramDet fieldNormSq
  rcases effectiveField_outer_reflection p1 q1 r1 with ⟨h11, h12, h13⟩
  rcases effectiveField_outer_reflection p2 q2 r2 with ⟨h21, h22, h23⟩
  rcases effectiveField_outer_reflection p3 q3 r3 with ⟨h31, h32, h33⟩
  rw [h11, h12, h13, h21, h22, h23, h31, h32, h33]
  unfold fieldDot
  ring

/-! ## 5. Uniform degeneracy and exact witnesses -/

theorem uniform_orientationGramDet_zero (s t u : ℕ) :
    orientationGramDet s s s t t t u u u = 0 := by
  unfold orientationGramDet
  rw [← fieldTriple_sq_eq_gramDet]
  rcases uniform_effectiveField s with ⟨_, _, hs⟩
  rcases uniform_effectiveField t with ⟨_, _, ht⟩
  rcases uniform_effectiveField u with ⟨_, _, hu⟩
  rw [hs, ht, hu]
  unfold fieldTriple fieldCross1 fieldCross2 fieldCross3
  ring

theorem profile_gramDet_witness :
    orientationGramDet 1 1 1 2 2 2 2 1 1 = 16 := by
  unfold orientationGramDet
  rw [← fieldTriple_sq_eq_gramDet, profile_chirality_witness_fieldTriple]
  norm_num

theorem profile_commutator_area_witness :
    fieldCrossNormSq
        (effectiveField1 1 1 1)
        (effectiveField2 1 1 1)
        (effectiveField3 1 1 1)
        (effectiveField1 2 2 2)
        (effectiveField2 2 2 2)
        (effectiveField3 2 2 2) = 32 := by
  unfold fieldCrossNormSq fieldCross1 fieldCross2 fieldCross3
    effectiveField1 effectiveField2 effectiveField3
    nativeCoefficient longCoefficient imbalanceCoefficient
  norm_num
  nlinarith [spinOneSqrtTwo_sq]

theorem profile_commutator_trace_sq_witness :
    Matrix.trace
        (complexMatrixCommutator
            (orientationHamiltonian 1 1 1)
            (orientationHamiltonian 2 2 2) *
          complexMatrixCommutator
            (orientationHamiltonian 1 1 1)
            (orientationHamiltonian 2 2 2)) = -64 := by
  rw [orientationHamiltonian_eq_spinOneField,
    orientationHamiltonian_eq_spinOneField,
    spinOneField_trace_commutator_sq,
    profile_commutator_area_witness]
  norm_num

theorem profile_chirality_sq_witness :
    orientationChirality 1 1 1 2 2 2 2 1 1 ^ 2 = -64 := by
  rw [orientationChirality_sq_eq_neg_four_mul_gramDet,
    profile_gramDet_witness]
  norm_num

#print axioms fieldCrossNormSq_lagrange
#print axioms fieldTriple_sq_eq_gramDet
#print axioms spinOneField_trace_commutator_sq
#print axioms spinOneField_commutator_eq_zero_iff_crossNormSq_eq_zero
#print axioms fieldTriple_eq_or_eq_neg_of_pairwiseDot_eq
#print axioms orientationChirality_sq_eq_neg_four_mul_gramDet
#print axioms orientationChirality_eq_or_eq_neg_of_gramDet_eq
#print axioms orientationGramDet_simultaneous_reflection
#print axioms uniform_orientationGramDet_zero
#print axioms profile_commutator_trace_sq_witness
#print axioms profile_chirality_sq_witness

end

end UnifiedTheory.Audit.KFOrientationSpinOneGram
