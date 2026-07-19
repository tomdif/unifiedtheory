/-
  Audit/KFOrientationSpinOneHeisenberg.lean

  EXACT HEISENBERG CENTRALIZER AND TRANSVERSE OSCILLATION

  The adjoint action of a spin-one field Hamiltonian is completely classified
  on the three-dimensional linear observable sector.  Its double commutator is
  the vector triple-product decomposition into a transverse term and a conserved
  field-parallel term.

  For a positive fiber profile, the only commuting linear observable direction
  is the Hamiltonian direction itself.  Every transverse observable obeys the
  exact algebraic harmonic relation L^2 X = -rho^2 X, where L(X)=i[H,X].
  On the full linear sector L^3=-rho^2 L.  This gives the algebraic mechanism
  behind the previously proved recurrent conditional propagator.

  This is a finite conditional Heisenberg model.  It does not select the physical
  Hamiltonian of a causal set, impose constraints, or derive continuum dynamics.
-/

import UnifiedTheory.Audit.KFOrientationSpinOneGram

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationSpinOneHeisenberg

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate
open Matrix
open UnifiedTheory.Audit.KFOrientationRankTwoConsequences
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationQuantumProjectors
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationSpinOneRelational
open UnifiedTheory.Audit.KFOrientationSpinOneGram

/-! ## 1. Linearity and vector triple product -/

def heisenbergGenerator (H X : SpinOneMatrix) : SpinOneMatrix :=
  Complex.I • complexMatrixCommutator H X

theorem complexMatrixCommutator_smul_right
    (A B : SpinOneMatrix) (z : ℂ) :
    complexMatrixCommutator A (z • B) =
      z • complexMatrixCommutator A B := by
  simp [complexMatrixCommutator, smul_sub]

theorem complexMatrixCommutator_add_right
    (A B C : SpinOneMatrix) :
    complexMatrixCommutator A (B + C) =
      complexMatrixCommutator A B + complexMatrixCommutator A C := by
  simp [complexMatrixCommutator, Matrix.mul_add, Matrix.add_mul]
  abel

theorem heisenbergGenerator_smul_right
    (H X : SpinOneMatrix) (z : ℂ) :
    heisenbergGenerator H (z • X) = z • heisenbergGenerator H X := by
  unfold heisenbergGenerator
  rw [complexMatrixCommutator_smul_right, smul_smul, smul_smul]
  congr 1
  ring

theorem heisenbergGenerator_add_right
    (H X Y : SpinOneMatrix) :
    heisenbergGenerator H (X + Y) =
      heisenbergGenerator H X + heisenbergGenerator H Y := by
  unfold heisenbergGenerator
  rw [complexMatrixCommutator_add_right, smul_add]

theorem field_cross_cross_neg_components
    (b1 b2 b3 x1 x2 x3 : ℝ) :
    -fieldCross1 b1 b2 b3
        (fieldCross1 b1 b2 b3 x1 x2 x3)
        (fieldCross2 b1 b2 b3 x1 x2 x3)
        (fieldCross3 b1 b2 b3 x1 x2 x3) =
      fieldNormSq b1 b2 b3 * x1 - fieldDot b1 b2 b3 x1 x2 x3 * b1
    ∧ -fieldCross2 b1 b2 b3
        (fieldCross1 b1 b2 b3 x1 x2 x3)
        (fieldCross2 b1 b2 b3 x1 x2 x3)
        (fieldCross3 b1 b2 b3 x1 x2 x3) =
      fieldNormSq b1 b2 b3 * x2 - fieldDot b1 b2 b3 x1 x2 x3 * b2
    ∧ -fieldCross3 b1 b2 b3
        (fieldCross1 b1 b2 b3 x1 x2 x3)
        (fieldCross2 b1 b2 b3 x1 x2 x3)
        (fieldCross3 b1 b2 b3 x1 x2 x3) =
      fieldNormSq b1 b2 b3 * x3 - fieldDot b1 b2 b3 x1 x2 x3 * b3 := by
  unfold fieldCross1 fieldCross2 fieldCross3 fieldNormSq fieldDot
  constructor
  · ring
  · constructor <;> ring

theorem spinOneFieldHamiltonian_linear_combination
    (r d b1 b2 b3 x1 x2 x3 : ℝ) :
    spinOneFieldHamiltonian
        (r * x1 - d * b1)
        (r * x2 - d * b2)
        (r * x3 - d * b3) =
      (r : ℂ) • spinOneFieldHamiltonian x1 x2 x3 -
        (d : ℂ) • spinOneFieldHamiltonian b1 b2 b3 := by
  unfold spinOneFieldHamiltonian
  push_cast
  module

theorem spinOneFieldHamiltonian_neg (x1 x2 x3 : ℝ) :
    -spinOneFieldHamiltonian x1 x2 x3 =
      spinOneFieldHamiltonian (-x1) (-x2) (-x3) := by
  unfold spinOneFieldHamiltonian
  push_cast
  module

/-! ## 2. Double commutator and Heisenberg closure -/

theorem spinOneField_double_commutator
    (b1 b2 b3 x1 x2 x3 : ℝ) :
    complexMatrixCommutator
        (spinOneFieldHamiltonian b1 b2 b3)
        (complexMatrixCommutator
          (spinOneFieldHamiltonian b1 b2 b3)
          (spinOneFieldHamiltonian x1 x2 x3)) =
      (fieldNormSq b1 b2 b3 : ℂ) •
          spinOneFieldHamiltonian x1 x2 x3 -
        (fieldDot b1 b2 b3 x1 x2 x3 : ℂ) •
          spinOneFieldHamiltonian b1 b2 b3 := by
  rw [spinOneField_commutator, complexMatrixCommutator_smul_right,
    spinOneField_commutator]
  rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  rcases field_cross_cross_neg_components b1 b2 b3 x1 x2 x3 with
    ⟨h1, h2, h3⟩
  rw [spinOneFieldHamiltonian_neg, h1, h2, h3,
    spinOneFieldHamiltonian_linear_combination]

theorem heisenbergGenerator_sq
    (b1 b2 b3 x1 x2 x3 : ℝ) :
    heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
        (heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
          (spinOneFieldHamiltonian x1 x2 x3)) =
      (-fieldNormSq b1 b2 b3 : ℂ) •
          spinOneFieldHamiltonian x1 x2 x3 +
        (fieldDot b1 b2 b3 x1 x2 x3 : ℂ) •
          spinOneFieldHamiltonian b1 b2 b3 := by
  unfold heisenbergGenerator
  rw [complexMatrixCommutator_smul_right, smul_smul,
    Complex.I_mul_I, neg_one_smul, spinOneField_double_commutator]
  module

theorem heisenbergGenerator_sq_of_transverse
    (b1 b2 b3 x1 x2 x3 : ℝ)
    (htrans : fieldDot b1 b2 b3 x1 x2 x3 = 0) :
    heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
        (heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
          (spinOneFieldHamiltonian x1 x2 x3)) =
      (-fieldNormSq b1 b2 b3 : ℂ) •
        spinOneFieldHamiltonian x1 x2 x3 := by
  rw [heisenbergGenerator_sq, htrans]
  norm_num

theorem heisenbergGenerator_self (b1 b2 b3 : ℝ) :
    heisenbergGenerator
        (spinOneFieldHamiltonian b1 b2 b3)
        (spinOneFieldHamiltonian b1 b2 b3) = 0 := by
  simp [heisenbergGenerator, complexMatrixCommutator]

theorem heisenbergGenerator_cubic
    (b1 b2 b3 x1 x2 x3 : ℝ) :
    heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
        (heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
          (heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
            (spinOneFieldHamiltonian x1 x2 x3))) =
      (-fieldNormSq b1 b2 b3 : ℂ) •
        heisenbergGenerator (spinOneFieldHamiltonian b1 b2 b3)
          (spinOneFieldHamiltonian x1 x2 x3) := by
  rw [heisenbergGenerator_sq, heisenbergGenerator_add_right,
    heisenbergGenerator_smul_right, heisenbergGenerator_smul_right,
    heisenbergGenerator_self]
  simp

/-! ## 3. Exact linear centralizer -/

theorem fieldCrossNormSq_eq_zero_iff_parallel_of_first_ne_zero
    (b1 b2 b3 x1 x2 x3 : ℝ) (hb1 : b1 ≠ 0) :
    fieldCrossNormSq b1 b2 b3 x1 x2 x3 = 0 ↔
      ∃ scale : ℝ,
        x1 = scale * b1 ∧ x2 = scale * b2 ∧ x3 = scale * b3 := by
  constructor
  · intro h
    have h1 : fieldCross1 b1 b2 b3 x1 x2 x3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross2 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross3 b1 b2 b3 x1 x2 x3)]
    have h2 : fieldCross2 b1 b2 b3 x1 x2 x3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross2 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross3 b1 b2 b3 x1 x2 x3)]
    have h3 : fieldCross3 b1 b2 b3 x1 x2 x3 = 0 := by
      unfold fieldCrossNormSq at h
      nlinarith [sq_nonneg (fieldCross1 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross2 b1 b2 b3 x1 x2 x3),
        sq_nonneg (fieldCross3 b1 b2 b3 x1 x2 x3)]
    refine ⟨x1 / b1, ?_⟩
    unfold fieldCross1 at h1
    unfold fieldCross2 at h2
    unfold fieldCross3 at h3
    constructor
    · field_simp [hb1]
    · constructor
      · field_simp [hb1]
        nlinarith
      · field_simp [hb1]
        nlinarith
  · rintro ⟨scale, rfl, rfl, rfl⟩
    unfold fieldCrossNormSq fieldCross1 fieldCross2 fieldCross3
    ring

theorem spinOneField_linear_centralizer_of_first_ne_zero
    (b1 b2 b3 x1 x2 x3 : ℝ) (hb1 : b1 ≠ 0) :
    complexMatrixCommutator
        (spinOneFieldHamiltonian b1 b2 b3)
        (spinOneFieldHamiltonian x1 x2 x3) = 0 ↔
      ∃ scale : ℝ,
        x1 = scale * b1 ∧ x2 = scale * b2 ∧ x3 = scale * b3 := by
  rw [spinOneField_commutator_eq_zero_iff_crossNormSq_eq_zero,
    fieldCrossNormSq_eq_zero_iff_parallel_of_first_ne_zero _ _ _ _ _ _ hb1]

theorem effectiveField1_pos
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < effectiveField1 p q r := by
  unfold effectiveField1
  apply mul_pos spinOneSqrtTwo_pos
  have hpQ : (0 : ℚ) < p := by exact_mod_cast hp
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hn : (0 : ℚ) < nativeCoefficient p q r := by
    unfold nativeCoefficient
    positivity
  exact_mod_cast hn

/-! ## 4. Positive-profile conservation law and transverse frequency -/

theorem orientationHamiltonian_linear_centralizer
    (p q r : ℕ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (x1 x2 x3 : ℝ) :
    complexMatrixCommutator
        (orientationHamiltonian p q r)
        (spinOneFieldHamiltonian x1 x2 x3) = 0 ↔
      ∃ scale : ℝ,
        x1 = scale * effectiveField1 p q r
        ∧ x2 = scale * effectiveField2 p q r
        ∧ x3 = scale * effectiveField3 p q r := by
  rw [orientationHamiltonian_eq_spinOneField]
  exact spinOneField_linear_centralizer_of_first_ne_zero _ _ _ _ _ _
    (ne_of_gt (effectiveField1_pos p q r hp hq hr))

theorem effectiveField_normSq_eq_orientationRadiusSq (p q r : ℕ) :
    fieldNormSq
        (effectiveField1 p q r)
        (effectiveField2 p q r)
        (effectiveField3 p q r) =
      orientationRadiusSq p q r := by
  unfold fieldNormSq fieldDot
  simpa only [pow_two] using effectiveField_norm_sq p q r

theorem orientation_heisenbergGenerator_sq_of_transverse
    (p q r : ℕ) (x1 x2 x3 : ℝ)
    (htrans : fieldDot
      (effectiveField1 p q r)
      (effectiveField2 p q r)
      (effectiveField3 p q r) x1 x2 x3 = 0) :
    heisenbergGenerator (orientationHamiltonian p q r)
        (heisenbergGenerator (orientationHamiltonian p q r)
          (spinOneFieldHamiltonian x1 x2 x3)) =
      (-(orientationRadius p q r ^ 2) : ℂ) •
        spinOneFieldHamiltonian x1 x2 x3 := by
  rw [orientationHamiltonian_eq_spinOneField,
    heisenbergGenerator_sq_of_transverse _ _ _ _ _ _ htrans,
    effectiveField_normSq_eq_orientationRadiusSq,
    ← orientationRadius_sq]
  push_cast
  rfl

theorem orientation_heisenbergGenerator_cubic
    (p q r : ℕ) (x1 x2 x3 : ℝ) :
    heisenbergGenerator (orientationHamiltonian p q r)
        (heisenbergGenerator (orientationHamiltonian p q r)
          (heisenbergGenerator (orientationHamiltonian p q r)
            (spinOneFieldHamiltonian x1 x2 x3))) =
      (-(orientationRadius p q r ^ 2) : ℂ) •
        heisenbergGenerator (orientationHamiltonian p q r)
          (spinOneFieldHamiltonian x1 x2 x3) := by
  rw [orientationHamiltonian_eq_spinOneField,
    heisenbergGenerator_cubic,
    effectiveField_normSq_eq_orientationRadiusSq,
    ← orientationRadius_sq]
  push_cast
  rfl

#print axioms field_cross_cross_neg_components
#print axioms spinOneField_double_commutator
#print axioms heisenbergGenerator_sq
#print axioms heisenbergGenerator_sq_of_transverse
#print axioms heisenbergGenerator_cubic
#print axioms spinOneField_linear_centralizer_of_first_ne_zero
#print axioms orientationHamiltonian_linear_centralizer
#print axioms orientation_heisenbergGenerator_sq_of_transverse
#print axioms orientation_heisenbergGenerator_cubic

end

end UnifiedTheory.Audit.KFOrientationSpinOneHeisenberg
