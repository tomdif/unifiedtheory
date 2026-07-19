/-
  Audit/KFOrientationCPChannelComposition.lean

  DEFECT PROPAGATION THROUGH TWO COARSE-GRAINING SCALES

  A second normalized block isometry compresses the three retained orientation
  chambers to two.  The Schwarz defect of the composed channel obeys the exact
  cocycle law

    D_(Psi o Phi)(A,B) = Psi(D_Phi(A,B)) + D_Psi(Phi(A),Phi(B)).

  The diamond orientation Hamiltonian is lossless at the first block but not at
  the second.  Thus multiplicative-domain membership is scale-relative and need
  not survive a further legitimate unital CP compression.
-/

import UnifiedTheory.Audit.KFOrientationCPChannel
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationCPChannelComposition

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannel
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationSpinOne

abbrev InfraredOrientationMatrix := Matrix (Fin 2) (Fin 2) ℂ
abbrev SecondBlockIsometry := Matrix (Fin 3) (Fin 2) ℂ

/-! ## 1. A second normalized block channel -/

/-- The first two retained chambers are averaged and the third is kept. -/
def secondBlockIsometry : SecondBlockIsometry :=
  !![(1 / spinOneSqrtTwo : ℂ), 0;
     (1 / spinOneSqrtTwo : ℂ), 0;
     0, 1]

theorem secondBlockIsometry_isometry :
    secondBlockIsometryᴴ * secondBlockIsometry =
      (1 : InfraredOrientationMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondBlockIsometry, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff];
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    try rw [spinOneSqrtTwo_sq_complex]
    norm_num

def secondCompression
    (A : CoarseOrientationMatrix) : InfraredOrientationMatrix :=
  secondBlockIsometryᴴ * A * secondBlockIsometry

def HasSecondSingleKrausCPCertificate
    (Psi : CoarseOrientationMatrix → InfraredOrientationMatrix) : Prop :=
  ∃ K : Matrix (Fin 2) (Fin 3) ℂ,
    ∀ A, Psi A = K * A * Kᴴ

theorem secondCompression_hasSingleKrausCPCertificate :
    HasSecondSingleKrausCPCertificate secondCompression := by
  refine ⟨secondBlockIsometryᴴ, ?_⟩
  intro A
  unfold secondCompression
  rw [Matrix.conjTranspose_conjTranspose]

theorem secondCompression_add (A B : CoarseOrientationMatrix) :
    secondCompression (A + B) = secondCompression A + secondCompression B := by
  unfold secondCompression
  rw [Matrix.mul_add, Matrix.add_mul]

theorem secondCompression_sub (A B : CoarseOrientationMatrix) :
    secondCompression (A - B) = secondCompression A - secondCompression B := by
  unfold secondCompression
  rw [Matrix.mul_sub, Matrix.sub_mul]

theorem secondCompression_zero :
    secondCompression (0 : CoarseOrientationMatrix) = 0 := by
  unfold secondCompression
  simp

theorem secondCompression_unital :
    secondCompression (1 : CoarseOrientationMatrix) =
      (1 : InfraredOrientationMatrix) := by
  unfold secondCompression
  rw [Matrix.mul_one, secondBlockIsometry_isometry]

theorem secondCompression_conjTranspose (A : CoarseOrientationMatrix) :
    secondCompression Aᴴ = (secondCompression A)ᴴ := by
  unfold secondCompression
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]

theorem secondCompression_posSemidef
    {A : CoarseOrientationMatrix} (hA : A.PosSemidef) :
    (secondCompression A).PosSemidef := by
  unfold secondCompression
  exact hA.conjTranspose_mul_mul_same secondBlockIsometry

def secondRangeProjection : CoarseOrientationMatrix :=
  secondBlockIsometry * secondBlockIsometryᴴ

def secondComplementProjection : CoarseOrientationMatrix :=
  1 - secondRangeProjection

theorem secondRangeProjection_isHermitian :
    secondRangeProjection.IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self secondBlockIsometry

theorem secondRangeProjection_idempotent :
    secondRangeProjection * secondRangeProjection = secondRangeProjection := by
  unfold secondRangeProjection
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc secondBlockIsometryᴴ,
    secondBlockIsometry_isometry, Matrix.one_mul]

theorem secondComplementProjection_isHermitian :
    secondComplementProjection.IsHermitian := by
  unfold secondComplementProjection Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    secondRangeProjection_isHermitian.eq]

theorem secondComplementProjection_idempotent :
    secondComplementProjection * secondComplementProjection =
      secondComplementProjection := by
  unfold secondComplementProjection
  calc
    (1 - secondRangeProjection) * (1 - secondRangeProjection) =
        1 - secondRangeProjection - secondRangeProjection +
          secondRangeProjection * secondRangeProjection := by
      noncomm_ring
    _ = 1 - secondRangeProjection - secondRangeProjection +
          secondRangeProjection := by
      rw [secondRangeProjection_idempotent]
    _ = 1 - secondRangeProjection := by
      abel

def secondCompressionLeakage
    (A : CoarseOrientationMatrix) : SecondBlockIsometry :=
  secondComplementProjection * A * secondBlockIsometry

/-! ## 2. Exact defect cocycle under composition -/

def secondCompressionDefect
    (A B : CoarseOrientationMatrix) : InfraredOrientationMatrix :=
  secondCompression (Aᴴ * B) -
    (secondCompression A)ᴴ * secondCompression B

theorem secondCompressionDefect_factor
    (A B : CoarseOrientationMatrix) :
    secondCompressionDefect A B =
      (secondCompressionLeakage A)ᴴ * secondCompressionLeakage B := by
  have hdefect :
      secondCompressionDefect A B =
        secondBlockIsometryᴴ * Aᴴ * secondComplementProjection * B *
          secondBlockIsometry := by
    unfold secondCompressionDefect secondCompression
      secondComplementProjection secondRangeProjection
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  symm
  calc
    (secondCompressionLeakage A)ᴴ * secondCompressionLeakage B =
        secondBlockIsometryᴴ * Aᴴ *
          (secondComplementProjection * secondComplementProjection) * B *
            secondBlockIsometry := by
      unfold secondCompressionLeakage
      simp only [Matrix.conjTranspose_mul,
        secondComplementProjection_isHermitian.eq, Matrix.mul_assoc]
    _ = secondBlockIsometryᴴ * Aᴴ *
          secondComplementProjection * B * secondBlockIsometry := by
      rw [secondComplementProjection_idempotent]
    _ = secondCompressionDefect A B := hdefect.symm

theorem secondCompressionDefect_posSemidef (A : CoarseOrientationMatrix) :
    (secondCompressionDefect A A).PosSemidef := by
  rw [secondCompressionDefect_factor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

def composedBlockCompression
    (A : FineOrientationMatrix) : InfraredOrientationMatrix :=
  secondCompression (blockCompression A)

def composedCompressionDefect
    (A B : FineOrientationMatrix) : InfraredOrientationMatrix :=
  composedBlockCompression (Aᴴ * B) -
    (composedBlockCompression A)ᴴ * composedBlockCompression B

/-- Schwarz covariance accumulated by a composition is transported old
covariance plus covariance newly generated at the next scale. -/
theorem composedCompressionDefect_cocycle
    (A B : FineOrientationMatrix) :
    composedCompressionDefect A B =
      secondCompression (compressionDefect A B) +
        secondCompressionDefect (blockCompression A) (blockCompression B) := by
  unfold composedCompressionDefect composedBlockCompression
    secondCompressionDefect compressionDefect
  rw [secondCompression_sub]
  abel

/-! ## 3. Delayed defect generation for the orientation Hamiltonian -/

def orientationSecondStageDefectExact : InfraredOrientationMatrix :=
  !![(2 : ℂ), ((1 - spinOneSqrtTwo : ℝ) : ℂ);
     ((1 - spinOneSqrtTwo : ℝ) : ℂ),
       (((3 - 2 * spinOneSqrtTwo) / 2 : ℝ) : ℂ)]

/-- A single discarded noise amplitude whose Gram square is the complete
second-stage orientation defect. -/
def orientationNoiseAmplitude : Matrix (Fin 1) (Fin 2) ℂ :=
  !![Complex.I * spinOneSqrtTwo,
     Complex.I * ((spinOneSqrtTwo - 2) / 2)]

theorem secondCompressionDefect_orientation_exact :
    secondCompressionDefect
        (blockCompression fineDiamondOrientationHamiltonian)
        (blockCompression fineDiamondOrientationHamiltonian) =
      orientationSecondStageDefectExact := by
  rw [blockCompression_fineDiamondOrientationHamiltonian]
  have hsqrt_ne_complex : (spinOneSqrtTwo : ℂ) ≠ 0 := by
    exact_mod_cast spinOneSqrtTwo_ne_zero
  have hinv :
      (spinOneSqrtTwo : ℂ)⁻¹ = spinOneSqrtTwo / 2 := by
    field_simp [hsqrt_ne_complex]
    exact spinOneSqrtTwo_sq_complex.symm
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [secondCompressionDefect, secondCompression,
      secondBlockIsometry, orientationSecondStageDefectExact,
      skewHamiltonian, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals
    field_simp [hsqrt_ne_complex]
  all_goals
    have hsqrt :
        (spinOneSqrtTwo : ℂ) * spinOneSqrtTwo = 2 := by
      rw [← pow_two, spinOneSqrtTwo_sq_complex]
    try simp only [Complex.I_sq]
    try simp_rw [hinv]
    ring_nf at hsqrt ⊢
  all_goals
    have hsqrt3 :
        (spinOneSqrtTwo : ℂ) ^ 3 =
          2 * (spinOneSqrtTwo : ℂ) := by
      calc
        (spinOneSqrtTwo : ℂ) ^ 3 =
            (spinOneSqrtTwo : ℂ) ^ 2 * spinOneSqrtTwo := by ring
        _ = 2 * (spinOneSqrtTwo : ℂ) := by rw [hsqrt]
    have hsqrt4 : (spinOneSqrtTwo : ℂ) ^ 4 = 4 := by
      calc
        (spinOneSqrtTwo : ℂ) ^ 4 =
            (spinOneSqrtTwo : ℂ) ^ 2 *
              (spinOneSqrtTwo : ℂ) ^ 2 := by ring
        _ = (4 : ℂ) := by rw [hsqrt]; norm_num
    norm_num [Complex.I_sq, hsqrt, hsqrt3, hsqrt4, pow_succ]; ring

theorem orientationSecondStageDefect_singleNoiseGram :
    orientationSecondStageDefectExact =
      orientationNoiseAmplitudeᴴ * orientationNoiseAmplitude := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [orientationSecondStageDefectExact, orientationNoiseAmplitude,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Fin.ext_iff]
  all_goals
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    have hsqrt :
        (spinOneSqrtTwo : ℂ) * spinOneSqrtTwo = 2 := by
      rw [← pow_two, spinOneSqrtTwo_sq_complex]
    try simp only [Complex.I_sq]
    ring_nf at hsqrt ⊢
  all_goals
    norm_num [Complex.I_sq, hsqrt, pow_succ] <;> ring

theorem secondCompressionDefect_orientation_singleNoiseGram :
    secondCompressionDefect
        (blockCompression fineDiamondOrientationHamiltonian)
        (blockCompression fineDiamondOrientationHamiltonian) =
      orientationNoiseAmplitudeᴴ * orientationNoiseAmplitude := by
  rw [secondCompressionDefect_orientation_exact,
    orientationSecondStageDefect_singleNoiseGram]

theorem orientationNoiseAmplitude_ne_zero :
    orientationNoiseAmplitude ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  have hentry :
      orientationNoiseAmplitude 0 0 =
        Complex.I * (spinOneSqrtTwo : ℂ) := by
    norm_num [orientationNoiseAmplitude]
  rw [hentry] at h00
  norm_num at h00
  exact spinOneSqrtTwo_ne_zero h00

/-- The delayed covariance is generated by one nonzero discarded noise row. -/
theorem secondCompressionDefect_orientation_is_singleNoiseMode :
    ∃ R : Matrix (Fin 1) (Fin 2) ℂ,
      R ≠ 0 ∧
        secondCompressionDefect
            (blockCompression fineDiamondOrientationHamiltonian)
            (blockCompression fineDiamondOrientationHamiltonian) = Rᴴ * R := by
  exact ⟨orientationNoiseAmplitude, orientationNoiseAmplitude_ne_zero,
    secondCompressionDefect_orientation_singleNoiseGram⟩

theorem secondCompressionDefect_orientation_apply_zero_zero :
    secondCompressionDefect
        (blockCompression fineDiamondOrientationHamiltonian)
        (blockCompression fineDiamondOrientationHamiltonian) 0 0 = 2 := by
  rw [secondCompressionDefect_orientation_exact]
  norm_num [orientationSecondStageDefectExact]

theorem secondCompressionDefect_orientation_ne_zero :
    secondCompressionDefect
        (blockCompression fineDiamondOrientationHamiltonian)
        (blockCompression fineDiamondOrientationHamiltonian) ≠ 0 := by
  intro h
  have h00 := congrFun (congrFun h 0) 0
  rw [secondCompressionDefect_orientation_apply_zero_zero] at h00
  norm_num at h00

theorem composedOrientationDefect_eq_secondStage :
    composedCompressionDefect fineDiamondOrientationHamiltonian
        fineDiamondOrientationHamiltonian =
      secondCompressionDefect
        (blockCompression fineDiamondOrientationHamiltonian)
        (blockCompression fineDiamondOrientationHamiltonian) := by
  rw [composedCompressionDefect_cocycle,
    fineDiamondOrientationHamiltonian_defect_zero,
    secondCompression_zero, zero_add]

theorem composedOrientationDefect_ne_zero :
    composedCompressionDefect fineDiamondOrientationHamiltonian
      fineDiamondOrientationHamiltonian ≠ 0 := by
  rw [composedOrientationDefect_eq_secondStage]
  exact secondCompressionDefect_orientation_ne_zero

/-- The first normalized channel is multiplicative on the orientation
Hamiltonian, but the composed two-scale channel has nonzero Schwarz defect. -/
theorem multiplicative_domain_not_stable_under_further_compression :
    compressionDefect fineDiamondOrientationHamiltonian
        fineDiamondOrientationHamiltonian = 0
      ∧ composedCompressionDefect fineDiamondOrientationHamiltonian
          fineDiamondOrientationHamiltonian ≠ 0 := by
  exact ⟨fineDiamondOrientationHamiltonian_defect_zero,
    composedOrientationDefect_ne_zero⟩

#print axioms secondBlockIsometry_isometry
#print axioms secondCompression_hasSingleKrausCPCertificate
#print axioms secondCompression_unital
#print axioms secondCompressionDefect_factor
#print axioms composedCompressionDefect_cocycle
#print axioms secondCompressionDefect_orientation_exact
#print axioms secondCompressionDefect_orientation_is_singleNoiseMode
#print axioms secondCompressionDefect_orientation_apply_zero_zero
#print axioms multiplicative_domain_not_stable_under_further_compression

end

end UnifiedTheory.Audit.KFOrientationCPChannelComposition
