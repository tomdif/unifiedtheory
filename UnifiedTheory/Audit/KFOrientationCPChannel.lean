/-
  Audit/KFOrientationCPChannel.lean

  A UNITAL CP BLOCK CHANNEL AND ITS MULTIPLICATIVE DEFECT

  The diamond-to-chain chamber quotient admits a per-fiber normalized incidence
  isometry V.  Compression Phi(A)=V^* A V is therefore unital and has an exact
  one-Kraus completely-positive certificate.  Its Schwarz defect factors as

      D(A,B) = leakage(A)^* leakage(B),

  making the operator-valued covariance kernel and its multiplicative-domain
  boundary explicit.

  The certified orientation Hamiltonian is a sharp boundary case: its leakage
  and Schwarz defect vanish, although its compressed image contains the
  long-range channel omitted by the independently recomputed coarse ansatz.
  A coupling to the collapsed chamber has zero retained image but a nonzero
  defect, giving a concrete discarded-covariance witness.

  These are finite matrix-channel statements.  They do not define an iterated
  RG channel, a continuum environment, or a physical causal-set state.
-/

import UnifiedTheory.Audit.KFOrientationDynamicsCoarseGraining
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Analysis.Complex.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationCPChannel

noncomputable section

open scoped BigOperators Polynomial ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFMultirankCoarseGraining
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationDynamicsCoarseGraining
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationSpinOneRelational

abbrev FineOrientationMatrix := Matrix (Fin 6) (Fin 6) ℂ
abbrev CoarseOrientationMatrix := Matrix (Fin 3) (Fin 3) ℂ
abbrev BlockIsometry := Matrix (Fin 6) (Fin 3) ℂ

/-! ## 1. Per-fiber normalized block isometry -/

/-- Columns are normalized indicators of the three surviving chamber fibers
`{0,1}`, `{2}`, and `{4,5}`. Fine chamber `3` is collapsed. -/
def normalizedBlockIsometry : BlockIsometry :=
  !![(1 / spinOneSqrtTwo : ℂ), 0, 0;
     (1 / spinOneSqrtTwo : ℂ), 0, 0;
     0, 1, 0;
     0, 0, 0;
     0, 0, (1 / spinOneSqrtTwo : ℂ);
     0, 0, (1 / spinOneSqrtTwo : ℂ)]

theorem normalizedBlockIsometry_isometry :
    normalizedBlockIsometryᴴ * normalizedBlockIsometry =
      (1 : CoarseOrientationMatrix) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [normalizedBlockIsometry, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff] <;>
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    try rw [spinOneSqrtTwo_sq_complex]
    norm_num

/-! ## 2. The unital single-Kraus compression -/

def blockCompression (A : FineOrientationMatrix) : CoarseOrientationMatrix :=
  normalizedBlockIsometryᴴ * A * normalizedBlockIsometry

/-- A finite single-Kraus certificate: `Phi(A)=K A K^*`. This is the
standard finite-dimensional completely-positive form. -/
def HasSingleKrausCPCertificate
    (Phi : FineOrientationMatrix → CoarseOrientationMatrix) : Prop :=
  ∃ K : Matrix (Fin 3) (Fin 6) ℂ,
    ∀ A, Phi A = K * A * Kᴴ

theorem blockCompression_hasSingleKrausCPCertificate :
    HasSingleKrausCPCertificate blockCompression := by
  refine ⟨normalizedBlockIsometryᴴ, ?_⟩
  intro A
  unfold blockCompression
  rw [Matrix.conjTranspose_conjTranspose]

theorem blockCompression_add (A B : FineOrientationMatrix) :
    blockCompression (A + B) = blockCompression A + blockCompression B := by
  unfold blockCompression
  rw [Matrix.mul_add, Matrix.add_mul]

theorem blockCompression_smul (z : ℂ) (A : FineOrientationMatrix) :
    blockCompression (z • A) = z • blockCompression A := by
  unfold blockCompression
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem blockCompression_unital :
    blockCompression (1 : FineOrientationMatrix) =
      (1 : CoarseOrientationMatrix) := by
  unfold blockCompression
  rw [Matrix.mul_one, normalizedBlockIsometry_isometry]

theorem blockCompression_conjTranspose (A : FineOrientationMatrix) :
    blockCompression Aᴴ = (blockCompression A)ᴴ := by
  unfold blockCompression
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  rw [Matrix.mul_assoc]

theorem blockCompression_posSemidef
    {A : FineOrientationMatrix} (hA : A.PosSemidef) :
    (blockCompression A).PosSemidef := by
  unfold blockCompression
  exact hA.conjTranspose_mul_mul_same normalizedBlockIsometry

/-! ## 3. Leakage and the operator-valued Schwarz kernel -/

def blockRangeProjection : FineOrientationMatrix :=
  normalizedBlockIsometry * normalizedBlockIsometryᴴ

def blockComplementProjection : FineOrientationMatrix :=
  1 - blockRangeProjection

theorem blockRangeProjection_isHermitian :
    blockRangeProjection.IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self normalizedBlockIsometry

theorem blockRangeProjection_idempotent :
    blockRangeProjection * blockRangeProjection = blockRangeProjection := by
  unfold blockRangeProjection
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc normalizedBlockIsometryᴴ,
    normalizedBlockIsometry_isometry, Matrix.one_mul]

theorem blockComplementProjection_isHermitian :
    blockComplementProjection.IsHermitian := by
  unfold blockComplementProjection Matrix.IsHermitian
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    blockRangeProjection_isHermitian.eq]

theorem blockComplementProjection_idempotent :
    blockComplementProjection * blockComplementProjection =
      blockComplementProjection := by
  unfold blockComplementProjection
  calc
    (1 - blockRangeProjection) * (1 - blockRangeProjection) =
        1 - blockRangeProjection - blockRangeProjection +
          blockRangeProjection * blockRangeProjection := by
      noncomm_ring
    _ = 1 - blockRangeProjection - blockRangeProjection +
          blockRangeProjection := by
      rw [blockRangeProjection_idempotent]
    _ = 1 - blockRangeProjection := by
      abel

def compressionLeakage (A : FineOrientationMatrix) : BlockIsometry :=
  blockComplementProjection * A * normalizedBlockIsometry

theorem compressionLeakage_eq_intertwiningDefect
    (A : FineOrientationMatrix) :
    compressionLeakage A =
      A * normalizedBlockIsometry -
        normalizedBlockIsometry * blockCompression A := by
  unfold compressionLeakage blockComplementProjection blockRangeProjection
    blockCompression
  simp only [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc]

def compressionDefect
    (A B : FineOrientationMatrix) : CoarseOrientationMatrix :=
  blockCompression (Aᴴ * B) -
    (blockCompression A)ᴴ * blockCompression B

theorem compressionDefect_factor
    (A B : FineOrientationMatrix) :
    compressionDefect A B =
      (compressionLeakage A)ᴴ * compressionLeakage B := by
  have hdefect :
      compressionDefect A B =
        normalizedBlockIsometryᴴ * Aᴴ * blockComplementProjection * B *
          normalizedBlockIsometry := by
    unfold compressionDefect blockCompression blockComplementProjection
      blockRangeProjection
    simp only [Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.mul_assoc]
  symm
  calc
    (compressionLeakage A)ᴴ * compressionLeakage B =
        normalizedBlockIsometryᴴ * Aᴴ *
          (blockComplementProjection * blockComplementProjection) * B *
            normalizedBlockIsometry := by
      unfold compressionLeakage
      simp only [Matrix.conjTranspose_mul,
        blockComplementProjection_isHermitian.eq, Matrix.mul_assoc]
    _ = normalizedBlockIsometryᴴ * Aᴴ *
          blockComplementProjection * B * normalizedBlockIsometry := by
      rw [blockComplementProjection_idempotent]
    _ = compressionDefect A B := hdefect.symm

/-- Kadison-Schwarz for this concrete unital single-Kraus channel. -/
theorem compressionDefect_posSemidef (A : FineOrientationMatrix) :
    (compressionDefect A A).PosSemidef := by
  rw [compressionDefect_factor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-! ### Complete positivity of the defect kernel -/

/-- The finite operator-valued quadratic form associated with the defect
kernel. Coefficients act in the retained matrix algebra. -/
def compressionDefectQuadratic
    {n : ℕ} (A : Fin n → FineOrientationMatrix)
    (C : Fin n → CoarseOrientationMatrix) : CoarseOrientationMatrix :=
  ∑ i, ∑ j, (C i)ᴴ * compressionDefect (A i) (A j) * C j

theorem compressionDefectQuadratic_factor
    {n : ℕ} (A : Fin n → FineOrientationMatrix)
    (C : Fin n → CoarseOrientationMatrix) :
    compressionDefectQuadratic A C =
      (∑ i, compressionLeakage (A i) * C i)ᴴ *
        (∑ i, compressionLeakage (A i) * C i) := by
  unfold compressionDefectQuadratic
  simp_rw [compressionDefect_factor]
  simp only [Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.mul_sum, Matrix.mul_assoc]
  rw [Finset.sum_comm]
  simp only [Matrix.sum_mul]
  simp only [Matrix.mul_assoc]

theorem compressionDefectQuadratic_posSemidef
    {n : ℕ} (A : Fin n → FineOrientationMatrix)
    (C : Fin n → CoarseOrientationMatrix) :
    (compressionDefectQuadratic A C).PosSemidef := by
  rw [compressionDefectQuadratic_factor]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A concrete complete-positive-definite kernel criterion for maps valued in
the retained matrix algebra. -/
def IsCompletelyPositiveKernel
    (K : FineOrientationMatrix → FineOrientationMatrix →
      CoarseOrientationMatrix) : Prop :=
  ∀ (n : ℕ) (A : Fin n → FineOrientationMatrix)
    (C : Fin n → CoarseOrientationMatrix),
      (∑ i, ∑ j, (C i)ᴴ * K (A i) (A j) * C j).PosSemidef

/-- The Schwarz defect is a completely positive operator-valued kernel, not
only a pointwise positive diagonal. -/
theorem compressionDefect_isCompletelyPositiveKernel :
    IsCompletelyPositiveKernel compressionDefect := by
  intro n A C
  exact compressionDefectQuadratic_posSemidef A C

/-- The diagonal Schwarz equality holds exactly when no component leaks from
the normalized retained subspace. -/
theorem compressionDefect_self_eq_zero_iff
    (A : FineOrientationMatrix) :
    compressionDefect A A = 0 ↔ compressionLeakage A = 0 := by
  rw [compressionDefect_factor,
    Matrix.conjTranspose_mul_self_eq_zero]

/-- Full multiplicative-domain membership requires both right and left leakage
to vanish. For Hermitian observables the two conditions coincide. -/
def InCompressionMultiplicativeDomain (A : FineOrientationMatrix) : Prop :=
  compressionLeakage A = 0 ∧ compressionLeakage Aᴴ = 0

theorem hermitian_mem_multiplicativeDomain_iff
    (A : FineOrientationMatrix) (hA : A.IsHermitian) :
    InCompressionMultiplicativeDomain A ↔ compressionDefect A A = 0 := by
  unfold InCompressionMultiplicativeDomain
  rw [hA.eq, and_self, compressionDefect_self_eq_zero_iff]

/-- Multiplicative-domain membership gives exact multiplication when the
member occurs on the left. -/
theorem blockCompression_mul_of_mem_multiplicativeDomain
    {A : FineOrientationMatrix} (hA : InCompressionMultiplicativeDomain A)
    (B : FineOrientationMatrix) :
    blockCompression (A * B) = blockCompression A * blockCompression B := by
  have hzero : compressionDefect Aᴴ B = 0 := by
    rw [compressionDefect_factor, hA.2]
    simp
  unfold compressionDefect at hzero
  rw [Matrix.conjTranspose_conjTranspose,
    blockCompression_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at hzero
  exact sub_eq_zero.mp hzero

/-- Multiplicative-domain membership also gives exact multiplication when the
member occurs on the right. -/
theorem blockCompression_mul_of_mem_multiplicativeDomain_right
    {A : FineOrientationMatrix} (hA : InCompressionMultiplicativeDomain A)
    (B : FineOrientationMatrix) :
    blockCompression (B * A) = blockCompression B * blockCompression A := by
  have hzero : compressionDefect Bᴴ A = 0 := by
    rw [compressionDefect_factor, hA.1]
    simp
  unfold compressionDefect at hzero
  rw [Matrix.conjTranspose_conjTranspose,
    blockCompression_conjTranspose,
    Matrix.conjTranspose_conjTranspose] at hzero
  exact sub_eq_zero.mp hzero

/-! ## 4. Two independent coarse-graining gates -/

/-- Failure of closure in a selected effective ansatz is measured relative to
an independently supplied coarse target. -/
def coarseAnsatzResidual
    (A : FineOrientationMatrix) (coarseTarget : CoarseOrientationMatrix) :
    CoarseOrientationMatrix :=
  blockCompression A - coarseTarget

theorem coarseAnsatzResidual_eq_zero_iff
    (A : FineOrientationMatrix) (coarseTarget : CoarseOrientationMatrix) :
    coarseAnsatzResidual A coarseTarget = 0 ↔
      blockCompression A = coarseTarget := by
  exact sub_eq_zero

/-- Gate one: the compressed observable closes in the selected coarse ansatz. -/
def PassesAnsatzClosureGate
    (A : FineOrientationMatrix) (coarseTarget : CoarseOrientationMatrix) : Prop :=
  coarseAnsatzResidual A coarseTarget = 0

/-- Gate two: the channel is multiplicative on the retained observable. -/
def PassesMultiplicativeDomainGate (A : FineOrientationMatrix) : Prop :=
  InCompressionMultiplicativeDomain A

/-- Passing both gates means both effective-ansatz closure and absence of
discarded multiplicative covariance. -/
def PassesBothCoarseGrainingGates
    (A : FineOrientationMatrix) (coarseTarget : CoarseOrientationMatrix) : Prop :=
  PassesAnsatzClosureGate A coarseTarget ∧
    PassesMultiplicativeDomainGate A

/-! ## 5. The orientation channel is a multiplicative-domain boundary case -/

def fineDiamondOrientationHamiltonian : FineOrientationMatrix :=
  Complex.I • diamondOrientationRankTwo.map (Rat.castHom ℂ)

theorem fineDiamondOrientationHamiltonian_isHermitian :
    fineDiamondOrientationHamiltonian.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fineDiamondOrientationHamiltonian, diamondOrientationRankTwo,
      Matrix.conjTranspose_apply]

theorem blockCompression_fineDiamondOrientationHamiltonian :
    blockCompression fineDiamondOrientationHamiltonian =
      skewHamiltonian spinOneSqrtTwo 1 spinOneSqrtTwo := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blockCompression, fineDiamondOrientationHamiltonian,
      normalizedBlockIsometry, diamondOrientationRankTwo, skewHamiltonian,
      Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Fin.ext_iff] <;>
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    try rw [spinOneSqrtTwo_sq_complex]
    norm_num

theorem fineDiamondOrientationHamiltonian_leakage_zero :
    compressionLeakage fineDiamondOrientationHamiltonian = 0 := by
  rw [compressionLeakage_eq_intertwiningDefect]
  rw [blockCompression_fineDiamondOrientationHamiltonian]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [fineDiamondOrientationHamiltonian, normalizedBlockIsometry,
      diamondOrientationRankTwo, skewHamiltonian, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff] <;>
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    try rw [spinOneSqrtTwo_sq_complex]
    norm_num

theorem fineDiamondOrientationHamiltonian_mem_multiplicativeDomain :
    InCompressionMultiplicativeDomain fineDiamondOrientationHamiltonian := by
  rw [hermitian_mem_multiplicativeDomain_iff _
    fineDiamondOrientationHamiltonian_isHermitian,
    compressionDefect_self_eq_zero_iff]
  exact fineDiamondOrientationHamiltonian_leakage_zero

theorem fineDiamondOrientationHamiltonian_defect_zero :
    compressionDefect fineDiamondOrientationHamiltonian
      fineDiamondOrientationHamiltonian = 0 := by
  rw [compressionDefect_self_eq_zero_iff]
  exact fineDiamondOrientationHamiltonian_leakage_zero

theorem unitalCompressed_orientationTraceStrength :
    Matrix.trace
        (blockCompression fineDiamondOrientationHamiltonian *
          blockCompression fineDiamondOrientationHamiltonian) = 10 := by
  rw [blockCompression_fineDiamondOrientationHamiltonian]
  have hdecomp := skewHamiltonian_spinOne_decomposition
    spinOneSqrtTwo 1 0
  have hsqrt :
      (spinOneSqrtTwo : ℂ) * spinOneSqrtTwo = 2 := by
    rw [← pow_two, spinOneSqrtTwo_sq_complex]
  have hspin :
      skewHamiltonian spinOneSqrtTwo 1 spinOneSqrtTwo =
        spinOneFieldHamiltonian 2 1 0 := by
    simpa [spinOneFieldHamiltonian, hsqrt] using hdecomp
  rw [hspin]
  rw [spinOneField_trace_product]
  norm_num [fieldDot]

theorem unitalCompression_ne_globalHalfPush :
    blockCompression fineDiamondOrientationHamiltonian ≠
      normalizedBlockedOrientationHamiltonian := by
  rw [blockCompression_fineDiamondOrientationHamiltonian,
    normalizedBlockedOrientationHamiltonian_eq]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [skewHamiltonian] at h01
  have hsqrt := spinOneSqrtTwo_sq
  nlinarith [spinOneSqrtTwo_pos]

theorem unitalCompression_ne_coarseNative :
    blockCompression fineDiamondOrientationHamiltonian ≠
      coarseNativeOrientationHamiltonian := by
  rw [blockCompression_fineDiamondOrientationHamiltonian,
    coarseNativeOrientationHamiltonian_eq]
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [skewHamiltonian] at h01
  have hsqrt := spinOneSqrtTwo_sq
  nlinarith [spinOneSqrtTwo_pos]

/-- Closure in the independently recomputed coarse ansatz and membership in
the channel's multiplicative domain are logically different tests in this
benchmark: the former fails while the Schwarz defect vanishes. -/
theorem ansatz_nonclosure_with_zero_Schwarz_defect :
    blockCompression fineDiamondOrientationHamiltonian ≠
        coarseNativeOrientationHamiltonian
      ∧ compressionDefect fineDiamondOrientationHamiltonian
          fineDiamondOrientationHamiltonian = 0 := by
  exact ⟨unitalCompression_ne_coarseNative,
    fineDiamondOrientationHamiltonian_defect_zero⟩

theorem orientation_passes_domain_gate_fails_ansatz_gate :
    PassesMultiplicativeDomainGate fineDiamondOrientationHamiltonian ∧
      ¬ PassesAnsatzClosureGate fineDiamondOrientationHamiltonian
        coarseNativeOrientationHamiltonian := by
  constructor
  · exact fineDiamondOrientationHamiltonian_mem_multiplicativeDomain
  · unfold PassesAnsatzClosureGate
    rw [coarseAnsatzResidual_eq_zero_iff]
    exact unitalCompression_ne_coarseNative

/-! ## 6. A nonzero discarded-covariance witness -/

/-- A Hermitian coupling between the surviving singleton chamber `2` and the
collapsed chamber `3`. Its retained image is zero. -/
def collapsedChamberCoupling : FineOrientationMatrix :=
  !![0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 1, 0, 0;
     0, 0, 1, 0, 0, 0;
     0, 0, 0, 0, 0, 0;
     0, 0, 0, 0, 0, 0]

def singletonCoarseProjector : CoarseOrientationMatrix :=
  !![0, 0, 0;
     0, 1, 0;
     0, 0, 0]

theorem collapsedChamberCoupling_isHermitian :
    collapsedChamberCoupling.IsHermitian := by
  unfold Matrix.IsHermitian
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [collapsedChamberCoupling, Matrix.conjTranspose_apply,
      Fin.ext_iff]

theorem blockCompression_collapsedChamberCoupling :
    blockCompression collapsedChamberCoupling = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [blockCompression, collapsedChamberCoupling,
      normalizedBlockIsometry, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem collapsedChamberCoupling_defect :
    compressionDefect collapsedChamberCoupling collapsedChamberCoupling =
      singletonCoarseProjector := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [compressionDefect, blockCompression,
      collapsedChamberCoupling, singletonCoarseProjector,
      normalizedBlockIsometry, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem collapsedChamberCoupling_defect_ne_zero :
    compressionDefect collapsedChamberCoupling collapsedChamberCoupling ≠ 0 := by
  rw [collapsedChamberCoupling_defect]
  intro h
  have h11 := congrFun (congrFun h 1) 1
  norm_num [singletonCoarseProjector] at h11

theorem collapsedChamberCoupling_not_mem_multiplicativeDomain :
    ¬ InCompressionMultiplicativeDomain collapsedChamberCoupling := by
  rw [hermitian_mem_multiplicativeDomain_iff _
    collapsedChamberCoupling_isHermitian]
  exact collapsedChamberCoupling_defect_ne_zero

theorem collapsedCoupling_passes_zero_ansatz_fails_domain_gate :
    PassesAnsatzClosureGate collapsedChamberCoupling 0 ∧
      ¬ PassesMultiplicativeDomainGate collapsedChamberCoupling := by
  constructor
  · unfold PassesAnsatzClosureGate
    rw [coarseAnsatzResidual_eq_zero_iff]
    exact blockCompression_collapsedChamberCoupling
  · exact collapsedChamberCoupling_not_mem_multiplicativeDomain

/-- Neither gate implies the other. The orientation Hamiltonian passes the
multiplicative-domain gate but fails native-ansatz closure; the collapsed
coupling closes on the zero ansatz but fails the multiplicative-domain gate. -/
theorem coarseGraining_gates_logically_independent :
    (∃ A : FineOrientationMatrix, ∃ coarseTarget : CoarseOrientationMatrix,
        PassesMultiplicativeDomainGate A ∧
          ¬ PassesAnsatzClosureGate A coarseTarget)
      ∧
    (∃ A : FineOrientationMatrix, ∃ coarseTarget : CoarseOrientationMatrix,
        PassesAnsatzClosureGate A coarseTarget ∧
          ¬ PassesMultiplicativeDomainGate A) := by
  exact ⟨
    ⟨fineDiamondOrientationHamiltonian,
      coarseNativeOrientationHamiltonian,
      orientation_passes_domain_gate_fails_ansatz_gate⟩,
    ⟨collapsedChamberCoupling, 0,
      collapsedCoupling_passes_zero_ansatz_fails_domain_gate⟩⟩

/-- The defect cannot be reconstructed from the retained image: zero and the
collapsed coupling have the same coarse image but different defects. -/
theorem compressionDefect_not_determined_by_image :
    ∃ A B : FineOrientationMatrix,
      blockCompression A = blockCompression B ∧
        compressionDefect A A ≠ compressionDefect B B := by
  refine ⟨0, collapsedChamberCoupling, ?_, ?_⟩
  · rw [blockCompression_collapsedChamberCoupling]
    unfold blockCompression
    simp
  · have hzero :
        compressionDefect (0 : FineOrientationMatrix) 0 = 0 := by
      unfold compressionDefect blockCompression
      simp
    rw [hzero]
    exact Ne.symm collapsedChamberCoupling_defect_ne_zero

/-- Strong functional form of non-reconstructibility: there is no map of the
retained operator alone that returns the diagonal Schwarz defect for every
fine observable. -/
theorem no_compressionDefect_reconstructor :
    ¬ ∃ reconstruct : CoarseOrientationMatrix → CoarseOrientationMatrix,
      ∀ A : FineOrientationMatrix,
        reconstruct (blockCompression A) = compressionDefect A A := by
  rintro ⟨reconstruct, hreconstruct⟩
  have himage :
      blockCompression (0 : FineOrientationMatrix) =
        blockCompression collapsedChamberCoupling := by
    rw [blockCompression_collapsedChamberCoupling]
    unfold blockCompression
    simp
  have hdefect :
      compressionDefect (0 : FineOrientationMatrix) 0 =
        compressionDefect collapsedChamberCoupling
          collapsedChamberCoupling := by
    calc
      compressionDefect (0 : FineOrientationMatrix) 0 =
          reconstruct (blockCompression (0 : FineOrientationMatrix)) :=
        (hreconstruct 0).symm
      _ = reconstruct (blockCompression collapsedChamberCoupling) := by
        rw [himage]
      _ = compressionDefect collapsedChamberCoupling
          collapsedChamberCoupling := hreconstruct collapsedChamberCoupling
  have hzero : compressionDefect (0 : FineOrientationMatrix) 0 = 0 := by
    unfold compressionDefect blockCompression
    simp
  rw [hzero] at hdefect
  exact collapsedChamberCoupling_defect_ne_zero hdefect.symm

#print axioms normalizedBlockIsometry_isometry
#print axioms blockCompression_hasSingleKrausCPCertificate
#print axioms blockCompression_unital
#print axioms blockCompression_posSemidef
#print axioms compressionDefect_factor
#print axioms compressionDefect_posSemidef
#print axioms compressionDefectQuadratic_factor
#print axioms compressionDefect_isCompletelyPositiveKernel
#print axioms hermitian_mem_multiplicativeDomain_iff
#print axioms blockCompression_mul_of_mem_multiplicativeDomain
#print axioms blockCompression_mul_of_mem_multiplicativeDomain_right
#print axioms coarseAnsatzResidual_eq_zero_iff
#print axioms blockCompression_fineDiamondOrientationHamiltonian
#print axioms fineDiamondOrientationHamiltonian_mem_multiplicativeDomain
#print axioms fineDiamondOrientationHamiltonian_defect_zero
#print axioms ansatz_nonclosure_with_zero_Schwarz_defect
#print axioms coarseGraining_gates_logically_independent
#print axioms collapsedChamberCoupling_defect
#print axioms collapsedChamberCoupling_not_mem_multiplicativeDomain
#print axioms compressionDefect_not_determined_by_image
#print axioms no_compressionDefect_reconstructor

end

end UnifiedTheory.Audit.KFOrientationCPChannel
