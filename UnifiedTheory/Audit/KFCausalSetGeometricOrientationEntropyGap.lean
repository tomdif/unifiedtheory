/-
  Audit/KFCausalSetGeometricOrientationEntropyGap.lean

  UNIFORM MIXEDNESS GAP FOR GEOMETRIC ORIENTATION

  The all-rank geometric orientation theorem proves the sharp pointwise band

      |y| < 1/4

  for the balanced two-history kernel

      D_y = (1/2-y) P_+ + (1/2+y) P_-.

  This file extracts the quantitative quantum-information content of that
  band.  At every event of every finite causal order:

  * both orientation spectral weights lie strictly between `1/4` and `3/4`;
  * neither chirality can have Born probability at least `3/4`;
  * `det D_y > 3/16`, uniformly separating geometry from every scalar-amplitude
    (rank-one) history kernel;
  * `Tr(D_y^2) < 5/8`, so geometric orientation is uniformly far from pure;
  * the second latent component has residual weight greater than `3/8`;
  * the spectral condition number is less than `3`;
  * the binary spectral entropy is strictly larger than `binEntropy(1/4)`,
    approximately `0.811278` bits.

  These are finite, model-internal no-purification theorems.  They do not
  identify the orientation kernel with a continuum entropy, thermodynamic
  entropy, or experimentally measured particle chirality.
-/

import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetGeometricOrientationEntropyGap

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationDynamics
open UnifiedTheory.Audit.KFCausalSetGeometricOrientationAsymptotics
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

/-! ## 1. Spectral coordinates of the balanced orientation kernel -/

/-- The smaller spectral weight of the balanced orientation kernel. -/
def orientationMinorityWeight (y : ℝ) : ℝ :=
  1 / 2 - |y|

/-- The larger spectral weight of the balanced orientation kernel. -/
def orientationMajorityWeight (y : ℝ) : ℝ :=
  1 / 2 + |y|

/-- Spectral purity of the two orientation weights. -/
def orientationSpectralPurity (y : ℝ) : ℝ :=
  orientationMinorityWeight y ^ 2 + orientationMajorityWeight y ^ 2

/-- Binary spectral entropy in nats. -/
noncomputable def orientationSpectralEntropyNats (y : ℝ) : ℝ :=
  Real.binEntropy (orientationMinorityWeight y)

/-- Binary spectral entropy in bits. -/
noncomputable def orientationSpectralEntropyBits (y : ℝ) : ℝ :=
  orientationSpectralEntropyNats y / Real.log 2

/-- Ratio of the larger to the smaller spectral weight. -/
def orientationSpectralConditionNumber (y : ℝ) : ℝ :=
  orientationMajorityWeight y / orientationMinorityWeight y

theorem orientationMinorityWeight_add_majorityWeight (y : ℝ) :
    orientationMinorityWeight y + orientationMajorityWeight y = 1 := by
  unfold orientationMinorityWeight orientationMajorityWeight
  ring

theorem orientationMinorityWeight_mul_majorityWeight (y : ℝ) :
    orientationMinorityWeight y * orientationMajorityWeight y =
      1 / 4 - y * y := by
  unfold orientationMinorityWeight orientationMajorityWeight
  calc
    (1 / 2 - |y|) * (1 / 2 + |y|) = 1 / 4 - |y| ^ 2 := by ring
    _ = 1 / 4 - y ^ 2 := by rw [sq_abs]
    _ = 1 / 4 - y * y := by ring

theorem orientationSpectralPurity_formula (y : ℝ) :
    orientationSpectralPurity y = 1 / 2 + 2 * y ^ 2 := by
  unfold orientationSpectralPurity orientationMinorityWeight
    orientationMajorityWeight
  calc
    (1 / 2 - |y|) ^ 2 + (1 / 2 + |y|) ^ 2 =
        1 / 2 + 2 * |y| ^ 2 := by ring
    _ = 1 / 2 + 2 * y ^ 2 := by rw [sq_abs]

/-- The two projector coefficients are precisely the unordered minority and
majority spectral weights. -/
theorem orientationProjectorWeights_min_max (y : ℝ) :
    min (1 / 2 - y) (1 / 2 + y) = orientationMinorityWeight y
      ∧ max (1 / 2 - y) (1 / 2 + y) = orientationMajorityWeight y := by
  by_cases hy : 0 ≤ y
  · have hOrder : 1 / 2 - y ≤ (1 / 2 + y : ℝ) := by linarith
    rw [min_eq_left hOrder, max_eq_right hOrder]
    unfold orientationMinorityWeight orientationMajorityWeight
    rw [abs_of_nonneg hy]
    constructor <;> rfl
  · have hy' : y ≤ 0 := le_of_not_ge hy
    have hOrder : 1 / 2 + y ≤ (1 / 2 - y : ℝ) := by linarith
    rw [min_eq_right hOrder, max_eq_left hOrder]
    unfold orientationMinorityWeight orientationMajorityWeight
    rw [abs_of_nonpos hy']
    constructor <;> ring

theorem balancedHistoryKernel_bornWeight_min_max (y : ℝ) :
    min
        (bornWeight (balancedHistoryKernel y) positiveOrientationProjector)
        (bornWeight (balancedHistoryKernel y) negativeOrientationProjector) =
      orientationMinorityWeight y
      ∧ max
        (bornWeight (balancedHistoryKernel y) positiveOrientationProjector)
        (bornWeight (balancedHistoryKernel y) negativeOrientationProjector) =
      orientationMajorityWeight y := by
  rw [balancedHistoryKernel_positive_bornWeight,
    balancedHistoryKernel_negative_bornWeight]
  exact orientationProjectorWeights_min_max y

/-! ## 2. Generic consequences of the sharp quarter band -/

theorem orientationMinorityWeight_gt_quarter {y : ℝ}
    (hy : |y| < 1 / 4) :
    1 / 4 < orientationMinorityWeight y := by
  unfold orientationMinorityWeight
  linarith

theorem orientationMinorityWeight_le_half (y : ℝ) :
    orientationMinorityWeight y ≤ 1 / 2 := by
  unfold orientationMinorityWeight
  exact sub_le_self _ (abs_nonneg y)

theorem orientationMajorityWeight_lt_three_quarters {y : ℝ}
    (hy : |y| < 1 / 4) :
    orientationMajorityWeight y < 3 / 4 := by
  unfold orientationMajorityWeight
  linarith

theorem orientationMajorityWeight_ge_half (y : ℝ) :
    1 / 2 ≤ orientationMajorityWeight y := by
  unfold orientationMajorityWeight
  exact le_add_of_nonneg_right (abs_nonneg y)

theorem orientationSpectralPurity_lt_five_eighths {y : ℝ}
    (hy : |y| < 1 / 4) :
    orientationSpectralPurity y < 5 / 8 := by
  rw [orientationSpectralPurity_formula]
  have hsq : y ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    norm_num
    exact hy
  nlinarith

theorem orientationInteriorResidual_gt_three_eighths {y : ℝ}
    (hy : |y| < 1 / 4) :
    3 / 8 < orientationInteriorResidual y := by
  have hsq : y ^ 2 < (1 / 4 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    norm_num
    exact hy
  unfold orientationInteriorResidual
  nlinarith [show y * y = y ^ 2 by ring]

theorem orientationSpectralConditionNumber_lt_three {y : ℝ}
    (hy : |y| < 1 / 4) :
    orientationSpectralConditionNumber y < 3 := by
  have hMinorityPos : 0 < orientationMinorityWeight y :=
    lt_trans (by norm_num) (orientationMinorityWeight_gt_quarter hy)
  rw [orientationSpectralConditionNumber, div_lt_iff₀ hMinorityPos]
  unfold orientationMinorityWeight orientationMajorityWeight
  linarith

theorem orientationSpectralEntropyNats_gt_quarter {y : ℝ}
    (hy : |y| < 1 / 4) :
    Real.binEntropy (1 / 4) < orientationSpectralEntropyNats y := by
  unfold orientationSpectralEntropyNats
  apply Real.binEntropy_strictMonoOn
  · constructor <;> norm_num
  · constructor
    · linarith [orientationMinorityWeight_gt_quarter hy]
    · simpa using orientationMinorityWeight_le_half y
  · exact orientationMinorityWeight_gt_quarter hy

theorem orientationSpectralEntropyBits_gt_quarter {y : ℝ}
    (hy : |y| < 1 / 4) :
    Real.binEntropy (1 / 4) / Real.log 2 <
      orientationSpectralEntropyBits y := by
  unfold orientationSpectralEntropyBits
  exact (div_lt_div_iff_of_pos_right
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))).2
    (orientationSpectralEntropyNats_gt_quarter hy)

/-- Matrix purity agrees exactly with the two-weight spectral formula. -/
theorem balancedHistoryKernel_trace_square (y : ℝ) :
    (Matrix.trace
      (balancedHistoryKernel y * balancedHistoryKernel y)).re =
        orientationSpectralPurity y := by
  rw [orientationSpectralPurity_formula]
  norm_num [balancedHistoryKernel, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq]
  ring

/-! ## 3. Uniform consequences for every finite causal geometry -/

/-- Real form of the local geometric orientation parameter. -/
def geometricOrientationParameterR {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) : ℝ :=
  ((causalOrientationDensityQ parent i : ℚ) : ℝ)

theorem geometricOrientationParameterR_abs_lt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    |geometricOrientationParameterR parent i| < 1 / 4 := by
  exact causalOrientationDensityR_abs_lt_quarter parent i

/-- Both chirality outcomes retain probability strictly between `1/4` and
`3/4`; geometry alone never supplies a nearly deterministic sign. -/
theorem geometricOrientation_bornWeight_band {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    (1 / 4 < bornWeight
        (balancedHistoryKernel (geometricOrientationParameterR parent i))
        positiveOrientationProjector
      ∧ bornWeight
        (balancedHistoryKernel (geometricOrientationParameterR parent i))
        positiveOrientationProjector < 3 / 4)
      ∧ (1 / 4 < bornWeight
        (balancedHistoryKernel (geometricOrientationParameterR parent i))
        negativeOrientationProjector
      ∧ bornWeight
        (balancedHistoryKernel (geometricOrientationParameterR parent i))
        negativeOrientationProjector < 3 / 4) := by
  rw [balancedHistoryKernel_positive_bornWeight,
    balancedHistoryKernel_negative_bornWeight]
  have hy := abs_lt.mp (geometricOrientationParameterR_abs_lt_quarter parent i)
  constructor <;> constructor <;> linarith

/-- The optimal chirality Born probability is strictly below `3/4`. -/
theorem geometricOrientation_predictability_lt_three_quarters {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    max
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          positiveOrientationProjector)
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          negativeOrientationProjector) < 3 / 4 := by
  rw [(balancedHistoryKernel_bornWeight_min_max
    (geometricOrientationParameterR parent i)).2]
  exact orientationMajorityWeight_lt_three_quarters
    (geometricOrientationParameterR_abs_lt_quarter parent i)

/-- The unavoidable minority chirality weight is strictly above `1/4`. -/
theorem geometricOrientation_endpoint_admixture_gt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    1 / 4 < min
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          positiveOrientationProjector)
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          negativeOrientationProjector) := by
  rw [(balancedHistoryKernel_bornWeight_min_max
    (geometricOrientationParameterR parent i)).1]
  exact orientationMinorityWeight_gt_quarter
    (geometricOrientationParameterR_abs_lt_quarter parent i)

theorem geometricOrientation_det_gt_three_sixteenths {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    3 / 16 <
      (Matrix.det
        (balancedHistoryKernel
          (geometricOrientationParameterR parent i))).re := by
  rw [balancedHistoryKernel_det]
  norm_num
  have hy := geometricOrientationParameterR_abs_lt_quarter parent i
  have hsq : (geometricOrientationParameterR parent i) ^ 2 <
      (1 / 4 : ℝ) ^ 2 := by
    rw [sq_lt_sq]
    norm_num
    exact hy
  nlinarith [show (geometricOrientationParameterR parent i) *
      geometricOrientationParameterR parent i =
        (geometricOrientationParameterR parent i) ^ 2 by ring]

theorem geometricOrientation_purity_lt_five_eighths {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    (Matrix.trace
      (balancedHistoryKernel (geometricOrientationParameterR parent i) *
        balancedHistoryKernel (geometricOrientationParameterR parent i))).re <
      5 / 8 := by
  rw [balancedHistoryKernel_trace_square]
  exact orientationSpectralPurity_lt_five_eighths
    (geometricOrientationParameterR_abs_lt_quarter parent i)

theorem geometricOrientation_latentResidual_gt_three_eighths {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    3 / 8 < orientationInteriorResidual
      (geometricOrientationParameterR parent i) :=
  orientationInteriorResidual_gt_three_eighths
    (geometricOrientationParameterR_abs_lt_quarter parent i)

theorem geometricOrientation_conditionNumber_lt_three {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    orientationSpectralConditionNumber
      (geometricOrientationParameterR parent i) < 3 :=
  orientationSpectralConditionNumber_lt_three
    (geometricOrientationParameterR_abs_lt_quarter parent i)

theorem geometricOrientation_entropyNats_gt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    Real.binEntropy (1 / 4) < orientationSpectralEntropyNats
      (geometricOrientationParameterR parent i) :=
  orientationSpectralEntropyNats_gt_quarter
    (geometricOrientationParameterR_abs_lt_quarter parent i)

theorem geometricOrientation_entropyBits_gt_quarter {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    Real.binEntropy (1 / 4) / Real.log 2 < orientationSpectralEntropyBits
      (geometricOrientationParameterR parent i) :=
  orientationSpectralEntropyBits_gt_quarter
    (geometricOrientationParameterR_abs_lt_quarter parent i)

/-- Determinant gives an invariant, uniform separation from every rank-one
scalar-amplitude history kernel, not merely from the two chiral projectors. -/
theorem geometricOrientation_det_gap_from_scalarAmplitude {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n)
    {rho : SquareMatrix 2} (hScalar : IsScalarAmplitudeKernel rho) :
    (Matrix.det rho).re + 3 / 16 <
      (Matrix.det
        (balancedHistoryKernel
          (geometricOrientationParameterR parent i))).re := by
  rw [scalarAmplitudeKernel_det_zero hScalar]
  norm_num
  exact geometricOrientation_det_gt_three_sixteenths parent i

/-- Capstone: every finite geometric orientation kernel has a universal
probability, determinant, purity, latent-rank, conditioning, and entropy gap
from the pure scalar-amplitude boundary. -/
theorem geometric_orientation_uniform_mixedness_gap {n : ℕ}
    (parent : CardinalCausalOrder n) (i : Fin n) :
    max
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          positiveOrientationProjector)
        (bornWeight
          (balancedHistoryKernel (geometricOrientationParameterR parent i))
          negativeOrientationProjector) < 3 / 4
      ∧ 3 / 16 <
        (Matrix.det
          (balancedHistoryKernel
            (geometricOrientationParameterR parent i))).re
      ∧ (Matrix.trace
          (balancedHistoryKernel (geometricOrientationParameterR parent i) *
            balancedHistoryKernel
              (geometricOrientationParameterR parent i))).re < 5 / 8
      ∧ 3 / 8 < orientationInteriorResidual
          (geometricOrientationParameterR parent i)
      ∧ orientationSpectralConditionNumber
          (geometricOrientationParameterR parent i) < 3
      ∧ Real.binEntropy (1 / 4) / Real.log 2 <
          orientationSpectralEntropyBits
            (geometricOrientationParameterR parent i) := by
  exact ⟨geometricOrientation_predictability_lt_three_quarters parent i,
    geometricOrientation_det_gt_three_sixteenths parent i,
    geometricOrientation_purity_lt_five_eighths parent i,
    geometricOrientation_latentResidual_gt_three_eighths parent i,
    geometricOrientation_conditionNumber_lt_three parent i,
    geometricOrientation_entropyBits_gt_quarter parent i⟩

#print axioms orientationProjectorWeights_min_max
#print axioms orientationSpectralPurity_lt_five_eighths
#print axioms orientationSpectralEntropyBits_gt_quarter
#print axioms balancedHistoryKernel_trace_square
#print axioms geometricOrientation_bornWeight_band
#print axioms geometricOrientation_det_gt_three_sixteenths
#print axioms geometricOrientation_purity_lt_five_eighths
#print axioms geometricOrientation_det_gap_from_scalarAmplitude
#print axioms geometric_orientation_uniform_mixedness_gap

end

end UnifiedTheory.Audit.KFCausalSetGeometricOrientationEntropyGap
