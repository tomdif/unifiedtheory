/-
  Audit/KFOrientationHistoryRefinementChannel.lean

  AN EXPLICIT CPTP REALIZATION OF MULTIPLICATIVE ORIENTATION REFINEMENT

  The preceding refinement audit studied the conditional law `y ⋆ z = 2yz`.
  Here that law is no longer merely postulated at the two-level density-matrix
  layer.  We construct a four-Kraus quantum channel from two orientation qubits
  to one orientation qubit.  It measures each input in the curvature (Pauli-Y)
  basis and prepares the output whose sign is the negative product of the two
  measured signs.  The induced channel obeys exactly

      Phi (D_y tensor D_z) = D_(2yz).

  Thus multiplication of normalized coherence is realized by a genuine CPTP
  coarse-graining map.  What remains open is the physical theorem identifying
  this finite channel with unlabeled causal-set refinement dynamics.
-/

import UnifiedTheory.LayerB.KrausExistence
import UnifiedTheory.Audit.KFOrientationHistoryRefinement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel

noncomputable section

open scoped BigOperators Kronecker ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationHistoryRefinement

abbrev PairKet := Matrix (Fin 4) (Fin 1) ℂ

theorem starRingEnd_two_complex : (starRingEnd ℂ) (2 : ℂ) = 2 := by
  have hTwo : (2 : ℂ) = ((2 : ℝ) : ℂ) := by norm_num
  rw [hTwo, Complex.conj_ofReal]

/-! ## 1. Curvature-basis product kets -/

def positivePositiveKet : PairKet :=
  !![(1 / 2 : ℂ); Complex.I / 2; Complex.I / 2; -1 / 2]

def positiveNegativeKet : PairKet :=
  !![(1 / 2 : ℂ); -Complex.I / 2; Complex.I / 2; 1 / 2]

def negativePositiveKet : PairKet :=
  !![(1 / 2 : ℂ); Complex.I / 2; -Complex.I / 2; 1 / 2]

def negativeNegativeKet : PairKet :=
  !![(1 / 2 : ℂ); -Complex.I / 2; -Complex.I / 2; -1 / 2]

/-- Four measure-and-prepare Kraus operators.  Equal input curvature signs
prepare the negative orientation ket; unequal signs prepare the positive ket.
This is the `output sign = -(input sign product)` convention required by the
repository's parameterization `D_y = I/2 - yY`. -/
def refinementKrausOperator (i : Fin 4) : Matrix (Fin 2) (Fin 4) ℂ :=
  match i with
  | ⟨0, _⟩ => negativeHolonomyKet * positivePositiveKetᴴ
  | ⟨1, _⟩ => positiveHolonomyKet * positiveNegativeKetᴴ
  | ⟨2, _⟩ => positiveHolonomyKet * negativePositiveKetᴴ
  | ⟨3, _⟩ => negativeHolonomyKet * negativeNegativeKetᴴ

theorem refinementKraus_complete :
    (∑ i, (refinementKrausOperator i).conjTranspose *
      refinementKrausOperator i) = (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  have hPositive : positiveHolonomyKetᴴ * positiveHolonomyKet =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    exact positiveHolonomyKet_normalized
  have hNegative : negativeHolonomyKetᴴ * negativeHolonomyKet =
      (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
    ext i j
    fin_cases i
    fin_cases j
    exact negativeHolonomyKet_normalized
  have rankOneGram
      (out : PathKet) (pair : PairKet)
      (hout : outᴴ * out = (1 : Matrix (Fin 1) (Fin 1) ℂ)) :
      (out * pairᴴ)ᴴ * (out * pairᴴ) = pair * pairᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    rw [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc outᴴ out pairᴴ, hout, Matrix.one_mul]
  rw [Fin.sum_univ_four]
  rw [show (refinementKrausOperator 0)ᴴ * refinementKrausOperator 0 =
      positivePositiveKet * positivePositiveKetᴴ by
        exact rankOneGram _ _ hNegative]
  rw [show (refinementKrausOperator 1)ᴴ * refinementKrausOperator 1 =
      positiveNegativeKet * positiveNegativeKetᴴ by
        exact rankOneGram _ _ hPositive]
  rw [show (refinementKrausOperator 2)ᴴ * refinementKrausOperator 2 =
      negativePositiveKet * negativePositiveKetᴴ by
        exact rankOneGram _ _ hPositive]
  rw [show (refinementKrausOperator 3)ᴴ * refinementKrausOperator 3 =
      negativeNegativeKet * negativeNegativeKetᴴ by
        exact rankOneGram _ _ hNegative]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positivePositiveKet,
      positiveNegativeKet, negativePositiveKet, negativeNegativeKet,
      Matrix.mul_apply, Matrix.vecMul, dotProduct,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.I_sq] <;> ring_nf <;> norm_num [Complex.I_sq]

/-- The explicit two-qubit-to-one-qubit refinement channel. -/
def orientationRefinementKraus : KrausRepresentation 4 2 4 where
  K := refinementKrausOperator
  complete := refinementKraus_complete

theorem orientationRefinement_isCPTP :
    IsCPTP orientationRefinementKraus.toLinearMap :=
  kraus_isCPTP _

/-! ## 2. Tensor input and exact channel action -/

/-- Left qubit index in the canonical order `00,01,10,11`. -/
def pairLeftIndex (i : Fin 4) : Fin 2 :=
  match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 0
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1

/-- Right qubit index in the canonical order `00,01,10,11`. -/
def pairRightIndex (i : Fin 4) : Fin 2 :=
  match i with
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 0
  | ⟨3, _⟩ => 1

/-- Tensor product of two two-history kernels in the canonical
`|00>, |01>, |10>, |11>` order, stated entrywise to keep later finite
normalization proofs transparent. -/
def historyKernelTensor (rho sigma : SquareMatrix 2) : SquareMatrix 4 :=
  fun i j => rho (pairLeftIndex i) (pairLeftIndex j) *
    sigma (pairRightIndex i) (pairRightIndex j)

set_option maxHeartbeats 600000 in
-- Expanding the canonical `4 x 4` tensor requires sixteen finite polynomial checks.
/-- Closed form of the tensor of two balanced kernels.  Keeping this as a
separate lemma prevents every later Born calculation from re-normalizing the
`Fin 2 × Fin 2 ≃ Fin 4` reindexing. -/
theorem historyKernelTensor_balanced_exact (y z : ℝ) :
    historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z) =
      !![(1 / 4 : ℂ), Complex.I * (z : ℂ) / 2,
          Complex.I * (y : ℂ) / 2, (-(y * z : ℝ) : ℂ);
         -Complex.I * (z : ℂ) / 2, 1 / 4, (y * z : ℝ),
          Complex.I * (y : ℂ) / 2;
         -Complex.I * (y : ℂ) / 2, (y * z : ℝ), 1 / 4,
          Complex.I * (z : ℂ) / 2;
         (-(y * z : ℝ) : ℂ), -Complex.I * (y : ℂ) / 2,
          -Complex.I * (z : ℂ) / 2, 1 / 4] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [historyKernelTensor, pairLeftIndex, pairRightIndex,
      balancedHistoryKernel, Fin.ext_iff, Matrix.cons_val,
      Fin.coe_ofNat_eq_mod, Nat.reduceMod]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

/-- Born weight of one product curvature ket against a two-qubit input. -/
def pairMeasurementWeight (pair : PairKet) (rho : SquareMatrix 4) : ℂ :=
  (pairᴴ * rho * pair) 0 0

set_option maxHeartbeats 400000 in
-- This finite Born contraction expands two nested `Fin 4` matrix sums.
theorem pairMeasurementWeight_positivePositive (y z : ℝ) :
    pairMeasurementWeight positivePositiveKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 - y) * (1 / 2 - z) : ℝ) : ℂ) := by
  rw [historyKernelTensor_balanced_exact]
  norm_num [pairMeasurementWeight, positivePositiveKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.ext_iff,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  rw [starRingEnd_two_complex]
  norm_num
  ring

set_option maxHeartbeats 400000 in
-- This finite Born contraction expands two nested `Fin 4` matrix sums.
theorem pairMeasurementWeight_positiveNegative (y z : ℝ) :
    pairMeasurementWeight positiveNegativeKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 - y) * (1 / 2 + z) : ℝ) : ℂ) := by
  rw [historyKernelTensor_balanced_exact]
  norm_num [pairMeasurementWeight, positiveNegativeKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.ext_iff,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  rw [starRingEnd_two_complex]
  norm_num
  ring

set_option maxHeartbeats 400000 in
-- This finite Born contraction expands two nested `Fin 4` matrix sums.
theorem pairMeasurementWeight_negativePositive (y z : ℝ) :
    pairMeasurementWeight negativePositiveKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 + y) * (1 / 2 - z) : ℝ) : ℂ) := by
  rw [historyKernelTensor_balanced_exact]
  norm_num [pairMeasurementWeight, negativePositiveKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.ext_iff,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  rw [starRingEnd_two_complex]
  norm_num
  ring

set_option maxHeartbeats 400000 in
-- This finite Born contraction expands two nested `Fin 4` matrix sums.
theorem pairMeasurementWeight_negativeNegative (y z : ℝ) :
    pairMeasurementWeight negativeNegativeKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 + y) * (1 / 2 + z) : ℝ) : ℂ) := by
  rw [historyKernelTensor_balanced_exact]
  norm_num [pairMeasurementWeight, negativeNegativeKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_four, Fin.ext_iff,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_fin_one,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod,
    Complex.I_sq]
  ring_nf
  rw [Complex.I_sq]
  rw [starRingEnd_two_complex]
  norm_num
  ring

/-- The four product-curvature outcomes factor into the two one-qubit endpoint
weights.  This is the probability-theoretic core of coherence multiplication. -/
theorem pairMeasurementWeight_balanced (y z : ℝ) :
    pairMeasurementWeight positivePositiveKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 - y) * (1 / 2 - z) : ℝ) : ℂ)
    ∧ pairMeasurementWeight positiveNegativeKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 - y) * (1 / 2 + z) : ℝ) : ℂ)
    ∧ pairMeasurementWeight negativePositiveKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 + y) * (1 / 2 - z) : ℝ) : ℂ)
    ∧ pairMeasurementWeight negativeNegativeKet
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z)) =
      (((1 / 2 + y) * (1 / 2 + z) : ℝ) : ℂ) :=
  ⟨pairMeasurementWeight_positivePositive y z,
    pairMeasurementWeight_positiveNegative y z,
    pairMeasurementWeight_negativePositive y z,
    pairMeasurementWeight_negativeNegative y z⟩

/-- A rank-one measure-and-prepare Kraus term is the measured Born weight times
the prepared pure-state projector. -/
theorem rankOneKraus_apply
    (out : PathKet) (pair : PairKet) (rho : SquareMatrix 4) :
    (out * pairᴴ) * rho * (out * pairᴴ)ᴴ =
      pairMeasurementWeight pair rho • (out * outᴴ) := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  calc
    (out * pairᴴ) * rho * (pair * outᴴ) =
        out * (pairᴴ * rho * pair) * outᴴ := by
          simp only [Matrix.mul_assoc]
    _ = pairMeasurementWeight pair rho • (out * outᴴ) := by
      ext i j
      simp only [Matrix.mul_apply, Fin.sum_univ_one, Fin.isValue,
        pairMeasurementWeight, Matrix.smul_apply, smul_eq_mul]
      ring

theorem orientationRefinement_apply_balanced (y z : ℝ) :
    orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z))
      = balancedHistoryKernel (refinementCompose y z) := by
  obtain ⟨hPP, hPN, hNP, hNN⟩ := pairMeasurementWeight_balanced y z
  unfold orientationRefinementKraus KrausRepresentation.apply
  rw [Fin.sum_univ_four]
  simp only [refinementKrausOperator]
  rw [rankOneKraus_apply, rankOneKraus_apply,
    rankOneKraus_apply, rankOneKraus_apply]
  rw [hPP, hPN, hNP, hNN]
  change _ • ketDensity negativeHolonomyKet +
      _ • ketDensity positiveHolonomyKet +
      _ • ketDensity positiveHolonomyKet +
      _ • ketDensity negativeHolonomyKet = _
  rw [positiveKet_density_eq_projector, negativeKet_density_eq_projector]
  rw [positiveOrientationProjector_exact, negativeOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, refinementCompose, Fin.ext_iff,
      Complex.I_sq] <;> ring

theorem orientationRefinement_multiplies_normalizedCoherence (y z : ℝ) :
    normalizedHistoryCoherence (refinementCompose y z) =
      normalizedHistoryCoherence y * normalizedHistoryCoherence z :=
  normalizedHistoryCoherence_refinementCompose y z

/-! ## 3. Symmetry, endpoint truth table, and rigidity on the balanced sector -/

theorem orientationRefinement_balanced_swap_symmetric (y z : ℝ) :
    orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z))
      = orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel z) (balancedHistoryKernel y)) := by
  rw [orientationRefinement_apply_balanced,
    orientationRefinement_apply_balanced, refinementCompose_comm]

theorem orientationRefinement_balanced_reflection_equivariant (y z : ℝ) :
    orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel (-y)) (balancedHistoryKernel z))
      = pathHistoryReflection
        (orientationRefinementKraus.apply
          (historyKernelTensor (balancedHistoryKernel y) (balancedHistoryKernel z))) := by
  rw [orientationRefinement_apply_balanced, orientationRefinement_apply_balanced,
    pathHistoryReflection_balancedHistoryKernel]
  congr 1
  simp [refinementCompose]

theorem orientationRefinement_endpoint_truth_table :
    orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel (-1 / 2))
          (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (1 / 2)
    ∧ orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel (-1 / 2))
          (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (-1 / 2)
    ∧ orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel (1 / 2))
          (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (-1 / 2)
    ∧ orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel (1 / 2))
          (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (1 / 2) := by
  simp only [orientationRefinement_apply_balanced]
  norm_num [refinementCompose]

/-- The rigidity interval written directly as an affine combination of its two
pure endpoints, with complex scalars so a complex-linear channel can consume
the identity without a scalar-tower detour. -/
theorem balancedHistoryKernel_endpoint_affine (y : ℝ) :
    balancedHistoryKernel y =
      (((1 / 2 - y : ℝ) : ℂ) • balancedHistoryKernel (-1 / 2)) +
        (((1 / 2 + y : ℝ) : ℂ) • balancedHistoryKernel (1 / 2)) := by
  rw [balancedHistoryKernel_negativeEndpoint,
    balancedHistoryKernel_positiveEndpoint]
  exact balancedHistoryKernel_projector_mixture y

/-- Bilinearity of the reindexed tensor product, packaged in the exact
four-corner form used by the channel rigidity proof. -/
theorem historyKernelTensor_four_corner
    (a b c d : ℂ) (rho0 rho1 sigma0 sigma1 : SquareMatrix 2) :
    historyKernelTensor (a • rho0 + b • rho1) (c • sigma0 + d • sigma1) =
      (a * c) • historyKernelTensor rho0 sigma0 +
      (a * d) • historyKernelTensor rho0 sigma1 +
      (b * c) • historyKernelTensor rho1 sigma0 +
      (b * d) • historyKernelTensor rho1 sigma1 := by
  ext i j
  simp only [historyKernelTensor, Matrix.add_apply, Matrix.smul_apply,
    smul_eq_mul]
  ring

/-- **Balanced-sector channel rigidity.**  A complex-linear map is fixed on
the complete balanced product sector by only four pure-state values.  If those
values implement the orientation parity truth table, the full nonlinear-looking
parameter law `y ⋆ z = 2yz` follows from ordinary tensor bilinearity and channel
linearity.  No agreement hypothesis on mixed inputs is assumed. -/
theorem balancedSector_refinementChannel_rigidity
    (Psi : SquareMatrix 4 →ₗ[ℂ] SquareMatrix 2)
    (hNN : Psi (historyKernelTensor (balancedHistoryKernel (-1 / 2))
        (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (1 / 2))
    (hNP : Psi (historyKernelTensor (balancedHistoryKernel (-1 / 2))
        (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (-1 / 2))
    (hPN : Psi (historyKernelTensor (balancedHistoryKernel (1 / 2))
        (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (-1 / 2))
    (hPP : Psi (historyKernelTensor (balancedHistoryKernel (1 / 2))
        (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (1 / 2)) :
    ∀ y z : ℝ,
      Psi (historyKernelTensor (balancedHistoryKernel y)
        (balancedHistoryKernel z)) =
      balancedHistoryKernel (refinementCompose y z) := by
  intro y z
  rw [balancedHistoryKernel_endpoint_affine y,
    balancedHistoryKernel_endpoint_affine z,
    historyKernelTensor_four_corner]
  simp only [map_add, map_smul]
  rw [hNN, hNP, hPN, hPP]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [balancedHistoryKernel, refinementCompose, Fin.ext_iff,
      Complex.I_sq] <;> ring

/-- Any linear channel with the same four pure endpoint outputs agrees with the
constructed CPTP channel on every product of balanced kernels. -/
theorem balancedSector_refinementChannel_unique
    (Psi : SquareMatrix 4 →ₗ[ℂ] SquareMatrix 2)
    (hNN : Psi (historyKernelTensor (balancedHistoryKernel (-1 / 2))
        (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (1 / 2))
    (hNP : Psi (historyKernelTensor (balancedHistoryKernel (-1 / 2))
        (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (-1 / 2))
    (hPN : Psi (historyKernelTensor (balancedHistoryKernel (1 / 2))
        (balancedHistoryKernel (-1 / 2))) = balancedHistoryKernel (-1 / 2))
    (hPP : Psi (historyKernelTensor (balancedHistoryKernel (1 / 2))
        (balancedHistoryKernel (1 / 2))) = balancedHistoryKernel (1 / 2)) :
    ∀ y z : ℝ,
      Psi (historyKernelTensor (balancedHistoryKernel y)
        (balancedHistoryKernel z)) =
      orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel y)
          (balancedHistoryKernel z)) := by
  intro y z
  rw [balancedSector_refinementChannel_rigidity Psi hNN hNP hPN hPP,
    orientationRefinement_apply_balanced]

/-- Associativity has an operational channel form: either binary bracketing of
three independent balanced inputs gives exactly the same output density matrix. -/
theorem orientationRefinement_balanced_associative (x y z : ℝ) :
    orientationRefinementKraus.apply
        (historyKernelTensor
          (orientationRefinementKraus.apply
            (historyKernelTensor (balancedHistoryKernel x)
              (balancedHistoryKernel y)))
          (balancedHistoryKernel z)) =
      orientationRefinementKraus.apply
        (historyKernelTensor (balancedHistoryKernel x)
          (orientationRefinementKraus.apply
            (historyKernelTensor (balancedHistoryKernel y)
              (balancedHistoryKernel z)))) := by
  rw [orientationRefinement_apply_balanced,
    orientationRefinement_apply_balanced,
    orientationRefinement_apply_balanced,
    orientationRefinement_apply_balanced,
    refinementCompose_assoc]

/-- The channel realization promotes the former conditional law to a theorem
of finite quantum dynamics.  It does not assert that causal-set refinement is
this channel. -/
theorem finite_CPTP_refinement_realization :
    IsCPTP orientationRefinementKraus.toLinearMap
    ∧ (∀ y z : ℝ,
      orientationRefinementKraus.apply
          (historyKernelTensor (balancedHistoryKernel y)
            (balancedHistoryKernel z)) =
        balancedHistoryKernel (refinementCompose y z))
    ∧ (∀ y z : ℝ,
      orientationRefinementKraus.apply
          (historyKernelTensor (balancedHistoryKernel (-y))
            (balancedHistoryKernel z)) =
        pathHistoryReflection
          (orientationRefinementKraus.apply
            (historyKernelTensor (balancedHistoryKernel y)
              (balancedHistoryKernel z)))) := by
  exact ⟨orientationRefinement_isCPTP,
    orientationRefinement_apply_balanced,
    orientationRefinement_balanced_reflection_equivariant⟩

#print axioms refinementKraus_complete
#print axioms orientationRefinement_isCPTP
#print axioms orientationRefinement_apply_balanced
#print axioms orientationRefinement_balanced_reflection_equivariant
#print axioms orientationRefinement_endpoint_truth_table
#print axioms balancedSector_refinementChannel_rigidity
#print axioms balancedSector_refinementChannel_unique
#print axioms orientationRefinement_balanced_associative
#print axioms finite_CPTP_refinement_realization

end

end UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel
