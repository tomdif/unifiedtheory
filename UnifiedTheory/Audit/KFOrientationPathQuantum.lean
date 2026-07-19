/-
  Audit/KFOrientationPathQuantum.lean

  QUANTUM PROMOTION OF THE FINITE ORIENTATION PATH HOLONOMY

  The preceding tower audit found that the difference between two exact
  quotient routes Hermitianizes to Pauli Y.  This file asks how far that fact
  can be promoted without adding hidden physical assumptions.

  The answer is an exact finite two-level quantum sector:

  * the two quotient routes form an orthonormal path basis;
  * the two holonomy signs have normalized eigenkets with relative phase ±i;
  * either definite path gives Born weights 1/2 for both holonomy signs;
  * either holonomy eigenket gives a deterministic sign;
  * route-basis dephasing erases the sign, which lives only in an imaginary
    off-diagonal history phase;
  * route, curvature, and coherence close the full Pauli algebra with
    spin-half Casimir `3/4`;
  * spin-half transport changes ket sign at `2*pi`, returns it at `4*pi`,
    and leaves density matrices invariant already at `2*pi`;
  * the holonomy generates an exact real rotation mixing the two paths;
  * this evolution is unitary and conserves both holonomy projectors;
  * the independently derived cubic chirality sign selects the same two
    projectors on the explicit reflected witness pair.

  This proves a finite quantum-compatible spinor orientation sector.  It does not
  derive quantum amplitudes over physical causal-set histories, select the
  evolution parameter as time or scale, or identify the sector with a fermion,
  gauge charge, or continuum field.
-/

import UnifiedTheory.Audit.KFOrientationCPChannelTower
import UnifiedTheory.Audit.KFOrientationSpinOneRelational

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationPathQuantum

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationQuantumConsequences
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationSpinOneRelational

abbrev PathKet := Matrix (Fin 2) (Fin 1) ℂ

/-! ## 1. Exact path and holonomy bases -/

def path13Ket : PathKet :=
  !![(1 : ℂ); 0]

def path22Ket : PathKet :=
  !![(0 : ℂ); 1]

def positiveHolonomyKet : PathKet :=
  !![((1 / spinOneSqrtTwo : ℝ) : ℂ);
     Complex.I * ((1 / spinOneSqrtTwo : ℝ) : ℂ)]

def negativeHolonomyKet : PathKet :=
  !![((1 / spinOneSqrtTwo : ℝ) : ℂ);
     -Complex.I * ((1 / spinOneSqrtTwo : ℝ) : ℂ)]

def ketInner (psi phi : PathKet) : ℂ :=
  (psiᴴ * phi) 0 0

def ketDensity (psi : PathKet) : SquareMatrix 2 :=
  psi * psiᴴ

theorem path13Ket_normalized : ketInner path13Ket path13Ket = 1 := by
  norm_num [ketInner, path13Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem path22Ket_normalized : ketInner path22Ket path22Ket = 1 := by
  norm_num [ketInner, path22Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem pathKets_orthogonal : ketInner path13Ket path22Ket = 0 := by
  norm_num [ketInner, path13Ket, path22Ket, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem positiveHolonomyKet_normalized :
    ketInner positiveHolonomyKet positiveHolonomyKet = 1 := by
  norm_num [ketInner, positiveHolonomyKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff,
    Complex.I_sq]
  field_simp [spinOneSqrtTwo_ne_zero]
  norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

theorem negativeHolonomyKet_normalized :
    ketInner negativeHolonomyKet negativeHolonomyKet = 1 := by
  norm_num [ketInner, negativeHolonomyKet, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff,
    Complex.I_sq]
  field_simp [spinOneSqrtTwo_ne_zero]
  norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

theorem holonomyKets_orthogonal :
    ketInner positiveHolonomyKet negativeHolonomyKet = 0 := by
  norm_num [ketInner, positiveHolonomyKet, negativeHolonomyKet,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_succ,
    Fin.ext_iff, Complex.I_sq]
  field_simp [spinOneSqrtTwo_ne_zero]
  norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

theorem positiveHolonomyKet_path_superposition :
    positiveHolonomyKet =
      ((1 / spinOneSqrtTwo : ℝ) : ℂ) • path13Ket +
        (Complex.I * ((1 / spinOneSqrtTwo : ℝ) : ℂ)) • path22Ket := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveHolonomyKet, path13Ket, path22Ket, Fin.ext_iff]

theorem negativeHolonomyKet_path_superposition :
    negativeHolonomyKet =
      ((1 / spinOneSqrtTwo : ℝ) : ℂ) • path13Ket -
        (Complex.I * ((1 / spinOneSqrtTwo : ℝ) : ℂ)) • path22Ket := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [negativeHolonomyKet, path13Ket, path22Ket, Fin.ext_iff]

theorem positiveOrientationProjector_exact :
    positiveOrientationProjector =
      !![(1 / 2 : ℂ), -Complex.I / 2;
         Complex.I / 2, 1 / 2] := by
  unfold positiveOrientationProjector
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] <;> ring

theorem negativeOrientationProjector_exact :
    negativeOrientationProjector =
      !![(1 / 2 : ℂ), Complex.I / 2;
         -Complex.I / 2, 1 / 2] := by
  unfold negativeOrientationProjector
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [Fin.ext_iff] <;> ring

theorem positiveKet_density_eq_projector :
    ketDensity positiveHolonomyKet = positiveOrientationProjector := by
  rw [positiveOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ketDensity, positiveHolonomyKet, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.I_sq]
  all_goals
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

theorem negativeKet_density_eq_projector :
    ketDensity negativeHolonomyKet = negativeOrientationProjector := by
  rw [negativeOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [ketDensity, negativeHolonomyKet, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff,
      Complex.I_sq]
  all_goals
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    norm_num [← pow_two, spinOneSqrtTwo_sq_complex]

theorem quotientCurvature_positiveKet :
    quotientCurvatureHamiltonian * positiveHolonomyKet =
      positiveHolonomyKet := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [positiveHolonomyKet, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem quotientCurvature_negativeKet :
    quotientCurvatureHamiltonian * negativeHolonomyKet =
      -negativeHolonomyKet := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [negativeHolonomyKet, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals rw [← mul_assoc, Complex.I_mul_I]
  all_goals ring

/-! ## 2. Honest density matrices and Born complementarity -/

def IsPathDensity (rho : SquareMatrix 2) : Prop :=
  rho.IsHermitian ∧ rho.PosSemidef ∧ Matrix.trace rho = 1

theorem ketDensity_isHermitian (psi : PathKet) :
    (ketDensity psi).IsHermitian := by
  exact Matrix.isHermitian_mul_conjTranspose_self psi

theorem ketDensity_posSemidef (psi : PathKet) :
    (ketDensity psi).PosSemidef := by
  exact Matrix.posSemidef_self_mul_conjTranspose psi

theorem ketDensity_trace (psi : PathKet) :
    Matrix.trace (ketDensity psi) = ketInner psi psi := by
  unfold ketDensity ketInner
  rw [Matrix.trace_mul_comm]
  simp [Matrix.trace]

theorem ketDensity_isPathDensity_of_normalized
    (psi : PathKet) (hpsi : ketInner psi psi = 1) :
    IsPathDensity (ketDensity psi) := by
  exact ⟨ketDensity_isHermitian psi,
    ketDensity_posSemidef psi,
    (ketDensity_trace psi).trans hpsi⟩

def path13Density : SquareMatrix 2 := ketDensity path13Ket

def path22Density : SquareMatrix 2 := ketDensity path22Ket

theorem path13Density_exact :
    path13Density = !![(1 : ℂ), 0; 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path13Density, ketDensity, path13Ket, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem path22Density_exact :
    path22Density = !![(0 : ℂ), 0; 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [path22Density, ketDensity, path22Ket, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ, Fin.ext_iff]

theorem path13Density_isPathDensity : IsPathDensity path13Density := by
  exact ketDensity_isPathDensity_of_normalized path13Ket
    path13Ket_normalized

theorem path22Density_isPathDensity : IsPathDensity path22Density := by
  exact ketDensity_isPathDensity_of_normalized path22Ket
    path22Ket_normalized

theorem positiveOrientationProjector_isPathDensity :
    IsPathDensity positiveOrientationProjector := by
  rw [← positiveKet_density_eq_projector]
  exact ketDensity_isPathDensity_of_normalized positiveHolonomyKet
    positiveHolonomyKet_normalized

theorem negativeOrientationProjector_isPathDensity :
    IsPathDensity negativeOrientationProjector := by
  rw [← negativeKet_density_eq_projector]
  exact ketDensity_isPathDensity_of_normalized negativeHolonomyKet
    negativeHolonomyKet_normalized

/-- Real Born weight `Re Tr(rho P)` for the finite path sector. -/
def bornWeight (rho projector : SquareMatrix 2) : ℝ :=
  (Matrix.trace (rho * projector)).re

theorem path13_positive_bornWeight :
    bornWeight path13Density positiveOrientationProjector = 1 / 2 := by
  rw [positiveOrientationProjector_exact]
  rw [path13Density_exact]
  norm_num [bornWeight, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.ext_iff]

theorem path13_negative_bornWeight :
    bornWeight path13Density negativeOrientationProjector = 1 / 2 := by
  rw [negativeOrientationProjector_exact]
  rw [path13Density_exact]
  norm_num [bornWeight, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.ext_iff]

theorem path22_positive_bornWeight :
    bornWeight path22Density positiveOrientationProjector = 1 / 2 := by
  rw [positiveOrientationProjector_exact]
  rw [path22Density_exact]
  norm_num [bornWeight, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.ext_iff]

theorem path22_negative_bornWeight :
    bornWeight path22Density negativeOrientationProjector = 1 / 2 := by
  rw [negativeOrientationProjector_exact]
  rw [path22Density_exact]
  norm_num [bornWeight, Matrix.trace, Matrix.mul_apply,
    Fin.sum_univ_succ, Fin.ext_iff]

theorem positiveHolonomy_born_deterministic :
    bornWeight positiveOrientationProjector positiveOrientationProjector = 1
      ∧ bornWeight positiveOrientationProjector
          negativeOrientationProjector = 0 := by
  constructor
  · unfold bornWeight
    rw [positiveOrientationProjector_idempotent,
      positiveOrientationProjector_trace]
    norm_num
  · unfold bornWeight
    rw [orientationProjectors_orthogonal]
    norm_num

theorem negativeHolonomy_born_deterministic :
    bornWeight negativeOrientationProjector negativeOrientationProjector = 1
      ∧ bornWeight negativeOrientationProjector
          positiveOrientationProjector = 0 := by
  constructor
  · unfold bornWeight
    rw [negativeOrientationProjector_idempotent,
      negativeOrientationProjector_trace]
    norm_num
  · unfold bornWeight
    rw [negativeOrientationProjector_exact,
      positiveOrientationProjector_exact]
    norm_num [Matrix.trace, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ext_iff, Complex.I_sq]

/-- A definite quotient route is maximally unbiased with respect to the
binary orientation holonomy, whereas a holonomy eigenstate is deterministic. -/
theorem path_holonomy_complementarity :
    bornWeight path13Density positiveOrientationProjector = 1 / 2
      ∧ bornWeight path13Density negativeOrientationProjector = 1 / 2
      ∧ bornWeight path22Density positiveOrientationProjector = 1 / 2
      ∧ bornWeight path22Density negativeOrientationProjector = 1 / 2
      ∧ bornWeight positiveOrientationProjector
          positiveOrientationProjector = 1
      ∧ bornWeight positiveOrientationProjector
          negativeOrientationProjector = 0
      ∧ bornWeight negativeOrientationProjector
          negativeOrientationProjector = 1
      ∧ bornWeight negativeOrientationProjector
          positiveOrientationProjector = 0 := by
  exact ⟨path13_positive_bornWeight,
    path13_negative_bornWeight,
    path22_positive_bornWeight,
    path22_negative_bornWeight,
    positiveHolonomy_born_deterministic.1,
    positiveHolonomy_born_deterministic.2,
    negativeHolonomy_born_deterministic.1,
    negativeHolonomy_born_deterministic.2⟩

/-! ## 3. Orientation is stored in path coherence -/

/-- Complete dephasing in the two-route basis. -/
def pathDephase (rho : SquareMatrix 2) : SquareMatrix 2 :=
  !![rho 0 0, 0;
     0, rho 1 1]

theorem pathDephase_positiveOrientation :
    pathDephase positiveOrientationProjector = (1 / 2 : ℂ) • 1 := by
  rw [positiveOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathDephase, Fin.ext_iff]

theorem pathDephase_negativeOrientation :
    pathDephase negativeOrientationProjector = (1 / 2 : ℂ) • 1 := by
  rw [negativeOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathDephase, Fin.ext_iff]

theorem dephased_orientation_born_half :
    bornWeight (pathDephase positiveOrientationProjector)
        positiveOrientationProjector = 1 / 2
      ∧ bornWeight (pathDephase positiveOrientationProjector)
          negativeOrientationProjector = 1 / 2
      ∧ bornWeight (pathDephase negativeOrientationProjector)
          positiveOrientationProjector = 1 / 2
      ∧ bornWeight (pathDephase negativeOrientationProjector)
          negativeOrientationProjector = 1 / 2 := by
  rw [pathDephase_positiveOrientation, pathDephase_negativeOrientation]
  unfold bornWeight
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.trace_smul,
    positiveOrientationProjector_trace,
    negativeOrientationProjector_trace]
  norm_num

/-- The binary sign is pure inter-path coherence: route-basis dephasing maps
both signs to the same maximally mixed state and erases their distinction. -/
theorem orientation_holonomy_requires_path_coherence :
    positiveOrientationProjector ≠ negativeOrientationProjector
      ∧ pathDephase positiveOrientationProjector =
          pathDephase negativeOrientationProjector
      ∧ bornWeight (pathDephase positiveOrientationProjector)
          positiveOrientationProjector = 1 / 2
      ∧ bornWeight (pathDephase positiveOrientationProjector)
          negativeOrientationProjector = 1 / 2 := by
  constructor
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    rw [positiveOrientationProjector_exact] at h01
    rw [negativeOrientationProjector_exact] at h01
    norm_num at h01
    have him := congrArg Complex.im h01
    norm_num at him
  · exact ⟨pathDephase_positiveOrientation.trans
        pathDephase_negativeOrientation.symm,
      dephased_orientation_born_half.1,
      dephased_orientation_born_half.2.1⟩

/-! ## 3b. The sign is an imaginary history phase -/

/-- The finite decoherence kernel of the two refinement histories.  At this
level it is simply the density matrix written in the route basis. -/
def pathHistoryKernel (rho : SquareMatrix 2) (p q : Fin 2) : ℂ :=
  rho p q

/-- The quantum measure of a finite set of refinement histories, obtained by
summing the real part of its decoherence kernel. -/
def pathHistoryMeasure (rho : SquareMatrix 2) (event : Finset (Fin 2)) : ℝ :=
  ∑ p ∈ event, ∑ q ∈ event, (pathHistoryKernel rho p q).re

/-- The complete real parts of the two orientation decoherence kernels agree.
Consequently no route event measure can distinguish the signs. -/
theorem orientation_projectors_same_real_history_kernel
    (p q : Fin 2) :
    (pathHistoryKernel positiveOrientationProjector p q).re =
      (pathHistoryKernel negativeOrientationProjector p q).re := by
  rw [positiveOrientationProjector_exact,
    negativeOrientationProjector_exact]
  fin_cases p <;> fin_cases q <;>
    norm_num [pathHistoryKernel, Fin.ext_iff]

theorem orientation_projectors_same_history_measure
    (event : Finset (Fin 2)) :
    pathHistoryMeasure positiveOrientationProjector event =
      pathHistoryMeasure negativeOrientationProjector event := by
  unfold pathHistoryMeasure
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact orientation_projectors_same_real_history_kernel p q

/-- The missing sign is precisely the imaginary ordered inter-path
coherence: reflection reverses its sign. -/
theorem orientation_projectors_opposite_imaginary_history_phase :
    (pathHistoryKernel positiveOrientationProjector 1 0).im = 1 / 2
      ∧ (pathHistoryKernel negativeOrientationProjector 1 0).im = -1 / 2 := by
  rw [positiveOrientationProjector_exact,
    negativeOrientationProjector_exact]
  norm_num [pathHistoryKernel, Fin.ext_iff]

/-- Every real-valued history event has the same measure in both sectors,
while the full complex decoherence kernels remain distinct.  The binary
orientation is therefore a phase observable, not a classical route label. -/
theorem orientation_sign_is_imaginary_history_phase :
    (∀ event : Finset (Fin 2),
      pathHistoryMeasure positiveOrientationProjector event =
        pathHistoryMeasure negativeOrientationProjector event)
      ∧ positiveOrientationProjector ≠ negativeOrientationProjector
      ∧ (pathHistoryKernel positiveOrientationProjector 1 0).im = 1 / 2
      ∧ (pathHistoryKernel negativeOrientationProjector 1 0).im = -1 / 2 := by
  exact ⟨orientation_projectors_same_history_measure,
    orientation_holonomy_requires_path_coherence.1,
    orientation_projectors_opposite_imaginary_history_phase.1,
    orientation_projectors_opposite_imaginary_history_phase.2⟩

/-! ## 4. The full path-qubit and spin-half algebra -/

/-- Which quotient route was taken: `+1` for `(1,3)`, `-1` for `(2,2)`. -/
def pathRouteObservable : SquareMatrix 2 :=
  !![(1 : ℂ), 0;
     0, -1]

/-- Coherence between the two route labels. -/
def pathCoherenceObservable : SquareMatrix 2 :=
  !![(0 : ℂ), 1;
     1, 0]

def pathCommutator (A B : SquareMatrix 2) : SquareMatrix 2 :=
  A * B - B * A

theorem pathPauli_X_sq :
    pathCoherenceObservable * pathCoherenceObservable = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathCoherenceObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]

theorem pathPauli_Y_sq :
    quotientCurvatureHamiltonian * quotientCurvatureHamiltonian = 1 :=
  quotientCurvatureHamiltonian_sq

theorem pathPauli_Z_sq :
    pathRouteObservable * pathRouteObservable = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathRouteObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]

theorem pathPauli_XY_commutator :
    pathCommutator pathCoherenceObservable
        quotientCurvatureHamiltonian =
      (2 * Complex.I) • pathRouteObservable := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathCommutator, pathCoherenceObservable,
      pathRouteObservable, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ext_iff, Complex.I_sq] <;> ring

theorem pathPauli_YZ_commutator :
    pathCommutator quotientCurvatureHamiltonian
        pathRouteObservable =
      (2 * Complex.I) • pathCoherenceObservable := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathCommutator, pathCoherenceObservable,
      pathRouteObservable, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ext_iff, Complex.I_sq] <;> ring

theorem pathPauli_ZX_commutator :
    pathCommutator pathRouteObservable pathCoherenceObservable =
      (2 * Complex.I) • quotientCurvatureHamiltonian := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathCommutator, pathCoherenceObservable,
      pathRouteObservable, Matrix.mul_apply, Fin.sum_univ_succ,
      Fin.ext_iff]
  all_goals ring_nf
  all_goals try rw [Complex.I_sq]
  all_goals ring

/-- Route and curvature generate the missing coherence observable. -/
theorem route_and_holonomy_generate_coherence :
    (-Complex.I / 2) •
        pathCommutator quotientCurvatureHamiltonian pathRouteObservable =
      pathCoherenceObservable := by
  rw [pathPauli_YZ_commutator]
  simp only [smul_smul]
  ring_nf
  rw [Complex.I_sq]
  module

def pathSpinX : SquareMatrix 2 :=
  (1 / 2 : ℂ) • pathCoherenceObservable

def pathSpinY : SquareMatrix 2 :=
  (1 / 2 : ℂ) • quotientCurvatureHamiltonian

def pathSpinZ : SquareMatrix 2 :=
  (1 / 2 : ℂ) • pathRouteObservable

theorem pathSpin_commutator_XY :
    pathCommutator pathSpinX pathSpinY = Complex.I • pathSpinZ := by
  unfold pathSpinX pathSpinY pathSpinZ pathCommutator
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathSpinX, pathSpinY, pathSpinZ, pathCommutator,
      pathCoherenceObservable, pathRouteObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring

theorem pathSpin_commutator_YZ :
    pathCommutator pathSpinY pathSpinZ = Complex.I • pathSpinX := by
  unfold pathSpinX pathSpinY pathSpinZ pathCommutator
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathSpinX, pathSpinY, pathSpinZ, pathCommutator,
      pathCoherenceObservable, pathRouteObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring

theorem pathSpin_commutator_ZX :
    pathCommutator pathSpinZ pathSpinX = Complex.I • pathSpinY := by
  unfold pathSpinX pathSpinY pathSpinZ pathCommutator
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathSpinX, pathSpinY, pathSpinZ, pathCommutator,
      pathCoherenceObservable, pathRouteObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem pathSpin_casimir :
    pathSpinX * pathSpinX + pathSpinY * pathSpinY +
        pathSpinZ * pathSpinZ = (3 / 4 : ℂ) • 1 := by
  unfold pathSpinX pathSpinY pathSpinZ
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathSpinX, pathSpinY, pathSpinZ,
      pathCoherenceObservable, pathRouteObservable, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- Explicit Pauli coordinates for every operator on the two-path space. -/
def pathPauliCoeff0 (A : SquareMatrix 2) : ℂ :=
  (A 0 0 + A 1 1) / 2

def pathPauliCoeffX (A : SquareMatrix 2) : ℂ :=
  (A 0 1 + A 1 0) / 2

def pathPauliCoeffY (A : SquareMatrix 2) : ℂ :=
  (Complex.I / 2) * (A 0 1 - A 1 0)

def pathPauliCoeffZ (A : SquareMatrix 2) : ℂ :=
  (A 0 0 - A 1 1) / 2

/-- The route observable and its curvature-generated coherence close to the
complete `M_2(C)` operator algebra. -/
theorem pathPauli_decomposition (A : SquareMatrix 2) :
    A = pathPauliCoeff0 A • 1 +
      pathPauliCoeffX A • pathCoherenceObservable +
      pathPauliCoeffY A • quotientCurvatureHamiltonian +
      pathPauliCoeffZ A • pathRouteObservable := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [pathPauliCoeff0, pathPauliCoeffX, pathPauliCoeffY,
      pathPauliCoeffZ, pathCoherenceObservable, pathRouteObservable,
      Fin.ext_iff]
  all_goals field_simp
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

/-- Exact spin-half synthesis, conditional only on interpreting the two route
labels as a coherent quantum alternative. -/
theorem finite_path_spin_half_algebra :
    pathCommutator pathSpinX pathSpinY = Complex.I • pathSpinZ
      ∧ pathCommutator pathSpinY pathSpinZ = Complex.I • pathSpinX
      ∧ pathCommutator pathSpinZ pathSpinX = Complex.I • pathSpinY
      ∧ pathSpinX * pathSpinX + pathSpinY * pathSpinY +
          pathSpinZ * pathSpinZ = (3 / 4 : ℂ) • 1
      ∧ (∀ A : SquareMatrix 2,
          A = pathPauliCoeff0 A • 1 +
            pathPauliCoeffX A • pathCoherenceObservable +
            pathPauliCoeffY A • quotientCurvatureHamiltonian +
            pathPauliCoeffZ A • pathRouteObservable) :=
  ⟨pathSpin_commutator_XY,
    pathSpin_commutator_YZ,
    pathSpin_commutator_ZX,
    pathSpin_casimir,
    pathPauli_decomposition⟩

/-! ## 5. Exact unitary path mixing generated by holonomy -/

/-- The curvature-generated evolution.  The exact matrix is a real rotation
because `-i sigma_y` is the real antisymmetric generator. -/
def holonomyEvolution (t : ℝ) : SquareMatrix 2 :=
  !![((Real.cos t : ℝ) : ℂ), ((-Real.sin t : ℝ) : ℂ);
     ((Real.sin t : ℝ) : ℂ), ((Real.cos t : ℝ) : ℂ)]

theorem holonomyEvolution_generator_form (t : ℝ) :
    holonomyEvolution t =
      (Real.cos t : ℂ) • 1 -
        (Complex.I * Real.sin t) • quotientCurvatureHamiltonian := by
  rw [quotientCurvatureHamiltonian_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Fin.ext_iff]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem holonomyEvolution_conjTranspose (t : ℝ) :
    (holonomyEvolution t)ᴴ = holonomyEvolution (-t) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Matrix.conjTranspose_apply,
      Real.cos_neg, Real.sin_neg, Fin.ext_iff, Complex.star_def,
      ← Complex.ofReal_cos, ← Complex.ofReal_sin]

theorem holonomyEvolution_unitary (t : ℝ) :
    (holonomyEvolution t)ᴴ * holonomyEvolution t = 1 := by
  rw [holonomyEvolution_conjTranspose]
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    apply Complex.ext <;>
      norm_num [holonomyEvolution, Matrix.mul_apply,
        Fin.sum_univ_succ, Real.cos_neg, Real.sin_neg, Fin.ext_iff,
        ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  all_goals
    nlinarith [Real.sin_sq_add_cos_sq t]

theorem holonomyEvolution_add (t u : ℝ) :
    holonomyEvolution (t + u) =
      holonomyEvolution t * holonomyEvolution u := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Matrix.mul_apply, Fin.sum_univ_succ,
      Real.sin_add, Real.cos_add, Fin.ext_iff] <;> ring

theorem holonomyEvolution_zero : holonomyEvolution 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Fin.ext_iff]

theorem holonomyEvolution_inverse (t : ℝ) :
    holonomyEvolution (-t) * holonomyEvolution t = 1 := by
  rw [← holonomyEvolution_add]
  simp [holonomyEvolution_zero]

/-- Spin-half parameterization: `exp(-i theta sigma_y/2)`. -/
def pathSpinHalfEvolution (theta : ℝ) : SquareMatrix 2 :=
  holonomyEvolution (theta / 2)

theorem pathSpinHalfEvolution_unitary (theta : ℝ) :
    (pathSpinHalfEvolution theta)ᴴ * pathSpinHalfEvolution theta = 1 :=
  holonomyEvolution_unitary (theta / 2)

theorem pathSpinHalfEvolution_add (theta phi : ℝ) :
    pathSpinHalfEvolution (theta + phi) =
      pathSpinHalfEvolution theta * pathSpinHalfEvolution phi := by
  unfold pathSpinHalfEvolution
  rw [show (theta + phi) / 2 = theta / 2 + phi / 2 by ring,
    holonomyEvolution_add]

theorem pathSpinHalfEvolution_two_pi :
    pathSpinHalfEvolution (2 * Real.pi) = -1 := by
  unfold pathSpinHalfEvolution
  rw [show (2 * Real.pi) / 2 = Real.pi by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Real.cos_pi, Real.sin_pi, Fin.ext_iff]

theorem pathSpinHalfEvolution_four_pi :
    pathSpinHalfEvolution (4 * Real.pi) = 1 := by
  unfold pathSpinHalfEvolution
  rw [show (4 * Real.pi) / 2 = 2 * Real.pi by ring]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, Real.cos_two_pi, Real.sin_two_pi,
      Fin.ext_iff]

theorem pathSpinHalfEvolution_two_pi_ket (psi : PathKet) :
    pathSpinHalfEvolution (2 * Real.pi) * psi = -psi := by
  rw [pathSpinHalfEvolution_two_pi]
  simp

theorem pathSpinHalfEvolution_four_pi_ket (psi : PathKet) :
    pathSpinHalfEvolution (4 * Real.pi) * psi = psi := by
  rw [pathSpinHalfEvolution_four_pi]
  simp

def pathSpinHalfEvolveDensity (theta : ℝ)
    (rho : SquareMatrix 2) : SquareMatrix 2 :=
  pathSpinHalfEvolution theta * rho * (pathSpinHalfEvolution theta)ᴴ

/-- A full `2*pi` rotation changes ket sign but leaves every density matrix
unchanged; `4*pi` returns the ket itself. -/
theorem pathSpinHalf_two_pi_density_invariant (rho : SquareMatrix 2) :
    pathSpinHalfEvolveDensity (2 * Real.pi) rho = rho := by
  unfold pathSpinHalfEvolveDensity
  rw [pathSpinHalfEvolution_two_pi]
  simp

theorem finite_path_spinor_periodicity (psi : PathKet)
    (rho : SquareMatrix 2) :
    pathSpinHalfEvolution (2 * Real.pi) * psi = -psi
      ∧ pathSpinHalfEvolution (4 * Real.pi) * psi = psi
      ∧ pathSpinHalfEvolveDensity (2 * Real.pi) rho = rho :=
  ⟨pathSpinHalfEvolution_two_pi_ket psi,
    pathSpinHalfEvolution_four_pi_ket psi,
    pathSpinHalf_two_pi_density_invariant rho⟩

theorem holonomyEvolution_path13 (t : ℝ) :
    holonomyEvolution t * path13Ket =
      !![((Real.cos t : ℝ) : ℂ); ((Real.sin t : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, path13Ket, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]

theorem holonomyEvolution_path22 (t : ℝ) :
    holonomyEvolution t * path22Ket =
      !![((-Real.sin t : ℝ) : ℂ); ((Real.cos t : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [holonomyEvolution, path22Ket, Matrix.mul_apply,
      Fin.sum_univ_succ, Fin.ext_iff]

theorem holonomyEvolution_halfTurn_path_swap :
    holonomyEvolution (Real.pi / 2) * path13Ket = path22Ket
      ∧ holonomyEvolution (Real.pi / 2) * path22Ket = -path13Ket := by
  constructor
  · rw [holonomyEvolution_path13]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [path22Ket, Real.cos_pi_div_two,
        Real.sin_pi_div_two, Fin.ext_iff]
  · rw [holonomyEvolution_path22]
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [path13Ket, Real.cos_pi_div_two,
        Real.sin_pi_div_two, Fin.ext_iff]

theorem holonomyEvolution_commutes_curvature (t : ℝ) :
    holonomyEvolution t * quotientCurvatureHamiltonian =
      quotientCurvatureHamiltonian * holonomyEvolution t := by
  rw [holonomyEvolution_generator_form]
  noncomm_ring

theorem holonomyEvolution_preserves_positiveProjector (t : ℝ) :
    (holonomyEvolution t)ᴴ * positiveOrientationProjector *
        holonomyEvolution t = positiveOrientationProjector := by
  have hComm : holonomyEvolution t * positiveOrientationProjector =
      positiveOrientationProjector * holonomyEvolution t := by
    unfold positiveOrientationProjector
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add,
      Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
    rw [holonomyEvolution_commutes_curvature]
  calc
    (holonomyEvolution t)ᴴ * positiveOrientationProjector *
          holonomyEvolution t =
        (holonomyEvolution t)ᴴ *
          (positiveOrientationProjector * holonomyEvolution t) := by
            rw [Matrix.mul_assoc]
    _ = (holonomyEvolution t)ᴴ *
          (holonomyEvolution t * positiveOrientationProjector) := by
            rw [hComm]
    _ = ((holonomyEvolution t)ᴴ * holonomyEvolution t) *
          positiveOrientationProjector := by
            rw [Matrix.mul_assoc]
    _ = positiveOrientationProjector := by
      rw [holonomyEvolution_unitary, Matrix.one_mul]

theorem holonomyEvolution_preserves_negativeProjector (t : ℝ) :
    (holonomyEvolution t)ᴴ * negativeOrientationProjector *
        holonomyEvolution t = negativeOrientationProjector := by
  have hComm : holonomyEvolution t * negativeOrientationProjector =
      negativeOrientationProjector * holonomyEvolution t := by
    unfold negativeOrientationProjector
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub,
      Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    rw [holonomyEvolution_commutes_curvature]
  calc
    (holonomyEvolution t)ᴴ * negativeOrientationProjector *
          holonomyEvolution t =
        (holonomyEvolution t)ᴴ *
          (negativeOrientationProjector * holonomyEvolution t) := by
            rw [Matrix.mul_assoc]
    _ = (holonomyEvolution t)ᴴ *
          (holonomyEvolution t * negativeOrientationProjector) := by
            rw [hComm]
    _ = ((holonomyEvolution t)ᴴ * holonomyEvolution t) *
          negativeOrientationProjector := by
            rw [Matrix.mul_assoc]
    _ = negativeOrientationProjector := by
      rw [holonomyEvolution_unitary, Matrix.one_mul]

theorem holonomyEvolution_preserves_curvature (t : ℝ) :
    (holonomyEvolution t)ᴴ * quotientCurvatureHamiltonian *
        holonomyEvolution t = quotientCurvatureHamiltonian := by
  calc
    (holonomyEvolution t)ᴴ * quotientCurvatureHamiltonian *
          holonomyEvolution t =
        (holonomyEvolution t)ᴴ *
          (quotientCurvatureHamiltonian * holonomyEvolution t) := by
            rw [Matrix.mul_assoc]
    _ = (holonomyEvolution t)ᴴ *
          (holonomyEvolution t * quotientCurvatureHamiltonian) := by
            rw [holonomyEvolution_commutes_curvature]
    _ = ((holonomyEvolution t)ᴴ * holonomyEvolution t) *
          quotientCurvatureHamiltonian := by
            rw [Matrix.mul_assoc]
    _ = quotientCurvatureHamiltonian := by
      rw [holonomyEvolution_unitary, Matrix.one_mul]

/-- Algebraic refinement-stability gate for a candidate transport on the
two-path space. -/
def IsHolonomyStableTransport (U : SquareMatrix 2) : Prop :=
  Uᴴ * U = 1 ∧
    Uᴴ * quotientCurvatureHamiltonian * U =
      quotientCurvatureHamiltonian

theorem holonomyEvolution_isStableTransport (t : ℝ) :
    IsHolonomyStableTransport (holonomyEvolution t) :=
  ⟨holonomyEvolution_unitary t,
    holonomyEvolution_preserves_curvature t⟩

def evolveDensity (t : ℝ) (rho : SquareMatrix 2) : SquareMatrix 2 :=
  holonomyEvolution t * rho * (holonomyEvolution t)ᴴ

/-- Holonomy Born weights are constants of the curvature-generated motion. -/
theorem bornWeight_evolve_positive (t : ℝ) (rho : SquareMatrix 2) :
    bornWeight (evolveDensity t rho) positiveOrientationProjector =
      bornWeight rho positiveOrientationProjector := by
  unfold bornWeight evolveDensity
  have hPres := holonomyEvolution_preserves_positiveProjector t
  have hTrace :
      Matrix.trace
          ((holonomyEvolution t * rho * (holonomyEvolution t)ᴴ) *
            positiveOrientationProjector) =
        Matrix.trace (rho * ((holonomyEvolution t)ᴴ *
          positiveOrientationProjector * holonomyEvolution t)) := by
    calc
      Matrix.trace
          ((holonomyEvolution t * rho * (holonomyEvolution t)ᴴ) *
            positiveOrientationProjector) =
        Matrix.trace
          (holonomyEvolution t * rho *
            ((holonomyEvolution t)ᴴ * positiveOrientationProjector)) := by
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace
          (((holonomyEvolution t)ᴴ * positiveOrientationProjector) *
            holonomyEvolution t * rho) := by
              rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace
          (rho * (((holonomyEvolution t)ᴴ *
            positiveOrientationProjector) * holonomyEvolution t)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (rho * ((holonomyEvolution t)ᴴ *
          positiveOrientationProjector * holonomyEvolution t)) := by
            simp only [Matrix.mul_assoc]
  rw [hTrace, hPres]

theorem bornWeight_evolve_negative (t : ℝ) (rho : SquareMatrix 2) :
    bornWeight (evolveDensity t rho) negativeOrientationProjector =
      bornWeight rho negativeOrientationProjector := by
  unfold bornWeight evolveDensity
  have hPres := holonomyEvolution_preserves_negativeProjector t
  have hTrace :
      Matrix.trace
          ((holonomyEvolution t * rho * (holonomyEvolution t)ᴴ) *
            negativeOrientationProjector) =
        Matrix.trace (rho * ((holonomyEvolution t)ᴴ *
          negativeOrientationProjector * holonomyEvolution t)) := by
    calc
      Matrix.trace
          ((holonomyEvolution t * rho * (holonomyEvolution t)ᴴ) *
            negativeOrientationProjector) =
        Matrix.trace
          (holonomyEvolution t * rho *
            ((holonomyEvolution t)ᴴ * negativeOrientationProjector)) := by
              simp only [Matrix.mul_assoc]
      _ = Matrix.trace
          (((holonomyEvolution t)ᴴ * negativeOrientationProjector) *
            holonomyEvolution t * rho) := by
              rw [Matrix.trace_mul_cycle]
      _ = Matrix.trace
          (rho * (((holonomyEvolution t)ᴴ *
            negativeOrientationProjector) * holonomyEvolution t)) := by
              rw [Matrix.trace_mul_comm]
      _ = Matrix.trace (rho * ((holonomyEvolution t)ᴴ *
          negativeOrientationProjector * holonomyEvolution t)) := by
            simp only [Matrix.mul_assoc]
  rw [hTrace, hPres]

/-! ## 6. Exact relational-chirality bridge -/

/-- Normalize the cubic relational chirality so that the explicit asymmetric
witness has sign `+1` and its reflection has sign `-1`. -/
def normalizedRelationalChirality
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) : ℝ :=
  (orientationChirality p1 q1 r1 p2 q2 r2 p3 q3 r3).im / 8

theorem normalizedRelationalChirality_reflection
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) :
    normalizedRelationalChirality
        r1 q1 p1 r2 q2 p2 r3 q3 p3 =
      -normalizedRelationalChirality
        p1 q1 r1 p2 q2 r2 p3 q3 r3 := by
  unfold normalizedRelationalChirality
  rw [orientationChirality_simultaneous_reflection]
  simp
  ring

theorem normalizedRelationalChirality_witness :
    normalizedRelationalChirality 1 1 1 2 2 2 2 1 1 = 1 := by
  unfold normalizedRelationalChirality
  rw [profile_chirality_witness]
  norm_num

theorem normalizedRelationalChirality_reflected_witness :
    normalizedRelationalChirality 1 1 1 2 2 2 1 1 2 = -1 := by
  unfold normalizedRelationalChirality
  rw [reflected_profile_chirality_witness]
  norm_num

/-- The normalized relational sign selects a spectral projector of the path
holonomy.  This is an algebraic identification of two finite `Z2` labels. -/
def chiralitySelectedProjector
    (p1 q1 r1 p2 q2 r2 p3 q3 r3 : ℕ) : SquareMatrix 2 :=
  let chi := normalizedRelationalChirality
    p1 q1 r1 p2 q2 r2 p3 q3 r3
  (((1 + chi) / 2 : ℝ) : ℂ) • positiveOrientationProjector +
    (((1 - chi) / 2 : ℝ) : ℂ) • negativeOrientationProjector

theorem chiralitySelectedProjector_witness :
    chiralitySelectedProjector 1 1 1 2 2 2 2 1 1 =
      positiveOrientationProjector := by
  unfold chiralitySelectedProjector
  rw [normalizedRelationalChirality_witness]
  norm_num

theorem chiralitySelectedProjector_reflected_witness :
    chiralitySelectedProjector 1 1 1 2 2 2 1 1 2 =
      negativeOrientationProjector := by
  unfold chiralitySelectedProjector
  rw [normalizedRelationalChirality_reflected_witness]
  norm_num

/-- Reflection of the relational triple swaps the selected path-holonomy
sector on the explicit nondegenerate witness. -/
theorem relational_chirality_selects_binary_path_holonomy :
    chiralitySelectedProjector 1 1 1 2 2 2 2 1 1 =
        positiveOrientationProjector
      ∧ chiralitySelectedProjector 1 1 1 2 2 2 1 1 2 =
        negativeOrientationProjector
      ∧ positiveOrientationProjector * negativeOrientationProjector = 0 :=
  ⟨chiralitySelectedProjector_witness,
    chiralitySelectedProjector_reflected_witness,
    orientationProjectors_orthogonal⟩

/-! ## 7. Promotion boundary -/

/-- Explicit data still required to promote the finite sector to physical
quantum geometry.  No inhabitant is asserted in this file. -/
structure PhysicalPathPromotionData where
  quantumHistoriesConstructed : Bool
  complexDecoherenceFunctionalConstructed : Bool
  strongPositivityAndNormalizationProved : Bool
  unlabeledHistoryInvarianceProved : Bool
  amplitudesDerivedFromMicroscopicDynamics : Bool
  refinementParameterPhysicallySelected : Bool
  coherenceCompositionDerivedFromRefinement : Bool
  extremalPhaseSelectionPhysicallyDerived : Bool
  holonomyRefinementInvariant : Bool
  chiralityCouplingDerived : Bool
  continuumObservableIdentified : Bool

def PhysicalPathPromotionData.Passes
    (data : PhysicalPathPromotionData) : Prop :=
  data.quantumHistoriesConstructed = true
    ∧ data.complexDecoherenceFunctionalConstructed = true
    ∧ data.strongPositivityAndNormalizationProved = true
    ∧ data.unlabeledHistoryInvarianceProved = true
    ∧ data.amplitudesDerivedFromMicroscopicDynamics = true
    ∧ data.refinementParameterPhysicallySelected = true
    ∧ data.coherenceCompositionDerivedFromRefinement = true
    ∧ data.extremalPhaseSelectionPhysicallyDerived = true
    ∧ data.holonomyRefinementInvariant = true
    ∧ data.chiralityCouplingDerived = true
    ∧ data.continuumObservableIdentified = true

/-- What is closed algebraically before the physical-promotion contract. -/
theorem finite_path_quantum_sector :
    ketInner path13Ket path13Ket = 1
      ∧ ketInner path22Ket path22Ket = 1
      ∧ ketInner path13Ket path22Ket = 0
      ∧ ketInner positiveHolonomyKet positiveHolonomyKet = 1
      ∧ ketInner negativeHolonomyKet negativeHolonomyKet = 1
      ∧ ketInner positiveHolonomyKet negativeHolonomyKet = 0
      ∧ quotientCurvatureHamiltonian * positiveHolonomyKet =
          positiveHolonomyKet
      ∧ quotientCurvatureHamiltonian * negativeHolonomyKet =
          -negativeHolonomyKet
      ∧ (∀ t, (holonomyEvolution t)ᴴ * holonomyEvolution t = 1)
      ∧ (∀ t u, holonomyEvolution (t + u) =
          holonomyEvolution t * holonomyEvolution u) :=
  ⟨path13Ket_normalized,
    path22Ket_normalized,
    pathKets_orthogonal,
    positiveHolonomyKet_normalized,
    negativeHolonomyKet_normalized,
    holonomyKets_orthogonal,
    quotientCurvature_positiveKet,
    quotientCurvature_negativeKet,
    holonomyEvolution_unitary,
    holonomyEvolution_add⟩

#print axioms path_holonomy_complementarity
#print axioms orientation_holonomy_requires_path_coherence
#print axioms orientation_sign_is_imaginary_history_phase
#print axioms finite_path_spin_half_algebra
#print axioms finite_path_spinor_periodicity
#print axioms holonomyEvolution_unitary
#print axioms holonomyEvolution_add
#print axioms holonomyEvolution_isStableTransport
#print axioms bornWeight_evolve_positive
#print axioms relational_chirality_selects_binary_path_holonomy
#print axioms finite_path_quantum_sector

end

end UnifiedTheory.Audit.KFOrientationPathQuantum
