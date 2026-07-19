/-
  Audit/KFOrientationHigherRankDecoherence.lean

  MINIMAL HIGHER-RANK DATA FOR MIXED ORIENTATION KERNELS

  Scalar path amplitudes generate rank-one outer products.  The causal-growth
  restriction theorem therefore cannot realize a balanced interior `D_y`.
  This file identifies the minimal extension exactly:

  * every scalar-amplitude kernel has determinant zero;
  * every strict interior balanced kernel has positive determinant and is not
    scalar-amplitude realizable;
  * a two-component latent amplitude gives an explicit Gram realization of
    every `D_y` in the full positivity interval;
  * hence latent rank two is sufficient everywhere and necessary in the
    interior, while the two endpoints collapse back to rank one.
-/

import UnifiedTheory.Audit.KFCausalSetOrientationRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFOrientationHigherRankDecoherence

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFOrientationSpinOne
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFCausalSetBellCausality

/-! ## 1. The scalar-amplitude obstruction -/

/-- A two-history kernel comes from one scalar amplitude per history. -/
def IsScalarAmplitudeKernel (rho : SquareMatrix 2) : Prop :=
  ∃ amplitude : Fin 2 → ℂ,
    ∀ i j, rho i j = amplitude i * star (amplitude j)

/-- Every scalar-amplitude two-history kernel has rank at most one. -/
theorem scalarAmplitudeKernel_det_zero {rho : SquareMatrix 2}
    (hScalar : IsScalarAmplitudeKernel rho) :
    Matrix.det rho = 0 := by
  obtain ⟨amplitude, hAmplitude⟩ := hScalar
  rw [Matrix.det_fin_two,
    hAmplitude 0 0, hAmplitude 1 1,
    hAmplitude 0 1, hAmplitude 1 0]
  ring

/-- Exact determinant of the balanced orientation family. -/
theorem balancedHistoryKernel_det (y : ℝ) :
    Matrix.det (balancedHistoryKernel y) =
      ((1 / 4 - y * y : ℝ) : ℂ) := by
  rw [Matrix.det_fin_two]
  norm_num [balancedHistoryKernel, Fin.ext_iff, Complex.I_sq]
  calc
    (1 / 4 : ℂ) + Complex.I * (y : ℂ) *
        (Complex.I * (y : ℂ)) =
      1 / 4 + Complex.I ^ 2 * (y : ℂ) ^ 2 := by ring
    _ = 1 / 4 - (y : ℂ) * y := by
      rw [Complex.I_sq]
      ring

/-- Every strict interior balanced kernel has positive determinant. -/
theorem balancedHistoryKernel_det_pos {y : ℝ} (hy : |y| < 1 / 2) :
    0 < (Matrix.det (balancedHistoryKernel y)).re := by
  rw [balancedHistoryKernel_det]
  norm_num
  have hyBounds := (abs_lt.mp hy)
  nlinarith

/-- No strict interior `D_y` can come from scalar path amplitudes. -/
theorem strictInterior_not_scalarAmplitudeKernel {y : ℝ}
    (hy : |y| < 1 / 2) :
    ¬ IsScalarAmplitudeKernel (balancedHistoryKernel y) := by
  intro hScalar
  have hZero := scalarAmplitudeKernel_det_zero hScalar
  have hPositive := balancedHistoryKernel_det_pos hy
  rw [hZero] at hPositive
  norm_num at hPositive

/-! ## 2. An explicit two-component purification -/

/-- A latent two-component amplitude.  Rows are the two route histories and
columns are two unresolved microscopic/environmental alternatives. -/
abbrev TwoComponentOrientationAmplitude := Matrix (Fin 2) (Fin 2) ℂ

/-- Its observable history kernel is the Gram matrix obtained after the latent
component is discarded. -/
def twoComponentAmplitudeKernel
    (amplitude : TwoComponentOrientationAmplitude) : SquareMatrix 2 :=
  amplitude * amplitude.conjTranspose

/-- The residual second-component weight in a Cholesky factor of `D_y`. -/
def orientationInteriorResidual (y : ℝ) : ℝ :=
  1 / 2 - 2 * y * y

theorem orientationInteriorResidual_nonneg {y : ℝ} (hy : |y| ≤ 1 / 2) :
    0 ≤ orientationInteriorResidual y := by
  have hyBounds := abs_le.mp hy
  unfold orientationInteriorResidual
  nlinarith

/-- Explicit rank-two Cholesky amplitude for the complete balanced interval.
The second column vanishes exactly at endpoint saturation. -/
def balancedHistoryRankTwoAmplitude (y : ℝ) :
    TwoComponentOrientationAmplitude :=
  !![(((1 / spinOneSqrtTwo : ℝ) : ℂ)), 0;
     -Complex.I * (((spinOneSqrtTwo * y : ℝ) : ℂ)),
       ((Real.sqrt (orientationInteriorResidual y) : ℝ) : ℂ)]

/-- Two latent components suffice to realize every admissible balanced kernel. -/
theorem balancedHistoryRankTwoAmplitude_realizes {y : ℝ}
    (hy : |y| ≤ 1 / 2) :
    twoComponentAmplitudeKernel (balancedHistoryRankTwoAmplitude y) =
      balancedHistoryKernel y := by
  have hResidual := orientationInteriorResidual_nonneg hy
  have hSqrt :
      (Real.sqrt (orientationInteriorResidual y)) ^ 2 =
        orientationInteriorResidual y := Real.sq_sqrt hResidual
  have hNormResidual :
      (2 * y ^ 2 + (Real.sqrt (orientationInteriorResidual y)) ^ 2) * 2 = 1 := by
    rw [hSqrt]
    unfold orientationInteriorResidual
    ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [twoComponentAmplitudeKernel,
      balancedHistoryRankTwoAmplitude, balancedHistoryKernel,
      Matrix.mul_apply, Matrix.conjTranspose_apply,
      Fin.sum_univ_succ, Fin.ext_iff, Complex.I_sq]
  all_goals
    field_simp [spinOneSqrtTwo_ne_zero]
  all_goals
    norm_num [← pow_two, spinOneSqrtTwo_sq_complex] at *
  all_goals
    exact_mod_cast hNormResidual

/-- A kernel is realizable by at most two latent amplitude components. -/
def IsTwoComponentAmplitudeKernel (rho : SquareMatrix 2) : Prop :=
  ∃ amplitude : TwoComponentOrientationAmplitude,
    twoComponentAmplitudeKernel amplitude = rho

theorem balancedHistoryKernel_isTwoComponent {y : ℝ}
    (hy : |y| ≤ 1 / 2) :
    IsTwoComponentAmplitudeKernel (balancedHistoryKernel y) :=
  ⟨balancedHistoryRankTwoAmplitude y,
    balancedHistoryRankTwoAmplitude_realizes hy⟩

/-- **Minimal-rank classification.**  Throughout the allowed interval two
components suffice.  In the strict interior one component is impossible. -/
theorem balancedHistoryKernel_minimal_latent_rank {y : ℝ}
    (hy : |y| ≤ 1 / 2) :
    IsTwoComponentAmplitudeKernel (balancedHistoryKernel y)
      ∧ (|y| < 1 / 2 →
        ¬ IsScalarAmplitudeKernel (balancedHistoryKernel y)) := by
  exact ⟨balancedHistoryKernel_isTwoComponent hy,
    fun hInterior => strictInterior_not_scalarAmplitudeKernel hInterior⟩

/-- The second latent component is absent exactly at the two endpoints. -/
theorem orientationInteriorResidual_eq_zero_iff {y : ℝ}
    (hy : |y| ≤ 1 / 2) :
    orientationInteriorResidual y = 0 ↔ |y| = 1 / 2 := by
  have hyBounds := abs_le.mp hy
  constructor
  · intro hZero
    unfold orientationInteriorResidual at hZero
    have hySq : y * y = (1 / 2 : ℝ) * (1 / 2) := by nlinarith
    have hAbsSq : |y| ^ 2 = (1 / 2 : ℝ) ^ 2 := by
      simpa [pow_two, sq_abs] using hySq
    nlinarith [abs_nonneg y]
  · intro hEndpoint
    have hAbsSq := congrArg (fun x : ℝ => x ^ 2) hEndpoint
    change |y| ^ 2 = (1 / 2 : ℝ) ^ 2 at hAbsSq
    rw [sq_abs] at hAbsSq
    unfold orientationInteriorResidual
    norm_num at hAbsSq ⊢
    nlinarith

/-! ## 3. Why choosing the sign requires chirality breaking -/

/-- A balanced kernel is reflection fixed exactly at the completely mixed
center.  Reflection symmetry cannot select either pure endpoint. -/
theorem balancedHistoryKernel_reflection_fixed_iff (y : ℝ) :
    pathHistoryReflection (balancedHistoryKernel y) =
        balancedHistoryKernel y ↔ y = 0 := by
  rw [pathHistoryReflection_balancedHistoryKernel]
  constructor
  · intro hFixed
    have hParameter : -y = y :=
      balancedHistoryKernel_injective hFixed
    linarith
  · rintro rfl
    norm_num

/-- Endpoint selection necessarily breaks reflection symmetry. -/
theorem orientationEndpoint_not_reflection_fixed {y : ℝ}
    (hEndpoint : |y| = 1 / 2) :
    pathHistoryReflection (balancedHistoryKernel y) ≠
      balancedHistoryKernel y := by
  intro hFixed
  have hyZero :=
    (balancedHistoryKernel_reflection_fixed_iff y).1 hFixed
  rw [hyZero] at hEndpoint
  norm_num at hEndpoint

/-- The imaginary part of the elementary chiral quarter-turn fixes the sign
of the endpoint parameter. -/
def chiralBoundaryOrientationParameter (chirality : Fin 2) : ℝ :=
  (chiralMaximalEventPhase chirality).im / 2

theorem chiralBoundaryOrientationParameter_endpoint
    (chirality : Fin 2) :
    |chiralBoundaryOrientationParameter chirality| = 1 / 2 := by
  fin_cases chirality <;>
    norm_num [chiralBoundaryOrientationParameter,
      chiralMaximalEventPhase]

/-- Microscopic reflection conjugates the edge character and sends the
selected orientation endpoint to its reflected partner. -/
theorem chiralBoundaryOrientationKernel_reflection
    (chirality : Fin 2) :
    pathHistoryReflection
        (balancedHistoryKernel
          (chiralBoundaryOrientationParameter chirality)) =
      balancedHistoryKernel
        (chiralBoundaryOrientationParameter
          (reflectedMicroscopicChirality chirality)) := by
  rw [pathHistoryReflection_balancedHistoryKernel]
  fin_cases chirality <;>
    norm_num [chiralBoundaryOrientationParameter,
      chiralMaximalEventPhase, reflectedMicroscopicChirality]

/-- Capstone: mixed balanced orientation is precisely higher-rank
decoherence data, not another scalar phase choice. -/
theorem higher_rank_orientation_decoherence_boundary {y : ℝ}
    (hy : |y| ≤ 1 / 2) :
    IsTwoComponentAmplitudeKernel (balancedHistoryKernel y)
      ∧ (orientationInteriorResidual y = 0 ↔ |y| = 1 / 2)
      ∧ (|y| < 1 / 2 →
        ¬ IsScalarAmplitudeKernel (balancedHistoryKernel y)) := by
  exact ⟨balancedHistoryKernel_isTwoComponent hy,
    orientationInteriorResidual_eq_zero_iff hy,
    fun hInterior => strictInterior_not_scalarAmplitudeKernel hInterior⟩

#print axioms scalarAmplitudeKernel_det_zero
#print axioms strictInterior_not_scalarAmplitudeKernel
#print axioms balancedHistoryRankTwoAmplitude_realizes
#print axioms balancedHistoryKernel_minimal_latent_rank
#print axioms balancedHistoryKernel_reflection_fixed_iff
#print axioms orientationEndpoint_not_reflection_fixed
#print axioms chiralBoundaryOrientationKernel_reflection
#print axioms higher_rank_orientation_decoherence_boundary

end

end UnifiedTheory.Audit.KFOrientationHigherRankDecoherence
