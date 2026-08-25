/-
  Audit/KFCausalCSpecVarianceSafeHorizonProjection.lean

  VARIANCE-SAFE HORIZON PROJECTION

  The original covariance projection divides by the horizon variance and is
  therefore undefined at deterministic stages.  For a genuine finite
  probability distribution this is unnecessary: zero variance means that the
  horizon observable is constant on the positive-weight support.  Its
  covariance with every observable is then zero automatically.

  We totalize the projection by returning the raw source when the horizon
  variance is zero and the usual orthogonal residual otherwise.  The result is
  covariance-orthogonal at every stage, including the deterministic root.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

/-- Variance is the weighted squared norm of the centered observable whenever
the weights have total mass one. -/
theorem variance_eq_sum_weight_mul_centered_sq
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ) (hw : (∑ i, w i) = 1) :
    variance w J =
      ∑ i, w i * (J i - expectation w J) ^ 2 := by
  unfold variance covariance expectation
  calc
    (∑ i, w i * (J i * J i)) -
          (∑ i, w i * J i) * (∑ i, w i * J i) =
        (∑ i, w i * J i ^ 2) -
          (∑ i, w i * J i) ^ 2 := by
            congr 1
            · apply Finset.sum_congr rfl
              intro i _
              ring
            · ring
    _ = ∑ i, w i *
          (J i - ∑ j, w j * J j) ^ 2 := by
      let E : ℝ := ∑ i, w i * J i
      let S : ℝ := ∑ i, w i * J i ^ 2
      change S - E ^ 2 = ∑ i, w i * (J i - E) ^ 2
      have hExpanded :
          (∑ i, w i * (J i - E) ^ 2) =
            S - 2 * E * E + E ^ 2 * (∑ i, w i) := by
        calc
          (∑ i, w i * (J i - E) ^ 2) =
              ∑ i, (w i * J i ^ 2 -
                (2 * E) * (w i * J i) + E ^ 2 * w i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
          _ = S - 2 * E * E + E ^ 2 * (∑ i, w i) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [← Finset.mul_sum, ← Finset.mul_sum]
      rw [hExpanded, hw]
      ring

/-- At zero variance, each weighted centered square vanishes separately. -/
theorem weight_mul_centered_sq_eq_zero_of_variance_eq_zero
    {ι : Type*} [Fintype ι]
    (w J : ι → ℝ)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J = 0) :
    ∀ i, w i * (J i - expectation w J) ^ 2 = 0 := by
  have hsum :
      (∑ i, w i * (J i - expectation w J) ^ 2) = 0 := by
    rw [← variance_eq_sum_weight_mul_centered_sq w J hw, hvar]
  intro i
  have htermNonneg :
      0 ≤ w i * (J i - expectation w J) ^ 2 :=
    mul_nonneg (hwNonneg i) (sq_nonneg _)
  have htermLe :
      w i * (J i - expectation w J) ^ 2 ≤
        ∑ j, w j * (J j - expectation w J) ^ 2 := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (fun j _ => mul_nonneg (hwNonneg j)
        (sq_nonneg (J j - expectation w J)))
      (Finset.mem_univ i)
  rw [hsum] at htermLe
  exact le_antisymm htermLe htermNonneg

/-- For nonnegative unit-mass weights, a zero-variance observable is
covariance-orthogonal to every other observable. -/
theorem covariance_eq_zero_of_variance_eq_zero
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J = 0) :
    covariance w G J = 0 := by
  have hpoint :=
    weight_mul_centered_sq_eq_zero_of_variance_eq_zero
      w J hwNonneg hw hvar
  have hWeightedProduct :
      expectation w (fun i => G i * J i) =
        expectation w (fun i => G i * expectation w J) := by
    unfold expectation
    apply Finset.sum_congr rfl
    intro i _
    have hz : w i = 0 ∨ (J i - expectation w J) ^ 2 = 0 :=
      mul_eq_zero.mp (hpoint i)
    rcases hz with hwi | hcenter
    · rw [hwi]
      ring
    · have hJ : J i = expectation w J := by
        nlinarith [sq_nonneg (J i - expectation w J)]
      change w i * (G i * J i) =
        w i * (G i * expectation w J)
      rw [hJ]
  unfold covariance
  rw [hWeightedProduct]
  have hconst :
      expectation w (fun i => G i * expectation w J) =
        expectation w J * expectation w G := by
    calc
      expectation w (fun i => G i * expectation w J) =
          expectation w (fun i => expectation w J * G i) := by
            congr
            funext i
            ring
      _ = expectation w J * expectation w G :=
        expectation_const_mul w G (expectation w J)
  rw [hconst]
  ring

/-- The zero-variance result in the horizon-first covariance orientation. -/
theorem covariance_horizon_eq_zero_of_variance_eq_zero
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J = 0) :
    covariance w J G = 0 := by
  rw [covariance_comm]
  exact covariance_eq_zero_of_variance_eq_zero w J G hwNonneg hw hvar

/-- A total covariance projection.  At a deterministic horizon stage every
source is already orthogonal, so the raw source is retained. -/
noncomputable def varianceSafeHorizonOrthogonalResidual
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ) : ι → ℝ :=
  if variance w J = 0 then G else horizonOrthogonalResidual w J G

/-- The variance-safe residual is horizon-orthogonal without a nonzero-
variance premise. -/
theorem covariance_varianceSafeHorizonOrthogonalResidual_self
    {ι : Type*} [Fintype ι]
    (w J G : ι → ℝ)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hw : (∑ i, w i) = 1) :
    covariance w (varianceSafeHorizonOrthogonalResidual w J G) J = 0 := by
  by_cases hvar : variance w J = 0
  · rw [varianceSafeHorizonOrthogonalResidual, if_pos hvar]
    exact covariance_eq_zero_of_variance_eq_zero
      w J G hwNonneg hw hvar
  · rw [varianceSafeHorizonOrthogonalResidual, if_neg hvar]
    exact covariance_horizonOrthogonalResidual_self w J G hvar

/-- At a zero-variance stage every polarized second-order horizon leakage
vanishes, so no quadratic corrector is needed there either. -/
theorem horizonSecondOrderCrossLeakage_eq_zero_of_variance_eq_zero
    {ι : Type*} [Fintype ι]
    (w J A B : ι → ℝ)
    (hwNonneg : ∀ i, 0 ≤ w i)
    (hw : (∑ i, w i) = 1)
    (hvar : variance w J = 0) :
    horizonSecondOrderCrossLeakage w J A B = 0 := by
  unfold horizonSecondOrderCrossLeakage
  exact covariance_horizon_eq_zero_of_variance_eq_zero
    w J (fun i => centeredSource w A i * centeredSource w B i)
    hwNonneg hw hvar

#print axioms variance_eq_sum_weight_mul_centered_sq
#print axioms covariance_eq_zero_of_variance_eq_zero
#print axioms covariance_varianceSafeHorizonOrthogonalResidual_self
#print axioms horizonSecondOrderCrossLeakage_eq_zero_of_variance_eq_zero

end


end UnifiedTheory.Audit.KFCausalCSpecVarianceSafeHorizonProjection
