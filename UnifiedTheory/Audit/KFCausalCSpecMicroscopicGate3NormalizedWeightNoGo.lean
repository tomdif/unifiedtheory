/-
  Audit/KFCausalCSpecMicroscopicGate3NormalizedWeightNoGo.lean

  Normalized-weight no-go for the componentwise Gate 3 source floor.

  The named microscopic Gate 3 convergence target asks for a positive real
  `sourceBase` below `-centeredSource w source i` at every finite outcome.
  For nonnegative normalized weights this is impossible: a centered source has
  weighted expectation zero, whereas that componentwise floor would make its
  negative weighted expectation strictly positive.

  This does not obstruct the direct aggregate-rate interface.  It shows that
  a normalized physical instantiation must use an aggregate/local-on-support
  descent hypothesis instead of a strictly positive centered-source floor on
  every outcome.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3NormalizedWeightNoGo

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalCSpecBridgeDefectObservable
open UnifiedTheory.Audit.KFCausalCSpecContinuationProfile
open UnifiedTheory.Audit.KFCausalCSpecGlobalization

/-- A source centered with respect to normalized finite weights has zero
weighted expectation. -/
theorem normalized_centeredSource_expectation_eq_zero
    {ι : Type*} [Fintype ι]
    (w source : ι → ℝ)
    (hweight_sum : (∑ i, w i) = 1) :
    expectation w (centeredSource w source) = 0 := by
  unfold expectation centeredSource
  calc
    (∑ i, w i * (source i - ∑ j, w j * source j)) =
        ∑ i, (w i * source i - (∑ j, w j * source j) * w i) := by
          apply Finset.sum_congr rfl
          intro i _
          ring
    _ = (∑ i, w i * source i) -
        (∑ j, w j * source j) * (∑ i, w i) := by
          rw [Finset.sum_sub_distrib]
          congr 1
          rw [Finset.mul_sum]
    _ = 0 := by
          rw [hweight_sum]
          ring

/-- **Normalized component-floor no-go.**  Nonnegative normalized weights
cannot support a strictly positive lower bound on `-centeredSource` at every
outcome. -/
theorem normalizedWeights_forbid_positive_uniform_centeredSourceFloor
    {ι : Type*} [Fintype ι]
    (w source : ι → ℝ)
    (sourceBase : ℝ)
    (hweight_sum : (∑ i, w i) = 1)
    (hweight_nonneg : ∀ i, 0 ≤ w i)
    (hsource_pos : 0 < sourceBase)
    (hsource_floor : ∀ i, sourceBase ≤ -centeredSource w source i) :
    False := by
  have hsum_le :
      (∑ i, w i * sourceBase) ≤
        ∑ i, w i * (-centeredSource w source i) := by
    exact Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hsource_floor i) (hweight_nonneg i))
  have hleft : (∑ i, w i * sourceBase) = sourceBase := by
    calc
      (∑ i, w i * sourceBase) = (∑ i, w i) * sourceBase := by
        rw [Finset.sum_mul]
      _ = sourceBase := by rw [hweight_sum, one_mul]
  have hright :
      (∑ i, w i * (-centeredSource w source i)) = 0 := by
    calc
      (∑ i, w i * (-centeredSource w source i)) =
          ∑ i, -(w i * centeredSource w source i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = -(∑ i, w i * centeredSource w source i) := by
            rw [Finset.sum_neg_distrib]
      _ = -expectation w (centeredSource w source) := by rfl
      _ = 0 := by
            rw [normalized_centeredSource_expectation_eq_zero
              w source hweight_sum, neg_zero]
  rw [hleft, hright] at hsum_le
  exact (not_lt_of_ge hsum_le) hsource_pos

/-- The current strong convergence certificate cannot be instantiated with
nonnegative normalized physical weights.  Its positive `weightBase` field
makes all weights nonnegative, while its positive componentwise centered-source
floor contradicts normalization. -/
theorem physicalHauptvermutungConvergenceCertificate_not_of_normalizedWeights
    {ι : Type*} [Fintype ι]
    {w J source countWindow curvatureBias spectralLocality : ℕ → ι → ℝ}
    {scale c step descentRate remainder total : ℕ → ℝ}
    {edge : ℕ → ι → E4}
    {candidate : ℕ → ι → Equiv.Perm Direction}
    {stepFloor weightBase sourceBase : ℝ}
    (hweight_sum : ∀ n, (∑ i, w n i) = 1) :
    ¬ PhysicalHauptvermutungConvergenceCertificate w J source
      countWindow curvatureBias spectralLocality
      scale c step descentRate remainder total edge candidate
      stepFloor weightBase sourceBase := by
  intro C
  exact
    normalizedWeights_forbid_positive_uniform_centeredSourceFloor
      (w 0) (source 0) sourceBase (hweight_sum 0)
      (fun i =>
        le_trans (le_of_lt C.weightBase_pos) (C.weight_floor 0 i))
      C.sourceBase_pos (C.centered_source_floor 0)

#print axioms normalized_centeredSource_expectation_eq_zero
#print axioms normalizedWeights_forbid_positive_uniform_centeredSourceFloor
#print axioms physicalHauptvermutungConvergenceCertificate_not_of_normalizedWeights

end UnifiedTheory.Audit.KFCausalCSpecMicroscopicGate3NormalizedWeightNoGo
