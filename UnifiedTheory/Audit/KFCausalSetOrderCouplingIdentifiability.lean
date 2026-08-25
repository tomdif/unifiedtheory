/-
  Audit/KFCausalSetOrderCouplingIdentifiability.lean

  A REALIZABLE ORDER WITNESS FOR EFFECTIVE-PAIR IDENTIFIABILITY

  The complete chiral law already proves injectivity of its effective pair
  coupling by evaluating the abstract signature function at `(omega,m) =
  (2,0)`.  A nonempty finite precursor, however, always has a maximal event,
  so that signature is not itself a causal-order witness.

  Here the full precursor of the two-antichain supplies the realizable
  signature `(2,2)`.  Its chiral phase is `-1` in either orientation, hence
  its raw amplitude is exactly `-g`.  One scalar order-local amplitude
  therefore identifies the effective coupling, including the canonical
  effective coupling.  This is an identifiability reduction, not a derivation
  of the canonical numerical value from order data.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetOrderCouplingIdentifiability

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetChiralGrowth
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw

/-! ## 1. Identifiability at the realizable `(2,2)` signature -/

/-- At the full two-antichain signature, the effective-pair amplitude is
exactly the negative of the effective coupling, independently of chirality. -/
@[simp]
theorem effectivePairChiralSignatureWeight_two_two
    (g : ℝ) (chirality : Fin 2) :
    effectivePairChiralSignatureWeight g chirality 2 2 = -(g : ℂ) := by
  rw [effectivePairChiralSignatureWeight,
    chiralGaussianPower_eq_phase_pow]
  norm_num [ancestorUnorderedPairCount, pow_two,
    chiralMaximalEventPhase_mul_self]

/-- A single realizable two-ancestor/two-maximal signature value faithfully
identifies the effective unordered-pair coupling. -/
theorem effectivePairChiralSignatureWeight_two_two_eq_iff
    (g₁ g₂ : ℝ) (chirality : Fin 2) :
    effectivePairChiralSignatureWeight g₁ chirality 2 2 =
        effectivePairChiralSignatureWeight g₂ chirality 2 2 ↔
      g₁ = g₂ := by
  rw [effectivePairChiralSignatureWeight_two_two,
    effectivePairChiralSignatureWeight_two_two]
  simp

/-- Specialization of two-antichain identifiability to the effective coupling
of the fixed canonical square-root parameter. -/
theorem twoAntichainSignature_selects_canonicalEffectivePairCoupling
    (g : ℝ) (chirality : Fin 2) :
    effectivePairChiralSignatureWeight g chirality 2 2 =
        effectivePairChiralSignatureWeight
          (effectivePairCoupling canonicalPairCoupling) chirality 2 2 ↔
      g = effectivePairCoupling canonicalPairCoupling := by
  exact effectivePairChiralSignatureWeight_two_two_eq_iff
    g (effectivePairCoupling canonicalPairCoupling) chirality

/-! ## 2. The full precursor of the two-antichain realizes the signature -/

/-- Every selected event of an antichain precursor is maximal within that
precursor.  This local proof keeps the identifiability module independent of
the later source-ensemble development. -/
theorem antichainPast_maximalCount_eq_ancestorCount_orderCoupling
    {n : ℕ} (past : CausalPastSet (cardinalCausalAntichain n)) :
    past.maximalCount = past.ancestorCount := by
  unfold CausalPastSet.maximalCount CausalPastSet.ancestorCount
  apply Nat.card_congr
  exact Equiv.subtypeEquiv (Equiv.refl (Fin n)) (by
    intro i
    constructor
    · exact fun h => h.1
    · intro hMem
      exact ⟨hMem, by
        intro j _hJ hRel
        have hij : i = j := by
          simpa [cardinalCausalAntichain] using hRel
        exact hij.symm⟩)

/-- The full precursor of the two-antichain has exactly the realizable
Rideout--Sorkin signature `(omega,m) = (2,2)`. -/
theorem fullTwoAntichainPast_signature :
    (fullCausalPastSet (cardinalCausalAntichain 2)).ancestorCount = 2 ∧
      (fullCausalPastSet (cardinalCausalAntichain 2)).maximalCount = 2 := by
  constructor
  · exact fullCausalPastSet_ancestorCount (cardinalCausalAntichain 2)
  · rw [antichainPast_maximalCount_eq_ancestorCount_orderCoupling,
      fullCausalPastSet_ancestorCount]

/-- Evaluating the effective-pair edge law on the realized full precursor of
the two-antichain reads off `-g`. -/
@[simp]
theorem effectivePairChiral_fullTwoAntichain_amplitude
    (g : ℝ) (chirality : Fin 2) :
    (rideoutSorkinSignatureAmplitude
      (effectivePairChiralSignatureWeight g chirality)).amplitude
        (cardinalCausalAntichain 2)
        (fullCausalPastSet (cardinalCausalAntichain 2)) = -(g : ℂ) := by
  change effectivePairChiralSignatureWeight g chirality
      (fullCausalPastSet (cardinalCausalAntichain 2)).ancestorCount
      (fullCausalPastSet (cardinalCausalAntichain 2)).maximalCount = -(g : ℂ)
  rw [fullCausalPastSet_ancestorCount,
    antichainPast_maximalCount_eq_ancestorCount_orderCoupling,
    fullCausalPastSet_ancestorCount]
  exact effectivePairChiralSignatureWeight_two_two g chirality

/-- Equality of one raw amplitude on one concrete parent/precursor pair is
equivalent to equality of the effective couplings. -/
theorem effectivePairCoupling_eq_iff_fullTwoAntichain_amplitude_eq
    (g₁ g₂ : ℝ) (chirality : Fin 2) :
    (rideoutSorkinSignatureAmplitude
      (effectivePairChiralSignatureWeight g₁ chirality)).amplitude
        (cardinalCausalAntichain 2)
        (fullCausalPastSet (cardinalCausalAntichain 2)) =
      (rideoutSorkinSignatureAmplitude
        (effectivePairChiralSignatureWeight g₂ chirality)).amplitude
          (cardinalCausalAntichain 2)
          (fullCausalPastSet (cardinalCausalAntichain 2)) ↔
      g₁ = g₂ := by
  rw [effectivePairChiral_fullTwoAntichain_amplitude,
    effectivePairChiral_fullTwoAntichain_amplitude]
  simp

/-- The honest Gate 1 reduction: matching the canonical raw amplitude on the
full precursor of the two-antichain is equivalent to selecting the canonical
effective coupling.  A separate physical theorem must still derive the
left-hand amplitude equality from order data. -/
theorem fullTwoAntichainAmplitude_selects_canonicalEffectivePairCoupling
    (g : ℝ) (chirality : Fin 2) :
    (rideoutSorkinSignatureAmplitude
      (effectivePairChiralSignatureWeight g chirality)).amplitude
        (cardinalCausalAntichain 2)
        (fullCausalPastSet (cardinalCausalAntichain 2)) =
      (rideoutSorkinSignatureAmplitude
        (effectivePairChiralSignatureWeight
          (effectivePairCoupling canonicalPairCoupling) chirality)).amplitude
          (cardinalCausalAntichain 2)
          (fullCausalPastSet (cardinalCausalAntichain 2)) ↔
      g = effectivePairCoupling canonicalPairCoupling := by
  exact effectivePairCoupling_eq_iff_fullTwoAntichain_amplitude_eq
    g (effectivePairCoupling canonicalPairCoupling) chirality

#print axioms effectivePairChiralSignatureWeight_two_two_eq_iff
#print axioms fullTwoAntichainPast_signature
#print axioms effectivePairCoupling_eq_iff_fullTwoAntichain_amplitude_eq
#print axioms fullTwoAntichainAmplitude_selects_canonicalEffectivePairCoupling

end

end UnifiedTheory.Audit.KFCausalSetOrderCouplingIdentifiability
