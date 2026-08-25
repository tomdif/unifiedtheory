/-
  Audit/KFCausalTransitionFiberSignature.lean

  Signature rigidity inside one unlabeled Rideout--Sorkin transition fiber.

  Equal unlabeled children already have equal precursor cardinality.  This
  file proves the companion statement for the number of maximal precursor
  events by counting Hasse covers in the child.  Consequently every slot in
  one transition fiber has exactly the same `(omega,m)` signature, so a
  nonzero signature-local amplitude cannot cancel under coherent quotient
  aggregation.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
import UnifiedTheory.Audit.KFCausalBornShellGeneralLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalTransitionFiberSignature

noncomputable section

open scoped BigOperators
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetTransitionEdges
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalSetChiralDynamics

/-- A strict Hasse cover in a fixed-cardinality causal order. -/
def IsCausalCover {n : ℕ} (P : CardinalCausalOrder n)
    (i j : Fin n) : Prop :=
  P.rel i j = true ∧ i ≠ j ∧
    ∀ k : Fin n, P.rel i k = true → P.rel k j = true → k = i ∨ k = j

noncomputable instance isCausalCoverDecidable {n : ℕ}
    (P : CardinalCausalOrder n) (i j : Fin n) :
    Decidable (IsCausalCover P i j) := Classical.propDecidable _

/-- Number of Hasse covers in a fixed-cardinality causal order. -/
def causalCoverCount {n : ℕ} (P : CardinalCausalOrder n) : ℕ :=
  ∑ pair : Fin n × Fin n,
    if IsCausalCover P pair.1 pair.2 then 1 else 0

/-- Hasse-cover count is invariant under order isomorphism. -/
theorem causalCoverCount_eq_of_isomorphic {n : ℕ}
    {first second : CardinalCausalOrder n}
    (hIso : CardinalCausalOrderIsomorphic first second) :
    causalCoverCount first = causalCoverCount second := by
  classical
  obtain ⟨e, hRel⟩ := hIso
  let pairEquiv : (Fin n × Fin n) ≃ (Fin n × Fin n) :=
    Equiv.prodCongr e e
  have hCover (i j : Fin n) :
      IsCausalCover first i j ↔ IsCausalCover second (e i) (e j) := by
    constructor
    · rintro ⟨hij, hne, hbetween⟩
      refine ⟨by simpa [hRel i j] using hij, fun h => hne (e.injective h), ?_⟩
      intro k hik hkj
      obtain hki | hkj' := hbetween (e.symm k)
        (by rw [hRel]; simpa using hik)
        (by rw [hRel]; simpa using hkj)
      · exact Or.inl (by simpa using congrArg e hki)
      · exact Or.inr (by simpa using congrArg e hkj')
    · rintro ⟨hij, hne, hbetween⟩
      refine ⟨by simpa [hRel i j] using hij, fun h => hne (congrArg e h), ?_⟩
      intro k hik hkj
      obtain hki | hkj' := hbetween (e k)
        (by simpa [hRel i k] using hik)
        (by simpa [hRel k j] using hkj)
      · exact Or.inl (e.injective hki)
      · exact Or.inr (e.injective hkj')
  unfold causalCoverCount
  calc
    (∑ pair : Fin n × Fin n,
        if IsCausalCover first pair.1 pair.2 then 1 else 0) =
      ∑ pair : Fin n × Fin n,
        if IsCausalCover second (e pair.1) (e pair.2) then 1 else 0 := by
          apply Finset.sum_congr rfl
          intro pair _
          by_cases hFirst : IsCausalCover first pair.1 pair.2
          · have hSecond := (hCover pair.1 pair.2).mp hFirst
            simp [hFirst, hSecond]
          · have hSecond :
                ¬ IsCausalCover second (e pair.1) (e pair.2) :=
              fun h => hFirst ((hCover pair.1 pair.2).mpr h)
            simp [hFirst, hSecond]
    _ = ∑ pair : Fin n × Fin n,
        if IsCausalCover second pair.1 pair.2 then 1 else 0 := by
      exact pairEquiv.sum_comp
        (fun pair : Fin n × Fin n =>
          if IsCausalCover second pair.1 pair.2 then 1 else 0)

/-- Old-old covers are unchanged when a new maximal event is adjoined. -/
theorem precursorExtension_cover_old_old {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (i j : Fin n) :
    IsCausalCover (precursorOneElementExtension parent past)
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) ↔
      IsCausalCover parent i j := by
  constructor
  · rintro ⟨hij, hne, hbetween⟩
    refine ⟨by simpa [precursorOneElementExtension, precursorExtensionRel] using hij,
      fun h => hne (congrArg finSumFinEquiv (congrArg Sum.inl h)), ?_⟩
    intro k hik hkj
    have hk := hbetween (finSumFinEquiv (Sum.inl k))
      (by simpa [precursorOneElementExtension, precursorExtensionRel] using hik)
      (by simpa [precursorOneElementExtension, precursorExtensionRel] using hkj)
    rcases hk with hk | hk
    · exact Or.inl (Sum.inl_injective (finSumFinEquiv.injective hk))
    · exact Or.inr (Sum.inl_injective (finSumFinEquiv.injective hk))
  · rintro ⟨hij, hne, hbetween⟩
    refine ⟨by simpa [precursorOneElementExtension, precursorExtensionRel] using hij,
      fun h => hne (Sum.inl_injective (finSumFinEquiv.injective h)), ?_⟩
    intro k hik hkj
    cases hk : finSumFinEquiv.symm k with
    | inl old =>
        have hOld := hbetween old
          (by simpa [precursorOneElementExtension, precursorExtensionRel, hk] using hik)
          (by simpa [precursorOneElementExtension, precursorExtensionRel, hk] using hkj)
        rcases hOld with hOld | hOld
        · exact Or.inl (by apply finSumFinEquiv.symm.injective; simpa [hk, hOld])
        · exact Or.inr (by apply finSumFinEquiv.symm.injective; simpa [hk, hOld])
    | inr newborn =>
        simp [precursorOneElementExtension, precursorExtensionRel, hk] at hkj

/-- An old event is covered by the newborn exactly when it is maximal in the
precursor past. -/
theorem precursorExtension_cover_old_new {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (i : Fin n) (newborn : Fin 1) :
    IsCausalCover (precursorOneElementExtension parent past)
        (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr newborn)) ↔
      past.IsMaximal i := by
  constructor
  · rintro ⟨hi, _hne, hbetween⟩
    refine ⟨by simpa [precursorOneElementExtension, precursorExtensionRel] using hi, ?_⟩
    intro j hj hij
    have h := hbetween (finSumFinEquiv (Sum.inl j))
      (by simpa [precursorOneElementExtension, precursorExtensionRel] using hij)
      (by simpa [precursorOneElementExtension, precursorExtensionRel] using hj)
    rcases h with h | h
    · exact Sum.inl_injective (finSumFinEquiv.injective h)
    · exact (Sum.inl_ne_inr (finSumFinEquiv.injective h)).elim
  · rintro ⟨hi, hmax⟩
    refine ⟨by simpa [precursorOneElementExtension, precursorExtensionRel] using hi,
      ?_, ?_⟩
    · intro h
      exact Sum.inl_ne_inr (finSumFinEquiv.injective h)
    intro k hik hkn
    cases hk : finSumFinEquiv.symm k with
    | inl old =>
        left
        apply finSumFinEquiv.symm.injective
        simp only [Equiv.symm_apply_apply]
        have hold : old = i := hmax old
          (by simpa [precursorOneElementExtension, precursorExtensionRel, hk] using hkn)
          (by simpa [precursorOneElementExtension, precursorExtensionRel, hk] using hik)
        simp [hk, hold]
    | inr new' =>
        right
        apply finSumFinEquiv.symm.injective
        simp [hk, Subsingleton.elim new' newborn]

theorem precursorExtension_not_cover_new_old {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (newborn : Fin 1) (j : Fin n) :
    ¬ IsCausalCover (precursorOneElementExtension parent past)
        (finSumFinEquiv (Sum.inr newborn)) (finSumFinEquiv (Sum.inl j)) := by
  intro h
  exact Bool.false_ne_true (by
    simpa [precursorOneElementExtension, precursorExtensionRel] using h.1)

theorem precursorExtension_not_cover_new_new {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent)
    (first second : Fin 1) :
    ¬ IsCausalCover (precursorOneElementExtension parent past)
        (finSumFinEquiv (Sum.inr first)) (finSumFinEquiv (Sum.inr second)) := by
  intro h
  apply h.2.1
  exact congrArg (fun newborn => finSumFinEquiv (Sum.inr newborn))
    (Subsingleton.elim first second)

def causalPastMaximalCount {n : ℕ} {parent : CardinalCausalOrder n}
    (past : CausalPastSet parent) : ℕ :=
  ∑ i : Fin n, if past.IsMaximal i then 1 else 0

theorem causalPastMaximalCount_eq {n : ℕ}
    {parent : CardinalCausalOrder n} (past : CausalPastSet parent) :
    causalPastMaximalCount past = past.maximalCount := by
  classical
  unfold causalPastMaximalCount CausalPastSet.maximalCount
  rw [Nat.card_eq_fintype_card]
  calc
    (∑ i : Fin n, if past.IsMaximal i then 1 else 0) =
        (Finset.univ.filter fun i : Fin n => past.IsMaximal i).card := by
      simpa using Finset.sum_boole (fun i : Fin n => past.IsMaximal i) Finset.univ
    _ = Fintype.card {i : Fin n // past.IsMaximal i} := by
      rw [← Finset.card_subtype]
      simp

theorem causalCoverCount_precursorOneElementExtension {n : ℕ}
    (parent : CardinalCausalOrder n) (past : CausalPastSet parent) :
    causalCoverCount (precursorOneElementExtension parent past) =
      causalCoverCount parent + past.maximalCount := by
  classical
  let pairEquiv :
      ((Fin n ⊕ Fin 1) × (Fin n ⊕ Fin 1)) ≃
        (Fin (n + 1) × Fin (n + 1)) :=
    Equiv.prodCongr finSumFinEquiv finSumFinEquiv
  unfold causalCoverCount
  rw [← pairEquiv.sum_comp]
  simp only [Fintype.sum_prod_type, Fintype.sum_sum_type]
  simp only [pairEquiv, Equiv.prodCongr_apply, Prod.map_apply,
    precursorExtension_cover_old_old,
    precursorExtension_cover_old_new,
    precursorExtension_not_cover_new_old,
    precursorExtension_not_cover_new_new, if_false, Finset.sum_const_zero,
    add_zero, Fintype.sum_unique]
  rw [Finset.sum_add_distrib]
  change _ + causalPastMaximalCount past = _ + past.maximalCount
  rw [causalPastMaximalCount_eq]

/-- Equal unlabeled children have equal numbers of maximal precursor events. -/
theorem maximalCount_eq_of_causalTransitionTarget_eq {n : ℕ}
    (parent : CardinalCausalOrder n) (first second : CausalPastSet parent)
    (hTarget : causalTransitionTarget parent first =
      causalTransitionTarget parent second) :
    first.maximalCount = second.maximalCount := by
  have hIso : CardinalCausalOrderIsomorphic
      (precursorOneElementExtension parent first)
      (precursorOneElementExtension parent second) := Quotient.exact hTarget
  have hCount := causalCoverCount_eq_of_isomorphic hIso
  rw [causalCoverCount_precursorOneElementExtension,
    causalCoverCount_precursorOneElementExtension] at hCount
  omega

/-- Every Gaussian quarter-turn has a nonzero real or imaginary coordinate. -/
theorem gaussianIPow_first_ne_zero_or_second_ne_zero (m : ℕ) :
    (gaussianIPow m).1 ≠ 0 ∨ (gaussianIPow m).2 ≠ 0 := by
  induction m with
  | zero => simp [gaussianIPow]
  | succ m ih =>
      simp only [gaussianIPow, gaussianMulI]
      rcases ih with h | h
      · exact Or.inr h
      · exact Or.inl (neg_ne_zero.mpr h)

/-- The real signed coefficient at the signature exponent of a represented
child is its nonzero fiber multiplicity times the common Gaussian real sign. -/
theorem interactingChiralRealAggregateSignedFiberSum_at_target {n : ℕ}
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    interactingChiralRealAggregateSignedFiberSum parent
        (causalTransitionTarget parent base)
        (ancestorPairExponent base.ancestorCount) =
      (Fintype.card
          (LabeledCausalTransitionFiber parent
            (causalTransitionTarget parent base)) : ℤ) *
        (gaussianIPow base.maximalCount).1 := by
  classical
  unfold interactingChiralRealAggregateSignedFiberSum
  calc
    (∑ past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        if ancestorPairExponent base.ancestorCount =
            ancestorPairExponent past.val.ancestorCount then
          (gaussianIPow past.val.maximalCount).1 else 0) =
      ∑ _past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        (gaussianIPow base.maximalCount).1 := by
          apply Finset.sum_congr rfl
          intro past _
          have hAncestor := ancestorCount_eq_of_causalTransitionTarget_eq
            parent past.val base past.property
          have hMaximal := maximalCount_eq_of_causalTransitionTarget_eq
            parent past.val base past.property
          rw [hAncestor, hMaximal]
          simp
    _ = _ := by simp

/-- Imaginary companion of the real signed-fiber formula. -/
theorem interactingChiralImagAggregateSignedFiberSum_at_target {n : ℕ}
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    interactingChiralImagAggregateSignedFiberSum parent
        (causalTransitionTarget parent base)
        (ancestorPairExponent base.ancestorCount) =
      (Fintype.card
          (LabeledCausalTransitionFiber parent
            (causalTransitionTarget parent base)) : ℤ) *
        (gaussianIPow base.maximalCount).2 := by
  classical
  unfold interactingChiralImagAggregateSignedFiberSum
  calc
    (∑ past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        if ancestorPairExponent base.ancestorCount =
            ancestorPairExponent past.val.ancestorCount then
          (gaussianIPow past.val.maximalCount).2 else 0) =
      ∑ _past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        (gaussianIPow base.maximalCount).2 := by
          apply Finset.sum_congr rfl
          intro past _
          have hAncestor := ancestorCount_eq_of_causalTransitionTarget_eq
            parent past.val base past.property
          have hMaximal := maximalCount_eq_of_causalTransitionTarget_eq
            parent past.val base past.property
          rw [hAncestor, hMaximal]
          simp
    _ = _ := by simp

/-- Every represented physical child has a concrete real-or-imaginary signed
fiber witness at its common signature exponent. -/
theorem exists_nonzero_complex_signedFiberSum_at_target {n : ℕ}
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    (interactingChiralRealAggregateSignedFiberSum parent
        (causalTransitionTarget parent base)
        (ancestorPairExponent base.ancestorCount) ≠ 0) ∨
      interactingChiralImagAggregateSignedFiberSum parent
        (causalTransitionTarget parent base)
        (ancestorPairExponent base.ancestorCount) ≠ 0 := by
  have hCardNat : 0 < Fintype.card
      (LabeledCausalTransitionFiber parent
        (causalTransitionTarget parent base)) :=
    Fintype.card_pos_iff.mpr ⟨⟨base, rfl⟩⟩
  have hCardInt : (Fintype.card
      (LabeledCausalTransitionFiber parent
        (causalTransitionTarget parent base)) : ℤ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hCardNat
  rcases gaussianIPow_first_ne_zero_or_second_ne_zero base.maximalCount with
      hReal | hImag
  · left
    rw [interactingChiralRealAggregateSignedFiberSum_at_target]
    exact mul_ne_zero hCardInt hReal
  · right
    rw [interactingChiralImagAggregateSignedFiberSum_at_target]
    exact mul_ne_zero hCardInt hImag

/-- Exact factorization of a coherently aggregated signature-local child:
fiber multiplicity times its common microscopic signature amplitude. -/
theorem labeledAggregatedInteractingChiralAmplitude_at_target {n : ℕ}
    (lambda : ℝ) (chirality : Fin 2)
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        parent (causalTransitionTarget parent base) =
      (Fintype.card
          (LabeledCausalTransitionFiber parent
            (causalTransitionTarget parent base)) : ℂ) *
        interactingChiralSignatureWeight lambda chirality
          base.ancestorCount base.maximalCount := by
  classical
  unfold labeledAggregatedCausalEdgeAmplitude
  calc
    (∑ past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        (interactingChiralCausalEdgeAmplitude lambda chirality).amplitude
          parent past.val) =
      ∑ _past : LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base),
        interactingChiralSignatureWeight lambda chirality
          base.ancestorCount base.maximalCount := by
            apply Finset.sum_congr rfl
            intro past _
            have hAncestor := ancestorCount_eq_of_causalTransitionTarget_eq
              parent past.val base past.property
            have hMaximal := maximalCount_eq_of_causalTransitionTarget_eq
              parent past.val base past.property
            simp [interactingChiralCausalEdgeAmplitude,
              rideoutSorkinSignatureAmplitude, hAncestor, hMaximal]
    _ = _ := by simp

/-- Coherent quotient aggregation preserves full raw support: every represented
child has nonzero aggregate whenever the pair coupling is nonzero. -/
theorem labeledAggregatedInteractingChiralAmplitude_at_target_ne_zero {n : ℕ}
    {lambda : ℝ} (hLambda : lambda ≠ 0) (chirality : Fin 2)
    (parent : CardinalCausalOrder n) (base : CausalPastSet parent) :
    labeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude lambda chirality)
        parent (causalTransitionTarget parent base) ≠ 0 := by
  rw [labeledAggregatedInteractingChiralAmplitude_at_target]
  apply mul_ne_zero
  · have hCardNat : 0 < Fintype.card
        (LabeledCausalTransitionFiber parent
          (causalTransitionTarget parent base)) :=
      Fintype.card_pos_iff.mpr ⟨⟨base, rfl⟩⟩
    exact_mod_cast Nat.ne_of_gt hCardNat
  · exact
      (interactingChiralSignatureWeight_fullSupport_iff
        lambda chirality).mpr hLambda base.ancestorCount base.maximalCount

/-- The canonical complete-chiral law has nonzero raw amplitude on every
physical unlabeled one-element extension, not merely on the chosen atlas. -/
theorem canonical_unlabeledAggregatedInteractingChiralAmplitude_ne_zero_of_physical
    (chirality : Fin 2) {n : ℕ}
    (parent : UnlabeledCardinalCausalOrder n)
    (child : UnlabeledCardinalCausalOrder (n + 1))
    (hPhysical : IsUnlabeledOneElementExtension parent child) :
    unlabeledAggregatedCausalEdgeAmplitude
        (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
        parent child ≠ 0 := by
  refine Quotient.inductionOn parent ?_ hPhysical
  intro parentRep hPhysicalRep
  rw [unlabeledAggregatedCausalEdgeAmplitude_mk]
  have hMultiplicity :
      0 < labeledCausalTransitionMultiplicity parentRep child :=
    (labeledCausalTransitionMultiplicity_pos_iff parentRep child).2
      hPhysicalRep
  obtain ⟨base⟩ := Fintype.card_pos_iff.mp hMultiplicity
  rw [← base.property]
  exact labeledAggregatedInteractingChiralAmplitude_at_target_ne_zero
    canonicalPairCoupling_ne_zero chirality parentRep base

/-- Full support of the normalized complete law on the physical birth graph. -/
theorem completeChiralCausalSetGrowthLaw_transition_ne_zero_of_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n)
    (hPhysical : IsPhysicalCausalGrowthStep n pathPrefix child) :
    (completeChiralCausalSetGrowthLaw chirality).transition
        n pathPrefix child ≠ 0 := by
  unfold completeChiralCausalSetGrowthLaw
  change canonicalInteractingChiralTransition chirality
      (currentUnlabeledCausalOrder n pathPrefix) child ≠ 0
  unfold canonicalInteractingChiralTransition
  exact div_ne_zero
    (canonical_unlabeledAggregatedInteractingChiralAmplitude_ne_zero_of_physical
      chirality (currentUnlabeledCausalOrder n pathPrefix) child hPhysical)
    (canonical_unlabeled_interactingChiral_partition_ne_zero
      chirality (currentUnlabeledCausalOrder n pathPrefix))

/-- Exact support classification of the complete chiral transition law. -/
theorem completeChiralCausalSetGrowthLaw_transition_ne_zero_iff_physical
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : CausalSetGrowthBranch n) :
    (completeChiralCausalSetGrowthLaw chirality).transition
          n pathPrefix child ≠ 0 ↔
      IsPhysicalCausalGrowthStep n pathPrefix child := by
  constructor
  · intro hNonzero
    by_contra hNotPhysical
    exact hNonzero
      (completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
        chirality n pathPrefix child hNotPhysical)
  · exact completeChiralCausalSetGrowthLaw_transition_ne_zero_of_physical
      chirality n pathPrefix child

#print axioms maximalCount_eq_of_causalTransitionTarget_eq
#print axioms exists_nonzero_complex_signedFiberSum_at_target
#print axioms completeChiralCausalSetGrowthLaw_transition_ne_zero_of_physical
#print axioms completeChiralCausalSetGrowthLaw_transition_ne_zero_iff_physical

end

end UnifiedTheory.Audit.KFCausalTransitionFiberSignature
