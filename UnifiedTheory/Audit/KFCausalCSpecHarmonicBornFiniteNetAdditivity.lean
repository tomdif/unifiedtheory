/-
  Audit/KFCausalCSpecHarmonicBornFiniteNetAdditivity.lean

  ADDITIVITY AND STATE AXIOMS FOR THE FINITE CAUSAL BORN NET

  The causal Born net is already isotonic and its full unital algebras
  commute on disjoint finite regions.  This module proves the next finite
  net axioms:

  * the empty-region algebra is the scalar algebra;
  * the full-region algebra is the ambient finite field algebra;
  * the algebra of a union is the supremum of the two region algebras;
  * every restricted regional functional is normalized and positive.

  It also records an important boundary of the present construction.  The
  ambient algebra uses pointwise multiplication, so genuinely supported
  observables in disjoint regions have product zero.  Thus the finite net is
  not yet a tensor-product many-body net carrying cross-region correlations.

  These are finite algebraic results.  They do not prove continuum
  additivity, covariance, the time-slice axiom, or an AQFT scaling limit.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteLocality

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteNetAdditivity

noncomputable section

open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet

universe u

variable {site : Type u}

/-! ## 1. Splitting supported observables -/

/-- Keep the values of a field observable on one finite region and set all
other sites to zero. -/
noncomputable def observableRestriction
    (region : Finset site)
    (observable : FiniteFieldObservable site) :
    FiniteFieldObservable site := by
  classical
  exact fun i => if i ∈ region then observable i else 0

/-- Remove the values of a field observable on one finite region. -/
noncomputable def observableResidual
    (region : Finset site)
    (observable : FiniteFieldObservable site) :
    FiniteFieldObservable site := by
  classical
  exact fun i => if i ∈ region then 0 else observable i

@[simp]
theorem observableRestriction_add_observableResidual
    (region : Finset site)
    (observable : FiniteFieldObservable site) :
    observableRestriction region observable +
        observableResidual region observable = observable := by
  classical
  funext i
  by_cases hi : i ∈ region <;>
    simp [observableRestriction, observableResidual, hi]

theorem observableRestriction_supported
    (region : Finset site)
    (observable : FiniteFieldObservable site) :
    observableRestriction region observable ∈
      regionSupportedObservables region := by
  classical
  intro i hi
  simp [observableRestriction, hi]

open Classical in
theorem observableResidual_supported_of_supported_union
    {first second : Finset site}
    {observable : FiniteFieldObservable site}
    (hObservable : observable ∈
      regionSupportedObservables (first ∪ second)) :
    observableResidual first observable ∈
      regionSupportedObservables second := by
  classical
  intro i hiSecond
  by_cases hiFirst : i ∈ first
  · simp [observableResidual, hiFirst]
  · have hiUnion : i ∉ first ∪ second := by
      simp [hiFirst, hiSecond]
    simp only [observableResidual, hiFirst, ↓reduceIte]
    exact hObservable i hiUnion

/-! ## 2. Finite additivity and endpoint algebras -/

open Classical in
/-- Finite additivity: the algebra assigned to a union is exactly the
supremum of the two local algebras. -/
theorem finiteLocalObservableAlgebra_union_eq_sup
    [Fintype site] [Nonempty site]
    (first second : Finset site) :
    finiteLocalObservableAlgebra (first ∪ second) =
      finiteLocalObservableAlgebra first ⊔
        finiteLocalObservableAlgebra second := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    intro observable hObservable
    rw [← observableRestriction_add_observableResidual first observable]
    apply (finiteLocalObservableAlgebra first ⊔
      finiteLocalObservableAlgebra second).add_mem
    · exact StarSubalgebra.mem_sup_left
        (StarAlgebra.subset_adjoin ℂ
          (regionSupportedObservables first)
          (observableRestriction_supported first observable))
    · exact StarSubalgebra.mem_sup_right
        (StarAlgebra.subset_adjoin ℂ
          (regionSupportedObservables second)
          (observableResidual_supported_of_supported_union hObservable))
  · apply sup_le
    · exact finiteLocalObservableAlgebra_isotony Finset.subset_union_left
    · exact finiteLocalObservableAlgebra_isotony Finset.subset_union_right

/-- The empty region carries only the scalar algebra supplied by unital
adjoining. -/
theorem finiteLocalObservableAlgebra_empty_eq_bot
    [Fintype site] :
    finiteLocalObservableAlgebra (∅ : Finset site) = ⊥ := by
  apply le_antisymm
  · apply StarAlgebra.adjoin_le
    intro observable hObservable
    have hzero : observable = 0 := by
      funext i
      exact hObservable i (by simp)
    rw [hzero]
    exact (⊥ : StarSubalgebra ℂ (FiniteFieldObservable site)).zero_mem
  · exact bot_le

/-- On a finite site type, the full region carries the entire ambient field
algebra. -/
theorem finiteLocalObservableAlgebra_univ_eq_top
    [Fintype site] :
    finiteLocalObservableAlgebra (Finset.univ : Finset site) = ⊤ := by
  apply top_unique
  intro observable _
  apply StarAlgebra.subset_adjoin ℂ
    (regionSupportedObservables (Finset.univ : Finset site))
  intro i hi
  exact (hi (Finset.mem_univ i)).elim

/-! ## 3. Restricted regional states -/

section RegionalStates

variable [Fintype site] [Nonempty site]

/-- Every regional restriction of the causal Born functional is normalized. -/
theorem harmonicRegionStateFunctional_normalized
    (chirality : Fin 2)
    (R : HarmonicSingleGenerationReadout site)
    (i : site)
    (region : Finset site) :
    harmonicRegionStateFunctional chirality R i region 1 = 1 := by
  change Matrix.trace ((harmonicReadoutDensity chirality R i).M * 1) = 1
  exact harmonicLocalStateFunctional_normalized chirality R i

/-- Every regional restriction of the causal Born functional is positive on
star-squares. -/
theorem harmonicRegionStateFunctional_positive
    (chirality : Fin 2)
    (R : HarmonicSingleGenerationReadout site)
    (i : site)
    (region : Finset site)
    (observable : finiteLocalObservableAlgebra region) :
    0 ≤ (harmonicRegionStateFunctional chirality R i region
      (star observable * observable)).re := by
  simpa [harmonicRegionStateFunctional] using
    harmonicLocalStateFunctional_positive chirality R i
      (observable : FiniteFieldObservable site)

end RegionalStates

/-! ## 4. Honest direct-product boundary -/

/-- The pointwise ambient multiplication makes supported observables on
disjoint regions annihilate one another.  This is stronger than commutativity,
but also shows why the present finite algebra is not yet a tensor-product
many-body algebra. -/
theorem regionSupportedObservables_mul_eq_zero_of_disjoint
    {first second : Finset site}
    (hdisjoint : Disjoint first second)
    {firstObservable secondObservable : FiniteFieldObservable site}
    (hFirst : firstObservable ∈ regionSupportedObservables first)
    (hSecond : secondObservable ∈ regionSupportedObservables second) :
    firstObservable * secondObservable = 0 := by
  funext i
  change firstObservable i * secondObservable i = 0
  by_cases hi : i ∈ first
  · have hiSecond : i ∉ second := by
      intro hi'
      exact (Finset.disjoint_left.mp hdisjoint) hi hi'
    rw [hSecond i hiSecond]
    simp
  · rw [hFirst i hi]
    simp

/-- In particular, matrix observables placed at distinct recovered sites have
zero product in the current pointwise field algebra. -/
theorem observableAt_mul_observableAt_eq_zero_of_ne
    {firstSite secondSite : site}
    (hSites : firstSite ≠ secondSite)
    (firstMatrix secondMatrix : SingleGenerationObservable) :
    observableAt firstSite firstMatrix *
        observableAt secondSite secondMatrix = 0 := by
  classical
  funext i
  by_cases hi : i = firstSite
  · subst i
    simp [observableAt, hSites]
  · simp [observableAt, hi]

#print axioms finiteLocalObservableAlgebra_union_eq_sup
#print axioms finiteLocalObservableAlgebra_empty_eq_bot
#print axioms finiteLocalObservableAlgebra_univ_eq_top
#print axioms harmonicRegionStateFunctional_normalized
#print axioms harmonicRegionStateFunctional_positive
#print axioms regionSupportedObservables_mul_eq_zero_of_disjoint
#print axioms observableAt_mul_observableAt_eq_zero_of_ne

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteNetAdditivity
