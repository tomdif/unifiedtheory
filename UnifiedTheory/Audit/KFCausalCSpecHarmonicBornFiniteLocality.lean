/-
  Audit/KFCausalCSpecHarmonicBornFiniteLocality.lean

  FINITE EINSTEIN LOCALITY FOR THE CAUSAL BORN NET

  The finite causal Born net already has isotony, normalized positive local
  states, and exact Born compatibility.  This module proves its missing
  finite locality statement: the unital star algebras assigned to disjoint
  recovered regions commute elementwise.

  The proof is not restricted to the zero-supported generators.  It passes
  through the star-algebra commutant twice, so it covers the full generated
  unital algebras, including their scalar parts.

  This is finite algebraic microcausality.  It is not yet continuum
  spacelike commutativity, because no continuum embedding or physical
  spacelike-separation map is supplied here.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteLocality

noncomputable section

open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet

universe u

variable {site : Type u}

/-- Pointwise star preserves support in a finite recovered region. -/
theorem star_mem_regionSupportedObservables
    {region : Finset site}
    {observable : FiniteFieldObservable site}
    (hObservable : observable ∈ regionSupportedObservables region) :
    star observable ∈ regionSupportedObservables region := by
  intro i hi
  change star (observable i) = 0
  rw [hObservable i hi]
  exact star_zero _

/-- Zero-supported generators on disjoint regions commute pointwise. -/
theorem regionSupportedObservables_mul_comm_of_disjoint
    {first second : Finset site}
    (hdisjoint : Disjoint first second)
    {firstObservable secondObservable : FiniteFieldObservable site}
    (hFirst : firstObservable ∈ regionSupportedObservables first)
    (hSecond : secondObservable ∈ regionSupportedObservables second) :
    firstObservable * secondObservable =
      secondObservable * firstObservable := by
  funext i
  change firstObservable i * secondObservable i =
    secondObservable i * firstObservable i
  by_cases hi : i ∈ first
  · have hiSecond : i ∉ second := by
      intro hi'
      exact (Finset.disjoint_left.mp hdisjoint) hi hi'
    rw [hSecond i hiSecond]
    simp
  · rw [hFirst i hi]
    simp

/-- Finite Einstein locality: every observable in the local star algebra of
one recovered region commutes with every observable in the local star algebra
of a disjoint region.  The commutant argument promotes generator-level
support disjointness to the complete unital star algebras. -/
theorem finiteLocalObservableAlgebra_commute_of_disjoint
    [Fintype site]
    {first second : Finset site}
    (hdisjoint : Disjoint first second)
    (firstObservable : finiteLocalObservableAlgebra first)
    (secondObservable : finiteLocalObservableAlgebra second) :
    (firstObservable : FiniteFieldObservable site) *
        (secondObservable : FiniteFieldObservable site) =
      (secondObservable : FiniteFieldObservable site) *
        (firstObservable : FiniteFieldObservable site) := by
  have hSecondGeneratorsCentralize :
      regionSupportedObservables second ⊆
        StarSubalgebra.centralizer ℂ
          (regionSupportedObservables first) := by
    intro secondGenerator hSecond
    apply (StarSubalgebra.mem_centralizer_iff (R := ℂ)).2
    intro firstGenerator hFirst
    constructor
    · exact regionSupportedObservables_mul_comm_of_disjoint
        hdisjoint hFirst hSecond
    · exact regionSupportedObservables_mul_comm_of_disjoint
        hdisjoint (star_mem_regionSupportedObservables hFirst) hSecond
  have hSecondAlgebraCentralizes :
      finiteLocalObservableAlgebra second ≤
        StarSubalgebra.centralizer ℂ
          (regionSupportedObservables first) := by
    exact StarAlgebra.adjoin_le hSecondGeneratorsCentralize
  have hFirstInDoubleCentralizer :
      (firstObservable : FiniteFieldObservable site) ∈
        StarSubalgebra.centralizer ℂ
          (StarSubalgebra.centralizer ℂ
            (regionSupportedObservables first) :
              Set (FiniteFieldObservable site)) := by
    exact
      (StarAlgebra.adjoin_le_centralizer_centralizer ℂ
        (regionSupportedObservables first)) firstObservable.property
  have hSecondInCentralizer :
      (secondObservable : FiniteFieldObservable site) ∈
        StarSubalgebra.centralizer ℂ
          (regionSupportedObservables first) :=
    hSecondAlgebraCentralizes secondObservable.property
  exact
    ((((StarSubalgebra.mem_centralizer_iff (R := ℂ)).1
      hFirstInDoubleCentralizer)
      (secondObservable : FiniteFieldObservable site)
      hSecondInCentralizer).1).symm

#print axioms star_mem_regionSupportedObservables
#print axioms regionSupportedObservables_mul_comm_of_disjoint
#print axioms finiteLocalObservableAlgebra_commute_of_disjoint

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornFiniteLocality
