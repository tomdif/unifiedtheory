/-
  Audit/KFCausalCSpecHarmonicBornManyBodyNet.lean

  A FINITE MANY-BODY MATRIX NET FOR THE HARMONIC BORN INTERFACE

  This module is deliberately separate from
  `KFCausalCSpecHarmonicBornLocalNet`.  That earlier construction is the
  direct product of one matrix algebra at every site, so observables with
  disjoint support have zero product.  Here the basis is the full finite
  configuration space `site → Fin singleGenDim`; a one-site matrix acts on
  its selected coordinate and as the identity on all other coordinates.

  Consequently, lifts at distinct sites commute but their products need not
  vanish.  In particular, distinct-site computational projectors have a
  nonzero product.  This is a finite many-body algebraic construction only;
  it does not assert a continuum tensor-product completion or a correlated
  physical state.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecHarmonicBornManyBodyNet

noncomputable section

universe u

open Matrix
open UnifiedTheory.Audit.KFCausalCSpecHarmonicBornLocalNet
open UnifiedTheory.LayerC.SMBornRuleGeneralN
open UnifiedTheory.LayerC.SMHilbertInstantiation

variable {site : Type u} [Fintype site] [Nonempty site] [DecidableEq site]

/-- The many-body computational basis: one single-generation outcome at
every finite recovered site. -/
abbrev ManyBodyBasis (site : Type u) := site → Fin singleGenDim

/-- The full matrix algebra on the finite many-body basis.  This is distinct
from the pointwise direct-product algebra `FiniteFieldObservable`. -/
abbrev ManyBodyObservable (site : Type u) :=
  Matrix (ManyBodyBasis site) (ManyBodyBasis site) ℂ

/-- Lift a one-site matrix to the full finite configuration space.  The
update equality says that the input and output configurations agree away
from `i`; the matrix `A` supplies the entry on the selected coordinate. -/
def tensorObservableAt
    (i : site) (A : SingleGenerationObservable) :
    ManyBodyObservable site :=
  fun input output ↦
    if Function.update input i (output i) = output then
      A (input i) (output i)
    else
      0

@[simp]
theorem tensorObservableAt_apply
    (i : site) (A : SingleGenerationObservable)
    (input output : ManyBodyBasis site) :
    tensorObservableAt i A input output =
      if Function.update input i (output i) = output then
        A (input i) (output i)
      else
        0 :=
  rfl

/-- If the two one-site lifts can both contribute to a matrix-product term,
the intermediate configuration is forced uniquely. -/
private theorem intermediate_eq_update
    {i j : site} (hij : i ≠ j)
    {input output middle : ManyBodyBasis site}
    (hFirst : Function.update input i (middle i) = middle)
    (hSecond : Function.update middle j (output j) = output) :
    middle = Function.update input i (output i) := by
  funext k
  by_cases hki : k = i
  · subst k
    have hAtI := congrFun hSecond i
    simpa [hij] using hAtI
  · have hAway := congrFun hFirst k
    simpa [hki] using hAway.symm

/-- Entrywise product formula for lifts at distinct sites.  Its update
condition is precisely equality of `input` and `output` away from the two
selected sites. -/
theorem tensorObservableAt_mul_apply_of_ne
    {i j : site} (hij : i ≠ j)
    (A B : SingleGenerationObservable)
    (input output : ManyBodyBasis site) :
    (tensorObservableAt i A * tensorObservableAt j B) input output =
      if Function.update
          (Function.update input i (output i)) j (output j) = output then
        A (input i) (output i) * B (input j) (output j)
      else
        0 := by
  rw [Matrix.mul_apply]
  let middle : ManyBodyBasis site :=
    Function.update input i (output i)
  by_cases hOutput : Function.update middle j (output j) = output
  · rw [if_pos]
    · rw [Finset.sum_eq_single middle]
      · simp [tensorObservableAt, middle, hOutput, hij.symm]
      · intro other _ hOther
        simp only [tensorObservableAt]
        by_cases hFirst : Function.update input i (other i) = other
        · rw [if_pos hFirst]
          by_cases hSecond : Function.update other j (output j) = output
          · have : other = middle := by
              simpa [middle] using
                intermediate_eq_update hij hFirst hSecond
            exact (hOther this).elim
          · simp [hSecond]
        · simp [hFirst]
      · simp
    · exact hOutput
  · rw [if_neg]
    · apply Finset.sum_eq_zero
      intro other _
      simp only [tensorObservableAt]
      by_cases hFirst : Function.update input i (other i) = other
      · rw [if_pos hFirst]
        by_cases hSecond : Function.update other j (output j) = output
        · have hMiddle : other = middle := by
            simpa [middle] using
              intermediate_eq_update hij hFirst hSecond
          subst other
          exact (hOutput hSecond).elim
        · simp [hSecond]
      · simp [hFirst]
    · exact hOutput

/-- Locality in the finite many-body algebra: arbitrary matrix observables
lifted at distinct sites commute under the ambient matrix multiplication. -/
theorem tensorObservableAt_mul_comm_of_ne
    {i j : site} (hij : i ≠ j)
    (A B : SingleGenerationObservable) :
    tensorObservableAt i A * tensorObservableAt j B =
      tensorObservableAt j B * tensorObservableAt i A := by
  ext input output
  rw [tensorObservableAt_mul_apply_of_ne hij]
  rw [tensorObservableAt_mul_apply_of_ne hij.symm]
  rw [Function.update_comm hij (output i) (output j) input]
  simp only [mul_comm]

/-- Reversing the input and output configurations reverses the update
condition defining a one-site tensor lift. -/
private theorem update_selected_eq_iff
    (i : site) (input output : ManyBodyBasis site) :
    Function.update input i (output i) = output ↔
      Function.update output i (input i) = input := by
  constructor
  · intro h
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · have hAway := congrFun h k
      simpa [hki] using hAway.symm
  · intro h
    funext k
    by_cases hki : k = i
    · subst k
      simp
    · have hAway := congrFun h k
      simpa [hki] using hAway.symm

/-- The adjoint of a one-site lift is the lift of the one-site adjoint. -/
theorem star_tensorObservableAt
    (i : site) (A : SingleGenerationObservable) :
    star (tensorObservableAt i A) =
      tensorObservableAt i (star A) := by
  ext input output
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  by_cases h : Function.update input i (output i) = output
  · have hReverse := (update_selected_eq_iff i input output).mp h
    simp [tensorObservableAt, h, hReverse,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]
  · have hReverse :
        Function.update output i (input i) ≠ input := by
      simpa [update_selected_eq_iff i input output] using h
    simp [tensorObservableAt, h, hReverse,
      Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]

/-- The computational-basis projector lifted at one many-body site. -/
def manyBodyComputationalProjector
    (i : site) (outcome : Fin singleGenDim) :
    ManyBodyObservable site :=
  tensorObservableAt i (computationalProjector singleGenDim outcome)

/-- Computational projectors at two distinct sites have nonzero product.
This sharply distinguishes the many-body construction from the existing
pointwise direct-product net, where all such cross-site products vanish. -/
theorem manyBodyComputationalProjector_mul_ne_zero_of_ne
    {i j : site} (hij : i ≠ j)
    (firstOutcome secondOutcome : Fin singleGenDim) :
    manyBodyComputationalProjector i firstOutcome *
        manyBodyComputationalProjector j secondOutcome ≠ 0 := by
  let configuration : ManyBodyBasis site := fun k ↦
    if k = i then firstOutcome
    else if k = j then secondOutcome
    else 0
  intro hZero
  have hEntry := congrFun (congrFun hZero configuration) configuration
  simp only [manyBodyComputationalProjector] at hEntry
  rw [tensorObservableAt_mul_apply_of_ne hij] at hEntry
  have hFirst : configuration i = firstOutcome := by
    simp [configuration]
  have hSecond : configuration j = secondOutcome := by
    simp [configuration, hij.symm]
  have hConfigurationFixed :
      Function.update
          (Function.update configuration i (configuration i))
          j (configuration j) = configuration := by
    simp
  rw [if_pos hConfigurationFixed] at hEntry
  rw [hFirst, hSecond] at hEntry
  simp [computationalProjector] at hEntry

/-! ## Regional generators and isotony -/

/-- One-site tensor lifts whose selected site lies in `region`. -/
def manyBodyRegionGenerators (region : Finset site) :
    Set (ManyBodyObservable site) :=
  {observable | ∃ i ∈ region, ∃ A : SingleGenerationObservable,
    observable = tensorObservableAt i A}

/-- The unital star algebra generated by all one-site tensor lifts in a
finite region. -/
def manyBodyLocalObservableAlgebra (region : Finset site) :
    StarSubalgebra ℂ (ManyBodyObservable site) :=
  StarAlgebra.adjoin ℂ (manyBodyRegionGenerators region)

/-- Because the one-site matrix ranges over the full matrix algebra, the set
of regional generators is already closed under adjoint. -/
theorem star_manyBodyRegionGenerators (region : Finset site) :
    star (manyBodyRegionGenerators region) =
      manyBodyRegionGenerators region := by
  ext observable
  constructor
  · intro h
    rw [Set.mem_star] at h
    rcases h with ⟨i, hi, A, hA⟩
    refine ⟨i, hi, star A, ?_⟩
    calc
      observable = star (star observable) := (star_star observable).symm
      _ = star (tensorObservableAt i A) := congrArg star hA
      _ = tensorObservableAt i (star A) := star_tensorObservableAt i A
  · rintro ⟨i, hi, A, rfl⟩
    rw [Set.mem_star]
    exact ⟨i, hi, star A, star_tensorObservableAt i A⟩

theorem manyBodyRegionGenerators_mono
    {first second : Finset site} (h : first ⊆ second) :
    manyBodyRegionGenerators first ⊆
      manyBodyRegionGenerators second := by
  rintro observable ⟨i, hi, A, rfl⟩
  exact ⟨i, h hi, A, rfl⟩

/-- Isotony of the finite many-body regional net. -/
theorem manyBodyLocalObservableAlgebra_isotony
    {first second : Finset site} (h : first ⊆ second) :
    manyBodyLocalObservableAlgebra first ≤
      manyBodyLocalObservableAlgebra second :=
  StarAlgebra.adjoin_mono (R := ℂ) (manyBodyRegionGenerators_mono h)

/-- Finite many-body microcausality: every observable in one regional star
algebra commutes with every observable in a disjoint regional star algebra.
This upgrades distinct-site generator commutation to the full algebras
generated by the two regions. -/
theorem manyBodyLocalObservableAlgebra_commute_of_disjoint
    {first second : Finset site} (hDisjoint : Disjoint first second)
    {A B : ManyBodyObservable site}
    (hA : A ∈ manyBodyLocalObservableAlgebra first)
    (hB : B ∈ manyBodyLocalObservableAlgebra second) :
    Commute A B := by
  change A ∈ Algebra.adjoin ℂ
    (manyBodyRegionGenerators first ∪
      star (manyBodyRegionGenerators first)) at hA
  change B ∈ Algebra.adjoin ℂ
    (manyBodyRegionGenerators second ∪
      star (manyBodyRegionGenerators second)) at hB
  rw [star_manyBodyRegionGenerators first, Set.union_self] at hA
  rw [star_manyBodyRegionGenerators second, Set.union_self] at hB
  apply Algebra.commute_of_mem_adjoin_of_forall_mem_commute hB
  intro generatorB hGeneratorB
  exact (Algebra.commute_of_mem_adjoin_of_forall_mem_commute hA (by
    intro generatorA hGeneratorA
    rcases hGeneratorA with ⟨i, hi, matrixA, rfl⟩
    rcases hGeneratorB with ⟨j, hj, matrixB, rfl⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      exact (Finset.disjoint_left.mp hDisjoint hi) hj
    exact (tensorObservableAt_mul_comm_of_ne hij matrixA matrixB).symm)).symm

theorem tensorObservableAt_mem_manyBodyLocalObservableAlgebra
    {region : Finset site} {i : site} (hi : i ∈ region)
    (A : SingleGenerationObservable) :
    tensorObservableAt i A ∈ manyBodyLocalObservableAlgebra region :=
  StarAlgebra.subset_adjoin ℂ (manyBodyRegionGenerators region)
    ⟨i, hi, A, rfl⟩

#print axioms tensorObservableAt_mul_apply_of_ne
#print axioms tensorObservableAt_mul_comm_of_ne
#print axioms manyBodyComputationalProjector_mul_ne_zero_of_ne
#print axioms manyBodyLocalObservableAlgebra_isotony
#print axioms manyBodyLocalObservableAlgebra_commute_of_disjoint

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornManyBodyNet
