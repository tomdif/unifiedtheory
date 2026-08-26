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

end

end UnifiedTheory.Audit.KFCausalCSpecHarmonicBornManyBodyNet
