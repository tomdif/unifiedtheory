/-
  Audit/KFCausalCylinderRecordTransport.lean

  CAUSAL-RECORD TRANSPORT DERIVED FROM SEQUENTIAL GROWTH

  The earlier native-record dynamics isolated the intertwiner

      Q_c V = V P_c

  as the exact law needed to transport a sharp causal fact through recorded
  refinement.  This file derives that equation for the canonical history
  representation of sequential growth.

  At rank `n`, the carrier basis is the finite set of growth prefixes.  The
  one-step map `V_n` sends a prefix `h` only to its children `(h,b)`, weighted
  by the microscopic transition amplitude.  For a cylinder event `c`, `P_c`
  is its diagonal projector at rank `n`, while `Q_c` is the diagonal
  projector onto every one-step continuation of `c`.  Because a child retains
  its prefix definitionally, the projectors intertwine with `V_n` for every
  event and every transition law:

      Q_c V_n = V_n P_c.

  Thus no alignment postulate is needed for facts which already exist as
  finite cylinders.  Born normalization additionally makes `V_n` an
  isometry.  A native physical child becomes such a cylinder immediately
  after its birth, so its identity is transported exactly through every later
  refinement.

  This does not select a future child before it is born.  Sequential growth
  derives nondemolition transport of realized causal facts; it does not put
  mutually exclusive future-child projectors on the one-dimensional fiber of
  an unresolved parent.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalNativeSuccessorRecord

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCylinderRecordTransport

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalBornShellGeneralLaw
open UnifiedTheory.Audit.KFCausalBornNormalizationTransfer
open UnifiedTheory.Audit.KFCausalNativeSuccessorRecord

universe u v

/-! ## 1. Cylinder projectors and the canonical growth dilation -/

/-- The sharp diagonal projector associated with a finite event. -/
noncomputable def finiteEventProjector {History : Type u} [Fintype History]
    (event : Finset History) : Matrix History History ℂ := by
  classical
  exact fun row column => if row = column ∧ row ∈ event then 1 else 0

theorem finiteEventProjector_apply_self_of_mem {History : Type u}
    [Fintype History] (event : Finset History) (history : History)
    (hMem : history ∈ event) :
    finiteEventProjector event history history = 1 := by
  classical
  simp [finiteEventProjector, hMem]

theorem finiteEventProjector_apply_self_of_not_mem {History : Type u}
    [Fintype History] (event : Finset History) (history : History)
    (hNotMem : history ∉ event) :
    finiteEventProjector event history history = 0 := by
  classical
  simp [finiteEventProjector, hNotMem]

theorem finiteEventProjector_mul_apply_of_mem {History : Type u}
    {Column : Type v} [Fintype History]
    (event : Finset History) (operator : Matrix History Column ℂ)
    (row : History) (column : Column) (hMem : row ∈ event) :
    (finiteEventProjector event * operator) row column =
      operator row column := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single row]
  · simp [finiteEventProjector, hMem]
  · intro other _ hOther
    simp [finiteEventProjector, Ne.symm hOther]
  · simp

theorem finiteEventProjector_mul_apply_of_not_mem {History : Type u}
    {Column : Type v} [Fintype History]
    (event : Finset History) (operator : Matrix History Column ℂ)
    (row : History) (column : Column) (hNotMem : row ∉ event) :
    (finiteEventProjector event * operator) row column = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro other _
  by_cases hSame : row = other
  · subst other
    simp [finiteEventProjector, hNotMem]
  · simp [finiteEventProjector, hSame]

theorem mul_finiteEventProjector_apply_of_mem {Row : Type u}
    {History : Type v} [Fintype History]
    (operator : Matrix Row History ℂ) (event : Finset History)
    (row : Row) (column : History) (hMem : column ∈ event) :
    (operator * finiteEventProjector event) row column =
      operator row column := by
  classical
  rw [Matrix.mul_apply, Finset.sum_eq_single column]
  · simp [finiteEventProjector, hMem]
  · intro other _ hOther
    simp [finiteEventProjector, hOther]
  · simp

theorem mul_finiteEventProjector_apply_of_not_mem {Row : Type u}
    {History : Type v} [Fintype History]
    (operator : Matrix Row History ℂ) (event : Finset History)
    (row : Row) (column : History) (hNotMem : column ∉ event) :
    (operator * finiteEventProjector event) row column = 0 := by
  classical
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro other _
  by_cases hSame : other = column
  · subst other
    simp [finiteEventProjector, hNotMem]
  · simp [finiteEventProjector, hSame]

/-- The amplitude-weighted one-step extension map supplied by sequential
growth itself.  Its support is fixed by prefix extension; only its nonzero
coefficients depend on the transition law. -/
def rankedGrowthDilation {Branch : ℕ → Type u}
    [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ) :
    Matrix (RankedGrowthPath Branch n × Branch n)
      (RankedGrowthPath Branch n) ℂ :=
  fun refined coarse =>
    if refined.1 = coarse then transition coarse refined.2 else 0

@[simp]
theorem rankedGrowthDilation_snoc {Branch : ℕ → Type u}
    [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (pathPrefix : RankedGrowthPath Branch n) (branch : Branch n) :
    rankedGrowthDilation transition (pathPrefix.snoc branch) pathPrefix =
      transition pathPrefix branch := by
  simp [rankedGrowthDilation, RankedGrowthPath.snoc]

theorem rankedGrowthDilation_eq_zero_of_prefix_ne
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (refined : RankedGrowthPath Branch (n + 1))
    (coarse : RankedGrowthPath Branch n)
    (hPrefix : refined.1 ≠ coarse) :
    rankedGrowthDilation transition refined coarse = 0 := by
  simp [rankedGrowthDilation, hPrefix]

/-- The one-step cylinder over an event, written with the product type exposed
so its canonical matrix carrier is definitionally the output of
`rankedGrowthDilation`.  It is the same finite set as
`refineRankedGrowthEvent`. -/
def oneStepCylinder {Branch : ℕ → Type u}
    [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (event : Finset (RankedGrowthPath Branch n)) :
    Finset (RankedGrowthPath Branch n × Branch n) :=
  event ×ˢ Finset.univ

theorem oneStepCylinder_eq_refineRankedGrowthEvent
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (event : Finset (RankedGrowthPath Branch n)) :
    oneStepCylinder event = refineRankedGrowthEvent event := rfl

/-! ## 2. Sequential growth forces the record intertwiner -/

/-- **Intrinsic cylinder-record transport.**  The diagonal projector onto all
refinements of an event intertwines the canonical sequential-growth dilation
with the original event projector.  In physical notation this is exactly

    `Q_c V = V P_c`.

The proof uses only the defining fact that every refined history retains its
coarse prefix.  It is independent of normalization, phases, and dynamics on
the allowed edges. -/
theorem refine_projector_mul_growthDilation
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteEventProjector (oneStepCylinder event) *
        rankedGrowthDilation transition =
      rankedGrowthDilation transition * finiteEventProjector event := by
  classical
  ext refined coarse
  obtain ⟨refinedPrefix, branch⟩ := refined
  by_cases hPrefix : refinedPrefix = coarse
  · subst coarse
    by_cases hMem : refinedPrefix ∈ event
    · rw [finiteEventProjector_mul_apply_of_mem _ _ _ _ (by
          simpa [oneStepCylinder] using hMem),
        mul_finiteEventProjector_apply_of_mem _ _ _ _ hMem]
    · rw [finiteEventProjector_mul_apply_of_not_mem _ _ _ _ (by
          simpa [oneStepCylinder] using hMem),
        mul_finiteEventProjector_apply_of_not_mem _ _ _ _ hMem]
  · by_cases hRefinedMem : refinedPrefix ∈ event
    · rw [finiteEventProjector_mul_apply_of_mem _ _ _ _ (by
          simpa [oneStepCylinder] using hRefinedMem)]
      by_cases hCoarseMem : coarse ∈ event
      · rw [mul_finiteEventProjector_apply_of_mem _ _ _ _ hCoarseMem]
      · rw [mul_finiteEventProjector_apply_of_not_mem _ _ _ _ hCoarseMem]
        simp [rankedGrowthDilation, hPrefix]
    · rw [finiteEventProjector_mul_apply_of_not_mem _ _ _ _ (by
          simpa [oneStepCylinder] using hRefinedMem)]
      by_cases hCoarseMem : coarse ∈ event
      · rw [mul_finiteEventProjector_apply_of_mem _ _ _ _ hCoarseMem]
        simp [rankedGrowthDilation, hPrefix]
      · rw [mul_finiteEventProjector_apply_of_not_mem _ _ _ _ hCoarseMem]

/-- The intertwining law holds for the transition amplitudes of every
coherently normalized ranked growth law. -/
theorem coherentGrowthLaw_transports_cylinder
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteEventProjector (oneStepCylinder event) *
        rankedGrowthDilation (law.transition n) =
      rankedGrowthDilation (law.transition n) *
        finiteEventProjector event :=
  refine_projector_mul_growthDilation (law.transition n) event

/-- The same law holds for every Born-normalized ranked growth law. -/
theorem bornGrowthLaw_transports_cylinder
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteEventProjector (oneStepCylinder event) *
        rankedGrowthDilation (law.transition n) =
      rankedGrowthDilation (law.transition n) *
        finiteEventProjector event :=
  refine_projector_mul_growthDilation (law.transition n) event

/-! ## 3. Born normalization supplies lossless refinement -/

/-- The canonical sequential-growth dilation is an isometry exactly in the
direction needed here whenever the transition amplitudes obey the local Born
normalization law. -/
theorem rankedGrowthDilation_isometry_of_bornNormalized
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (hBorn : ∀ pathPrefix,
      ∑ branch, Complex.normSq (transition pathPrefix branch) = 1) :
    IsIsometry (rankedGrowthDilation transition) := by
  classical
  unfold IsIsometry
  ext first second
  rw [Matrix.mul_apply]
  simp only [Matrix.conjTranspose_apply]
  rw [Fintype.sum_prod_type]
  by_cases hSame : first = second
  · subst second
    rw [Finset.sum_eq_single first]
    · have hMass : finiteComplexBornMass (transition first) = 1 := by
        rw [← ofReal_finiteComplexBornMass, hBorn first]
        norm_num
      simpa [finiteComplexBornMass, rankedGrowthDilation] using hMass
    · intro other _ hOther
      apply Finset.sum_eq_zero
      intro branch _
      simp [rankedGrowthDilation, hOther]
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun pathPrefix _ => by
      apply Finset.sum_eq_zero
      intro branch _
      by_cases hFirst : pathPrefix = first
      · subst pathPrefix
        simp [rankedGrowthDilation, hSame]
      · simp [rankedGrowthDilation, hFirst]))
    simp [hSame]

theorem bornGrowthLaw_dilation_isometry
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ) :
    IsIsometry (rankedGrowthDilation (law.transition n)) := by
  apply rankedGrowthDilation_isometry_of_bornNormalized
  exact law.bornNormalized n

/-! ## 4. The induced cylinder effect is exactly sharp -/

/-- An isometric intertwiner pulls the refined record projector back to the
original sharp projector.  This is the representation-independent algebraic
step from causal identity transport to the exact effect law. -/
theorem isometry_intertwiner_implies_effect
    {Incoming : Type u} {Recorded : Type v}
    [Fintype Incoming] [Fintype Recorded] [DecidableEq Incoming]
    (V : Matrix Recorded Incoming ℂ)
    (P : Matrix Incoming Incoming ℂ)
    (Q : Matrix Recorded Recorded ℂ)
    (hIsometry : IsIsometry V) (hTransport : Q * V = V * P) :
    Vᴴ * Q * V = P := by
  rw [Matrix.mul_assoc, hTransport, ← Matrix.mul_assoc, hIsometry,
    Matrix.one_mul]

/-- **Derived sharp cylinder effect.**  In a Born-normalized sequential
growth law, exhaustive future refinement of a cylinder pulls back to exactly
the original cylinder projector.  No sharp-effect postulate is used. -/
theorem bornGrowthLaw_cylinderEffect_eq_projector
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (event : Finset (RankedGrowthPath Branch n)) :
    (rankedGrowthDilation (law.transition n))ᴴ *
          finiteEventProjector (oneStepCylinder event) *
        rankedGrowthDilation (law.transition n) =
      finiteEventProjector event := by
  classical
  exact isometry_intertwiner_implies_effect
    (rankedGrowthDilation (law.transition n))
    (finiteEventProjector event)
    (finiteEventProjector (oneStepCylinder event))
    (bornGrowthLaw_dilation_isometry law n)
    (bornGrowthLaw_transports_cylinder law n event)

/-- A realized history has unit weight for its own exhaustively refined
cylinder. -/
theorem bornGrowthLaw_matchingHistory_weight_one
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (history : RankedGrowthPath Branch n) :
    ((rankedGrowthDilation (law.transition n))ᴴ *
          finiteEventProjector (oneStepCylinder ({history} :
            Finset (RankedGrowthPath Branch n))) *
        rankedGrowthDilation (law.transition n)) history history = 1 := by
  rw [bornGrowthLaw_cylinderEffect_eq_projector]
  exact finiteEventProjector_apply_self_of_mem _ _ (by simp)

/-- A distinct realized history has zero weight for the selected singleton
cylinder. -/
theorem bornGrowthLaw_distinctHistory_weight_zero
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
    (selected prepared : RankedGrowthPath Branch n)
    (hDistinct : prepared ≠ selected) :
    ((rankedGrowthDilation (law.transition n))ᴴ *
          finiteEventProjector (oneStepCylinder ({selected} :
            Finset (RankedGrowthPath Branch n))) *
        rankedGrowthDilation (law.transition n)) prepared prepared = 0 := by
  rw [bornGrowthLaw_cylinderEffect_eq_projector]
  exact finiteEventProjector_apply_self_of_not_mem _ _ (by
    simpa using hDistinct)

/-! ## 5. Every realized causal child is transported thereafter -/

/-- The singleton cylinder corresponding to one actual physical child of a
causal prefix. -/
def nativeChildCylinder {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : NativeCausalSuccessor n pathPrefix) :
    Finset (RankedGrowthPath CausalSetGrowthBranch (n + 1)) :=
  {pathPrefix.snoc child.1}

/-- Once a native physical child has occurred, sequential growth transports
that exact child fact through the next refinement.  Here `P_c` is the
singleton child-cylinder projector and `Q_c` its exhaustive continuation
projector. -/
theorem nativeChild_recordTransport
    (law : RankedNormalizedComplexGrowthLaw CausalSetGrowthBranch)
    {n : ℕ} (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : NativeCausalSuccessor n pathPrefix) :
    finiteEventProjector
          (oneStepCylinder (nativeChildCylinder pathPrefix child)) *
        rankedGrowthDilation (law.transition (n + 1)) =
      rankedGrowthDilation (law.transition (n + 1)) *
        finiteEventProjector (nativeChildCylinder pathPrefix child) :=
  coherentGrowthLaw_transports_cylinder law (n + 1)
    (nativeChildCylinder pathPrefix child)

/-- The canonical harmonic causal law therefore transports every realized
physical child record at every rank without an added alignment axiom. -/
theorem harmonicNativeChild_recordTransport
    (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : NativeCausalSuccessor n pathPrefix) :
    finiteEventProjector
          (oneStepCylinder (nativeChildCylinder pathPrefix child)) *
        rankedGrowthDilation
          ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
            (n + 1)) =
        rankedGrowthDilation
          ((canonicalHarmonicCriticalBornShellGrowthLaw chirality).transition
            (n + 1)) *
        finiteEventProjector (nativeChildCylinder pathPrefix child) :=
  nativeChild_recordTransport
    (canonicalHarmonicCriticalBornShellGrowthLaw chirality) pathPrefix child

/-- For the canonical harmonic law, a realized native child cylinder has the
exact sharp effect derived from its exhaustive future continuations. -/
theorem harmonicNativeChild_cylinderEffect_eq_projector
    (chirality : Fin 2) {n : ℕ}
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (child : NativeCausalSuccessor n pathPrefix) :
    let event := nativeChildCylinder pathPrefix child
    (rankedGrowthDilation
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            (n + 1)))ᴴ *
          finiteEventProjector (oneStepCylinder event) *
        rankedGrowthDilation
          ((canonicalHarmonicBornNormalizedGrowthLaw chirality).transition
            (n + 1)) =
      finiteEventProjector event := by
  exact bornGrowthLaw_cylinderEffect_eq_projector
    (canonicalHarmonicBornNormalizedGrowthLaw chirality) (n + 1)
    (nativeChildCylinder pathPrefix child)

/-! ## 6. Capstone and axiom audit -/

/-- Sequential growth itself derives the causal-record intertwiner for every
finite cylinder; Born normalization supplies the isometry needed by the sharp
outcome theorem, and the result applies in particular to every realized
native causal child. -/
theorem causalCylinderRecordTransport_capstone :
    (∀ {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
      (law : RankedNormalizedComplexGrowthLaw Branch) (n : ℕ)
      (event : Finset (RankedGrowthPath Branch n)),
      finiteEventProjector (oneStepCylinder event) *
          rankedGrowthDilation (law.transition n) =
        rankedGrowthDilation (law.transition n) *
          finiteEventProjector event) ∧
    (∀ {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
      (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ),
      IsIsometry (rankedGrowthDilation (law.transition n))) ∧
    (∀ {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
      (law : RankedBornNormalizedComplexGrowthLaw Branch) (n : ℕ)
      (event : Finset (RankedGrowthPath Branch n)),
      (rankedGrowthDilation (law.transition n))ᴴ *
            finiteEventProjector (oneStepCylinder event) *
          rankedGrowthDilation (law.transition n) =
        finiteEventProjector event) := by
  exact ⟨fun law n event => coherentGrowthLaw_transports_cylinder law n event,
    fun law n => bornGrowthLaw_dilation_isometry law n,
    fun law n event => bornGrowthLaw_cylinderEffect_eq_projector law n event⟩

#print axioms refine_projector_mul_growthDilation
#print axioms rankedGrowthDilation_isometry_of_bornNormalized
#print axioms bornGrowthLaw_cylinderEffect_eq_projector
#print axioms bornGrowthLaw_matchingHistory_weight_one
#print axioms bornGrowthLaw_distinctHistory_weight_zero
#print axioms nativeChild_recordTransport
#print axioms harmonicNativeChild_recordTransport
#print axioms harmonicNativeChild_cylinderEffect_eq_projector
#print axioms causalCylinderRecordTransport_capstone

end

end UnifiedTheory.Audit.KFCausalCylinderRecordTransport
