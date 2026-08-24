/-
  Audit/KFCausalCSpecPhysicalChiralGrowthRealization.lean

  Conditional physical CSpec realization under the complete chiral growth law.

  `KFCausalCSpecPhysicalGrowthRealization` proves that the native 140-event
  full-S3 CSpec atlas is reachable by ordinary one-element causal growth, and
  that the uniform growth law assigns the displayed atlas path nonzero
  amplitude.  `KFCausalSetCompleteChiralLaw` supplies the stronger zero-free
  complete chiral dynamics.

  This file isolates the exact remaining bridge between those two facts.  The
  denominator of the complete chiral transition is already proved zero-free in
  `KFCausalSetCompleteChiralLaw`; the only surviving atlas-path obstruction is
  finite numerator noncancellation in the raw coherent aggregate over the
  unlabeled transition fiber.

  The new hypothesis is finite and explicit: one nonzero raw aggregate
  condition for each atlas birth.  This is not yet a proof that the microscopic
  dynamics supplies the Hauptvermutung convergence certificate.

  No proof placeholders. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
import UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetBellCausality
open UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.Audit.KFCausalDeterminantPhysicalBoundary
open UnifiedTheory.Audit.KFCausalRegularPhaseEntry

/-- Prefix of the physical atlas path immediately before the `n -> n+1`
birth. -/
def atlasStepPrefix (n : ℕ) (hnext : n + 1 ≤ 140) :
    RankedGrowthPath CausalSetGrowthBranch n :=
  globalAtlasPhysicalGrowthPath n
    (Nat.le_trans (Nat.le_succ n) hnext)

/-- Child produced by the `n -> n+1` atlas birth. -/
def atlasStepChild (n : ℕ) (hnext : n + 1 ≤ 140) :
    CausalSetGrowthBranch n :=
  Quotient.mk _ (globalAtlasPhysicalPrefix (n + 1) hnext)

/-- The actual complete-chiral normalized transition assigned to the `n`th
atlas birth. -/
def atlasCompleteChiralTransition
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) : ℂ :=
  (completeChiralCausalSetGrowthLaw chirality).transition n
    (atlasStepPrefix n hnext) (atlasStepChild n hnext)

/-- The raw coherent numerator of the complete-chiral transition assigned to
the `n`th atlas birth, before division by the parent partition. -/
def atlasCompleteChiralRawAggregate
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) : ℂ :=
  unlabeledAggregatedCausalEdgeAmplitude
    (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
    (currentUnlabeledCausalOrder n (atlasStepPrefix n hnext))
    (atlasStepChild n hnext)

/-- The integer real-part polynomial whose value at the canonical pair
coupling is the real part of the raw coherent aggregate for the `n`th atlas
birth. -/
def atlasCompleteChiralRawAggregateRealPolynomial
    (n : ℕ) (hnext : n + 1 ≤ 140) : Polynomial ℤ :=
  interactingChiralRealAggregatePolynomial
    (globalAtlasPhysicalPrefix n
      (Nat.le_trans (Nat.le_succ n) hnext))
    (atlasStepChild n hnext)

/-- The integer imaginary-part polynomial whose value at the canonical pair
coupling is, up to chirality conjugation, the imaginary part of the raw
coherent aggregate for the `n`th atlas birth. -/
def atlasCompleteChiralRawAggregateImagPolynomial
    (n : ℕ) (hnext : n + 1 ≤ 140) : Polynomial ℤ :=
  interactingChiralImagAggregatePolynomial
    (globalAtlasPhysicalPrefix n
      (Nat.le_trans (Nat.le_succ n) hnext))
    (atlasStepChild n hnext)

/-- One signed real coefficient of the raw aggregate polynomial for the `n`th
atlas birth. -/
def atlasCompleteChiralRawAggregateRealCoeff
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) : ℤ :=
  (atlasCompleteChiralRawAggregateRealPolynomial n hnext).coeff k

/-- One signed imaginary coefficient of the raw aggregate polynomial for the
`n`th atlas birth. -/
def atlasCompleteChiralRawAggregateImagCoeff
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) : ℤ :=
  (atlasCompleteChiralRawAggregateImagPolynomial n hnext).coeff k

/-- The same atlas-birth coefficient as a signed count over the labeled
transition fiber at one exponent. -/
def atlasCompleteChiralRawAggregateSignedFiberSum
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) : ℤ :=
  interactingChiralRealAggregateSignedFiberSum
    (globalAtlasPhysicalPrefix n
      (Nat.le_trans (Nat.le_succ n) hnext))
    (atlasStepChild n hnext) k

/-- Imaginary signed count over the labeled transition fiber at one exponent
for the `n`th atlas birth. -/
def atlasCompleteChiralRawAggregateImagSignedFiberSum
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) : ℤ :=
  interactingChiralImagAggregateSignedFiberSum
    (globalAtlasPhysicalPrefix n
      (Nat.le_trans (Nat.le_succ n) hnext))
    (atlasStepChild n hnext) k

/-- The polynomial coefficient at one atlas birth is exactly the corresponding
signed transition-fiber sum. -/
theorem atlasCompleteChiralRawAggregateRealCoeff_eq_signedFiberSum
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) :
    atlasCompleteChiralRawAggregateRealCoeff n hnext k =
      atlasCompleteChiralRawAggregateSignedFiberSum n hnext k := by
  simpa [atlasCompleteChiralRawAggregateRealCoeff,
    atlasCompleteChiralRawAggregateRealPolynomial,
    atlasCompleteChiralRawAggregateSignedFiberSum,
    interactingChiralRealAggregateCoeff] using
    interactingChiralRealAggregateCoeff_eq_signedFiberSum
      (globalAtlasPhysicalPrefix n
        (Nat.le_trans (Nat.le_succ n) hnext))
      (atlasStepChild n hnext) k

/-- The imaginary polynomial coefficient at one atlas birth is exactly the
corresponding imaginary signed transition-fiber sum. -/
theorem atlasCompleteChiralRawAggregateImagCoeff_eq_signedFiberSum
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ) :
    atlasCompleteChiralRawAggregateImagCoeff n hnext k =
      atlasCompleteChiralRawAggregateImagSignedFiberSum n hnext k := by
  simpa [atlasCompleteChiralRawAggregateImagCoeff,
    atlasCompleteChiralRawAggregateImagPolynomial,
    atlasCompleteChiralRawAggregateImagSignedFiberSum,
    interactingChiralImagAggregateCoeff] using
    interactingChiralImagAggregateCoeff_eq_signedFiberSum
      (globalAtlasPhysicalPrefix n
        (Nat.le_trans (Nat.le_succ n) hnext))
      (atlasStepChild n hnext) k

/-- The raw atlas aggregate real part is exactly evaluation of its integer
transition-fiber polynomial at the canonical pair coupling. -/
theorem atlasCompleteChiralRawAggregate_re_eq_realPolynomial_eval
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    (atlasCompleteChiralRawAggregate chirality n hnext).re =
      (atlasCompleteChiralRawAggregateRealPolynomial n hnext).eval₂
        (Int.castRingHom ℝ) canonicalPairCoupling := by
  unfold atlasCompleteChiralRawAggregate
  unfold atlasCompleteChiralRawAggregateRealPolynomial
  unfold atlasStepPrefix
  rw [globalAtlasPhysicalGrowthPath_currentOrder,
    unlabeledAggregatedCausalEdgeAmplitude_mk]
  exact interactingChiral_labeledAggregate_re_eq_polynomial_eval
    canonicalPairCoupling chirality
    (globalAtlasPhysicalPrefix n
      (Nat.le_trans (Nat.le_succ n) hnext))
    (atlasStepChild n hnext)

/-- Imaginary-polynomial nonzero status rules out raw coherent cancellation
for either complete-chiral branch. -/
theorem atlasCompleteChiralRawAggregate_ne_zero_of_imagPolynomial_ne_zero
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140)
    (hPolynomial :
      atlasCompleteChiralRawAggregateImagPolynomial n hnext ≠ 0) :
    atlasCompleteChiralRawAggregate chirality n hnext ≠ 0 := by
  have hLabeledPolynomial :
      interactingChiralImagAggregatePolynomial
        (globalAtlasPhysicalPrefix n
          (Nat.le_trans (Nat.le_succ n) hnext))
        (atlasStepChild n hnext) ≠ 0 := by
    simpa [atlasCompleteChiralRawAggregateImagPolynomial] using hPolynomial
  unfold atlasCompleteChiralRawAggregate
  unfold atlasStepPrefix
  rw [globalAtlasPhysicalGrowthPath_currentOrder,
    unlabeledAggregatedCausalEdgeAmplitude_mk]
  exact
    canonical_labeledInteractingChiralAggregate_ne_zero_of_imagPolynomial_ne_zero
      chirality
      (globalAtlasPhysicalPrefix n
        (Nat.le_trans (Nat.le_succ n) hnext))
      (atlasStepChild n hnext) hLabeledPolynomial

/-- The already zero-free complete-chiral parent partition for the `n`th
atlas birth. -/
def atlasCompleteChiralPartition
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) : ℂ :=
  unlabeledCausalEdgeAmplitudePartition
    (interactingChiralCausalEdgeAmplitude canonicalPairCoupling chirality)
    (currentUnlabeledCausalOrder n (atlasStepPrefix n hnext))

/-- The atlas transition is exactly its raw coherent aggregate divided by the
complete-chiral parent partition. -/
theorem atlasCompleteChiralTransition_eq_rawAggregate_div_partition
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    atlasCompleteChiralTransition chirality n hnext =
      atlasCompleteChiralRawAggregate chirality n hnext /
        atlasCompleteChiralPartition chirality n hnext := rfl

/-- The denominator of every complete-chiral atlas transition is nonzero. -/
theorem atlasCompleteChiralPartition_ne_zero
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    atlasCompleteChiralPartition chirality n hnext ≠ 0 := by
  unfold atlasCompleteChiralPartition
  exact canonical_unlabeled_interactingChiral_partition_ne_zero
    chirality _

/-- The finite raw noncancellation gate for the complete-chiral atlas path.
This is smaller than the normalized transition gate because denominator
zero-freeness is already theorem-proved. -/
def CompleteChiralAtlasRawAggregateNonzero (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    atlasCompleteChiralRawAggregate chirality n hnext ≠ 0

/-- A finite real-polynomial certificate for the complete-chiral atlas path.
It is sufficient, not definitionally necessary: a purely imaginary nonzero
aggregate would require the analogous imaginary-polynomial certificate. -/
def CompleteChiralAtlasRealAggregatePolynomialNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    atlasCompleteChiralRawAggregateRealPolynomial n hnext ≠ 0

/-- A finite imaginary-polynomial certificate for the complete-chiral atlas
path.  This is needed for births whose aggregate is purely imaginary in the
real coefficient channel. -/
def CompleteChiralAtlasImagAggregatePolynomialNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    atlasCompleteChiralRawAggregateImagPolynomial n hnext ≠ 0

/-- A finite coefficient-level certificate for the complete-chiral atlas path.
For each atlas birth, it asks for one exponent whose signed real aggregate
coefficient does not cancel. -/
def CompleteChiralAtlasRealAggregateCoeffNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    ∃ k : ℕ, atlasCompleteChiralRawAggregateRealCoeff n hnext k ≠ 0

/-- Imaginary coefficient-level certificate for the complete-chiral atlas
path. -/
def CompleteChiralAtlasImagAggregateCoeffNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    ∃ k : ℕ, atlasCompleteChiralRawAggregateImagCoeff n hnext k ≠ 0

/-- A finite signed-fiber-sum certificate for the complete-chiral atlas path.
This is the directly countable form of the coefficient gate. -/
def CompleteChiralAtlasRealAggregateSignedFiberSumNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    ∃ k : ℕ, atlasCompleteChiralRawAggregateSignedFiberSum n hnext k ≠ 0

/-- Imaginary signed-fiber-sum certificate for the complete-chiral atlas path. -/
def CompleteChiralAtlasImagAggregateSignedFiberSumNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    ∃ k : ℕ,
      atlasCompleteChiralRawAggregateImagSignedFiberSum n hnext k ≠ 0

/-- Corrected complex signed-fiber certificate: each atlas birth may be
certified by either a real or an imaginary signed transition-fiber count. -/
def CompleteChiralAtlasComplexSignedFiberSumNonzero : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    (∃ k : ℕ, atlasCompleteChiralRawAggregateSignedFiberSum n hnext k ≠ 0) ∨
      ∃ k : ℕ,
        atlasCompleteChiralRawAggregateImagSignedFiberSum n hnext k ≠ 0

/-- Which coefficient channel a finite atlas-birth witness uses. -/
inductive CompleteChiralAtlasCoefficientComponent
  | real
  | imag
deriving DecidableEq

/-- Constructive output schema for the finite signed-fiber search.  A table
chooses one exponent for each of the 140 atlas births and proves that the
corresponding signed transition-fiber count is nonzero. -/
structure CompleteChiralAtlasSignedFiberWitnessTable : Type where
  exponent :
    (n : ℕ) → n + 1 ≤ 140 → ℕ
  signedFiberSum_ne_zero :
    ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
      atlasCompleteChiralRawAggregateSignedFiberSum
        n hnext (exponent n hnext) ≠ 0

theorem completeChiralAtlasRealAggregateSignedFiberSumNonzero_of_witnessTable
    (W : CompleteChiralAtlasSignedFiberWitnessTable) :
    CompleteChiralAtlasRealAggregateSignedFiberSumNonzero := by
  intro n hnext
  exact ⟨W.exponent n hnext, W.signedFiberSum_ne_zero n hnext⟩

/-- Corrected constructive output schema for the finite signed-fiber search.
For each atlas birth the table chooses either the real or the imaginary
coefficient channel, then supplies one nonzero signed transition-fiber count
in that channel. -/
structure CompleteChiralAtlasComplexSignedFiberWitnessTable : Type where
  component :
    (n : ℕ) → n + 1 ≤ 140 → CompleteChiralAtlasCoefficientComponent
  exponent :
    (n : ℕ) → n + 1 ≤ 140 → ℕ
  signedFiberSum_ne_zero :
    ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
      match component n hnext with
      | .real =>
          atlasCompleteChiralRawAggregateSignedFiberSum
            n hnext (exponent n hnext) ≠ 0
      | .imag =>
          atlasCompleteChiralRawAggregateImagSignedFiberSum
            n hnext (exponent n hnext) ≠ 0

theorem completeChiralAtlasComplexSignedFiberSumNonzero_of_witnessTable
    (W : CompleteChiralAtlasComplexSignedFiberWitnessTable) :
    CompleteChiralAtlasComplexSignedFiberSumNonzero := by
  intro n hnext
  cases hComponent : W.component n hnext with
  | real =>
      exact Or.inl
        ⟨W.exponent n hnext, by
          simpa [hComponent] using W.signedFiberSum_ne_zero n hnext⟩
  | imag =>
      exact Or.inr
        ⟨W.exponent n hnext, by
          simpa [hComponent] using W.signedFiberSum_ne_zero n hnext⟩

/-- The old real-only signed-fiber certificate is a special case of the
corrected complex signed-fiber certificate. -/
theorem completeChiralAtlasComplexSignedFiberSumNonzero_of_realSignedFiberSum_nonzero
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero) :
    CompleteChiralAtlasComplexSignedFiberSumNonzero := by
  intro n hnext
  exact Or.inl (hSum n hnext)

/-- A single nonzero coefficient proves nonzero status of one concrete atlas
real aggregate polynomial. -/
theorem atlasCompleteChiralRawAggregateRealPolynomial_ne_zero_of_coeff_ne_zero
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ)
    (hCoeff :
      atlasCompleteChiralRawAggregateRealCoeff n hnext k ≠ 0) :
    atlasCompleteChiralRawAggregateRealPolynomial n hnext ≠ 0 := by
  intro hZero
  apply hCoeff
  unfold atlasCompleteChiralRawAggregateRealCoeff
  rw [hZero]
  simp

/-- Coefficient witnesses imply the real-polynomial nonzero gate. -/
theorem completeChiralAtlasRealAggregatePolynomialNonzero_of_coeff_nonzero
    (hCoeff : CompleteChiralAtlasRealAggregateCoeffNonzero) :
    CompleteChiralAtlasRealAggregatePolynomialNonzero := by
  intro n hnext
  rcases hCoeff n hnext with ⟨k, hk⟩
  exact
    atlasCompleteChiralRawAggregateRealPolynomial_ne_zero_of_coeff_ne_zero
      n hnext k hk

/-- A single nonzero imaginary coefficient proves nonzero status of one
concrete atlas imaginary aggregate polynomial. -/
theorem atlasCompleteChiralRawAggregateImagPolynomial_ne_zero_of_coeff_ne_zero
    (n : ℕ) (hnext : n + 1 ≤ 140) (k : ℕ)
    (hCoeff :
      atlasCompleteChiralRawAggregateImagCoeff n hnext k ≠ 0) :
    atlasCompleteChiralRawAggregateImagPolynomial n hnext ≠ 0 := by
  intro hZero
  apply hCoeff
  unfold atlasCompleteChiralRawAggregateImagCoeff
  rw [hZero]
  simp

/-- Imaginary coefficient witnesses imply the imaginary-polynomial nonzero
gate. -/
theorem completeChiralAtlasImagAggregatePolynomialNonzero_of_coeff_nonzero
    (hCoeff : CompleteChiralAtlasImagAggregateCoeffNonzero) :
    CompleteChiralAtlasImagAggregatePolynomialNonzero := by
  intro n hnext
  rcases hCoeff n hnext with ⟨k, hk⟩
  exact
    atlasCompleteChiralRawAggregateImagPolynomial_ne_zero_of_coeff_ne_zero
      n hnext k hk

/-- Signed transition-fiber witnesses imply the coefficient gate. -/
theorem completeChiralAtlasRealAggregateCoeffNonzero_of_signedFiberSum_nonzero
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero) :
    CompleteChiralAtlasRealAggregateCoeffNonzero := by
  intro n hnext
  rcases hSum n hnext with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [atlasCompleteChiralRawAggregateRealCoeff_eq_signedFiberSum]
  exact hk

/-- Imaginary signed transition-fiber witnesses imply the imaginary
coefficient gate. -/
theorem completeChiralAtlasImagAggregateCoeffNonzero_of_signedFiberSum_nonzero
    (hSum : CompleteChiralAtlasImagAggregateSignedFiberSumNonzero) :
    CompleteChiralAtlasImagAggregateCoeffNonzero := by
  intro n hnext
  rcases hSum n hnext with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  rw [atlasCompleteChiralRawAggregateImagCoeff_eq_signedFiberSum]
  exact hk

/-- Nonzero real-part polynomial certificate implies nonzero raw coherent
aggregate on one concrete atlas birth. -/
theorem atlasCompleteChiralRawAggregate_ne_zero_of_realPolynomial_ne_zero
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140)
    (hPolynomial :
      atlasCompleteChiralRawAggregateRealPolynomial n hnext ≠ 0) :
    atlasCompleteChiralRawAggregate chirality n hnext ≠ 0 := by
  intro hZero
  have hRealZero := congrArg Complex.re hZero
  rw [atlasCompleteChiralRawAggregate_re_eq_realPolynomial_eval] at hRealZero
  have hPolynomialZero :
      atlasCompleteChiralRawAggregateRealPolynomial n hnext = 0 :=
    (transcendental_iff.mp canonicalPairCoupling_transcendental)
      (atlasCompleteChiralRawAggregateRealPolynomial n hnext) (by
        simpa [Polynomial.aeval_def] using hRealZero)
  exact hPolynomial hPolynomialZero

/-- The current finite obstruction can be attacked by proving 140 concrete
integer polynomials nonzero. -/
theorem completeChiralAtlasRawAggregateNonzero_of_realPolynomial_nonzero
    (chirality : Fin 2)
    (hPolynomial : CompleteChiralAtlasRealAggregatePolynomialNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  intro n hnext
  exact atlasCompleteChiralRawAggregate_ne_zero_of_realPolynomial_ne_zero
    chirality n hnext (hPolynomial n hnext)

/-- Imaginary-polynomial certificates imply the raw coherent noncancellation
gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_imagPolynomial_nonzero
    (chirality : Fin 2)
    (hPolynomial : CompleteChiralAtlasImagAggregatePolynomialNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  intro n hnext
  exact atlasCompleteChiralRawAggregate_ne_zero_of_imagPolynomial_ne_zero
    chirality n hnext (hPolynomial n hnext)

/-- Coefficient witnesses imply the raw coherent noncancellation gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_realCoeff_nonzero
    (chirality : Fin 2)
    (hCoeff : CompleteChiralAtlasRealAggregateCoeffNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  exact
    completeChiralAtlasRawAggregateNonzero_of_realPolynomial_nonzero chirality
      (completeChiralAtlasRealAggregatePolynomialNonzero_of_coeff_nonzero
        hCoeff)

/-- Imaginary coefficient witnesses imply the raw coherent noncancellation
gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_imagCoeff_nonzero
    (chirality : Fin 2)
    (hCoeff : CompleteChiralAtlasImagAggregateCoeffNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  exact
    completeChiralAtlasRawAggregateNonzero_of_imagPolynomial_nonzero chirality
      (completeChiralAtlasImagAggregatePolynomialNonzero_of_coeff_nonzero
        hCoeff)

/-- Signed transition-fiber witnesses imply the raw coherent noncancellation
gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_signedFiberSum_nonzero
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  exact completeChiralAtlasRawAggregateNonzero_of_realCoeff_nonzero chirality
    (completeChiralAtlasRealAggregateCoeffNonzero_of_signedFiberSum_nonzero
      hSum)

/-- Imaginary signed transition-fiber witnesses imply the raw coherent
noncancellation gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_imagSignedFiberSum_nonzero
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasImagAggregateSignedFiberSumNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  exact completeChiralAtlasRawAggregateNonzero_of_imagCoeff_nonzero chirality
    (completeChiralAtlasImagAggregateCoeffNonzero_of_signedFiberSum_nonzero
      hSum)

/-- Mixed real/imaginary signed transition-fiber witnesses imply the raw
coherent noncancellation gate. -/
theorem completeChiralAtlasRawAggregateNonzero_of_complexSignedFiberSum_nonzero
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasComplexSignedFiberSumNonzero) :
    CompleteChiralAtlasRawAggregateNonzero chirality := by
  intro n hnext
  rcases hSum n hnext with hReal | hImag
  · rcases hReal with ⟨k, hk⟩
    exact atlasCompleteChiralRawAggregate_ne_zero_of_realPolynomial_ne_zero
      chirality n hnext
      (atlasCompleteChiralRawAggregateRealPolynomial_ne_zero_of_coeff_ne_zero
        n hnext k (by
          rw [atlasCompleteChiralRawAggregateRealCoeff_eq_signedFiberSum]
          exact hk))
  · rcases hImag with ⟨k, hk⟩
    exact atlasCompleteChiralRawAggregate_ne_zero_of_imagPolynomial_ne_zero
      chirality n hnext
      (atlasCompleteChiralRawAggregateImagPolynomial_ne_zero_of_coeff_ne_zero
        n hnext k (by
          rw [atlasCompleteChiralRawAggregateImagCoeff_eq_signedFiberSum]
          exact hk))

/-- The finite noncancellation gate needed to promote the already-physical
atlas path from the uniform law to the complete chiral law. -/
def CompleteChiralAtlasTransitionNonzero (chirality : Fin 2) : Prop :=
  ∀ (n : ℕ) (hnext : n + 1 ≤ 140),
    atlasCompleteChiralTransition chirality n hnext ≠ 0

/-- Raw coherent noncancellation is equivalent to normalized transition
noncancellation for the atlas path, because the complete-chiral denominator is
already proved nonzero at every parent. -/
theorem completeChiralAtlasRawAggregateNonzero_iff_transition_nonzero
    (chirality : Fin 2) :
    CompleteChiralAtlasRawAggregateNonzero chirality ↔
      CompleteChiralAtlasTransitionNonzero chirality := by
  constructor
  · intro hRaw n hnext
    rw [atlasCompleteChiralTransition_eq_rawAggregate_div_partition]
    exact div_ne_zero (hRaw n hnext)
      (atlasCompleteChiralPartition_ne_zero chirality n hnext)
  · intro hTransition n hnext
    by_contra hRawZero
    have hTransitionZero :
        atlasCompleteChiralTransition chirality n hnext = 0 := by
      rw [atlasCompleteChiralTransition_eq_rawAggregate_div_partition,
        hRawZero]
      simp
    exact hTransition n hnext hTransitionZero

/-- A direct one-way form for applying the raw finite noncancellation gate. -/
theorem completeChiralAtlasTransition_nonzero_of_rawAggregate_nonzero
    (chirality : Fin 2)
    (hRaw : CompleteChiralAtlasRawAggregateNonzero chirality) :
    CompleteChiralAtlasTransitionNonzero chirality :=
  (completeChiralAtlasRawAggregateNonzero_iff_transition_nonzero
    chirality).mp hRaw

/-- Every atlas birth used in the noncancellation gate is already physically
admissible as a one-element causal growth step. -/
theorem atlasStep_isPhysical
    (n : ℕ) (hnext : n + 1 ≤ 140) :
    IsPhysicalCausalGrowthStep n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext) := by
  exact (globalAtlasPhysicalGrowthPath_isPhysical (n + 1) hnext).2

/-- Outside the physical one-element extension graph, the complete chiral law
assigns zero transition amplitude.  Thus `CompleteChiralAtlasTransitionNonzero`
is precisely a coherent-aggregate noncancellation condition on physical atlas
births, not an additional support/admissibility assumption. -/
theorem completeChiral_atlasStep_support_gate
    (chirality : Fin 2) (n : ℕ) (hnext : n + 1 ≤ 140) :
    IsPhysicalCausalGrowthStep n
      (atlasStepPrefix n hnext) (atlasStepChild n hnext) ∧
    (¬ IsPhysicalCausalGrowthStep n
        (atlasStepPrefix n hnext) (atlasStepChild n hnext) →
      atlasCompleteChiralTransition chirality n hnext = 0) := by
  exact
    ⟨atlasStep_isPhysical n hnext,
      fun hNotPhysical =>
        UnifiedTheory.Audit.KFCausalSetCompleteChiralLaw.completeChiralCausalSetGrowthLaw_transition_eq_zero_of_not_physical
          chirality n (atlasStepPrefix n hnext)
          (atlasStepChild n hnext) hNotPhysical⟩

/-- If none of the 140 complete-chiral atlas transitions cancels after
unlabeled aggregation, every finite prefix of the atlas path has nonzero
complete-chiral path amplitude. -/
theorem globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : CompleteChiralAtlasTransitionNonzero chirality) :
    ∀ (n : ℕ) (h : n ≤ 140),
      finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) n
          (globalAtlasPhysicalGrowthPath n h) ≠ 0
  | 0, _ => by simp [finiteRankedPathAmplitude]
  | n + 1, h => by
      change
        finiteRankedPathAmplitude
            (completeChiralCausalSetGrowthLaw chirality) n
            (atlasStepPrefix n h) *
          atlasCompleteChiralTransition chirality n h ≠ 0
      exact mul_ne_zero
        (globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
          chirality hNonzero n (Nat.le_trans (Nat.le_succ n) h))
        (hNonzero n h)

/-- Conditional complete-chiral physical CSpec realization theorem.

The only remaining input is the finite noncancellation gate
`CompleteChiralAtlasTransitionNonzero chirality`; all order-theoretic
physicality and determinant-sector data are inherited from the already proved
physical atlas realization. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_transition_nonzero
    (chirality : Fin 2)
    (hNonzero : CompleteChiralAtlasTransitionNonzero chirality) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    ⟨globalAtlasPhysicalGrowthPath_isPhysical 140 le_rfl,
      globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
        chirality hNonzero 140 le_rfl,
      ⟨globalAtlasPhysicalEndpointOrderIso⟩,
      globalAtlasPhysicalEndpoint_containsBooleanCubeSeed,
      cSpecOddLoopHistory_orientation,
      cSpecOddLoop_derives_rightWeakMirror⟩

/-- Final raw-gate version of the complete-chiral physical CSpec realization
theorem.  All normalization denominators are discharged by the zero-free
complete chiral law; the only remaining finite input is raw coherent
noncancellation on the 140 atlas births. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_rawAggregate_nonzero
    (chirality : Fin 2)
    (hRaw : CompleteChiralAtlasRawAggregateNonzero chirality) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_transition_nonzero
      chirality
      (completeChiralAtlasTransition_nonzero_of_rawAggregate_nonzero
        chirality hRaw)

/-- Real-polynomial certificate version of the complete-chiral physical CSpec
realization theorem.  This reduces the next obstruction to proving nonzero
status of 140 explicit integer transition-fiber polynomials. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realPolynomial_nonzero
    (chirality : Fin 2)
    (hPolynomial : CompleteChiralAtlasRealAggregatePolynomialNonzero) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_rawAggregate_nonzero
      chirality
      (completeChiralAtlasRawAggregateNonzero_of_realPolynomial_nonzero
        chirality hPolynomial)

/-- Coefficient-certificate version of the complete-chiral physical CSpec
realization theorem.  The remaining finite input is now one nonzero signed
real coefficient for each of the 140 atlas-birth aggregate polynomials. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realCoeff_nonzero
    (chirality : Fin 2)
    (hCoeff : CompleteChiralAtlasRealAggregateCoeffNonzero) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realPolynomial_nonzero
      chirality
      (completeChiralAtlasRealAggregatePolynomialNonzero_of_coeff_nonzero
        hCoeff)

/-- Signed-fiber-sum version of the complete-chiral physical CSpec realization
theorem.  The remaining finite input is now an explicit nonzero signed count
over the labeled transition fiber for each atlas birth. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_signedFiberSum_nonzero
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasRealAggregateSignedFiberSumNonzero) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realCoeff_nonzero
      chirality
      (completeChiralAtlasRealAggregateCoeffNonzero_of_signedFiberSum_nonzero
        hSum)

/-- Mixed real/imaginary signed-fiber-sum version of the complete-chiral
physical CSpec realization theorem.  This is the corrected finite target for
atlas births whose real coefficient channel vanishes but whose imaginary
channel is nonzero. -/
theorem completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_complexSignedFiberSum_nonzero
    (chirality : Fin 2)
    (hSum : CompleteChiralAtlasComplexSignedFiberSumNonzero) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude
          (completeChiralCausalSetGrowthLaw chirality) 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ Nonempty
          (CausalOrderPoint (globalAtlasPhysicalPrefix 140 le_rfl) ≃o
            GlobalAtlasEvent)
      ∧ ContainsBooleanCubeSeed (globalAtlasPhysicalPrefix 140 le_rfl)
      ∧ cSpecAtlasOrientation 3 cSpecOddLoopHistory = -1
      ∧ IsNontrivialPurelyRightHanded
          (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory) := by
  exact
    completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_rawAggregate_nonzero
      chirality
      (completeChiralAtlasRawAggregateNonzero_of_complexSignedFiberSum_nonzero
        chirality hSum)

#print axioms atlasCompleteChiralTransition_eq_rawAggregate_div_partition
#print axioms atlasCompleteChiralRawAggregate_re_eq_realPolynomial_eval
#print axioms atlasCompleteChiralRawAggregateRealCoeff_eq_signedFiberSum
#print axioms atlasCompleteChiralRawAggregateImagCoeff_eq_signedFiberSum
#print axioms completeChiralAtlasRealAggregateSignedFiberSumNonzero_of_witnessTable
#print axioms completeChiralAtlasComplexSignedFiberSumNonzero_of_witnessTable
#print axioms completeChiralAtlasComplexSignedFiberSumNonzero_of_realSignedFiberSum_nonzero
#print axioms atlasCompleteChiralRawAggregateRealPolynomial_ne_zero_of_coeff_ne_zero
#print axioms atlasCompleteChiralRawAggregateImagPolynomial_ne_zero_of_coeff_ne_zero
#print axioms completeChiralAtlasRealAggregatePolynomialNonzero_of_coeff_nonzero
#print axioms completeChiralAtlasImagAggregatePolynomialNonzero_of_coeff_nonzero
#print axioms completeChiralAtlasRealAggregateCoeffNonzero_of_signedFiberSum_nonzero
#print axioms completeChiralAtlasImagAggregateCoeffNonzero_of_signedFiberSum_nonzero
#print axioms atlasCompleteChiralRawAggregate_ne_zero_of_realPolynomial_ne_zero
#print axioms atlasCompleteChiralRawAggregate_ne_zero_of_imagPolynomial_ne_zero
#print axioms completeChiralAtlasRawAggregateNonzero_of_realPolynomial_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_imagPolynomial_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_realCoeff_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_imagCoeff_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_signedFiberSum_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_imagSignedFiberSum_nonzero
#print axioms completeChiralAtlasRawAggregateNonzero_of_complexSignedFiberSum_nonzero
#print axioms atlasCompleteChiralPartition_ne_zero
#print axioms completeChiralAtlasRawAggregateNonzero_iff_transition_nonzero
#print axioms completeChiralAtlasTransition_nonzero_of_rawAggregate_nonzero
#print axioms atlasStep_isPhysical
#print axioms completeChiral_atlasStep_support_gate
#print axioms globalAtlasPhysicalGrowthPath_completeChiralAmplitude_ne_zero_of_transition_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_transition_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_rawAggregate_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realPolynomial_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_realCoeff_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_signedFiberSum_nonzero
#print axioms completeChiral_physicalGrowth_realizes_fullS3_CSpec_determinantSector_of_complexSignedFiberSum_nonzero

end

end UnifiedTheory.Audit.KFCausalCSpecPhysicalChiralGrowthRealization
