/-
  Audit/KFCausalNativeSuccessorInstrument.lean

  THE NATIVE CAUSAL SUCCESSOR INSTRUMENT

  `KFCausalNativeSuccessorRecord` derives the finite record carrier from the
  actual unlabeled children of a causal parent.  This module closes the
  finite-dimensional channel question while separating two operations that
  must not be conflated.

  * Coherent forgetting is the codiagonal on amplitudes.  It implements the
    independent-ket/bra cylinder sum, but for a genuinely branching record it
    is not a trace-preserving single-Kraus operation.
  * Physical record erasure is the partial trace.  Applied to the native
    recorded Stinespring state, it gives the Kraus channel indexed by the
    actual causal children.

  A harmless enumeration through `Fintype.equivFin` packages that intrinsic
  channel in the repository's `KrausRepresentation` API.  The induced map is
  independent of the enumeration because it is proved equal to the intrinsic
  sum over the native successor subtype.

  Finally, the canonical harmonic scalar law supplies a CPTP native
  instrument at every parent.  Its reduced one-dimensional channel is exactly
  the identity.  Thus the child record carries the causal information; the
  reduced scalar carrier cannot be a nontrivial laboratory observable.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalNativeSuccessorRecord
import UnifiedTheory.LayerB.KrausExistence

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNativeSuccessorInstrument

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.PartialTrace
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalNativeSuccessorRecord

/-! ## 1. The intrinsic native-child Kraus channel -/

/-- The channel sum indexed directly by genuine physical causal children.
No enumeration enters this definition. -/
def nativeCausalKrausMap {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension) :
    SquareMatrix dimension → SquareMatrix dimension :=
  fun density =>
    ∑ outcome, operator outcome * density * (operator outcome)ᴴ

/-- Tracing the native child record out of the Stinespring state gives the
intrinsic native-child channel exactly. -/
theorem nativeCausalKrausMap_eq_recordPartialTrace
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (density : SquareMatrix dimension) :
    partialTrace_right
        (nativeCausalRecordedDilation operator * density *
          (nativeCausalRecordedDilation operator)ᴴ) =
      nativeCausalKrausMap operator density := by
  exact partialTrace_right_krausToStinespring operator density

/-- Born completeness makes the intrinsic native-child channel trace
preserving. -/
theorem nativeCausalKrausMap_trace
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension))
    (density : SquareMatrix dimension) :
    Matrix.trace (nativeCausalKrausMap operator density) =
      Matrix.trace density := by
  unfold nativeCausalKrausMap
  rw [Matrix.trace_sum]
  have hTerm : ∀ outcome,
      Matrix.trace
          (operator outcome * density * (operator outcome)ᴴ) =
        Matrix.trace ((operator outcome)ᴴ * operator outcome * density) := by
    intro outcome
    rw [Matrix.trace_mul_comm (operator outcome * density)
      (operator outcome)ᴴ, Matrix.mul_assoc]
  simp_rw [hTerm]
  rw [← Matrix.trace_sum, ← Finset.sum_mul, hComplete, Matrix.one_mul]

/-- Reindex the native successor fiber only to enter the existing
`Fin k`-indexed Kraus API.  The physical outcome type remains intrinsic. -/
def nativeCausalSuccessorEquivFin (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    NativeCausalSuccessor n pathPrefix ≃
      Fin (Fintype.card (NativeCausalSuccessor n pathPrefix)) :=
  Fintype.equivFin _

/-- The enumerated matrix family used internally by `KrausRepresentation`. -/
def enumeratedNativeCausalOperator {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (index : Fin (Fintype.card (NativeCausalSuccessor n pathPrefix))) :
    SquareMatrix dimension :=
  operator ((nativeCausalSuccessorEquivFin n pathPrefix).symm index)

/-- Every Born-complete native causal operator family canonically determines
a finite Kraus representation.  Enumeration is an implementation detail. -/
def nativeCausalInstrument {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)) :
    KrausRepresentation dimension dimension
      (Fintype.card (NativeCausalSuccessor n pathPrefix)) where
  K := enumeratedNativeCausalOperator operator
  complete := by
    change (∑ index,
      (operator ((nativeCausalSuccessorEquivFin n pathPrefix).symm index))ᴴ *
        operator ((nativeCausalSuccessorEquivFin n pathPrefix).symm index)) = _
    have hReindex :
        (∑ index : Fin (Fintype.card
            (NativeCausalSuccessor n pathPrefix)),
          (operator ((nativeCausalSuccessorEquivFin n pathPrefix).symm index))ᴴ *
            operator
              ((nativeCausalSuccessorEquivFin n pathPrefix).symm index)) =
        ∑ outcome : NativeCausalSuccessor n pathPrefix,
          (operator outcome)ᴴ * operator outcome :=
      (nativeCausalSuccessorEquivFin n pathPrefix).symm.sum_comp
        (fun outcome => (operator outcome)ᴴ * operator outcome)
    rw [hReindex, hComplete]

/-- The native causal instrument is genuinely completely positive and trace
preserving in the repository's Choi/Kraus sense. -/
theorem nativeCausalInstrument_isCPTP
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension)) :
    IsCPTP (nativeCausalInstrument operator hComplete).toLinearMap :=
  kraus_isCPTP _

/-- The enumerated Kraus representation induces exactly the intrinsic sum
over physical children, so no physical result depends on the enumeration. -/
theorem nativeCausalInstrument_apply_eq_intrinsic
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix dimension))
    (density : SquareMatrix dimension) :
    (nativeCausalInstrument operator hComplete).apply density =
      nativeCausalKrausMap operator density := by
  unfold KrausRepresentation.apply nativeCausalKrausMap
  change (∑ index,
      operator ((nativeCausalSuccessorEquivFin n pathPrefix).symm index) *
        density *
          (operator
            ((nativeCausalSuccessorEquivFin n pathPrefix).symm index))ᴴ) = _
  exact (nativeCausalSuccessorEquivFin n pathPrefix).symm.sum_comp
    (fun outcome => operator outcome * density * (operator outcome)ᴴ)

/-! ## 2. Physical erasure versus coherent amplitude recombination -/

/-- The state-independent physical operation that forgets the child record is
the partial trace over the native successor fiber. -/
def nativeCausalRecordErasure {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n} :
    Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
      (NativeCausalRecordCarrier dimension n pathPrefix) ℂ →
        SquareMatrix dimension :=
  partialTrace_right

theorem nativeCausalRecordErasure_trace
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (recordedDensity :
      Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
        (NativeCausalRecordCarrier dimension n pathPrefix) ℂ) :
    Matrix.trace (nativeCausalRecordErasure recordedDensity) =
      Matrix.trace recordedDensity := by
  exact trace_partialTrace_right recordedDensity

theorem nativeCausalRecordErasure_isHermitian
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    {recordedDensity :
      Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
        (NativeCausalRecordCarrier dimension n pathPrefix) ℂ}
    (hHermitian : recordedDensity.IsHermitian) :
    (nativeCausalRecordErasure recordedDensity).IsHermitian :=
  isHermitian_partialTrace_right hHermitian

theorem nativeCausalRecordErasure_posSemidef
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    {recordedDensity :
      Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
        (NativeCausalRecordCarrier dimension n pathPrefix) ℂ}
    (hPositive : recordedDensity.PosSemidef) :
    (nativeCausalRecordErasure recordedDensity).PosSemidef :=
  posSemidef_partialTrace_right hPositive

/-- The native partial trace recovers the intrinsic CPTP channel from the
recorded dilation. -/
theorem nativeCausalRecordErasure_recovers_channel
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (operator : NativeCausalSuccessor n pathPrefix →
      SquareMatrix dimension)
    (density : SquareMatrix dimension) :
    nativeCausalRecordErasure
        (nativeCausalRecordedDilation operator * density *
          (nativeCausalRecordedDilation operator)ᴴ) =
      nativeCausalKrausMap operator density :=
  nativeCausalKrausMap_eq_recordPartialTrace operator density

/-- A coherent codiagonal with at least two distinct record outcomes is not
an isometry.  Consequently it cannot be the sole Kraus operator of a
trace-preserving erasure channel. -/
theorem nativeCausalRecordCounit_not_singleKrausComplete
    {dimension n : ℕ}
    {pathPrefix : RankedGrowthPath CausalSetGrowthBranch n}
    (carrier : Fin dimension)
    (first second : NativeCausalSuccessor n pathPrefix)
    (hDistinct : first ≠ second) :
    (nativeCausalRecordCounit dimension n pathPrefix)ᴴ *
          nativeCausalRecordCounit dimension n pathPrefix ≠
        (1 : Matrix (NativeCausalRecordCarrier dimension n pathPrefix)
          (NativeCausalRecordCarrier dimension n pathPrefix) ℂ) := by
  intro hComplete
  have hEntry := congr_fun
    (congr_fun hComplete (carrier, first)) (carrier, second)
  simp [nativeCausalRecordCounit, nativeCausalRecordProjection,
    Matrix.mul_apply, hDistinct] at hEntry

/-! ## 3. Canonical harmonic native instrument -/

/-- The all-rank harmonic causal amplitudes, lifted to the rank-one carrier,
give a native instrument with actual causal children as outcomes. -/
def nativeHarmonicCausalInstrument (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    KrausRepresentation 1 1
      (Fintype.card (NativeCausalSuccessor n pathPrefix)) :=
  nativeCausalInstrument
    (nativeHarmonicCausalOperator chirality n pathPrefix)
    (nativeHarmonicCausalOperator_complete chirality n pathPrefix)

theorem nativeHarmonicCausalInstrument_isCPTP
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsCPTP
      (nativeHarmonicCausalInstrument chirality n pathPrefix).toLinearMap :=
  nativeCausalInstrument_isCPTP _
    (nativeHarmonicCausalOperator_complete chirality n pathPrefix)

/-- Every trace-preserving channel on the one-dimensional carrier is the
identity.  Hence the reduced harmonic native channel contains no causal or
chiral discriminator; that information lives in the resolved child record. -/
theorem nativeHarmonicCausalInstrument_apply_eq_identity
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (density : SquareMatrix 1) :
    (nativeHarmonicCausalInstrument chirality n pathPrefix).apply density =
      density := by
  ext row column
  fin_cases row
  fin_cases column
  have hTrace :=
    (nativeHarmonicCausalInstrument chirality n pathPrefix).trace_apply density
  simpa [Matrix.trace, Fin.sum_univ_one] using hTrace

/-- The resolved operation for one actual causal child.  Unlike the reduced
channel, this retains which causal continuation occurred. -/
def nativeHarmonicOutcomeOperation
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (outcome : NativeCausalSuccessor n pathPrefix)
    (density : SquareMatrix 1) : SquareMatrix 1 :=
  nativeHarmonicCausalOperator chirality n pathPrefix outcome * density *
    (nativeHarmonicCausalOperator chirality n pathPrefix outcome)ᴴ

/-- The trace weight of a resolved child is its native causal Born weight,
times the incoming trace.  Thus the instrument has an exact operational
record even though its unconditioned scalar channel is the identity. -/
theorem nativeHarmonicOutcomeOperation_trace
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (outcome : NativeCausalSuccessor n pathPrefix)
    (density : SquareMatrix 1) :
    Matrix.trace
        (nativeHarmonicOutcomeOperation chirality n pathPrefix outcome density) =
      (star (nativeHarmonicCausalAmplitude chirality n pathPrefix outcome) *
        nativeHarmonicCausalAmplitude chirality n pathPrefix outcome) *
          Matrix.trace density := by
  simp [nativeHarmonicOutcomeOperation, nativeHarmonicCausalOperator,
    Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply]
  ring

/-- Erasing the record makes every harmonic scalar channel identical: it
forgets the parent, rank, and chirality.  This is the exact reduced-channel
no-go behind the statement that the new information lives in correlations
with the causal record. -/
theorem nativeHarmonicReducedChannel_causalDataBlind
    (firstChirality secondChirality : Fin 2)
    (firstRank secondRank : ℕ)
    (firstPrefix : RankedGrowthPath CausalSetGrowthBranch firstRank)
    (secondPrefix : RankedGrowthPath CausalSetGrowthBranch secondRank)
    (density : SquareMatrix 1) :
    (nativeHarmonicCausalInstrument firstChirality firstRank firstPrefix).apply
        density =
      (nativeHarmonicCausalInstrument secondChirality secondRank
        secondPrefix).apply density := by
  rw [nativeHarmonicCausalInstrument_apply_eq_identity,
    nativeHarmonicCausalInstrument_apply_eq_identity]

/-- The physically correct native record erasure therefore recovers the
incoming scalar state exactly for the canonical harmonic law. -/
theorem nativeHarmonicRecordErasure_recovers_input
    (chirality : Fin 2) (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (density : SquareMatrix 1) :
    nativeCausalRecordErasure
        (nativeCausalRecordedDilation
            (nativeHarmonicCausalOperator chirality n pathPrefix) * density *
          (nativeCausalRecordedDilation
            (nativeHarmonicCausalOperator chirality n pathPrefix))ᴴ) =
      density := by
  rw [nativeCausalRecordErasure_recovers_channel]
  rw [← nativeCausalInstrument_apply_eq_intrinsic
    (nativeHarmonicCausalOperator chirality n pathPrefix)
    (nativeHarmonicCausalOperator_complete chirality n pathPrefix)]
  exact nativeHarmonicCausalInstrument_apply_eq_identity
    chirality n pathPrefix density

/-! ## 4. Capstone and axiom audit -/

/-- The finite channel problem is closed: actual causal children index a
genuine CPTP instrument, the native partial trace is its state-independent
record erasure, and the harmonic realization exists at every rank.  The same
theorem exposes the remaining physical limit: after erasure the scalar
carrier evolves trivially, so nontrivial observables require the resolved
record or a higher-rank operator law. -/
theorem causalNativeSuccessorInstrument_capstone :
    (∀ (chirality : Fin 2) (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      IsCPTP
        (nativeHarmonicCausalInstrument chirality n pathPrefix).toLinearMap) ∧
    (∀ (chirality : Fin 2) (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (density : SquareMatrix 1),
      (nativeHarmonicCausalInstrument chirality n pathPrefix).apply density =
        density) ∧
    (∀ (firstChirality secondChirality : Fin 2)
      (firstRank secondRank : ℕ)
      (firstPrefix : RankedGrowthPath CausalSetGrowthBranch firstRank)
      (secondPrefix : RankedGrowthPath CausalSetGrowthBranch secondRank)
      (density : SquareMatrix 1),
      (nativeHarmonicCausalInstrument firstChirality firstRank firstPrefix).apply
          density =
        (nativeHarmonicCausalInstrument secondChirality secondRank
          secondPrefix).apply density) ∧
    (∀ (chirality : Fin 2) (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (density : SquareMatrix 1),
      nativeCausalRecordErasure
          (nativeCausalRecordedDilation
              (nativeHarmonicCausalOperator chirality n pathPrefix) * density *
            (nativeCausalRecordedDilation
              (nativeHarmonicCausalOperator chirality n pathPrefix))ᴴ) =
        density) := by
  exact ⟨nativeHarmonicCausalInstrument_isCPTP,
    nativeHarmonicCausalInstrument_apply_eq_identity,
    nativeHarmonicReducedChannel_causalDataBlind,
    nativeHarmonicRecordErasure_recovers_input⟩

#print axioms nativeCausalKrausMap_eq_recordPartialTrace
#print axioms nativeCausalKrausMap_trace
#print axioms nativeCausalInstrument_isCPTP
#print axioms nativeCausalInstrument_apply_eq_intrinsic
#print axioms nativeCausalRecordErasure_trace
#print axioms nativeCausalRecordErasure_isHermitian
#print axioms nativeCausalRecordErasure_posSemidef
#print axioms nativeCausalRecordCounit_not_singleKrausComplete
#print axioms nativeHarmonicCausalInstrument_isCPTP
#print axioms nativeHarmonicCausalInstrument_apply_eq_identity
#print axioms nativeHarmonicOutcomeOperation_trace
#print axioms nativeHarmonicReducedChannel_causalDataBlind
#print axioms nativeHarmonicRecordErasure_recovers_input
#print axioms causalNativeSuccessorInstrument_capstone

end

end UnifiedTheory.Audit.KFCausalNativeSuccessorInstrument
