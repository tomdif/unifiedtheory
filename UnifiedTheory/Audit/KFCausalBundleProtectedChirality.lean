/-
  Audit/KFCausalBundleProtectedChirality.lean

  BUNDLE-VALUED CAUSAL RECORDS WITH SIGN-TWISTED CHIRALITY

  Sequential growth preserves finite cylinder records because every child
  retains its prefix.  A same-carrier history dephasing, however, erases the
  orientation characters.  This file proves the smallest escape compatible
  with the repository's full-S3 sheet holonomy.

  The standard two-coordinate sheet representation has two adjacent
  transposition generators.  Their ordinary commutant is scalar, but there is
  a nonzero parity-odd operator J which anticommutes with both.  Multiplication
  by i makes J Hermitian for the intrinsic sheet Gram form.  When the causal
  orientation label flips on an odd sheet transport, the product Xi iJ is
  transported exactly.

  The history carrier is a direct sum of these internal fibers, represented
  finitely by History x Internal.  Record pinching removes only matrix entries
  between different histories and fixes every within-history fiber operator.
  Thus cylinder facts can become classical without erasing the relational
  chirality operator.  No global tensor-product factorization is assumed.

  The final concrete step is still isolated honestly: actual causal/CSpec
  growth must assign the already formalized sheet transports to its physical
  edges.  This file proves the operator law once those intrinsic transports
  are the two generating odd holonomies.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCylinderRecordTransport
import UnifiedTheory.Audit.KFCausalSheetGaugeNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalBundleProtectedChirality

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCylinderRecordTransport

universe u v

/-! ## 1. The parity-odd operator in the standard S3 carrier -/

/-- First adjacent sheet transposition in the basis
`e1=(1,-1,0), e2=(0,1,-1)`, now over the complex numbers. -/
def sheetSwapZeroOne : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(-1 : ℂ), 1; 0, 1]

/-- Second adjacent sheet transposition in the same carrier basis. -/
def sheetSwapOneTwo : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), 0; 1, -1]

/-- Intrinsic Gram form of the non-orthonormal basis `e1,e2`. -/
def sheetCarrierGram : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(2 : ℂ), -1; -1, 2]

/-- The unique (up to scale) orientation generator which changes sign under
both adjacent sheet transpositions. -/
def sheetOrientationGenerator : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(1 : ℂ), -2; 2, -1]

/-- Multiplication by `i` turns the Gram-skew orientation generator into a
Gram-Hermitian chirality observable.  Its square is `3 I`; normalization by
`sqrt 3` may be applied without changing any transport theorem. -/
def sheetChiralityObservable : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.I • sheetOrientationGenerator

theorem sheetSwapZeroOne_sq :
    sheetSwapZeroOne * sheetSwapZeroOne = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapZeroOne, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

theorem sheetSwapOneTwo_sq :
    sheetSwapOneTwo * sheetSwapOneTwo = 1 := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapOneTwo, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.one_apply]

/-- Both holonomy generators preserve the intrinsic sheet metric. -/
theorem sheetSwapZeroOne_gram_unitary :
    sheetSwapZeroOneᴴ * sheetCarrierGram * sheetSwapZeroOne =
      sheetCarrierGram := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapZeroOne, sheetCarrierGram, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

theorem sheetSwapOneTwo_gram_unitary :
    sheetSwapOneTwoᴴ * sheetCarrierGram * sheetSwapOneTwo =
      sheetCarrierGram := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapOneTwo, sheetCarrierGram, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_two]

/-- A transposition reverses the orientation generator. -/
theorem sheetSwapZeroOne_anticommutes_orientation :
    sheetSwapZeroOne * sheetOrientationGenerator =
      -(sheetOrientationGenerator * sheetSwapZeroOne) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapZeroOne, sheetOrientationGenerator,
      Matrix.mul_apply, Fin.sum_univ_two]

theorem sheetSwapOneTwo_anticommutes_orientation :
    sheetSwapOneTwo * sheetOrientationGenerator =
      -(sheetOrientationGenerator * sheetSwapOneTwo) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapOneTwo, sheetOrientationGenerator,
      Matrix.mul_apply, Fin.sum_univ_two]

/-- The sign-twisted commutant is one-dimensional: every complex operator
which reverses under both adjacent transpositions is a scalar multiple of
the orientation generator.  This is the parity-odd counterpart of the
ordinary commutant no-go. -/
theorem sheet_signTwisted_commutant_one_dimensional
    (operator : Matrix (Fin 2) (Fin 2) ℂ)
    (hZeroOne : sheetSwapZeroOne * operator =
      -(operator * sheetSwapZeroOne))
    (hOneTwo : sheetSwapOneTwo * operator =
      -(operator * sheetSwapOneTwo)) :
    operator = operator 0 0 • sheetOrientationGenerator := by
  have hC := congrArg (fun matrix => matrix 0 0) hZeroOne
  have hD := congrArg (fun matrix => matrix 0 1) hZeroOne
  have hB := congrArg (fun matrix => matrix 0 0) hOneTwo
  norm_num [sheetSwapZeroOne, sheetSwapOneTwo, Matrix.mul_apply,
    Fin.sum_univ_two] at hC hD hB
  have hc : operator 1 0 = 2 * operator 0 0 := by
    linear_combination hC
  have hd : operator 1 1 = -operator 0 0 := by
    linear_combination hD
  have hb : operator 0 1 = -2 * operator 0 0 := by
    linear_combination hB
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [sheetOrientationGenerator, Matrix.smul_apply, hb, hc, hd] <;> ring

theorem sheetSwapZeroOne_anticommutes_chirality :
    sheetSwapZeroOne * sheetChiralityObservable =
      -(sheetChiralityObservable * sheetSwapZeroOne) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapZeroOne, sheetChiralityObservable,
      sheetOrientationGenerator, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring

theorem sheetSwapOneTwo_anticommutes_chirality :
    sheetSwapOneTwo * sheetChiralityObservable =
      -(sheetChiralityObservable * sheetSwapOneTwo) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetSwapOneTwo, sheetChiralityObservable,
      sheetOrientationGenerator, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply] <;> ring

/-- The unnormalized chirality observable is Hermitian for the intrinsic Gram
form, even though the chosen sheet coordinates are not orthonormal. -/
theorem sheetChirality_gramHermitian :
    sheetChiralityObservableᴴ * sheetCarrierGram =
      sheetCarrierGram * sheetChiralityObservable := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    norm_num [sheetChiralityObservable, sheetOrientationGenerator,
      sheetCarrierGram, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.smul_apply, Fin.sum_univ_two, map_ofNat] <;> ring

/-- Its only missing normalization is the universal factor `sqrt 3`. -/
theorem sheetChirality_sq :
    sheetChiralityObservable * sheetChiralityObservable =
      (3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext row column
  fin_cases row <;> fin_cases column
  all_goals norm_num [sheetChiralityObservable, sheetOrientationGenerator,
    Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply,
    Fin.sum_univ_two]
  all_goals ring_nf
  all_goals norm_num [Complex.I_sq]

theorem sheetChirality_ne_zero : sheetChiralityObservable ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix => matrix 0 1) hZero
  norm_num [sheetChiralityObservable, sheetOrientationGenerator,
    Matrix.smul_apply] at hEntry

/-! ## 2. Direct-sum history fibers and record pinching -/

/-- Block pinching onto matrices which are diagonal only in the history
label.  All internal matrix entries within a history block survive. -/
noncomputable def blockRecordPinching {History : Type u} {Internal : Type v}
    (density : Matrix (History × Internal) (History × Internal) ℂ) :
    Matrix (History × Internal) (History × Internal) ℂ := by
  classical
  exact fun row column => if row.1 = column.1 then density row column else 0

theorem blockRecordPinching_apply_same {History : Type u}
    {Internal : Type v}
    (density : Matrix (History × Internal) (History × Internal) ℂ)
    (history : History) (row column : Internal) :
    blockRecordPinching density (history, row) (history, column) =
      density (history, row) (history, column) := by
  classical
  simp [blockRecordPinching]

theorem blockRecordPinching_apply_distinct {History : Type u}
    {Internal : Type v}
    (density : Matrix (History × Internal) (History × Internal) ℂ)
    {first second : History} (hDistinct : first ≠ second)
    (row column : Internal) :
    blockRecordPinching density (first, row) (second, column) = 0 := by
  classical
  simp [blockRecordPinching, hDistinct]

theorem blockRecordPinching_idempotent {History : Type u}
    {Internal : Type v}
    (density : Matrix (History × Internal) (History × Internal) ℂ) :
    blockRecordPinching (blockRecordPinching density) =
      blockRecordPinching density := by
  classical
  ext row column
  by_cases hSame : row.1 = column.1 <;>
    simp [blockRecordPinching, hSame]

/-- Block pinching preserves the total matrix trace.  Complete positivity is
standard for a block pinching, but is deliberately not folded into this
generic finite-type theorem: a state-independent physical instrument remains
a separate bridge in the claim ledger. -/
theorem blockRecordPinching_trace {History : Type u} {Internal : Type v}
    [Fintype History] [Fintype Internal]
    (density : Matrix (History × Internal) (History × Internal) ℂ) :
    Matrix.trace (blockRecordPinching density) = Matrix.trace density := by
  classical
  unfold Matrix.trace
  apply Finset.sum_congr rfl
  intro index _hIndex
  simp [blockRecordPinching]

/-- A history-dependent operator acting inside each internal fiber. -/
noncomputable def fiberwiseOperator {History : Type u} {Internal : Type v}
    (label : History → ℂ) (operator : Matrix Internal Internal ℂ) :
    Matrix (History × Internal) (History × Internal) ℂ := by
  classical
  exact fun row column =>
    if row.1 = column.1 then label row.1 * operator row.2 column.2 else 0

/-- Record formation fixes every within-history fiber observable. -/
theorem blockRecordPinching_fiberwiseOperator {History : Type u}
    {Internal : Type v}
    (label : History → ℂ) (operator : Matrix Internal Internal ℂ) :
    blockRecordPinching (fiberwiseOperator label operator) =
      fiberwiseOperator label operator := by
  classical
  ext row column
  by_cases hSame : row.1 = column.1 <;>
    simp [blockRecordPinching, fiberwiseOperator, hSame]

/-- In particular, the off-diagonal internal entry carrying sheet chirality
survives record pinching exactly. -/
theorem blockRecordPinching_preserves_sheetChirality {History : Type u}
    (orientation : History → ℂ) :
    blockRecordPinching
        (fiberwiseOperator orientation sheetChiralityObservable) =
      fiberwiseOperator orientation sheetChiralityObservable :=
  blockRecordPinching_fiberwiseOperator orientation sheetChiralityObservable

/-! ## 3. Bundle-valued sequential growth -/

/-- Sequential growth with an internal carrier transported along each birth
edge.  The direct-sum support is still fixed by prefix retention. -/
def bundleGrowthDilation {Branch : ℕ → Type u}
    [∀ rank, Fintype (Branch rank)] {Internal : Type v} [Fintype Internal]
    {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (transport : RankedGrowthPath Branch n → Branch n →
      Matrix Internal Internal ℂ) :
    Matrix ((RankedGrowthPath Branch n × Branch n) × Internal)
      (RankedGrowthPath Branch n × Internal) ℂ :=
  fun refined coarse =>
    if refined.1.1 = coarse.1 then
      transition coarse.1 refined.1.2 *
        transport coarse.1 refined.1.2 refined.2 coarse.2
    else 0

/-- Cylinder transport is unchanged by the internal sheet fiber: the record
projectors act as the identity within each block. -/
theorem bundleGrowth_transports_cylinder
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    {Internal : Type v} [Fintype Internal] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (transport : RankedGrowthPath Branch n → Branch n →
      Matrix Internal Internal ℂ)
    (event : Finset (RankedGrowthPath Branch n)) :
    finiteEventProjector ((oneStepCylinder event) ×ˢ Finset.univ) *
        bundleGrowthDilation transition transport =
      bundleGrowthDilation transition transport *
        finiteEventProjector (event ×ˢ Finset.univ) := by
  classical
  ext refined coarse
  obtain ⟨⟨refinedPrefix, branch⟩, refinedInternal⟩ := refined
  obtain ⟨coarsePrefix, coarseInternal⟩ := coarse
  by_cases hPrefix : refinedPrefix = coarsePrefix
  · subst coarsePrefix
    by_cases hMem : refinedPrefix ∈ event
    · rw [finiteEventProjector_mul_apply_of_mem _ _ _ _ (by
          simp [oneStepCylinder, hMem]),
        mul_finiteEventProjector_apply_of_mem _ _ _ _ (by simp [hMem])]
    · rw [finiteEventProjector_mul_apply_of_not_mem _ _ _ _ (by
          simp [oneStepCylinder, hMem]),
        mul_finiteEventProjector_apply_of_not_mem _ _ _ _ (by simp [hMem])]
  · by_cases hRefinedMem : refinedPrefix ∈ event
    · rw [finiteEventProjector_mul_apply_of_mem _ _ _ _ (by
          simp [oneStepCylinder, hRefinedMem])]
      by_cases hCoarseMem : coarsePrefix ∈ event
      · rw [mul_finiteEventProjector_apply_of_mem _ _ _ _ (by
            simp [hCoarseMem])]
      · rw [mul_finiteEventProjector_apply_of_not_mem _ _ _ _ (by
            simp [hCoarseMem])]
        simp [bundleGrowthDilation, hPrefix]
    · rw [finiteEventProjector_mul_apply_of_not_mem _ _ _ _ (by
          simp [oneStepCylinder, hRefinedMem])]
      by_cases hCoarseMem : coarsePrefix ∈ event
      · rw [mul_finiteEventProjector_apply_of_mem _ _ _ _ (by
            simp [hCoarseMem])]
        simp [bundleGrowthDilation, hPrefix]
      · rw [mul_finiteEventProjector_apply_of_not_mem _ _ _ _ (by
            simp [hCoarseMem])]

/-- Edgewise covariance condition for a relational internal observable. -/
def RelationalFiberTransport
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    {Internal : Type v} [Fintype Internal] {n : ℕ}
    (incomingLabel : RankedGrowthPath Branch n → ℂ)
    (outgoingLabel : RankedGrowthPath Branch n × Branch n → ℂ)
    (operator : Matrix Internal Internal ℂ)
    (transport : RankedGrowthPath Branch n → Branch n →
      Matrix Internal Internal ℂ) : Prop :=
  ∀ path branch,
    (outgoingLabel (path, branch) • operator) * transport path branch =
      transport path branch * (incomingLabel path • operator)

/-- Edgewise sign covariance promotes to the exact operator intertwiner on
the entire bundle-valued sequential-growth carrier. -/
theorem relationalFiberTransport_intertwiner
    {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
    {Internal : Type v} [Fintype Internal] {n : ℕ}
    (transition : RankedGrowthPath Branch n → Branch n → ℂ)
    (transport : RankedGrowthPath Branch n → Branch n →
      Matrix Internal Internal ℂ)
    (incomingLabel : RankedGrowthPath Branch n → ℂ)
    (outgoingLabel : RankedGrowthPath Branch n × Branch n → ℂ)
    (operator : Matrix Internal Internal ℂ)
    (hCovariant : RelationalFiberTransport incomingLabel outgoingLabel
      operator transport) :
    fiberwiseOperator outgoingLabel operator *
        bundleGrowthDilation transition transport =
      bundleGrowthDilation transition transport *
        fiberwiseOperator incomingLabel operator := by
  classical
  ext refined coarse
  obtain ⟨⟨refinedPrefix, branch⟩, refinedInternal⟩ := refined
  obtain ⟨coarsePrefix, coarseInternal⟩ := coarse
  by_cases hPrefix : refinedPrefix = coarsePrefix
  · subst coarsePrefix
    have hEntry := congrArg
      (fun matrix => matrix refinedInternal coarseInternal)
      (hCovariant refinedPrefix branch)
    have hEntry' :
        (∑ internal,
            outgoingLabel (refinedPrefix, branch) *
                operator refinedInternal internal *
              transport refinedPrefix branch internal coarseInternal) =
          ∑ internal,
            transport refinedPrefix branch refinedInternal internal *
              (incomingLabel refinedPrefix *
                operator internal coarseInternal) := by
      simpa only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul]
        using hEntry
    simp [Matrix.mul_apply, Fintype.sum_prod_type, fiberwiseOperator,
      bundleGrowthDilation]
    calc
      (∑ internal,
          outgoingLabel (refinedPrefix, branch) *
              operator refinedInternal internal *
            (transition refinedPrefix branch *
              transport refinedPrefix branch internal coarseInternal)) =
          transition refinedPrefix branch *
            ∑ internal,
              outgoingLabel (refinedPrefix, branch) *
                  operator refinedInternal internal *
                transport refinedPrefix branch internal coarseInternal := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro internal _hInternal
          ring
      _ = transition refinedPrefix branch *
            ∑ internal,
              transport refinedPrefix branch refinedInternal internal *
                (incomingLabel refinedPrefix *
                  operator internal coarseInternal) := by rw [hEntry']
      _ = ∑ internal,
          transition refinedPrefix branch *
            (transport refinedPrefix branch refinedInternal internal *
              (incomingLabel refinedPrefix *
                operator internal coarseInternal)) := by
          rw [Finset.mul_sum]
      _ = ∑ internal,
          transition refinedPrefix branch *
              transport refinedPrefix branch refinedInternal internal *
            (incomingLabel refinedPrefix *
              operator internal coarseInternal) := by
          apply Finset.sum_congr rfl
          intro internal _hInternal
          ring
  · simp [Matrix.mul_apply, Fintype.sum_prod_type, fiberwiseOperator,
      bundleGrowthDilation, hPrefix]

/-! ## 4. The explicit sign-twisted S3 growth law -/

/-- Each elementary internal edge is one of the two adjacent-transposition
generators of full S3 holonomy. -/
def generatingSheetTransport (branch : Fin 2) :
    Matrix (Fin 2) (Fin 2) ℂ :=
  if branch = 0 then sheetSwapZeroOne else sheetSwapOneTwo

/-- Both generating transports reverse the chirality operator.  The causal
orientation label reverses with them, so their product is transported rather
than erased. -/
theorem generatingSheetTransport_relationalChirality
    {n : ℕ} (orientation : RankedGrowthPath (fun _ => Fin 2) n → ℂ) :
    RelationalFiberTransport
      (Branch := fun _ => Fin 2) (n := n)
      (fun path => orientation path)
      (fun refined => -orientation refined.1)
      sheetChiralityObservable
      (fun _path branch => generatingSheetTransport branch) := by
  intro path branch
  fin_cases branch <;>
    ext row column <;> fin_cases row <;> fin_cases column <;>
    norm_num [generatingSheetTransport, sheetSwapZeroOne,
      sheetSwapOneTwo, sheetChiralityObservable,
      sheetOrientationGenerator, Matrix.mul_apply, Matrix.smul_apply,
      Fin.sum_univ_two] <;> ring

/-- Concrete bundle-valued sequential growth with the two generating odd
holonomies transports the relational chirality observable exactly. -/
theorem generatingS3Growth_transports_relationalChirality
    {n : ℕ}
    (transition : RankedGrowthPath (fun _ => Fin 2) n → Fin 2 → ℂ)
    (orientation : RankedGrowthPath (fun _ => Fin 2) n → ℂ) :
    fiberwiseOperator (fun refined => -orientation refined.1)
          sheetChiralityObservable *
        bundleGrowthDilation transition
          (fun _path branch => generatingSheetTransport branch) =
      bundleGrowthDilation transition
          (fun _path branch => generatingSheetTransport branch) *
        fiberwiseOperator orientation sheetChiralityObservable := by
  exact relationalFiberTransport_intertwiner transition
    (fun _path branch => generatingSheetTransport branch)
    orientation (fun refined => -orientation refined.1)
    sheetChiralityObservable
    (generatingSheetTransport_relationalChirality orientation)

/-! ## 5. Capstone and axiom audit -/

/-- The full result: cylinder records are transported on the direct-sum
carrier, record pinching leaves relational chirality intact, and the two odd
S3 holonomy generators transport the arrow-locked observable exactly. -/
theorem causalBundleProtectedChirality_capstone :
    sheetChiralityObservable ≠ 0
      ∧ sheetChiralityObservableᴴ * sheetCarrierGram =
          sheetCarrierGram * sheetChiralityObservable
      ∧ sheetChiralityObservable * sheetChiralityObservable =
          (3 : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      ∧ (∀ {Branch : ℕ → Type u} [∀ rank, Fintype (Branch rank)]
          {n : ℕ}
          (transition : RankedGrowthPath Branch n → Branch n → ℂ)
          (transport : RankedGrowthPath Branch n → Branch n →
            Matrix (Fin 2) (Fin 2) ℂ)
          (event : Finset (RankedGrowthPath Branch n)),
          finiteEventProjector ((oneStepCylinder event) ×ˢ Finset.univ) *
              bundleGrowthDilation transition transport =
            bundleGrowthDilation transition transport *
              finiteEventProjector (event ×ˢ Finset.univ))
      ∧ (∀ {History : Type u} (orientation : History → ℂ),
          blockRecordPinching
              (fiberwiseOperator orientation sheetChiralityObservable) =
            fiberwiseOperator orientation sheetChiralityObservable)
      ∧ (∀ {n : ℕ}
          (transition : RankedGrowthPath (fun _ => Fin 2) n → Fin 2 → ℂ)
          (orientation : RankedGrowthPath (fun _ => Fin 2) n → ℂ),
          fiberwiseOperator (fun refined => -orientation refined.1)
                sheetChiralityObservable *
              bundleGrowthDilation transition
                (fun _path branch => generatingSheetTransport branch) =
            bundleGrowthDilation transition
                (fun _path branch => generatingSheetTransport branch) *
              fiberwiseOperator orientation sheetChiralityObservable) := by
  exact ⟨sheetChirality_ne_zero, sheetChirality_gramHermitian,
    sheetChirality_sq,
    fun transition transport event =>
      bundleGrowth_transports_cylinder transition transport event,
    fun orientation => blockRecordPinching_preserves_sheetChirality orientation,
    fun transition orientation =>
      generatingS3Growth_transports_relationalChirality transition orientation⟩

#print axioms sheetSwapZeroOne_gram_unitary
#print axioms sheetSwapOneTwo_gram_unitary
#print axioms sheetSwapZeroOne_anticommutes_chirality
#print axioms sheetSwapOneTwo_anticommutes_chirality
#print axioms sheet_signTwisted_commutant_one_dimensional
#print axioms sheetChirality_gramHermitian
#print axioms sheetChirality_sq
#print axioms blockRecordPinching_trace
#print axioms blockRecordPinching_fiberwiseOperator
#print axioms bundleGrowth_transports_cylinder
#print axioms relationalFiberTransport_intertwiner
#print axioms generatingS3Growth_transports_relationalChirality
#print axioms causalBundleProtectedChirality_capstone

end

end UnifiedTheory.Audit.KFCausalBundleProtectedChirality
