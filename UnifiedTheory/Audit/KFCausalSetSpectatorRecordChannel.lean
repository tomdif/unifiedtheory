/-
  Audit/KFCausalSetSpectatorRecordChannel.lean

  SPECTATOR/RECORD TRACING: THE FIRST EXACT OBSTRUCTION

  A natural intrinsic classicalization candidate is to retain only mutually
  distinguishable causal records and trace over spectator information.  On the
  first three-bin source ensemble the canonical finite model is record-basis
  dephasing.  It is a genuine CPTP Kraus channel and is covariant under every
  relabeling of the record alphabet.

  The construction nevertheless fails the normalization appropriate to a
  decoherence functional.  A density matrix is normalized by its trace, while
  a decoherence functional is normalized by its all-event value

      D(Omega,Omega) = sum_i sum_j D(i,j).

  For the harmonic two-antichain source functional these are different:

      sum_ij D_ij = 1,       trace D = 3681/2113.

  Any trace-preserving map whose output is record-diagonal has all-event value
  equal to the preserved trace.  It therefore outputs 3681/2113, not one.
  This excludes every standard CPTP record-classicalizing channel at once,
  independently of covariance.  State-dependent renormalization would be
  nonlinear and hence is not a quantum channel.

  The chirality tripwire is also explicit: dephasing the route record itself
  identifies the two pure chiral projectors.  Protecting chirality requires an
  independently derived subsystem/conditional-expectation structure on which
  the record channel acts trivially; it does not follow from CPTP alone.

  The forced eigenbasis alternative is then constructed.  Pinching by the two
  chirality projectors is CPTP and fixes every balanced kernel.  Its exact
  record functional is diag(1/2-y,1/2+y).  Under an explicitly named tensor
  extension of the two-antichain source ensemble, the chiral cells are exactly
  decoherent and normalized while the geometric empty/full interference
  remains nonzero inside the selected pure cell.  The tensor extension is a
  conditional model, not a derived factorization of causal growth.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalSetSourceInterferenceRefinement
import UnifiedTheory.Audit.KFOrientationHistoryRefinementChannel

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel

noncomputable section

open scoped BigOperators ComplexConjugate
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationGrowthDecoherence
open UnifiedTheory.Audit.KFOrientationHistoryRigidity
open UnifiedTheory.Audit.KFOrientationPathQuantum
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalSetSourceQuantumEnsemble

abbrev SourceRecordMatrix := Matrix (Fin 3) (Fin 3) ℂ

/-! ## 1. Canonical record dephasing is CPTP -/

/-- Rank-one projector onto one source-record bin. -/
def sourceRecordProjector (record : Fin 3) : SourceRecordMatrix :=
  fun i j => if i = record then if j = record then 1 else 0 else 0

/-- Each record projector is Hermitian-idempotent. -/
theorem sourceRecordProjector_dagger_mul_self (record : Fin 3) :
    (sourceRecordProjector record)ᴴ * sourceRecordProjector record =
      sourceRecordProjector record := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : i = record
  · subst i
    by_cases hj : j = record
    · subst j
      simp [sourceRecordProjector, Matrix.conjTranspose_apply]
    · simp [sourceRecordProjector, Matrix.conjTranspose_apply, hj]
  · simp [sourceRecordProjector, Matrix.conjTranspose_apply, hi]

theorem sourceRecordProjector_complete :
    (∑ record, (sourceRecordProjector record)ᴴ *
      sourceRecordProjector record) = (1 : SourceRecordMatrix) := by
  simp_rw [sourceRecordProjector_dagger_mul_self]
  ext i j
  change (∑ record : Fin 3, sourceRecordProjector record i j) =
    (1 : SourceRecordMatrix) i j
  by_cases hij : i = j
  · subst j
    rw [Finset.sum_eq_single i]
    · simp [sourceRecordProjector]
    · intro record _ hRecord
      have hiRecord : i ≠ record := Ne.symm hRecord
      simp [sourceRecordProjector, hiRecord]
    · simp
  · have hSum : ∑ record : Fin 3, sourceRecordProjector record i j = 0 := by
      apply Finset.sum_eq_zero
      intro record _
      by_cases hi : i = record
      · subst i
        have hji : j ≠ record := Ne.symm hij
        simp [sourceRecordProjector, hji]
      · simp [sourceRecordProjector, hi]
    rw [hSum]
    simp [hij]

/-- The canonical channel which measures the three source records and forgets
all coherence between distinct records. -/
def sourceRecordDephasingKraus : KrausRepresentation 3 3 3 where
  K := sourceRecordProjector
  complete := sourceRecordProjector_complete

theorem sourceRecordDephasing_isCPTP :
    IsCPTP sourceRecordDephasingKraus.toLinearMap :=
  kraus_isCPTP _

/-- Entrywise record dephasing. -/
def sourceRecordDephase (rho : SourceRecordMatrix) : SourceRecordMatrix :=
  fun i j => if i = j then rho i i else 0

theorem sourceRecordDephasingKraus_apply
    (rho : SourceRecordMatrix) :
    sourceRecordDephasingKraus.apply rho = sourceRecordDephase rho := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sourceRecordDephasingKraus, sourceRecordProjector,
      sourceRecordDephase, KrausRepresentation.apply, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_three]

/-- Matrix reindexing by a permutation of record names. -/
def relabelSourceRecords (equivalence : Fin 3 ≃ Fin 3)
    (rho : SourceRecordMatrix) : SourceRecordMatrix :=
  fun i j => rho (equivalence.symm i) (equivalence.symm j)

/-- Record dephasing commutes with every permutation of record names.  This is
stronger than the two-antichain's residual relabeling covariance. -/
theorem sourceRecordDephase_relabel_covariant
    (equivalence : Fin 3 ≃ Fin 3) (rho : SourceRecordMatrix) :
    sourceRecordDephase (relabelSourceRecords equivalence rho) =
      relabelSourceRecords equivalence (sourceRecordDephase rho) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [sourceRecordDephase, relabelSourceRecords]
  · have hsymm : equivalence.symm i ≠ equivalence.symm j := by
      intro h
      exact hij (equivalence.symm.injective h)
    simp [sourceRecordDephase, relabelSourceRecords, hij, hsymm]

/-! ## 2. Trace normalization and decoherence normalization differ -/

/-- The normalization functional of a finite decoherence matrix: its value on
the total event. -/
def sourceRecordTotalMeasure (rho : SourceRecordMatrix) : ℂ :=
  ∑ i, ∑ j, rho i j

/-- A record-classical output has no off-diagonal entries. -/
def IsSourceRecordDiagonal (rho : SourceRecordMatrix) : Prop :=
  ∀ i j, i ≠ j → rho i j = 0

theorem sourceRecordDephase_isDiagonal (rho : SourceRecordMatrix) :
    IsSourceRecordDiagonal (sourceRecordDephase rho) := by
  intro i j hij
  simp [sourceRecordDephase, hij]

/-- On a record-diagonal matrix, total-event measure collapses to matrix
trace. -/
theorem sourceRecordTotalMeasure_eq_trace_of_diagonal
    {rho : SourceRecordMatrix} (hDiagonal : IsSourceRecordDiagonal rho) :
    sourceRecordTotalMeasure rho = Matrix.trace rho := by
  have h01 := hDiagonal 0 1 (by decide)
  have h02 := hDiagonal 0 2 (by decide)
  have h10 := hDiagonal 1 0 (by decide)
  have h12 := hDiagonal 1 2 (by decide)
  have h20 := hDiagonal 2 0 (by decide)
  have h21 := hDiagonal 2 1 (by decide)
  simp only [sourceRecordTotalMeasure, Fin.sum_univ_three, Matrix.trace]
  rw [h01, h02, h10, h12, h20, h21]
  simp [Matrix.diag]

/-- Diagonal entries of the source decoherence matrix are the singleton-bin
quantum measures, as complex numbers. -/
theorem harmonicSourceDecoherence_diagonal
    (chirality : Fin 2) (bin : Fin 3) :
    harmonicAntichainTwoSourceBinDecoherence chirality bin bin =
      ((harmonicAntichainTwoSourceBinQuantumMeasure chirality bin : ℝ) : ℂ) := by
  unfold harmonicAntichainTwoSourceBinDecoherence amplitudeDecoherence
    harmonicAntichainTwoSourceBinQuantumMeasure
  have hNorm := Complex.mul_conj
    (harmonicAntichainTwoNormalizedSourceBinAmplitude chirality bin)
  change _ * star _ = _
  convert hNorm using 1

/-- The harmonic source decoherence functional has matrix trace
`3681/2113`, even though its total-event value is one. -/
theorem harmonicSourceDecoherence_trace
    (chirality : Fin 2) :
    Matrix.trace (harmonicAntichainTwoSourceBinDecoherence chirality) =
      ((3681 / 2113 : ℝ) : ℂ) := by
  simp only [Matrix.trace, Fin.sum_univ_three]
  change harmonicAntichainTwoSourceBinDecoherence chirality 0 0 +
      harmonicAntichainTwoSourceBinDecoherence chirality 1 1 +
      harmonicAntichainTwoSourceBinDecoherence chirality 2 2 = _
  rw [harmonicSourceDecoherence_diagonal,
    harmonicSourceDecoherence_diagonal,
    harmonicSourceDecoherence_diagonal,
    harmonicAntichainTwoSourceBinQuantumMeasure_zero,
    harmonicAntichainTwoSourceBinQuantumMeasure_one,
    harmonicAntichainTwoSourceBinQuantumMeasure_two]
  norm_num

theorem harmonicSourceDecoherence_totalMeasure
    (chirality : Fin 2) :
    sourceRecordTotalMeasure
        (harmonicAntichainTwoSourceBinDecoherence chirality) = 1 := by
  unfold sourceRecordTotalMeasure
    harmonicAntichainTwoSourceBinDecoherence amplitudeDecoherence
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  rw [harmonicAntichainTwoNormalizedSourceBinAmplitude_sum]
  rw [← star_sum]
  rw [harmonicAntichainTwoNormalizedSourceBinAmplitude_sum]
  norm_num

/-- Exact entrywise form of the classical-looking diagonal produced by
canonical record tracing. -/
theorem sourceRecordDephasing_harmonic_entry
    (chirality : Fin 2) (i j : Fin 3) :
    (sourceRecordDephasingKraus.apply
        (harmonicAntichainTwoSourceBinDecoherence chirality)) i j =
      if i = j then
        ((harmonicAntichainTwoSourceBinQuantumMeasure chirality i : ℝ) : ℂ)
      else 0 := by
  rw [sourceRecordDephasingKraus_apply]
  unfold sourceRecordDephase
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte]
    exact harmonicSourceDecoherence_diagonal chirality i
  · simp [hij]

/-- Its three diagonal entries remain the original singleton-bin quantum
measures, whose sum is not one. -/
theorem sourceRecordDephasing_harmonic_diagonal_exact
    (chirality : Fin 2) :
    (sourceRecordDephasingKraus.apply
        (harmonicAntichainTwoSourceBinDecoherence chirality)) 0 0 =
        ((256 / 2113 : ℝ) : ℂ)
      ∧ (sourceRecordDephasingKraus.apply
        (harmonicAntichainTwoSourceBinDecoherence chirality)) 1 1 =
        ((1024 / 2113 : ℝ) : ℂ)
      ∧ (sourceRecordDephasingKraus.apply
        (harmonicAntichainTwoSourceBinDecoherence chirality)) 2 2 =
        ((2401 / 2113 : ℝ) : ℂ) := by
  rw [sourceRecordDephasing_harmonic_entry,
    sourceRecordDephasing_harmonic_entry,
    sourceRecordDephasing_harmonic_entry]
  simp only [↓reduceIte]
  rw [harmonicAntichainTwoSourceBinQuantumMeasure_zero,
    harmonicAntichainTwoSourceBinQuantumMeasure_one,
    harmonicAntichainTwoSourceBinQuantumMeasure_two]
  exact ⟨rfl, rfl, rfl⟩

/-- The only nonzero real inter-bin channel in the local source ensemble is
erased in one record-dephasing use.  This does not define a normalized output
decoherence functional, as the next theorem proves. -/
theorem sourceRecordDephasing_kills_emptyFull_offDiagonal
    (chirality : Fin 2) :
    (sourceRecordDephasingKraus.apply
      (harmonicAntichainTwoSourceBinDecoherence chirality)) 0 2 = 0 := by
  rw [sourceRecordDephasingKraus_apply]
  rfl

/-- The canonical CPTP record trace destroys decoherence-functional
normalization on the exact two-antichain ensemble. -/
theorem sourceRecordDephasing_breaks_totalMeasure
    (chirality : Fin 2) :
    sourceRecordTotalMeasure
        (sourceRecordDephasingKraus.apply
          (harmonicAntichainTwoSourceBinDecoherence chirality)) =
      ((3681 / 2113 : ℝ) : ℂ)
      ∧ sourceRecordTotalMeasure
          (sourceRecordDephasingKraus.apply
            (harmonicAntichainTwoSourceBinDecoherence chirality)) ≠ 1 := by
  have hDiagonal : IsSourceRecordDiagonal
      (sourceRecordDephasingKraus.apply
        (harmonicAntichainTwoSourceBinDecoherence chirality)) := by
    rw [sourceRecordDephasingKraus_apply]
    exact sourceRecordDephase_isDiagonal _
  rw [sourceRecordTotalMeasure_eq_trace_of_diagonal hDiagonal,
    KrausRepresentation.trace_apply, harmonicSourceDecoherence_trace]
  constructor
  · rfl
  · norm_num

/-! ## 3. Universal CPTP obstruction -/

/-- Any trace-preserving map which makes this ensemble record-diagonal has the
same wrong total-event normalization.  Complete positivity and covariance are
irrelevant: trace preservation plus record diagonality already imply the
obstruction. -/
theorem tracePreserving_recordDiagonal_forces_wrong_totalMeasure
    (Phi : SourceRecordMatrix → SourceRecordMatrix)
    (hTracePreserving : ∀ rho, Matrix.trace (Phi rho) = Matrix.trace rho)
    (chirality : Fin 2)
    (hDiagonal : IsSourceRecordDiagonal
      (Phi (harmonicAntichainTwoSourceBinDecoherence chirality))) :
    sourceRecordTotalMeasure
        (Phi (harmonicAntichainTwoSourceBinDecoherence chirality)) =
      ((3681 / 2113 : ℝ) : ℂ) := by
  rw [sourceRecordTotalMeasure_eq_trace_of_diagonal hDiagonal,
    hTracePreserving, harmonicSourceDecoherence_trace]

/-- **No-go.** There is no standard CPTP map on the source decoherence matrix
which simultaneously produces record-distinguishable sectors and preserves
the normalized total-event value. -/
theorem no_CPTP_recordDiagonal_preserves_sourceTotalMeasure
    (chirality : Fin 2) :
    ¬∃ Phi : SourceRecordMatrix →ₗ[ℂ] SourceRecordMatrix,
      IsCPTP Phi
        ∧ IsSourceRecordDiagonal
            (Phi (harmonicAntichainTwoSourceBinDecoherence chirality))
        ∧ sourceRecordTotalMeasure
            (Phi (harmonicAntichainTwoSourceBinDecoherence chirality)) = 1 := by
  rintro ⟨Phi, hCPTP, hDiagonal, hNormalized⟩
  have hWrong := tracePreserving_recordDiagonal_forces_wrong_totalMeasure
    Phi hCPTP.2 chirality hDiagonal
  rw [hNormalized] at hWrong
  norm_num at hWrong

/-! ## 4. Chirality tripwire -/

/-- Naive dephasing of the route record erases, rather than protects, the pure
chiral character.  A geometry-only record channel therefore requires a
separately derived tensor factor or protected algebra. -/
theorem naiveRecordDephasing_erases_chiralCharacter :
    positiveOrientationProjector ≠ negativeOrientationProjector
      ∧ pathDephase positiveOrientationProjector =
          pathDephase negativeOrientationProjector := by
  exact ⟨orientation_holonomy_requires_path_coherence.1,
    orientation_holonomy_requires_path_coherence.2.1⟩

/-! ## 5. The forced alternative: chirality-basis records -/

/-- The two record projectors in the curvature/chirality eigenbasis.  In the
repository's convention their eigenkets are proportional to `(1,+i)` and
`(1,-i)`, not `(1,+1)` and `(1,-1)`. -/
def chiralityRecordProjector (chirality : Fin 2) : SquareMatrix 2 :=
  if chirality = 0 then positiveOrientationProjector
  else negativeOrientationProjector

theorem orientationProjectors_orthogonal_reverse :
    negativeOrientationProjector * positiveOrientationProjector = 0 := by
  rw [negativeOrientationProjector_exact,
    positiveOrientationProjector_exact]
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.mul_apply, Fin.sum_univ_two, Fin.ext_iff]
  all_goals ring_nf
  all_goals rw [Complex.I_sq]
  all_goals norm_num

theorem chiralityRecordProjector_complete :
    (∑ chirality, (chiralityRecordProjector chirality)ᴴ *
      chiralityRecordProjector chirality) =
        (1 : SquareMatrix 2) := by
  rw [Fin.sum_univ_two]
  change positiveOrientationProjectorᴴ * positiveOrientationProjector +
      negativeOrientationProjectorᴴ * negativeOrientationProjector = 1
  rw [(positiveOrientationProjector_isPathDensity.1),
    (negativeOrientationProjector_isPathDensity.1),
    positiveOrientationProjector_idempotent,
    negativeOrientationProjector_idempotent,
    orientationProjectors_sum]

/-- Pinching in the chirality eigenbasis is a genuine CPTP channel. -/
def chiralityRecordPinchingKraus : KrausRepresentation 2 2 2 where
  K := chiralityRecordProjector
  complete := chiralityRecordProjector_complete

theorem chiralityRecordPinching_isCPTP :
    IsCPTP chiralityRecordPinchingKraus.toLinearMap :=
  kraus_isCPTP _

/-- Every balanced kernel is already diagonal in the chirality record basis,
so chirality pinching fixes the entire interval, including both pure endpoint
characters. -/
theorem chiralityRecordPinching_fixes_balanced (y : ℝ) :
    chiralityRecordPinchingKraus.apply (balancedHistoryKernel y) =
      balancedHistoryKernel y := by
  unfold chiralityRecordPinchingKraus KrausRepresentation.apply
  rw [Fin.sum_univ_two]
  change positiveOrientationProjector * balancedHistoryKernel y *
      positiveOrientationProjectorᴴ +
    negativeOrientationProjector * balancedHistoryKernel y *
      negativeOrientationProjectorᴴ = balancedHistoryKernel y
  rw [(positiveOrientationProjector_isPathDensity.1),
    (negativeOrientationProjector_isPathDensity.1)]
  rw [balancedHistoryKernel_projector_mixture]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul]
  rw [positiveOrientationProjector_idempotent,
    negativeOrientationProjector_idempotent,
    orientationProjectors_orthogonal,
    orientationProjectors_orthogonal_reverse]
  simp only [Matrix.zero_mul, add_zero, zero_add,
    smul_zero]
  rw [positiveOrientationProjector_idempotent,
    negativeOrientationProjector_idempotent]

/-- Decoherence functional of the two chirality-valued alternatives obtained
from the standard projective-measurement class operators. -/
def chiralityRecordDecoherence (y : ℝ) (first second : Fin 2) : ℂ :=
  Matrix.trace
    (chiralityRecordProjector first * balancedHistoryKernel y *
      chiralityRecordProjector second)

/-- The chirality partition is exactly diagonal.  The geometric parameter is
the eigenvalue gap, while the endpoint characters are deterministic records. -/
theorem chiralityRecordDecoherence_exact (y : ℝ) :
    (fun first second => chiralityRecordDecoherence y first second) =
      !![((1 / 2 - y : ℝ) : ℂ), 0;
         0, ((1 / 2 + y : ℝ) : ℂ)] := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    norm_num [chiralityRecordDecoherence, chiralityRecordProjector,
      positiveOrientationProjector_exact, negativeOrientationProjector_exact,
      balancedHistoryKernel, Matrix.trace, Matrix.mul_apply,
      Fin.sum_univ_two, Fin.ext_iff] <;>
    ring_nf
  all_goals rw [Complex.I_sq]
  all_goals ring

theorem chiralityRecordDecoherence_offDiagonal (y : ℝ) :
    chiralityRecordDecoherence y 0 1 = 0
      ∧ chiralityRecordDecoherence y 1 0 = 0 := by
  rw [show chiralityRecordDecoherence y 0 1 =
      (fun first second => chiralityRecordDecoherence y first second) 0 1
    from rfl,
    show chiralityRecordDecoherence y 1 0 =
      (fun first second => chiralityRecordDecoherence y first second) 1 0
    from rfl,
    chiralityRecordDecoherence_exact]
  norm_num

theorem chiralityRecordDecoherence_totalMeasure (y : ℝ) :
    ∑ first, ∑ second, chiralityRecordDecoherence y first second = 1 := by
  rw [Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two,
    chiralityRecordDecoherence_offDiagonal y |>.1,
    chiralityRecordDecoherence_offDiagonal y |>.2]
  have hExact := chiralityRecordDecoherence_exact y
  have h00 := congrFun (congrFun hExact 0) 0
  have h11 := congrFun (congrFun hExact 1) 1
  norm_num at h00 h11
  rw [h00, h11]
  norm_num

/-! ## 6. Conditional two-antichain extended-history search -/

/-- Minimal tensor extension of the source histories by the chirality-record
coordinate.  This product structure is a named ansatz; the current growth law
does not derive it. -/
def extendedSourceChiralityKernel
    (lawChirality : Fin 2) (y : ℝ)
    (first second : Fin 3 × Fin 2) : ℂ :=
  harmonicAntichainTwoSourceBinDecoherence lawChirality
      first.1 second.1 *
    chiralityRecordDecoherence y first.2 second.2

/-- Decoherence between the two cells obtained by retaining chirality and
coarse-graining over all three source bins. -/
def extendedChiralityCellDecoherence
    (lawChirality : Fin 2) (y : ℝ) (first second : Fin 2) : ℂ :=
  ∑ sourceFirst : Fin 3, ∑ sourceSecond : Fin 3,
    extendedSourceChiralityKernel lawChirality y
      (sourceFirst, first) (sourceSecond, second)

/-- Because the source total event is normalized, the conditional tensor
extension reduces exactly to the chirality-record functional after summing
over geometry. -/
theorem extendedChiralityCellDecoherence_eq_chirality
    (lawChirality : Fin 2) (y : ℝ) (first second : Fin 2) :
    extendedChiralityCellDecoherence lawChirality y first second =
      chiralityRecordDecoherence y first second := by
  unfold extendedChiralityCellDecoherence extendedSourceChiralityKernel
  simp_rw [← Finset.sum_mul]
  change sourceRecordTotalMeasure
      (harmonicAntichainTwoSourceBinDecoherence lawChirality) *
        chiralityRecordDecoherence y first second = _
  rw [harmonicSourceDecoherence_totalMeasure]
  simp

/-- The two chiral cells of the conditional extended ensemble are exactly
decoherent and normalized. -/
theorem extendedChiralityPartition_exactlyDecoherent
    (lawChirality : Fin 2) (y : ℝ) :
    extendedChiralityCellDecoherence lawChirality y 0 1 = 0
      ∧ extendedChiralityCellDecoherence lawChirality y 1 0 = 0
      ∧ (∑ first, ∑ second,
        extendedChiralityCellDecoherence lawChirality y first second) = 1 := by
  simp_rw [extendedChiralityCellDecoherence_eq_chirality]
  exact ⟨(chiralityRecordDecoherence_offDiagonal y).1,
    (chiralityRecordDecoherence_offDiagonal y).2,
    chiralityRecordDecoherence_totalMeasure y⟩

/-- Exact decoherence of the chiral alternatives does not classicalize the
geometry inside the selected cell.  At either pure endpoint, the surviving
chiral cell retains the original nonzero empty/full source off-diagonal. -/
theorem chiralRecordClassical_geometryInterferencePersists
    (lawChirality : Fin 2) :
    extendedSourceChiralityKernel lawChirality (-1 / 2) (0, 0) (2, 0) =
        ((-784 / 2113 : ℝ) : ℂ)
      ∧ extendedSourceChiralityKernel lawChirality (1 / 2) (0, 1) (2, 1) =
        ((-784 / 2113 : ℝ) : ℂ) := by
  unfold extendedSourceChiralityKernel
  change harmonicAntichainTwoSourceBinDecoherence lawChirality 0 2 *
      chiralityRecordDecoherence (-1 / 2) 0 0 = _ ∧
    harmonicAntichainTwoSourceBinDecoherence lawChirality 0 2 *
      chiralityRecordDecoherence (1 / 2) 1 1 = _
  rw [harmonicAntichainTwoSourceBinDecoherence_zero_two]
  have hNeg00 : chiralityRecordDecoherence (-1 / 2) 0 0 = 1 := by
    rw [show chiralityRecordDecoherence (-1 / 2) 0 0 =
        (fun first second =>
          chiralityRecordDecoherence (-1 / 2) first second) 0 0 from rfl,
      chiralityRecordDecoherence_exact]
    norm_num
  have hPos11 : chiralityRecordDecoherence (1 / 2) 1 1 = 1 := by
    rw [show chiralityRecordDecoherence (1 / 2) 1 1 =
        (fun first second =>
          chiralityRecordDecoherence (1 / 2) first second) 1 1 from rfl,
      chiralityRecordDecoherence_exact]
    norm_num
  rw [hNeg00, hPos11]
  norm_num

/-! ## 7. Correct projective scope -/

/-- A chosen decoherent cylinder partition remains decoherent under exhaustive
projective lift.  This does not classify partitions introduced for the first
time at a deeper rank. -/
theorem decoherentCylinderPair_remains_decoherent
    {Branch : ℕ → Type*} [∀ n, Fintype (Branch n)]
    (law : RankedNormalizedComplexGrowthLaw Branch) {depth : ℕ}
    (first second : Finset (RankedGrowthPath Branch depth))
    (hDecoherent : growthEventDecoherence
      (finiteRankedDepthDecoherence law depth) first second = 0)
    (steps : ℕ) :
    growthEventDecoherence
        (finiteRankedDepthDecoherence law (depth + steps))
        (refineRankedGrowthEventBy first steps)
        (refineRankedGrowthEventBy second steps) = 0 := by
  rw [finiteRankedDepthDecoherence_projective_by, hDecoherent]

/-- Positive eigenbasis verdict.  Chirality pinching is a valid protected
record channel on the balanced sector.  Under the explicitly named tensor
extension, the chiral partition is exactly classical while geometric
interference survives inside the selected pure sector. -/
theorem chiralityBasisRecord_searchVerdict :
    IsCPTP chiralityRecordPinchingKraus.toLinearMap
      ∧ (∀ y : ℝ,
        chiralityRecordPinchingKraus.apply (balancedHistoryKernel y) =
          balancedHistoryKernel y)
      ∧ (∀ lawChirality : Fin 2, ∀ y : ℝ,
        extendedChiralityCellDecoherence lawChirality y 0 1 = 0
          ∧ extendedChiralityCellDecoherence lawChirality y 1 0 = 0
          ∧ (∑ first, ∑ second,
            extendedChiralityCellDecoherence
              lawChirality y first second) = 1)
      ∧ (∀ lawChirality : Fin 2,
        extendedSourceChiralityKernel
            lawChirality (-1 / 2) (0, 0) (2, 0) =
              ((-784 / 2113 : ℝ) : ℂ)
          ∧ extendedSourceChiralityKernel
            lawChirality (1 / 2) (0, 1) (2, 1) =
              ((-784 / 2113 : ℝ) : ℂ)) := by
  exact ⟨chiralityRecordPinching_isCPTP,
    chiralityRecordPinching_fixes_balanced,
    extendedChiralityPartition_exactlyDecoherent,
    chiralRecordClassical_geometryInterferencePersists⟩

/-- The exact small-rank verdict: a canonical covariant CPTP record channel
exists, but it fails decoherence normalization; no standard CPTP replacement
can repair that while producing diagonal records; and indiscriminate record
dephasing fails the chiral-protection tripwire. -/
theorem spectatorRecordChannel_firstVerdict (chirality : Fin 2) :
    IsCPTP sourceRecordDephasingKraus.toLinearMap
      ∧ (∀ equivalence : Fin 3 ≃ Fin 3, ∀ rho : SourceRecordMatrix,
        sourceRecordDephase (relabelSourceRecords equivalence rho) =
          relabelSourceRecords equivalence (sourceRecordDephase rho))
      ∧ sourceRecordTotalMeasure
          (sourceRecordDephasingKraus.apply
            (harmonicAntichainTwoSourceBinDecoherence chirality)) ≠ 1
      ∧ (¬∃ Phi : SourceRecordMatrix →ₗ[ℂ] SourceRecordMatrix,
        IsCPTP Phi
          ∧ IsSourceRecordDiagonal
              (Phi (harmonicAntichainTwoSourceBinDecoherence chirality))
          ∧ sourceRecordTotalMeasure
              (Phi (harmonicAntichainTwoSourceBinDecoherence chirality)) = 1)
      ∧ pathDephase positiveOrientationProjector =
          pathDephase negativeOrientationProjector := by
  exact ⟨sourceRecordDephasing_isCPTP,
    sourceRecordDephase_relabel_covariant,
    (sourceRecordDephasing_breaks_totalMeasure chirality).2,
    no_CPTP_recordDiagonal_preserves_sourceTotalMeasure chirality,
    naiveRecordDephasing_erases_chiralCharacter.2⟩

#print axioms sourceRecordDephasing_isCPTP
#print axioms sourceRecordDephase_relabel_covariant
#print axioms harmonicSourceDecoherence_trace
#print axioms sourceRecordDephasing_harmonic_diagonal_exact
#print axioms sourceRecordDephasing_breaks_totalMeasure
#print axioms no_CPTP_recordDiagonal_preserves_sourceTotalMeasure
#print axioms naiveRecordDephasing_erases_chiralCharacter
#print axioms chiralityRecordPinching_fixes_balanced
#print axioms chiralityRecordDecoherence_exact
#print axioms extendedChiralityPartition_exactlyDecoherent
#print axioms chiralRecordClassical_geometryInterferencePersists
#print axioms decoherentCylinderPair_remains_decoherent
#print axioms chiralityBasisRecord_searchVerdict
#print axioms spectatorRecordChannel_firstVerdict

end

end UnifiedTheory.Audit.KFCausalSetSpectatorRecordChannel
