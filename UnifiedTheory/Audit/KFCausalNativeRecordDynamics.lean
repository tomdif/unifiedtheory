/-
  Audit/KFCausalNativeRecordDynamics.lean

  THE DYNAMICAL ORIGIN AND EXACT BOUNDARY OF SHARP CAUSAL EFFECTS

  The native resolution law previously assumed the sharp child effects

      K_c† K_c = |c><c|.

  This module replaces that probability-level input by a deeper recorded
  refinement law.  Let `V` be the Stinespring matrix which stacks the child
  operators, let `Q_c` read child `c` in the created record, and let `P_c`
  be the native child projector before refinement.  Exact causal record
  transport is the intertwining equation

      Q_c V = V P_c.

  It says that reading the child after refinement agrees with restricting to
  that same causal child before refinement.  If refinement is isometric,
  this equation forces the sharp effects.  If coherent forgetting also
  recovers the parent, it uniquely forces `K_c = P_c` and therefore the full
  native causal resolution law.

  The boundary is equally exact.  A rotated Pauli-Y measurement obeys Born
  completeness, coherent conservation, and binary relabeling covariance, but
  is not aligned with the native child basis.  Thus the existing abstract
  conservation and covariance laws cannot derive native sharpness without
  the record-transport bridge.

  Finally, native record protection and path-basis chirality cannot occupy
  the same two-dimensional carrier: native resolution identifies the two
  opposite orientation projectors.  A physical model must therefore derive
  a separate protected chiral algebra or a compatible embedding.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalNativeResolutionLaw
import UnifiedTheory.Audit.KFOrientationPathQuantum
import UnifiedTheory.LayerB.NaimarkDilation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNativeRecordDynamics

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.StinespringDilation
open UnifiedTheory.LayerB.NaimarkDilation
open UnifiedTheory.LayerB.ConcreteQuantumMeasurement
open UnifiedTheory.LayerB.CoherenceResource
open UnifiedTheory.LayerB.RobertsonSchrodinger
open UnifiedTheory.Audit.KFCausalRecordedRefinementDilation
open UnifiedTheory.Audit.KFCausalNativeResolutionLaw
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFOrientationPathQuantum

/-! ## 1. Sharp effects from exclusivity and reversible refinement -/

/-- Exclusive child response plus aggregate Born completeness already fixes
each individual effect.  This separates the two ingredients hidden in the
single equation `K_c† K_c = P_c`: causal alignment and lossless refinement. -/
theorem exclusive_bornComplete_implies_sharpEffect {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hExclusive : IsOutcomeExclusive operator)
    (hComplete :
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix outcomes)) :
    HasSharpOutcomeEffect operator := by
  intro observed
  ext prepared column
  by_cases hPrepared : prepared = observed
  · subst prepared
    by_cases hColumn : column = observed
    · subst column
      have hEntry := congr_fun (congr_fun hComplete observed) observed
      rw [Finset.sum_apply, Finset.sum_apply] at hEntry
      rw [Finset.sum_eq_single observed] at hEntry
      · simpa [causalOutcomeProjector, computationalProj] using hEntry
      · intro other _ hOther
        rw [Matrix.mul_apply]
        apply Finset.sum_eq_zero
        intro row _
        rw [Matrix.conjTranspose_apply,
          hExclusive other observed row hOther]
        simp
      · simp
    · rw [Matrix.mul_apply]
      apply Eq.trans (Finset.sum_eq_zero (fun row _ => by
        rw [hExclusive observed column row (fun h => hColumn h.symm)]
        simp))
      simp [causalOutcomeProjector, computationalProj, hColumn]
  · rw [Matrix.mul_apply]
    apply Eq.trans (Finset.sum_eq_zero (fun row _ => by
      rw [Matrix.conjTranspose_apply,
        hExclusive observed prepared row (fun h => hPrepared h.symm)]
      simp))
    simp [causalOutcomeProjector, computationalProj, hPrepared]

/-! ## 2. The causal record-transport intertwiner -/

/-- The created Naimark record and the pre-refinement native child observable
represent the same causal fact exactly when their projectors intertwine with
the recorded refinement. -/
def TransportsNativeCausalRecord {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes) : Prop :=
  ∀ outcome,
    naimarkProj (n := outcomes) outcome * krausToStinespring operator =
      krausToStinespring operator *
        causalOutcomeProjector outcomes outcome

theorem naimarkProj_mul_recordedRefinement_apply {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (outcome recorded : Fin outcomes) (row prepared : Fin outcomes) :
    (naimarkProj (n := outcomes) outcome * krausToStinespring operator)
        (row, recorded) prepared =
      if recorded = outcome then operator outcome row prepared else 0 := by
  classical
  rw [Matrix.mul_apply, Fintype.sum_prod_type]
  simp only [naimarkProj, krausToStinespring, ite_mul, one_mul, zero_mul]
  by_cases hRecorded : recorded = outcome
  · subst recorded
    rw [Finset.sum_eq_single row]
    · rw [Finset.sum_eq_single outcome]
      · simp
      · intro other _ hOther
        simp [hOther]
      · simp
    · intro other _ hOther
      apply Finset.sum_eq_zero
      intro record _
      simp [Ne.symm hOther]
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun carrier _ => by
      apply Finset.sum_eq_zero
      intro record _
      simp [hRecorded]))
    simp [hRecorded]

theorem recordedRefinement_mul_nativeProjector_apply {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (outcome recorded : Fin outcomes) (row prepared : Fin outcomes) :
    (krausToStinespring operator * causalOutcomeProjector outcomes outcome)
        (row, recorded) prepared =
      if prepared = outcome then operator recorded row outcome else 0 := by
  classical
  rw [Matrix.mul_apply]
  by_cases hPrepared : prepared = outcome
  · subst prepared
    rw [Finset.sum_eq_single outcome]
    · simp [krausToStinespring, causalOutcomeProjector,
        computationalProj]
    · intro other _ hOther
      simp [causalOutcomeProjector, computationalProj, hOther]
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun index _ => by
      simp [causalOutcomeProjector, computationalProj, hPrepared]))
    simp [hPrepared]

/-- Intertwining the native record is exactly the earlier no-false-child
condition, now expressed as conservation of a causal observable through the
recorded dynamics. -/
theorem transportsNativeCausalRecord_iff_exclusive {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes) :
    TransportsNativeCausalRecord operator ↔ IsOutcomeExclusive operator := by
  constructor
  · intro hTransport observed prepared row hDistinct
    have hEntry := congr_fun
      (congr_fun (hTransport observed) (row, observed)) prepared
    rw [naimarkProj_mul_recordedRefinement_apply,
      recordedRefinement_mul_nativeProjector_apply] at hEntry
    simpa [hDistinct, Ne.symm hDistinct] using hEntry
  · intro hExclusive outcome
    ext indexed prepared
    obtain ⟨row, recorded⟩ := indexed
    rw [naimarkProj_mul_recordedRefinement_apply,
      recordedRefinement_mul_nativeProjector_apply]
    by_cases hRecorded : recorded = outcome
    · subst recorded
      by_cases hPrepared : prepared = outcome
      · subst prepared
        simp
      · simp [hPrepared,
          hExclusive outcome prepared row (fun h => hPrepared h.symm)]
    · by_cases hPrepared : prepared = outcome
      · subst prepared
        simp [hRecorded, hExclusive recorded outcome row hRecorded]
      · simp [hRecorded, hPrepared]

/-- **Dynamical sharp-effect theorem.**  Lossless recorded refinement and
exact transport of the native causal record derive every sharp child Born
effect. -/
theorem isometry_recordTransport_implies_sharpEffect {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hIsometry : IsIsometry (krausToStinespring operator))
    (hTransport : TransportsNativeCausalRecord operator) :
    HasSharpOutcomeEffect operator := by
  exact exclusive_bornComplete_implies_sharpEffect operator
    ((transportsNativeCausalRecord_iff_exclusive operator).1 hTransport)
    ((krausToStinespring_isIsometry_iff_complete operator).1 hIsometry)

/-- **Exact quantum outcome law.**  For a prepared native child, the derived
effect assigns unit weight to the matching recorded child and zero weight to
every different child.  This is a consequence of isometry and causal-record
transport, not an additional probability axiom. -/
theorem recordTransport_quantumOutcome_exact {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hIsometry : IsIsometry (krausToStinespring operator))
    (hTransport : TransportsNativeCausalRecord operator)
    (observed prepared : Fin outcomes) :
    ((operator observed)ᴴ * operator observed) prepared prepared =
      if prepared = observed then 1 else 0 := by
  rw [isometry_recordTransport_implies_sharpEffect operator
    hIsometry hTransport observed]
  simp [causalOutcomeProjector, computationalProj]

/-- For an arbitrary density matrix, the probability of the quantum outcome
`c` is exactly its native-child diagonal weight. -/
theorem recordTransport_bornProbability_eq_nativeWeight {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hIsometry : IsIsometry (krausToStinespring operator))
    (hTransport : TransportsNativeCausalRecord operator)
    (density : ComplexDensityMatrix outcomes) (outcome : Fin outcomes) :
    (Matrix.trace
      (density.M * ((operator outcome)ᴴ * operator outcome))).re =
        (density.M outcome outcome).re := by
  rw [isometry_recordTransport_implies_sharpEffect operator
    hIsometry hTransport outcome]
  unfold causalOutcomeProjector
  have hBorn := computationalProj_bornProb outcomes density outcome
  rw [computationalProj_conjTranspose, computationalProj_idem] at hBorn
  exact hBorn

/-- A microscopic native-record refinement packages the three dynamical
requirements without assuming an effect or a Kraus support equation:
losslessness, coherent recovery, and transport of causal identity. -/
structure NativeRecordPreservingRefinement (outcomes : ℕ) where
  operator : Fin outcomes → SquareMatrix outcomes
  isometric : IsIsometry (krausToStinespring operator)
  counital : coherentRecordCounit outcomes outcomes *
      krausToStinespring operator = (1 : SquareMatrix outcomes)
  transportsRecord : TransportsNativeCausalRecord operator

/-- **Microscopic resolution theorem.**  Every lossless, counital refinement
which transports the native child record is the native causal resolution
law.  Sharp Born effects, exclusivity, locality, and nondemolition are all
consequences. -/
theorem NativeRecordPreservingRefinement.operator_eq_resolution
    {outcomes : ℕ} (refinement : NativeRecordPreservingRefinement outcomes) :
    refinement.operator = causalOutcomeProjector outcomes := by
  apply sharpOutcomeEffect_coherent_unique refinement.operator
    (isometry_recordTransport_implies_sharpEffect refinement.operator
      refinement.isometric refinement.transportsRecord)
  exact (coherentRecordRecovery_iff_sum_eq_one refinement.operator).1
    refinement.counital

/-- The reduced dynamics induced by a native-record-preserving refinement. -/
def NativeRecordPreservingRefinement.apply {outcomes : ℕ}
    (refinement : NativeRecordPreservingRefinement outcomes)
    (density : SquareMatrix outcomes) : SquareMatrix outcomes :=
  ∑ outcome,
    refinement.operator outcome * density *
      (refinement.operator outcome)ᴴ

/-- The newly derived microscopic state has no remaining channel freedom: its
reduced action is exactly the native conditional expectation/dephasing map. -/
theorem NativeRecordPreservingRefinement.apply_eq_dephase
    {outcomes : ℕ} (refinement : NativeRecordPreservingRefinement outcomes)
    (density : SquareMatrix outcomes) :
    refinement.apply density = dephase density := by
  unfold NativeRecordPreservingRefinement.apply
  rw [refinement.operator_eq_resolution]
  change (causalResolutionInstrument outcomes).apply density = dephase density
  exact causalResolutionInstrument_apply_eq_dephase density

/-- Exact repeatability: once child `c` is resolved, resolving the same child
again changes nothing. -/
theorem NativeRecordPreservingRefinement.operator_idempotent
    {outcomes : ℕ} (refinement : NativeRecordPreservingRefinement outcomes)
    (outcome : Fin outcomes) :
    refinement.operator outcome * refinement.operator outcome =
      refinement.operator outcome := by
  rw [refinement.operator_eq_resolution]
  exact computationalProj_idem outcomes outcome

/-- The protected observables are exactly the classical native-record
algebra.  This is the finite superselection statement generated by causal
record transport. -/
theorem NativeRecordPreservingRefinement.fixed_iff_recordDiagonal
    {outcomes : ℕ} (refinement : NativeRecordPreservingRefinement outcomes)
    (density : SquareMatrix outcomes) :
    refinement.apply density = density ↔
      ∀ first second, first ≠ second → density first second = 0 := by
  rw [refinement.apply_eq_dephase]
  exact isIncoherent_iff_diagonal density

/-! ## 3. Exact independence: conservation and covariance do not align records -/

/-- The two orientation projectors, used here as a measurement rotated away
from the native child basis. -/
def rotatedBinaryResolutionOperator (outcome : Fin 2) : SquareMatrix 2 :=
  if outcome = 0 then positiveOrientationProjector
  else negativeOrientationProjector

theorem rotatedBinaryResolutionOperator_coherent :
    ∑ outcome, rotatedBinaryResolutionOperator outcome =
      (1 : SquareMatrix 2) := by
  rw [Fin.sum_univ_two]
  simpa [rotatedBinaryResolutionOperator] using orientationProjectors_sum

theorem rotatedBinaryResolutionOperator_bornComplete :
    (∑ outcome,
      (rotatedBinaryResolutionOperator outcome)ᴴ *
        rotatedBinaryResolutionOperator outcome) =
      (1 : SquareMatrix 2) := by
  rw [Fin.sum_univ_two]
  change positiveOrientationProjectorᴴ * positiveOrientationProjector +
      negativeOrientationProjectorᴴ * negativeOrientationProjector = 1
  rw [(positiveOrientationProjector_isPathDensity.1).eq,
    (negativeOrientationProjector_isPathDensity.1).eq,
    positiveOrientationProjector_idempotent,
    negativeOrientationProjector_idempotent,
    orientationProjectors_sum]

theorem rotatedBinaryResolution_isometry :
    IsIsometry
      (krausToStinespring rotatedBinaryResolutionOperator) :=
  (krausToStinespring_isIsometry_iff_complete
    rotatedBinaryResolutionOperator).2
      rotatedBinaryResolutionOperator_bornComplete

theorem rotatedBinaryResolution_counital :
    coherentRecordCounit 2 2 *
        krausToStinespring rotatedBinaryResolutionOperator =
      (1 : SquareMatrix 2) :=
  (coherentRecordRecovery_iff_sum_eq_one
    rotatedBinaryResolutionOperator).2
      rotatedBinaryResolutionOperator_coherent

/-- Swap the two native child labels. -/
def swapBinaryOutcome (outcome : Fin 2) : Fin 2 :=
  if outcome = 0 then 1 else 0

/-- The unitary permutation matrix implementing the same swap on the carrier. -/
def binarySwapMatrix : SquareMatrix 2 :=
  !![(0 : ℂ), 1; 1, 0]

/-- Covariance of a binary operator family under simultaneous relabeling of
the outcome and its carrier coordinate. -/
def IsBinaryRelabelCovariant
    (operator : Fin 2 → SquareMatrix 2) : Prop :=
  ∀ outcome,
    binarySwapMatrix * operator outcome * binarySwapMatrix =
      operator (swapBinaryOutcome outcome)

theorem rotatedBinaryResolutionOperator_relabelCovariant :
    IsBinaryRelabelCovariant rotatedBinaryResolutionOperator := by
  intro outcome
  fin_cases outcome
  · change binarySwapMatrix * positiveOrientationProjector *
        binarySwapMatrix = negativeOrientationProjector
    rw [positiveOrientationProjector_exact,
      negativeOrientationProjector_exact]
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [binarySwapMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.I_sq]
  · change binarySwapMatrix * negativeOrientationProjector *
        binarySwapMatrix = positiveOrientationProjector
    rw [positiveOrientationProjector_exact,
      negativeOrientationProjector_exact]
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [binarySwapMatrix, Matrix.mul_apply, Fin.sum_univ_two,
        Complex.I_sq]

/-- The rotated law is not sharp in the native child basis. -/
theorem rotatedBinaryResolutionOperator_not_sharp :
    ¬ HasSharpOutcomeEffect rotatedBinaryResolutionOperator := by
  intro hSharp
  have hEffect := hSharp (0 : Fin 2)
  change positiveOrientationProjectorᴴ * positiveOrientationProjector =
      causalOutcomeProjector 2 0 at hEffect
  rw [(positiveOrientationProjector_isPathDensity.1).eq,
    positiveOrientationProjector_idempotent] at hEffect
  have hEntry := congr_fun (congr_fun hEffect (0 : Fin 2)) (1 : Fin 2)
  rw [positiveOrientationProjector_exact] at hEntry
  norm_num [causalOutcomeProjector, computationalProj] at hEntry

/-- The explicit rotated refinement does not transport the native causal
record, despite being lossless and exactly counital. -/
theorem rotatedBinaryResolution_not_recordTransport :
    ¬ TransportsNativeCausalRecord rotatedBinaryResolutionOperator := by
  intro hTransport
  exact rotatedBinaryResolutionOperator_not_sharp
    (isometry_recordTransport_implies_sharpEffect
      rotatedBinaryResolutionOperator rotatedBinaryResolution_isometry
      hTransport)

/-- **Alignment independence/no-go.**  Coherent conservation, reversible
Born refinement, and relabeling covariance still admit a non-native rotated
measurement.  The causal record-transport law is therefore genuinely new
input and cannot be deleted from the microscopic theorem. -/
theorem conservation_covariance_do_not_force_native_sharpness :
    ∃ operator : Fin 2 → SquareMatrix 2,
      (∑ outcome, operator outcome = (1 : SquareMatrix 2)) ∧
      ((∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix 2)) ∧
      IsBinaryRelabelCovariant operator ∧
      ¬ HasSharpOutcomeEffect operator := by
  exact ⟨rotatedBinaryResolutionOperator,
    rotatedBinaryResolutionOperator_coherent,
    rotatedBinaryResolutionOperator_bornComplete,
    rotatedBinaryResolutionOperator_relabelCovariant,
    rotatedBinaryResolutionOperator_not_sharp⟩

/-- **Dynamical alignment no-go.**  There is a lossless recorded refinement
with exact coherent recovery and relabeling covariance which nevertheless
does not transport the native child observable.  Therefore the alignment
equation is logically independent of all three existing principles. -/
theorem isometry_counit_covariance_do_not_force_recordTransport :
    ∃ operator : Fin 2 → SquareMatrix 2,
      IsIsometry (krausToStinespring operator) ∧
      coherentRecordCounit 2 2 * krausToStinespring operator =
        (1 : SquareMatrix 2) ∧
      IsBinaryRelabelCovariant operator ∧
      ¬ TransportsNativeCausalRecord operator := by
  exact ⟨rotatedBinaryResolutionOperator,
    rotatedBinaryResolution_isometry,
    rotatedBinaryResolution_counital,
    rotatedBinaryResolutionOperator_relabelCovariant,
    rotatedBinaryResolution_not_recordTransport⟩

/-! ## 4. The protected-algebra chirality tripwire -/

/-- Native record resolution cannot preserve the opposite Pauli-Y
orientation characters on the same two-dimensional carrier: it maps both to
the same classical record. -/
theorem nativeRecordResolution_erases_sameCarrier_chirality :
    positiveOrientationProjector ≠ negativeOrientationProjector ∧
      (causalResolutionInstrument 2).apply positiveOrientationProjector =
        (causalResolutionInstrument 2).apply
          negativeOrientationProjector := by
  constructor
  · exact orientation_holonomy_requires_path_coherence.1
  · rw [causalResolutionInstrument_apply_eq_dephase,
      causalResolutionInstrument_apply_eq_dephase,
      positiveOrientationProjector_exact,
      negativeOrientationProjector_exact]
    ext row column
    fin_cases row <;> fin_cases column <;>
      norm_num [dephase, Fin.ext_iff]

/-! ## 5. Capstone and axiom audit -/

/-- The exact upgraded boundary: sharp native effects are dynamically derived
from isometric record transport; counital recovery then forces the full law;
the alignment condition is independent of conservation and covariance; and
same-carrier native resolution cannot protect chirality. -/
theorem causalNativeRecordDynamics_capstone :
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes),
      IsIsometry (krausToStinespring operator) →
      TransportsNativeCausalRecord operator →
      HasSharpOutcomeEffect operator) ∧
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes)
      (_hIsometry : IsIsometry (krausToStinespring operator))
      (_hTransport : TransportsNativeCausalRecord operator)
      (observed prepared : Fin outcomes),
      ((operator observed)ᴴ * operator observed) prepared prepared =
        if prepared = observed then 1 else 0) ∧
    (∀ (outcomes : ℕ)
      (refinement : NativeRecordPreservingRefinement outcomes),
      refinement.operator = causalOutcomeProjector outcomes) ∧
    (∀ (outcomes : ℕ)
      (refinement : NativeRecordPreservingRefinement outcomes)
      (density : SquareMatrix outcomes),
      refinement.apply density = density ↔
        ∀ first second, first ≠ second → density first second = 0) ∧
    (∃ operator : Fin 2 → SquareMatrix 2,
      IsIsometry (krausToStinespring operator) ∧
      coherentRecordCounit 2 2 * krausToStinespring operator =
        (1 : SquareMatrix 2) ∧
      IsBinaryRelabelCovariant operator ∧
      ¬ TransportsNativeCausalRecord operator) ∧
    (positiveOrientationProjector ≠ negativeOrientationProjector ∧
      (causalResolutionInstrument 2).apply positiveOrientationProjector =
        (causalResolutionInstrument 2).apply
          negativeOrientationProjector) := by
  exact ⟨fun _ operator hIsometry hTransport =>
      isometry_recordTransport_implies_sharpEffect operator
        hIsometry hTransport,
    fun _ operator hIsometry hTransport =>
      recordTransport_quantumOutcome_exact operator hIsometry hTransport,
    fun _ refinement =>
      NativeRecordPreservingRefinement.operator_eq_resolution refinement,
    fun _ refinement =>
      NativeRecordPreservingRefinement.fixed_iff_recordDiagonal refinement,
    isometry_counit_covariance_do_not_force_recordTransport,
    nativeRecordResolution_erases_sameCarrier_chirality⟩

#print axioms exclusive_bornComplete_implies_sharpEffect
#print axioms transportsNativeCausalRecord_iff_exclusive
#print axioms isometry_recordTransport_implies_sharpEffect
#print axioms recordTransport_quantumOutcome_exact
#print axioms recordTransport_bornProbability_eq_nativeWeight
#print axioms NativeRecordPreservingRefinement.operator_eq_resolution
#print axioms NativeRecordPreservingRefinement.apply_eq_dephase
#print axioms NativeRecordPreservingRefinement.operator_idempotent
#print axioms NativeRecordPreservingRefinement.fixed_iff_recordDiagonal
#print axioms conservation_covariance_do_not_force_native_sharpness
#print axioms isometry_counit_covariance_do_not_force_recordTransport
#print axioms nativeRecordResolution_erases_sameCarrier_chirality
#print axioms causalNativeRecordDynamics_capstone

end

end UnifiedTheory.Audit.KFCausalNativeRecordDynamics
