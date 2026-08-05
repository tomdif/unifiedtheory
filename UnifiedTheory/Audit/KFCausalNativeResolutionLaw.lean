/-
  Audit/KFCausalNativeResolutionLaw.lean

  THE NATIVE CAUSAL RESOLUTION LAW

  The preceding native-successor instrument theorem leaves one microscopic
  choice open: which higher-rank operator belongs to each physical child?
  This module closes the smallest sharp-record ansatz without fitting any
  coefficient.

  At a causal parent, let `c` range over its genuine unlabeled one-element
  successors.  Use those same successors as an orthonormal record carrier and
  require the observable sharp effects `K_c† K_c = |c><c|`.  Positivity then
  derives exclusive response: a definite child can never trigger a different
  child outcome.  Universal coherent conservation derives nondemolition,
  derives full two-sided outcome locality, and uniquely forces

      K_c = |c><c|.

  The forced family is automatically Born complete.  It defines a CPTP,
  idempotent pinching channel which preserves every classical successor
  record and removes every off-diagonal coherence between distinct
  successors.  The construction is covariant under every relabeling, and is
  nontrivial whenever the parent has two distinct physical children.

  This is a candidate microscopic law selected by outcome locality plus the
  repository's coherent-conservation principle.  The mathematical law is
  exact; identifying its record carrier with a laboratory observable remains
  a physical bridge.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalNativeSuccessorInstrument
import UnifiedTheory.Audit.KFCausalDoubleConservationLaw
import UnifiedTheory.LayerB.ConcreteQuantumMeasurement
import UnifiedTheory.LayerB.CoherenceResource

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalNativeResolutionLaw

noncomputable section

open scoped BigOperators ComplexConjugate ComplexOrder
open Matrix
open UnifiedTheory.LayerB.Kraus
open UnifiedTheory.LayerB.Kraus.KrausRepresentation
open UnifiedTheory.LayerB.ConcreteQuantumMeasurement
open UnifiedTheory.LayerB.CoherenceResource
open UnifiedTheory.Audit.KFOrientationCPChannelTower
open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalNativeSuccessorRecord
open UnifiedTheory.Audit.KFCausalNativeSuccessorInstrument
open UnifiedTheory.Audit.KFCausalHolonomyBirthCouplingLaw
open UnifiedTheory.Audit.KFCausalDoubleConservationLaw

/-! ## 1. The sharp finite-outcome resolution law -/

/-- An outcome-indexed operator family is local when the operator for outcome
`outcome` has support only on that outcome's one-dimensional carrier ray. -/
def IsOutcomeLocal {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes) : Prop :=
  ∀ outcome row column,
    row ≠ outcome ∨ column ≠ outcome →
      operator outcome row column = 0

/-- An operator family has exclusive response when a definite successor
record can never trigger a different successor outcome.  Unlike
`IsOutcomeLocal`, this constrains only the input column: it does not assume
that a detected outcome is left on its own output ray. -/
def IsOutcomeExclusive {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes) : Prop :=
  ∀ observed prepared row, observed ≠ prepared →
    operator observed row prepared = 0

/-- Two-sided outcome locality implies the weaker, operational no-false-child
response condition. -/
theorem outcomeLocal_implies_exclusive {outcomes : ℕ}
    {operator : Fin outcomes → SquareMatrix outcomes}
    (hLocal : IsOutcomeLocal operator) :
    IsOutcomeExclusive operator := by
  intro observed prepared row hDistinct
  exact hLocal observed row prepared (Or.inr hDistinct.symm)

/-- A two-outcome witness showing that exclusive response alone is genuinely
weaker than full outcome locality: outcome zero accepts only input zero but
sends it to output ray one. -/
def exclusiveNotLocalWitness : Fin 2 → SquareMatrix 2 :=
  fun observed row prepared =>
    if observed = 0 ∧ row = 1 ∧ prepared = 0 then 1 else 0

theorem exclusiveNotLocalWitness_isExclusive :
    IsOutcomeExclusive exclusiveNotLocalWitness := by
  intro observed prepared row hDistinct
  rw [exclusiveNotLocalWitness, if_neg]
  intro hSupport
  exact hDistinct (hSupport.1.trans hSupport.2.2.symm)

theorem exclusiveNotLocalWitness_not_local :
    ¬ IsOutcomeLocal exclusiveNotLocalWitness := by
  intro hLocal
  have hEntry := hLocal (0 : Fin 2) (1 : Fin 2) (0 : Fin 2)
    (Or.inl (by decide))
  norm_num [exclusiveNotLocalWitness] at hEntry

/-- The canonical sharp projector associated with one resolved outcome. -/
def causalOutcomeProjector (outcomes : ℕ) (outcome : Fin outcomes) :
    SquareMatrix outcomes :=
  computationalProj outcomes outcome

theorem causalOutcomeProjector_local (outcomes : ℕ) :
    IsOutcomeLocal (causalOutcomeProjector outcomes) := by
  intro outcome row column hOutside
  simp only [causalOutcomeProjector, computationalProj_apply]
  rw [if_neg]
  intro hBoth
  rcases hOutside with hRow | hColumn
  · exact hRow hBoth.1
  · exact hColumn hBoth.2

/-- The sharp operators are coherently exhaustive. -/
theorem causalOutcomeProjector_sum_eq_one (outcomes : ℕ) :
    ∑ outcome, causalOutcomeProjector outcomes outcome =
      (1 : SquareMatrix outcomes) := by
  exact computationalProj_complete outcomes

/-- The same sharp family is Born complete. -/
theorem causalOutcomeProjector_born_complete (outcomes : ℕ) :
    (∑ outcome,
      (causalOutcomeProjector outcomes outcome)ᴴ *
        causalOutcomeProjector outcomes outcome) =
      (1 : SquareMatrix outcomes) := by
  exact computationalProj_kraus_complete outcomes

/-- Each child has the sharp Born effect belonging to its own native record.
This is a statement about observable outcome probabilities, not matrix
support: `K_c† K_c = |c><c|`. -/
def HasSharpOutcomeEffect {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes) : Prop :=
  ∀ outcome,
    (operator outcome)ᴴ * operator outcome =
      causalOutcomeProjector outcomes outcome

/-- The canonical successor projectors have exactly the sharp native Born
effects. -/
theorem causalOutcomeProjector_hasSharpEffect (outcomes : ℕ) :
    HasSharpOutcomeEffect (causalOutcomeProjector outcomes) := by
  intro outcome
  rw [causalOutcomeProjector, computationalProj_conjTranspose,
    computationalProj_idem]

/-- Sharp child-by-child effects already imply aggregate Born completeness;
coherent conservation is not needed for this quadratic consequence. -/
theorem sharpOutcomeEffect_bornComplete {outcomes : ℕ}
    {operator : Fin outcomes → SquareMatrix outcomes}
    (hSharp : HasSharpOutcomeEffect operator) :
    (∑ outcome, (operator outcome)ᴴ * operator outcome) =
      (1 : SquareMatrix outcomes) := by
  calc
    (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        ∑ outcome, causalOutcomeProjector outcomes outcome := by
      apply Finset.sum_congr rfl
      intro outcome _
      exact hSharp outcome
    _ = (1 : SquareMatrix outcomes) :=
      causalOutcomeProjector_sum_eq_one outcomes

/-- Sharp child-by-child Born effects prohibit false successor responses.
The proof extracts one matrix coordinate from a vanishing sum of squared
complex norms. -/
theorem sharpOutcomeEffect_implies_exclusive {outcomes : ℕ}
    {operator : Fin outcomes → SquareMatrix outcomes}
    (hSharp : HasSharpOutcomeEffect operator) :
    IsOutcomeExclusive operator := by
  intro observed prepared row hDistinct
  have hDiagonal := congr_fun
    (congr_fun (hSharp observed) prepared) prepared
  have hComplexSum :
      (∑ index, star (operator observed index prepared) *
        operator observed index prepared) = 0 := by
    simpa [Matrix.mul_apply, Matrix.conjTranspose_apply,
      causalOutcomeProjector, computationalProj, hDistinct,
      hDistinct.symm] using hDiagonal
  have hRealSum :
      (∑ index, Complex.normSq (operator observed index prepared)) = 0 := by
    have hReal := congrArg Complex.re hComplexSum
    simpa [map_sum, Complex.mul_re, Complex.normSq] using hReal
  have hCoordinate :
      Complex.normSq (operator observed row prepared) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun index _ => Complex.normSq_nonneg
        (operator observed index prepared))).mp hRealSum row
      (Finset.mem_univ row)
  exact Complex.normSq_eq_zero.mp hCoordinate

/-- **Operational rigidity.**  It is enough to prohibit false child
responses.  If a definite successor never triggers a different outcome and
unresolved amplitudes recombine coherently to the identity, then the output
nondemolition property is derived: every operator is the sharp projector onto
its successor ray. -/
theorem outcomeExclusive_coherent_unique {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hExclusive : IsOutcomeExclusive operator)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix outcomes)) :
    operator = causalOutcomeProjector outcomes := by
  funext outcome
  ext row column
  by_cases hColumn : column = outcome
  · subst column
    have hEntry :
        (∑ other, operator other row outcome) =
          (1 : SquareMatrix outcomes) row outcome := by
      simpa [Matrix.sum_apply] using
        congr_fun (congr_fun hCoherent row) outcome
    have hCollapse :
        (∑ other, operator other row outcome) =
          operator outcome row outcome := by
      rw [Finset.sum_eq_single outcome]
      · intro other _ hOther
        exact hExclusive other outcome row hOther
      · simp
    rw [hCollapse] at hEntry
    simpa [causalOutcomeProjector, computationalProj] using hEntry
  · rw [hExclusive outcome column row (fun h => hColumn h.symm)]
    simp [causalOutcomeProjector, computationalProj, hColumn]

/-- **Born/coherence rigidity.**  Exact native Born effects and coherent
conservation alone force the sharp resolution operators.  The support and
nondemolition properties are both consequences. -/
theorem sharpOutcomeEffect_coherent_unique {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hSharp : HasSharpOutcomeEffect operator)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix outcomes)) :
    operator = causalOutcomeProjector outcomes :=
  outcomeExclusive_coherent_unique operator
    (sharpOutcomeEffect_implies_exclusive hSharp) hCoherent

/-- Exclusive response plus coherent conservation derives the original
two-sided locality postulate rather than requiring it independently. -/
theorem outcomeExclusive_coherent_implies_local {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hExclusive : IsOutcomeExclusive operator)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix outcomes)) :
    IsOutcomeLocal operator := by
  rw [outcomeExclusive_coherent_unique operator hExclusive hCoherent]
  exact causalOutcomeProjector_local outcomes

/-- **Locality rigidity.**  Outcome locality and coherent conservation
uniquely force the sharp causal projectors.  Born completeness is therefore
a consequence rather than an independent fit in this ansatz. -/
theorem outcomeLocal_coherent_unique {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hLocal : IsOutcomeLocal operator)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix outcomes)) :
    operator = causalOutcomeProjector outcomes :=
  outcomeExclusive_coherent_unique operator
    (outcomeLocal_implies_exclusive hLocal) hCoherent

/-- The sharp resolution operators form a projective Born operator law. -/
def causalResolutionProjectiveBornLaw (outcomes : ℕ) :
    ProjectiveBornOperatorLaw outcomes outcomes where
  operator := causalOutcomeProjector outcomes
  bornComplete := causalOutcomeProjector_born_complete outcomes
  coherentlyExhaustive := causalOutcomeProjector_sum_eq_one outcomes

/-- Hence the law preserves every incoming coherent carrier amplitude and
every incoming Born quadratic form. -/
theorem causalResolution_preserves_both (outcomes : ℕ) :
    PreservesEveryCoherentCarrier
        (causalResolutionProjectiveBornLaw outcomes).operator ∧
      PreservesEveryBornCarrier
        (causalResolutionProjectiveBornLaw outcomes).operator :=
  projectiveBornOperatorLaw_preservesEveryParent
    (causalResolutionProjectiveBornLaw outcomes)

/-! ## 2. CPTP channel and exact action -/

/-- The canonical sharp record-resolution instrument. -/
def causalResolutionInstrument (outcomes : ℕ) :
    KrausRepresentation outcomes outcomes outcomes :=
  (causalResolutionProjectiveBornLaw outcomes).toKraus

theorem causalResolutionInstrument_isCPTP (outcomes : ℕ) :
    IsCPTP (causalResolutionInstrument outcomes).toLinearMap :=
  kraus_isCPTP _

/-- Sandwiching by one sharp outcome projector retains exactly the matching
diagonal entry. -/
theorem causalOutcomeProjector_sandwich
    {outcomes : ℕ} (outcome : Fin outcomes)
    (density : SquareMatrix outcomes) :
    causalOutcomeProjector outcomes outcome * density *
        (causalOutcomeProjector outcomes outcome)ᴴ =
      fun row column =>
        if row = outcome ∧ column = outcome then
          density outcome outcome
        else 0 := by
  ext row column
  by_cases hRow : row = outcome
  · subst row
    by_cases hColumn : column = outcome
    · subst column
      simp [causalOutcomeProjector, computationalProj,
        Matrix.mul_apply, Matrix.conjTranspose_apply]
    · simp [causalOutcomeProjector, computationalProj,
        Matrix.mul_apply, Matrix.conjTranspose_apply, hColumn]
  · simp [causalOutcomeProjector, computationalProj,
      Matrix.mul_apply, Matrix.conjTranspose_apply, hRow]

/-- The operator law is exactly complete dephasing in the resolved-outcome
basis. -/
theorem causalResolutionInstrument_apply_eq_dephase
    {outcomes : ℕ} (density : SquareMatrix outcomes) :
    (causalResolutionInstrument outcomes).apply density =
      dephase density := by
  change (∑ outcome,
      causalOutcomeProjector outcomes outcome * density *
        (causalOutcomeProjector outcomes outcome)ᴴ) = dephase density
  simp_rw [causalOutcomeProjector_sandwich]
  ext row column
  rw [Matrix.sum_apply]
  by_cases hRowColumn : row = column
  · subst column
    rw [Finset.sum_eq_single row]
    · simp [dephase]
    · intro other _ hOther
      rw [if_neg]
      intro hBoth
      exact hOther hBoth.1.symm
    · simp
  · apply Eq.trans (Finset.sum_eq_zero (fun outcome _ => by
      rw [if_neg]
      intro hBoth
      exact hRowColumn (hBoth.1.trans hBoth.2.symm)))
    simp [dephase, hRowColumn]

/-- Once a successor record has resolved, applying the law again changes
nothing. -/
theorem causalResolutionInstrument_idempotent
    {outcomes : ℕ} (density : SquareMatrix outcomes) :
    (causalResolutionInstrument outcomes).apply
        ((causalResolutionInstrument outcomes).apply density) =
      (causalResolutionInstrument outcomes).apply density := by
  rw [causalResolutionInstrument_apply_eq_dephase,
    causalResolutionInstrument_apply_eq_dephase,
    dephase_idempotent]

/-- Classical successor weights are nondemolished exactly. -/
theorem causalResolution_preserves_record_weight
    {outcomes : ℕ} (density : SquareMatrix outcomes)
    (outcome : Fin outcomes) :
    (causalResolutionInstrument outcomes).apply density outcome outcome =
      density outcome outcome := by
  rw [causalResolutionInstrument_apply_eq_dephase]
  exact dephase_diagonal_apply density outcome

/-- Coherence between two distinct physical outcomes is erased exactly. -/
theorem causalResolution_erases_cross_record
    {outcomes : ℕ} (density : SquareMatrix outcomes)
    (first second : Fin outcomes) (hDistinct : first ≠ second) :
    (causalResolutionInstrument outcomes).apply density first second = 0 := by
  rw [causalResolutionInstrument_apply_eq_dephase]
  exact dephase_offDiag_zero density hDistinct

/-- The fixed points are precisely the record-diagonal matrices. -/
theorem causalResolution_fixed_iff_recordDiagonal
    {outcomes : ℕ} (density : SquareMatrix outcomes) :
    (causalResolutionInstrument outcomes).apply density = density ↔
      ∀ first second, first ≠ second → density first second = 0 := by
  rw [causalResolutionInstrument_apply_eq_dephase]
  exact isIncoherent_iff_diagonal density

/-! ## 3. Relabeling covariance and uniqueness of the channel -/

/-- Transport a record matrix through a change of successor names. -/
def relabelCausalResolutionMatrix {firstOutcomes secondOutcomes : ℕ}
    (relabeling : Fin firstOutcomes ≃ Fin secondOutcomes)
    (density : SquareMatrix firstOutcomes) :
    SquareMatrix secondOutcomes :=
  fun row column => density (relabeling.symm row) (relabeling.symm column)

/-- The resolution law is independent of record names. -/
theorem causalResolution_relabel_covariant
    {firstOutcomes secondOutcomes : ℕ}
    (relabeling : Fin firstOutcomes ≃ Fin secondOutcomes)
    (density : SquareMatrix firstOutcomes) :
    dephase (relabelCausalResolutionMatrix relabeling density) =
      relabelCausalResolutionMatrix relabeling (dephase density) := by
  ext row column
  by_cases hEqual : row = column
  · subst column
    simp [relabelCausalResolutionMatrix]
  · have hSymm : relabeling.symm row ≠ relabeling.symm column := by
      intro h
      exact hEqual (relabeling.symm.injective h)
    simp [relabelCausalResolutionMatrix, dephase, hEqual, hSymm]

/-- **Channel rigidity.**  A state-independent map which preserves every
record weight and exactly separates distinct successor records is the causal
resolution channel. -/
theorem causalResolutionMap_unique {outcomes : ℕ}
    (channel : SquareMatrix outcomes → SquareMatrix outcomes)
    (hRecord : ∀ density outcome,
      channel density outcome outcome = density outcome outcome)
    (hSeparate : ∀ density first second, first ≠ second →
      channel density first second = 0) :
    channel = fun density =>
      (causalResolutionInstrument outcomes).apply density := by
  funext density
  ext row column
  by_cases hEqual : row = column
  · subst column
    rw [hRecord]
    symm
    exact causalResolution_preserves_record_weight density row
  · rw [hSeparate density row column hEqual,
      causalResolution_erases_cross_record density row column hEqual]

/-- A resolved channel is record-sufficient when its output depends only on
the diagonal successor record, not on any unregistered relative coherence. -/
def IsCausalRecordSufficient {outcomes : ℕ}
    (channel : SquareMatrix outcomes → SquareMatrix outcomes) : Prop :=
  ∀ first second, dephase first = dephase second →
    channel first = channel second

/-- A resolved channel is record-nondemolishing when it fixes every matrix
that already belongs to the classical successor-record algebra. -/
def IsCausalRecordNondemolition {outcomes : ℕ}
    (channel : SquareMatrix outcomes → SquareMatrix outcomes) : Prop :=
  ∀ density, IsIncoherent density → channel density = density

/-- The native resolution channel discards no information beyond relative
cross-successor coherence. -/
theorem causalResolution_recordSufficient (outcomes : ℕ) :
    IsCausalRecordSufficient (fun density =>
      (causalResolutionInstrument outcomes).apply density) := by
  intro first second hRecord
  simpa only [causalResolutionInstrument_apply_eq_dephase] using hRecord

/-- Once a successor record is classical, native resolution does not disturb
it. -/
theorem causalResolution_recordNondemolition (outcomes : ℕ) :
    IsCausalRecordNondemolition (fun density =>
      (causalResolutionInstrument outcomes).apply density) := by
  intro density hClassical
  change (causalResolutionInstrument outcomes).apply density = density
  rw [causalResolutionInstrument_apply_eq_dephase]
  exact hClassical

/-- **Conditional-expectation rigidity.**  Any state-independent operation
whose output depends only on the successor record and which fixes every
already-resolved record is exactly native causal resolution.  No linearity,
positivity, or Kraus presentation is needed for this uniqueness theorem. -/
theorem causalResolution_unique_of_recordPrinciples {outcomes : ℕ}
    (channel : SquareMatrix outcomes → SquareMatrix outcomes)
    (hSufficient : IsCausalRecordSufficient channel)
    (hNondemolition : IsCausalRecordNondemolition channel) :
    channel = fun density =>
      (causalResolutionInstrument outcomes).apply density := by
  funext density
  calc
    channel density = channel (dephase density) :=
      hSufficient density (dephase density)
        (dephase_idempotent density).symm
    _ = dephase density :=
      hNondemolition (dephase density) (dephase_isIncoherent density)
    _ = (causalResolutionInstrument outcomes).apply density :=
      (causalResolutionInstrument_apply_eq_dephase density).symm

/-! ## 4. Instantiation on actual unlabeled causal successors -/

/-- Number of genuine one-element causal children of this parent. -/
abbrev NativeCausalResolutionDimension (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) : ℕ :=
  Fintype.card (NativeCausalSuccessor n pathPrefix)

/-- The actual child `outcome` selects the projector onto its own ray in the
internally enumerated carrier. -/
def nativeCausalResolutionOperator (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (outcome : NativeCausalSuccessor n pathPrefix) :
    SquareMatrix (NativeCausalResolutionDimension n pathPrefix) :=
  causalOutcomeProjector _
    (nativeCausalSuccessorEquivFin n pathPrefix outcome)

/-- Actual physical children are coherently exhaustive. -/
theorem nativeCausalResolutionOperator_sum_eq_one (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ∑ outcome, nativeCausalResolutionOperator n pathPrefix outcome =
      (1 : SquareMatrix (NativeCausalResolutionDimension n pathPrefix)) := by
  let relabeling := nativeCausalSuccessorEquivFin n pathPrefix
  have hReindex :
      (∑ outcome : NativeCausalSuccessor n pathPrefix,
        causalOutcomeProjector _ (relabeling outcome)) =
        ∑ index, causalOutcomeProjector _ index :=
    relabeling.sum_comp (fun index => causalOutcomeProjector _ index)
  simp only [nativeCausalResolutionOperator]
  rw [hReindex,
    causalOutcomeProjector_sum_eq_one]

/-- Actual physical children are Born complete. -/
theorem nativeCausalResolutionOperator_born_complete (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    (∑ outcome,
      (nativeCausalResolutionOperator n pathPrefix outcome)ᴴ *
        nativeCausalResolutionOperator n pathPrefix outcome) =
      (1 : SquareMatrix (NativeCausalResolutionDimension n pathPrefix)) := by
  let relabeling := nativeCausalSuccessorEquivFin n pathPrefix
  have hReindex :
      (∑ outcome : NativeCausalSuccessor n pathPrefix,
        (causalOutcomeProjector _ (relabeling outcome))ᴴ *
          causalOutcomeProjector _ (relabeling outcome)) =
        ∑ index,
          (causalOutcomeProjector _ index)ᴴ *
            causalOutcomeProjector _ index :=
    relabeling.sum_comp (fun index =>
      (causalOutcomeProjector _ index)ᴴ * causalOutcomeProjector _ index)
  simp only [nativeCausalResolutionOperator]
  rw [hReindex,
    causalOutcomeProjector_born_complete]

/-- **All-rank native causal resolution law.**  No external outcome type and
no fitted transition coefficient remain. -/
def nativeCausalResolutionLaw (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    ProjectiveBornOperatorLaw
      (NativeCausalResolutionDimension n pathPrefix)
      (NativeCausalResolutionDimension n pathPrefix) where
  operator := fun index => causalOutcomeProjector _ index
  bornComplete := causalOutcomeProjector_born_complete _
  coherentlyExhaustive := causalOutcomeProjector_sum_eq_one _

/-- The same law packaged through the intrinsic physical-child API. -/
def nativeCausalResolutionInstrument (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    KrausRepresentation
      (NativeCausalResolutionDimension n pathPrefix)
      (NativeCausalResolutionDimension n pathPrefix)
      (NativeCausalResolutionDimension n pathPrefix) :=
  nativeCausalInstrument
    (nativeCausalResolutionOperator n pathPrefix)
    (nativeCausalResolutionOperator_born_complete n pathPrefix)

theorem nativeCausalResolutionInstrument_isCPTP (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n) :
    IsCPTP
      (nativeCausalResolutionInstrument n pathPrefix).toLinearMap :=
  nativeCausalInstrument_isCPTP _
    (nativeCausalResolutionOperator_born_complete n pathPrefix)

/-- The physical-child implementation is exactly the canonical resolution
channel in the internal coordinates. -/
theorem nativeCausalResolutionInstrument_apply_eq_dephase (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (density : SquareMatrix
      (NativeCausalResolutionDimension n pathPrefix)) :
    (nativeCausalResolutionInstrument n pathPrefix).apply density =
      dephase density := by
  unfold nativeCausalResolutionInstrument
  rw [nativeCausalInstrument_apply_eq_intrinsic]
  change (∑ outcome : NativeCausalSuccessor n pathPrefix,
      causalOutcomeProjector _
          (nativeCausalSuccessorEquivFin n pathPrefix outcome) * density *
        (causalOutcomeProjector _
          (nativeCausalSuccessorEquivFin n pathPrefix outcome))ᴴ) = _
  have hReindex :
      (∑ outcome : NativeCausalSuccessor n pathPrefix,
        causalOutcomeProjector _
            (nativeCausalSuccessorEquivFin n pathPrefix outcome) * density *
          (causalOutcomeProjector _
            (nativeCausalSuccessorEquivFin n pathPrefix outcome))ᴴ) =
        ∑ index,
          causalOutcomeProjector _ index * density *
            (causalOutcomeProjector _ index)ᴴ :=
    (nativeCausalSuccessorEquivFin n pathPrefix).sum_comp
      (fun index => causalOutcomeProjector _ index * density *
        (causalOutcomeProjector _ index)ᴴ)
  rw [hReindex]
  exact causalResolutionInstrument_apply_eq_dephase density

/-- Two genuine children witness nontrivial reduced dynamics: their coherent
matrix unit is killed in one causal resolution step. -/
theorem nativeCausalResolution_nontrivial_of_branching (n : ℕ)
    (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
    (first second : NativeCausalSuccessor n pathPrefix)
    (hDistinct : first ≠ second) :
    ∃ density : SquareMatrix (NativeCausalResolutionDimension n pathPrefix),
      (nativeCausalResolutionInstrument n pathPrefix).apply density ≠ density := by
  let firstIndex := nativeCausalSuccessorEquivFin n pathPrefix first
  let secondIndex := nativeCausalSuccessorEquivFin n pathPrefix second
  have hIndexDistinct : firstIndex ≠ secondIndex := by
    exact (nativeCausalSuccessorEquivFin n pathPrefix).injective.ne hDistinct
  let density : SquareMatrix (NativeCausalResolutionDimension n pathPrefix) :=
    fun row column => if row = firstIndex ∧ column = secondIndex then 1 else 0
  refine ⟨density, ?_⟩
  intro hFixed
  have hEntry := congr_fun (congr_fun hFixed firstIndex) secondIndex
  rw [nativeCausalResolutionInstrument_apply_eq_dephase] at hEntry
  simp [density, dephase, hIndexDistinct] at hEntry

/-! ## 5. Capstone and axiom audit -/

/-- The strengthened candidate law in one statement: exact child Born effects
derive exclusive response and, with coherent conservation, force sharp
successor projectors; record sufficiency and nondemolition independently
force their channel; the resulting all-rank law is CPTP and exact
native-record dephasing. -/
theorem causalNativeResolutionLaw_capstone :
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes),
      HasSharpOutcomeEffect operator →
      IsOutcomeExclusive operator) ∧
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes),
      HasSharpOutcomeEffect operator →
      (∑ outcome, (operator outcome)ᴴ * operator outcome) =
        (1 : SquareMatrix outcomes)) ∧
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes),
      HasSharpOutcomeEffect operator →
      (∑ outcome, operator outcome) = (1 : SquareMatrix outcomes) →
      operator = causalOutcomeProjector outcomes) ∧
    (∀ (outcomes : ℕ)
      (channel : SquareMatrix outcomes → SquareMatrix outcomes),
      IsCausalRecordSufficient channel →
      IsCausalRecordNondemolition channel →
      channel = fun density =>
        (causalResolutionInstrument outcomes).apply density) ∧
    (∀ (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n),
      IsCPTP
        (nativeCausalResolutionInstrument n pathPrefix).toLinearMap) ∧
    (∀ (n : ℕ)
      (pathPrefix : RankedGrowthPath CausalSetGrowthBranch n)
      (density : SquareMatrix
        (NativeCausalResolutionDimension n pathPrefix)),
      (nativeCausalResolutionInstrument n pathPrefix).apply density =
        dephase density) := by
  exact ⟨fun _ _ => sharpOutcomeEffect_implies_exclusive,
    fun _ _ => sharpOutcomeEffect_bornComplete,
    fun _ _ => sharpOutcomeEffect_coherent_unique _,
    fun _ _ => causalResolution_unique_of_recordPrinciples _,
    nativeCausalResolutionInstrument_isCPTP,
    nativeCausalResolutionInstrument_apply_eq_dephase⟩

#print axioms sharpOutcomeEffect_implies_exclusive
#print axioms sharpOutcomeEffect_bornComplete
#print axioms sharpOutcomeEffect_coherent_unique
#print axioms outcomeExclusive_coherent_unique
#print axioms outcomeExclusive_coherent_implies_local
#print axioms outcomeLocal_coherent_unique
#print axioms causalResolution_preserves_both
#print axioms causalResolutionInstrument_isCPTP
#print axioms causalResolutionInstrument_apply_eq_dephase
#print axioms causalResolutionInstrument_idempotent
#print axioms causalResolution_relabel_covariant
#print axioms causalResolutionMap_unique
#print axioms causalResolution_unique_of_recordPrinciples
#print axioms nativeCausalResolutionOperator_sum_eq_one
#print axioms nativeCausalResolutionOperator_born_complete
#print axioms nativeCausalResolutionInstrument_isCPTP
#print axioms nativeCausalResolutionInstrument_apply_eq_dephase
#print axioms nativeCausalResolution_nontrivial_of_branching
#print axioms causalNativeResolutionLaw_capstone

end

end UnifiedTheory.Audit.KFCausalNativeResolutionLaw
