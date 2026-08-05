/-
  Audit/KFCausalNativeResolutionLaw.lean

  THE NATIVE CAUSAL RESOLUTION LAW

  The preceding native-successor instrument theorem leaves one microscopic
  choice open: which higher-rank operator belongs to each physical child?
  This module closes the smallest sharp-record ansatz without fitting any
  coefficient.

  At a causal parent, let `c` range over its genuine unlabeled one-element
  successors.  Use those same successors as an orthonormal record carrier and
  require the operator for outcome `c` to be outcome-local: it has matrix
  support only on the ray labelled by `c`.  Universal coherent conservation
  then uniquely forces

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

/-- **Locality rigidity.**  Outcome locality and coherent conservation
uniquely force the sharp causal projectors.  Born completeness is therefore
a consequence rather than an independent fit in this ansatz. -/
theorem outcomeLocal_coherent_unique {outcomes : ℕ}
    (operator : Fin outcomes → SquareMatrix outcomes)
    (hLocal : IsOutcomeLocal operator)
    (hCoherent : ∑ outcome, operator outcome =
      (1 : SquareMatrix outcomes)) :
    operator = causalOutcomeProjector outcomes := by
  funext outcome
  ext row column
  by_cases hRow : row = outcome
  · subst row
    by_cases hColumn : column = outcome
    · subst column
      have hEntry :
          (∑ other, operator other outcome outcome) = 1 := by
        simpa [Matrix.sum_apply] using
          congr_fun (congr_fun hCoherent outcome) outcome
      have hCollapse :
          (∑ other, operator other outcome outcome) =
            operator outcome outcome outcome := by
        rw [Finset.sum_eq_single outcome]
        · intro other _ hOther
          exact hLocal other outcome outcome
            (Or.inl (fun hEqual => hOther hEqual.symm))
        · simp
      rw [hCollapse] at hEntry
      simpa [causalOutcomeProjector, computationalProj] using hEntry
    · rw [hLocal outcome outcome column (Or.inr hColumn)]
      simp [causalOutcomeProjector, computationalProj, hColumn]
  · rw [hLocal outcome row column (Or.inl hRow)]
    simp [causalOutcomeProjector, computationalProj, hRow]

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

/-- The new candidate law in one statement: outcome locality and coherent
conservation force sharp successor projectors; they automatically define an
all-rank CPTP, double-conserving, relabeling-covariant resolution channel;
and genuine causal branching makes that channel observably nontrivial on
coherent record data. -/
theorem causalNativeResolutionLaw_capstone :
    (∀ (outcomes : ℕ)
      (operator : Fin outcomes → SquareMatrix outcomes),
      IsOutcomeLocal operator →
      (∑ outcome, operator outcome) = (1 : SquareMatrix outcomes) →
      operator = causalOutcomeProjector outcomes) ∧
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
  exact ⟨fun _ _ => outcomeLocal_coherent_unique _,
    nativeCausalResolutionInstrument_isCPTP,
    nativeCausalResolutionInstrument_apply_eq_dephase⟩

#print axioms outcomeLocal_coherent_unique
#print axioms causalResolution_preserves_both
#print axioms causalResolutionInstrument_isCPTP
#print axioms causalResolutionInstrument_apply_eq_dephase
#print axioms causalResolutionInstrument_idempotent
#print axioms causalResolution_relabel_covariant
#print axioms causalResolutionMap_unique
#print axioms nativeCausalResolutionOperator_sum_eq_one
#print axioms nativeCausalResolutionOperator_born_complete
#print axioms nativeCausalResolutionInstrument_isCPTP
#print axioms nativeCausalResolutionInstrument_apply_eq_dephase
#print axioms nativeCausalResolution_nontrivial_of_branching
#print axioms causalNativeResolutionLaw_capstone

end

end UnifiedTheory.Audit.KFCausalNativeResolutionLaw
