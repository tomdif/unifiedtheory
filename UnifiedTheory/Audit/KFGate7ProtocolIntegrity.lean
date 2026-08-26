/-
  Audit/KFGate7ProtocolIntegrity.lean

  Typed integrity layer for the five Gate-7 preregistrations.

  The upstream ledger intentionally uses human-readable names in two
  different display formats.  This module does not compare those strings.
  Instead, one finite identifier indexes the authoritative prediction entry
  and falsification row together.  External results are represented by a
  separate provenance-bearing type, and the current result ledger is
  explicitly empty.
-/

import UnifiedTheory.LayerB.PreRegistrationLedger

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFGate7ProtocolIntegrity

open UnifiedTheory.LayerB.PreRegistrationLedger

/-! ## 1. Typed preregistration identifiers -/

/-- One constructor for each of the five actual forward predictions in the
authoritative preregistration ledger. -/
inductive PredictionId
  | higgsTrilinear
  | vub
  | baryonDarkMatterRatio
  | protonDecay
  | muonG2
deriving DecidableEq, Fintype, Repr

/-- Canonical order, matching `preRegisteredEntries` and
`falsificationTable`. -/
def predictionIds : List PredictionId :=
  [ .higgsTrilinear
  , .vub
  , .baryonDarkMatterRatio
  , .protonDecay
  , .muonG2 ]

/-- Total typed lookup into the existing prediction-entry definitions. -/
def predictionEntry : PredictionId → FrameworkPrediction
  | .higgsTrilinear => entry_kappa_lambda
  | .vub => entry_Vub
  | .baryonDarkMatterRatio => entry_omega_b_over_omega_DM
  | .protonDecay => entry_tau_proton
  | .muonG2 => entry_aMu

/-- Total typed lookup into the existing falsification-row definitions. -/
def predictionFalsificationRow : PredictionId → FalsificationRow
  | .higgsTrilinear => row_kappa_lambda
  | .vub => row_Vub
  | .baryonDarkMatterRatio => row_omega_b_DM
  | .protonDecay => row_tau_p
  | .muonG2 => row_aMu

/-- A typed pairing of an authoritative prediction entry with its
authoritative falsification row. -/
structure TypedPreRegistration where
  predictionId : PredictionId
  entry : FrameworkPrediction
  falsificationRow : FalsificationRow

/-- The unique typed registration selected by an identifier. -/
def typedPreRegistration (id : PredictionId) : TypedPreRegistration where
  predictionId := id
  entry := predictionEntry id
  falsificationRow := predictionFalsificationRow id

/-- The complete typed view of the existing five-entry ledger. -/
def typedPreRegistrationLedger : List TypedPreRegistration :=
  predictionIds.map typedPreRegistration

/-- There are exactly five typed prediction identifiers. -/
theorem predictionId_card : Fintype.card PredictionId = 5 := by
  decide

/-- The canonical identifier list contains every typed prediction. -/
theorem predictionIds_complete (id : PredictionId) : id ∈ predictionIds := by
  cases id <;> simp [predictionIds]

/-- No prediction identifier is repeated.  Thus the typed ledger cannot pair
one prediction with two rows merely because display strings happen to differ. -/
theorem predictionIds_nodup : predictionIds.Nodup := by
  decide

/-- Every identifier occurs exactly once in the canonical list. -/
theorem predictionId_count_eq_one (id : PredictionId) :
    predictionIds.count id = 1 := by
  cases id <;> decide

/-- Forgetting the typed keys recovers the authoritative prediction entries
exactly, in their existing order. -/
theorem predictionEntry_image_exact :
    predictionIds.map predictionEntry = preRegisteredEntries := by
  rfl

/-- Forgetting the typed keys recovers the authoritative falsification table
exactly, in its existing order. -/
theorem predictionFalsificationRow_image_exact :
    predictionIds.map predictionFalsificationRow = falsificationTable := by
  rfl

/-- The typed ledger has one unique key for every prediction. -/
theorem typedPreRegistrationLedger_keys_exact :
    typedPreRegistrationLedger.map TypedPreRegistration.predictionId =
      predictionIds := by
  rfl

/-- The typed ledger has exactly the five authoritative registrations. -/
theorem typedPreRegistrationLedger_length :
    typedPreRegistrationLedger.length = 5 := by
  rfl

/-- Projecting the typed ledger recovers all five existing prediction
entries, without comparing their display names to row labels. -/
theorem typedPreRegistrationLedger_entries_exact :
    typedPreRegistrationLedger.map TypedPreRegistration.entry =
      preRegisteredEntries := by
  rfl

/-- Projecting the typed ledger recovers all five existing falsification
rows, without comparing their display names to prediction labels. -/
theorem typedPreRegistrationLedger_rows_exact :
    typedPreRegistrationLedger.map TypedPreRegistration.falsificationRow =
      falsificationTable := by
  rfl

/-- The typed keys are unique. -/
theorem typedPreRegistrationLedger_keys_nodup :
    (typedPreRegistrationLedger.map
      TypedPreRegistration.predictionId).Nodup := by
  rw [typedPreRegistrationLedger_keys_exact]
  exact predictionIds_nodup

/-- The typed keys cover every prediction identifier. -/
theorem typedPreRegistrationLedger_covers (id : PredictionId) :
    id ∈ typedPreRegistrationLedger.map
      TypedPreRegistration.predictionId := by
  rw [typedPreRegistrationLedger_keys_exact]
  exact predictionIds_complete id

/-- Each identifier occurs exactly once as a typed-ledger key. -/
theorem typedPreRegistrationLedger_key_count_eq_one (id : PredictionId) :
    (typedPreRegistrationLedger.map
      TypedPreRegistration.predictionId).count id = 1 := by
  rw [typedPreRegistrationLedger_keys_exact]
  exact predictionId_count_eq_one id

/-! ## 2. External results are not preregistration metadata -/

/-- A nonempty external data source or stable dataset locator.  No concrete
source is asserted by this module. -/
structure DatasetSource where
  value : String
  nonempty : value ≠ ""

/-- A content digest supplied with an external dataset.  Both the digest
algorithm and encoded digest must be recorded. -/
structure DatasetDigest where
  algorithm : String
  value : String
  algorithm_nonempty : algorithm ≠ ""
  value_nonempty : value ≠ ""

/-- An externally supplied observation/publication timestamp.  The payload is
kept abstract apart from nonemptiness so this audit does not invent one. -/
structure ObservationTimestamp where
  value : String
  nonempty : value ≠ ""

/-- Verdicts that may be recorded only after applying the preregistered test
to an external result.  This type itself asserts no verdict. -/
inductive ExternalVerdict
  | survivesRegisteredTest
  | falsifiesRegisteredTest
  | inconclusive
deriving DecidableEq, Repr

/-- Provenance-bearing external evidence.  This is deliberately distinct from
`FrameworkPrediction` and `FalsificationRow`, which contain protocol metadata
rather than a newly observed result. -/
structure ExternalResultEntry where
  predictionId : PredictionId
  datasetSource : DatasetSource
  datasetDigest : DatasetDigest
  observedAt : ObservationTimestamp
  verdict : ExternalVerdict

/-- A result ledger covers Gate 7 empirically only if it contains external
evidence for every typed prediction identifier. -/
def ExternalResultLedgerCovers
    (results : List ExternalResultEntry) : Prop :=
  ∀ id : PredictionId,
    ∃ result ∈ results, result.predictionId = id

/-- No external result/provenance entries are currently asserted here. -/
def currentExternalResultLedger : List ExternalResultEntry := []

/-- In the absence of external result entries, all five identifiers remain in
the explicit pending list. -/
def currentPendingPredictionIds : List PredictionId := predictionIds

theorem currentExternalResultLedger_empty :
    currentExternalResultLedger = [] := rfl

theorem currentPendingPredictionIds_exact :
    currentPendingPredictionIds = predictionIds := rfl

theorem every_prediction_currently_pending (id : PredictionId) :
    id ∈ currentPendingPredictionIds := by
  exact predictionIds_complete id

/-- The present empty result ledger cannot cover the five predictions.  This
is the formal boundary between complete preregistration metadata and pending
external empirical work. -/
theorem currentExternalResultLedger_not_covers :
    ¬ ExternalResultLedgerCovers currentExternalResultLedger := by
  intro hCovers
  rcases hCovers .higgsTrilinear with ⟨result, hResult, _⟩
  simp [currentExternalResultLedger] at hResult

/-! ## 3. Optional freeze provenance -/

/-- A nonempty repository commit hash supplied by an actual freeze event. -/
structure CommitHash where
  value : String
  nonempty : value ≠ ""

/-- Evidence that a preregistration snapshot was frozen at a specific commit
and timestamp.  No `Inhabited` instance is provided. -/
structure FreezeProvenance where
  commitHash : CommitHash
  frozenAt : ObservationTimestamp

/-- No commit hash or freeze timestamp is fabricated by this audit. -/
def currentFreezeProvenance : Option FreezeProvenance := none

theorem currentFreezeProvenance_absent :
    currentFreezeProvenance = none := rfl

#print axioms predictionEntry_image_exact
#print axioms predictionFalsificationRow_image_exact
#print axioms typedPreRegistrationLedger_keys_nodup
#print axioms currentExternalResultLedger_not_covers
#print axioms currentFreezeProvenance_absent

end UnifiedTheory.Audit.KFGate7ProtocolIntegrity
