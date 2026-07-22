/-
  Audit/KFCausalCSpecGlobalAtlas.lean

  ONE GLOBAL FINITE CAUSAL SCHEME WITH AN INTRINSIC UNFILLED S3 ATLAS

  This file closes the finite global-realization problem left open by the
  separate Boolean-chart construction.  It constructs one finite causal
  poset whose genuine principal CSpec points contain four Boolean direction
  charts.  Every pair of charts has causal overlap records, no three distinct
  charts share a regular point, and the direction matching recovered from
  those records is total, unique, witness-independent, and exactly the
  witnessed S3 connection.  It composes on every genuine common regular
  point.  Hence the two unfilled triangle loops have adjacent-transposition
  holonomies and generate all of S3, while the associated rank-two connection
  has neither a global sheet labeling nor a nonzero parallel section.

  Private future tags make the regular events future-distinguishable.  They
  retain the key of the event they distinguish but add no overlap matching;
  direction transport is recovered from common causal overlap records.

  Honest boundary: the pinned CausalAlgebraicGeometry dependency defines
  CSpec as causally-prime upsets but does not equip it with a topology or an
  open-cover API.  The result is therefore a finite intrinsic CSpec atlas and
  nerve realization, not a theorem about topological open subsets.  Nor does
  it prove that the physical sequential-growth law dynamically generates
  this particular finite causal scheme.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecAtlasCocycleNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas

noncomputable section

open CausalAlgebraicGeometry.CausalAlgebra
open CausalAlgebraicGeometry.CausalPrimality
open CausalAlgebraicGeometry.CausalScheme
open CausalAlgebraicGeometry.BulletproofRecovery
open UnifiedTheory.Audit.KFCausalProduct3SheetBridge
open UnifiedTheory.Audit.KFCausalDiamondDirectionCover
open UnifiedTheory.Audit.KFCausalSheetConnectionLaplacian
open UnifiedTheory.Audit.KFCausalSheetHolonomyWitness
open UnifiedTheory.Audit.KFCausalCSpecSheetRealization
open UnifiedTheory.Audit.KFCausalCSpecAtlasCocycleNoGo

/-! ## A single finite causal carrier for four Boolean charts -/

/-- An overlap continuation record joins direction `direction` in `second`
to its transported direction in `first`. -/
structure GlobalOverlapKey where
  first : WitnessState
  second : WitnessState
  direction : Fin 3
deriving DecidableEq, Fintype

/-- The events whose principal CSpec points form the regular finite atlas. -/
inductive GlobalRegularKey
  | direction (chart : WitnessState) (direction : Fin 3)
  | overlap (key : GlobalOverlapKey)
deriving DecidableEq, Fintype

/-- The global causal events: four Boolean chart cells, pairwise continuation
records, and private future signatures for the regular events. -/
inductive GlobalAtlasEvent
  | cell (chart : WitnessState) (cell : TangentCube3)
  | overlap (key : GlobalOverlapKey)
  | tag (key : GlobalRegularKey)
deriving DecidableEq, Fintype

theorem globalOverlapKey_card : Fintype.card GlobalOverlapKey = 48 := by
  decide

theorem globalRegularKey_card : Fintype.card GlobalRegularKey = 60 := by
  decide

theorem globalAtlasEvent_card : Fintype.card GlobalAtlasEvent = 140 := by
  set_option maxRecDepth 10000 in
    decide

/-- A chart cell is incident to an overlap record precisely when it lies below
the recorded atom in either endpoint chart. -/
def overlapIncident (chart : WitnessState) (cell : TangentCube3)
    (key : GlobalOverlapKey) : Prop :=
  (chart = key.first ∧
      cell ⊆ {witnessSheetTransport key.first key.second key.direction}) ∨
    (chart = key.second ∧ cell ⊆ {key.direction})

/-- A private tag retains the entire past of the regular event it identifies.
This makes transitivity immediate while distinguishing its strict future. -/
def tagIncident (chart : WitnessState) (cell : TangentCube3) :
    GlobalRegularKey → Prop
  | .direction tagChart direction =>
      chart = tagChart ∧ cell ⊆ {direction}
  | .overlap key => overlapIncident chart cell key

/-- The global causal order.  Boolean order is retained within every chart;
overlap records sit above the atoms they match; private tags sit above their
corresponding regular event and all of that event's chart-cell past. -/
def globalAtlasLE : GlobalAtlasEvent → GlobalAtlasEvent → Prop
  | .cell firstChart firstCell, .cell secondChart secondCell =>
      firstChart = secondChart ∧ firstCell ⊆ secondCell
  | .cell chart cell, .overlap key => overlapIncident chart cell key
  | .cell chart cell, .tag key => tagIncident chart cell key
  | .overlap first, .overlap second => first = second
  | .overlap first, .tag (.overlap second) => first = second
  | .tag first, .tag second => first = second
  | _, _ => False

theorem globalAtlasLE_refl (event : GlobalAtlasEvent) :
    globalAtlasLE event event := by
  cases event <;> simp [globalAtlasLE]

theorem globalAtlasLE_antisymm (first second : GlobalAtlasEvent)
    (hForward : globalAtlasLE first second)
    (hBackward : globalAtlasLE second first) : first = second := by
  cases first <;> cases second
  case cell.cell firstChart firstCell secondChart secondCell =>
    change firstChart = secondChart ∧ firstCell ⊆ secondCell at hForward
    change secondChart = firstChart ∧ secondCell ⊆ firstCell at hBackward
    rcases hForward with ⟨hChart, hForward⟩
    rcases hBackward with ⟨_, hBackward⟩
    subst secondChart
    congr
    exact Set.Subset.antisymm hForward hBackward
  all_goals simp_all [globalAtlasLE]

theorem overlapIncident_mono {chart : WitnessState}
    {first second : TangentCube3} {key : GlobalOverlapKey}
    (hSubset : first ⊆ second) (hIncident : overlapIncident chart second key) :
    overlapIncident chart first key := by
  rcases hIncident with hIncident | hIncident
  · exact Or.inl ⟨hIncident.1, Set.Subset.trans hSubset hIncident.2⟩
  · exact Or.inr ⟨hIncident.1, Set.Subset.trans hSubset hIncident.2⟩

theorem tagIncident_mono {chart : WitnessState}
    {first second : TangentCube3} {key : GlobalRegularKey}
    (hSubset : first ⊆ second) (hIncident : tagIncident chart second key) :
    tagIncident chart first key := by
  cases key with
  | direction tagChart direction =>
      exact ⟨hIncident.1, Set.Subset.trans hSubset hIncident.2⟩
  | overlap key =>
      exact overlapIncident_mono hSubset hIncident

theorem globalAtlasLE_trans (first second third : GlobalAtlasEvent)
    (hFirstSecond : globalAtlasLE first second)
    (hSecondThird : globalAtlasLE second third) :
    globalAtlasLE first third := by
  cases first with
  | cell firstChart firstCell =>
      cases second with
      | cell secondChart secondCell =>
          rcases hFirstSecond with ⟨hChart, hSubset⟩
          subst secondChart
          cases third with
          | cell thirdChart thirdCell =>
              rcases hSecondThird with ⟨hChart, hThirdSubset⟩
              exact ⟨hChart, Set.Subset.trans hSubset hThirdSubset⟩
          | overlap key =>
              exact overlapIncident_mono hSubset hSecondThird
          | tag key =>
              exact tagIncident_mono hSubset hSecondThird
      | overlap secondKey =>
          cases third with
          | cell thirdChart thirdCell => contradiction
          | overlap thirdKey =>
              change secondKey = thirdKey at hSecondThird
              subst thirdKey
              exact hFirstSecond
          | tag key =>
              cases key with
              | direction tagChart direction => contradiction
              | overlap thirdKey =>
                  change secondKey = thirdKey at hSecondThird
                  subst thirdKey
                  exact hFirstSecond
      | tag secondKey =>
          cases third with
          | cell thirdChart thirdCell => contradiction
          | overlap thirdKey => contradiction
          | tag thirdKey =>
              change secondKey = thirdKey at hSecondThird
              subst thirdKey
              exact hFirstSecond
  | overlap firstKey =>
      cases second with
      | cell secondChart secondCell => contradiction
      | overlap secondKey =>
          change firstKey = secondKey at hFirstSecond
          subst secondKey
          cases third with
          | cell thirdChart thirdCell => contradiction
          | overlap thirdKey => exact hSecondThird
          | tag key => exact hSecondThird
      | tag secondKey =>
          cases secondKey with
          | direction tagChart direction => contradiction
          | overlap secondKey =>
              change firstKey = secondKey at hFirstSecond
              subst secondKey
              cases third with
              | cell thirdChart thirdCell => contradiction
              | overlap thirdKey => contradiction
              | tag thirdKey =>
                  change GlobalRegularKey.overlap firstKey = thirdKey at hSecondThird
                  subst thirdKey
                  rfl
  | tag firstKey =>
      cases second with
      | cell secondChart secondCell => contradiction
      | overlap secondKey => contradiction
      | tag secondKey =>
          change firstKey = secondKey at hFirstSecond
          subst secondKey
          cases third with
          | cell thirdChart thirdCell => contradiction
          | overlap thirdKey => contradiction
          | tag thirdKey => exact hSecondThird

noncomputable instance globalAtlasLEDecidable : DecidableRel globalAtlasLE :=
  Classical.decRel _

/-- The incidence algebra of the one global finite causal atlas. -/
abbrev globalAtlasCausalAlgebra : CAlg ℂ :=
  fromFinitePoset GlobalAtlasEvent globalAtlasLE
    globalAtlasLE_refl globalAtlasLE_antisymm globalAtlasLE_trans

@[simp]
theorem globalAtlasCausalAlgebra_le (first second : GlobalAtlasEvent) :
    globalAtlasCausalAlgebra.le first second ↔ globalAtlasLE first second :=
  Iff.rfl

/-- The corresponding native finite causal scheme. -/
noncomputable def globalAtlasCausalScheme : CausalSchemeData ℂ :=
  causalScheme_of_poset GlobalAtlasEvent globalAtlasLE
    globalAtlasLE_refl globalAtlasLE_antisymm globalAtlasLE_trans

theorem globalAtlasCausalScheme_algebra :
    globalAtlasCausalScheme.algebra = globalAtlasCausalAlgebra := by
  rfl

/-- Each chart retains an exact Boolean tangent-cube order internally. -/
@[simp]
theorem globalAtlasLE_cell_iff (chart : WitnessState)
    (first second : TangentCube3) :
    globalAtlasLE (.cell chart first) (.cell chart second) ↔
      first ⊆ second := by
  simp [globalAtlasLE]

/-! ## Genuine regular CSpec points -/

/-- The causal event represented by a regular-atlas key. -/
def globalRegularEvent : GlobalRegularKey → GlobalAtlasEvent
  | .direction chart direction => .cell chart {direction}
  | .overlap key => .overlap key

/-- Every global causal event has its genuine principal native CSpec point. -/
def globalAtlasCSpecPoint (event : GlobalAtlasEvent) :
    CSpec globalAtlasCausalAlgebra :=
  cspecPoint globalAtlasCausalAlgebra event

/-- Principal CSpec points used by the regular finite atlas. -/
def globalRegularCSpecPoint (key : GlobalRegularKey) :
    CSpec globalAtlasCausalAlgebra :=
  globalAtlasCSpecPoint (globalRegularEvent key)

/-- A direction's private future tag occurs above exactly that regular
direction point and above no overlap record. -/
theorem directionTag_mem_regularFuture_iff
    (key : GlobalRegularKey) (chart : WitnessState) (direction : Fin 3) :
    (.tag (.direction chart direction) : GlobalAtlasEvent) ∈
        principalUpset globalAtlasCausalAlgebra (globalRegularEvent key) ↔
      key = .direction chart direction := by
  cases key with
  | direction keyChart keyDirection =>
      simp [globalRegularEvent, fromFinitePoset,
        principalUpset, globalAtlasLE, tagIncident]
  | overlap key =>
      simp [globalRegularEvent, fromFinitePoset,
        principalUpset, globalAtlasLE]

/-- Among regular overlap records, each overlap's private future tag singles
out exactly its own principal point. -/
theorem overlapTag_mem_overlapFuture_iff
    (first second : GlobalOverlapKey) :
    (.tag (.overlap second) : GlobalAtlasEvent) ∈
        principalUpset globalAtlasCausalAlgebra
          (globalRegularEvent (.overlap first)) ↔
      first = second := by
  simp [globalRegularEvent, fromFinitePoset,
    principalUpset, globalAtlasLE]

/-- The regular direction and overlap events remain pairwise distinct after
passage to genuine principal CSpec points. -/
theorem globalRegularCSpecPoint_injective :
    Function.Injective globalRegularCSpecPoint := by
  intro first second hEqual
  have hFutures := congrArg Subtype.val hEqual
  cases first with
  | direction firstChart firstDirection =>
      have hMembership := Set.ext_iff.mp hFutures
        (.tag (.direction firstChart firstDirection))
      have hLeft :
          (.tag (.direction firstChart firstDirection) : GlobalAtlasEvent) ∈
            principalUpset globalAtlasCausalAlgebra
              (globalRegularEvent (.direction firstChart firstDirection)) :=
        (directionTag_mem_regularFuture_iff
          (.direction firstChart firstDirection) firstChart firstDirection).2 rfl
      have hRight := hMembership.mp hLeft
      exact (directionTag_mem_regularFuture_iff second firstChart firstDirection).1 hRight |>.symm
  | overlap firstKey =>
      cases second with
      | direction secondChart secondDirection =>
          have hMembership := Set.ext_iff.mp hFutures
            (.tag (.direction secondChart secondDirection))
          have hRight :
              (.tag (.direction secondChart secondDirection) : GlobalAtlasEvent) ∈
                principalUpset globalAtlasCausalAlgebra
                  (globalRegularEvent (.direction secondChart secondDirection)) :=
            (directionTag_mem_regularFuture_iff
              (.direction secondChart secondDirection)
                secondChart secondDirection).2 rfl
          have hLeft := hMembership.mpr hRight
          have hImpossible :=
            (directionTag_mem_regularFuture_iff
              (.overlap firstKey) secondChart secondDirection).1 hLeft
          contradiction
      | overlap secondKey =>
          have hMembership := Set.ext_iff.mp hFutures
            (.tag (.overlap firstKey))
          have hLeft :
              (.tag (.overlap firstKey) : GlobalAtlasEvent) ∈
                principalUpset globalAtlasCausalAlgebra
                  (globalRegularEvent (.overlap firstKey)) :=
            (overlapTag_mem_overlapFuture_iff firstKey firstKey).2 rfl
          have hRight := hMembership.mp hLeft
          have hKeys :=
            (overlapTag_mem_overlapFuture_iff secondKey firstKey).1 hRight
          simp [hKeys]

/-! ## The intrinsic unfilled four-chart CSpec nerve -/

/-- Incidence of a regular key with one of the four charts.  A direction
belongs to its unique chart; an overlap record belongs to its two endpoint
charts. -/
def regularKeyInChart (chart : WitnessState) : GlobalRegularKey → Prop
  | .direction keyChart _ => keyChart = chart
  | .overlap key => key.first = chart ∨ key.second = chart

/-- A finite chart is a subset of the genuine native CSpec consisting of the
regular principal points incident with that chart. -/
def globalRegularCSpecChart (chart : WitnessState) :
    Set (CSpec globalAtlasCausalAlgebra) :=
  {point | ∃ key, regularKeyInChart chart key ∧
    globalRegularCSpecPoint key = point}

theorem globalRegularCSpecPoint_mem_chart
    (chart : WitnessState) (key : GlobalRegularKey)
    (hMember : regularKeyInChart chart key) :
    globalRegularCSpecPoint key ∈ globalRegularCSpecChart chart := by
  exact ⟨key, hMember, rfl⟩

/-- Every pair of charts has a genuine shared CSpec overlap record. -/
theorem globalRegularCSpecChart_pair_intersection_nonempty
    (first second : WitnessState) :
    (globalRegularCSpecChart first ∩
      globalRegularCSpecChart second).Nonempty := by
  let key : GlobalOverlapKey := ⟨first, second, 0⟩
  refine ⟨globalRegularCSpecPoint (.overlap key), ?_, ?_⟩
  · apply globalRegularCSpecPoint_mem_chart
    exact Or.inl rfl
  · apply globalRegularCSpecPoint_mem_chart
    exact Or.inr rfl

/-- A regular key can never lie in three pairwise-distinct charts. -/
theorem regularKey_not_in_three_distinct_charts
    (first second third : WitnessState)
    (hFirstSecond : first ≠ second)
    (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third)
    (key : GlobalRegularKey) :
    ¬ (regularKeyInChart first key ∧
      regularKeyInChart second key ∧
      regularKeyInChart third key) := by
  cases key with
  | direction chart direction =>
      simp only [regularKeyInChart]
      aesop
  | overlap key =>
      simp only [regularKeyInChart]
      aesop

/-- The chart nerve has no filled two-simplex: three distinct charts have
empty common regular CSpec intersection. -/
theorem globalRegularCSpecChart_triple_intersection_empty
    (first second third : WitnessState)
    (hFirstSecond : first ≠ second)
    (hFirstThird : first ≠ third)
    (hSecondThird : second ≠ third) :
    globalRegularCSpecChart first ∩
        globalRegularCSpecChart second ∩
          globalRegularCSpecChart third = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro point hPoint
  rcases hPoint.1.1 with ⟨firstKey, hFirstMember, hFirstPoint⟩
  rcases hPoint.1.2 with ⟨secondKey, hSecondMember, hSecondPoint⟩
  rcases hPoint.2 with ⟨thirdKey, hThirdMember, hThirdPoint⟩
  have hFirstSecondKey : firstKey = secondKey :=
    globalRegularCSpecPoint_injective
      (hFirstPoint.trans hSecondPoint.symm)
  have hFirstThirdKey : firstKey = thirdKey :=
    globalRegularCSpecPoint_injective
      (hFirstPoint.trans hThirdPoint.symm)
  subst secondKey
  subst thirdKey
  exact regularKey_not_in_three_distinct_charts first second third
    hFirstSecond hFirstThird hSecondThird firstKey
      ⟨hFirstMember, hSecondMember, hThirdMember⟩

/-- In particular, the two witnessed transposition triangles are genuine
unfilled cycles in the regular CSpec nerve. -/
theorem witnessed_triangles_are_unfilled_CSpec_cycles :
    (globalRegularCSpecChart 0 ∩ globalRegularCSpecChart 1 ∩
        globalRegularCSpecChart 3 = ∅) ∧
      (globalRegularCSpecChart 0 ∩ globalRegularCSpecChart 2 ∩
        globalRegularCSpecChart 3 = ∅) := by
  constructor
  · exact globalRegularCSpecChart_triple_intersection_empty 0 1 3
      (by decide) (by decide) (by decide)
  · exact globalRegularCSpecChart_triple_intersection_empty 0 2 3
      (by decide) (by decide) (by decide)

/-! ## Direction transport recovered from causal overlap incidence -/

/-- Two endpoint directions match when their atom events share a global
overlap continuation record with the specified ordered endpoints.  This
definition reads only the global causal order and the endpoint metadata of
the overlap record; it does not mention a returned sheet permutation. -/
def GloballyMatchedDirection
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    Prop :=
  ∃ key : GlobalOverlapKey,
    key.first = first ∧ key.second = second ∧
      globalAtlasLE (.cell first {firstDirection}) (.overlap key) ∧
      globalAtlasLE (.cell second {secondDirection}) (.overlap key)

/-- The same matching relation stated natively inside CSpec: a common
overlap continuation event belongs to both strict-future prime sets. -/
def CSpecMatchedDirection
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    Prop :=
  ∃ key : GlobalOverlapKey,
    key.first = first ∧ key.second = second ∧
      (.overlap key : GlobalAtlasEvent) ∈
        (globalRegularCSpecPoint (.direction first firstDirection)).1 ∧
      (.overlap key : GlobalAtlasEvent) ∈
        (globalRegularCSpecPoint (.direction second secondDirection)).1

/-- One particular continuation record witnesses one particular matching. -/
def IsCSpecContinuationWitness
    (first second : WitnessState) (firstDirection secondDirection : Fin 3)
    (key : GlobalOverlapKey) : Prop :=
  key.first = first ∧ key.second = second ∧
    (.overlap key : GlobalAtlasEvent) ∈
      (globalRegularCSpecPoint (.direction first firstDirection)).1 ∧
    (.overlap key : GlobalAtlasEvent) ∈
      (globalRegularCSpecPoint (.direction second secondDirection)).1

theorem CSpecMatchedDirection_iff_exists_continuationWitness
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    CSpecMatchedDirection first second firstDirection secondDirection ↔
      ∃ key, IsCSpecContinuationWitness first second
        firstDirection secondDirection key := by
  rfl

theorem overlap_mem_directionCSpecFuture_iff
    (chart : WitnessState) (direction : Fin 3) (key : GlobalOverlapKey) :
    (.overlap key : GlobalAtlasEvent) ∈
        (globalRegularCSpecPoint (.direction chart direction)).1 ↔
      globalAtlasLE (.cell chart {direction}) (.overlap key) := by
  simp [globalRegularCSpecPoint, globalAtlasCSpecPoint, globalRegularEvent,
    cspecPoint, principalUpset, fromFinitePoset]

theorem CSpecMatchedDirection_iff_global
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    CSpecMatchedDirection first second firstDirection secondDirection ↔
      GloballyMatchedDirection first second firstDirection secondDirection := by
  simp only [CSpecMatchedDirection, GloballyMatchedDirection,
    overlap_mem_directionCSpecFuture_iff]

/-- The matching relation intrinsically recovers exactly the connection
transport encoded by the global causal continuations. -/
theorem globallyMatchedDirection_iff
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    GloballyMatchedDirection first second firstDirection secondDirection ↔
      firstDirection = witnessSheetTransport first second secondDirection := by
  constructor
  · rintro ⟨⟨keyFirst, keySecond, keyDirection⟩,
      hFirst, hSecond, hFirstIncident, hSecondIncident⟩
    dsimp only at hFirst hSecond
    subst first
    subst second
    change overlapIncident keyFirst {firstDirection}
      ⟨keyFirst, keySecond, keyDirection⟩ at hFirstIncident
    change overlapIncident keySecond {secondDirection}
      ⟨keyFirst, keySecond, keyDirection⟩ at hSecondIncident
    by_cases hEndpoints : keyFirst = keySecond
    · subst keySecond
      have hFirstDirection : firstDirection = keyDirection := by
        simpa [overlapIncident, witnessSheetTransport_refl] using hFirstIncident
      have hSecondDirection : secondDirection = keyDirection := by
        simpa [overlapIncident, witnessSheetTransport_refl] using hSecondIncident
      simp [hFirstDirection, hSecondDirection, witnessSheetTransport_refl]
    · have hFirstDirection :
          firstDirection =
            witnessSheetTransport keyFirst keySecond keyDirection := by
          rcases hFirstIncident with hIncident | hIncident
          · exact Set.singleton_subset_singleton.mp hIncident.2
          · exact False.elim (hEndpoints hIncident.1)
      have hSecondDirection : secondDirection = keyDirection := by
        rcases hSecondIncident with hIncident | hIncident
        · exact False.elim (hEndpoints hIncident.1.symm)
        · exact Set.singleton_subset_singleton.mp hIncident.2
      rw [hFirstDirection, hSecondDirection]
  · intro hDirection
    refine ⟨⟨first, second, secondDirection⟩, rfl, rfl, ?_, ?_⟩
    · exact Or.inl ⟨rfl, Set.singleton_subset_singleton.mpr hDirection⟩
    · exact Or.inr ⟨rfl, Set.Subset.rfl⟩

/-- Native CSpec future incidence recovers the same unique sheet transport. -/
theorem CSpecMatchedDirection_iff
    (first second : WitnessState) (firstDirection secondDirection : Fin 3) :
    CSpecMatchedDirection first second firstDirection secondDirection ↔
      firstDirection = witnessSheetTransport first second secondDirection := by
  rw [CSpecMatchedDirection_iff_global, globallyMatchedDirection_iff]

/-- **Witness independence.** Any two valid continuation witnesses with the
same endpoint sheet determine the same source sheet.  The matching therefore
does not depend on which continuation record was used to observe it. -/
theorem continuationWitness_independent
    (first second : WitnessState)
    (firstDirection firstDirection' secondDirection : Fin 3)
    (firstWitness secondWitness : GlobalOverlapKey)
    (hFirst : IsCSpecContinuationWitness first second
      firstDirection secondDirection firstWitness)
    (hSecond : IsCSpecContinuationWitness first second
      firstDirection' secondDirection secondWitness) :
    firstDirection = firstDirection' := by
  have hFirstMatch :
      CSpecMatchedDirection first second firstDirection secondDirection :=
    (CSpecMatchedDirection_iff_exists_continuationWitness
      first second firstDirection secondDirection).2 ⟨firstWitness, hFirst⟩
  have hSecondMatch :
      CSpecMatchedDirection first second firstDirection' secondDirection :=
    (CSpecMatchedDirection_iff_exists_continuationWitness
      first second firstDirection' secondDirection).2 ⟨secondWitness, hSecond⟩
  rw [(CSpecMatchedDirection_iff first second
      firstDirection secondDirection).1 hFirstMatch,
    (CSpecMatchedDirection_iff first second
      firstDirection' secondDirection).1 hSecondMatch]

/-- Each direction in the second chart has a unique causally matched
direction in the first chart. -/
theorem existsUnique_globallyMatchedDirection
    (first second : WitnessState) (secondDirection : Fin 3) :
    ∃! firstDirection,
      GloballyMatchedDirection first second firstDirection secondDirection := by
  refine ⟨witnessSheetTransport first second secondDirection,
    (globallyMatchedDirection_iff first second _ secondDirection).2 rfl, ?_⟩
  intro candidate hCandidate
  exact (globallyMatchedDirection_iff first second candidate secondDirection).1
    hCandidate

/-- **Overlap totality.** Every sheet of the second chart has exactly one
matching sheet of the first chart, witnessed inside their native prime future
sets. -/
theorem existsUnique_CSpecMatchedDirection
    (first second : WitnessState) (secondDirection : Fin 3) :
    ∃! firstDirection,
      CSpecMatchedDirection first second firstDirection secondDirection := by
  refine ⟨witnessSheetTransport first second secondDirection,
    (CSpecMatchedDirection_iff first second _ secondDirection).2 rfl, ?_⟩
  intro candidate hCandidate
  exact (CSpecMatchedDirection_iff first second candidate secondDirection).1
    hCandidate

/-- The direction selected solely by unique causal matching. -/
noncomputable def recoveredDirection
    (first second : WitnessState) (secondDirection : Fin 3) : Fin 3 :=
  Classical.choose
    (existsUnique_globallyMatchedDirection first second secondDirection)

theorem recoveredDirection_isMatched
    (first second : WitnessState) (secondDirection : Fin 3) :
    GloballyMatchedDirection first second
      (recoveredDirection first second secondDirection) secondDirection :=
  (Classical.choose_spec
    (existsUnique_globallyMatchedDirection first second secondDirection)).1

theorem recoveredDirection_isCSpecMatched
    (first second : WitnessState) (secondDirection : Fin 3) :
    CSpecMatchedDirection first second
      (recoveredDirection first second secondDirection) secondDirection :=
  (CSpecMatchedDirection_iff_global first second _ secondDirection).2
    (recoveredDirection_isMatched first second secondDirection)

theorem recoveredDirection_eq_witness
    (first second : WitnessState) (secondDirection : Fin 3) :
    recoveredDirection first second secondDirection =
      witnessSheetTransport first second secondDirection :=
  (globallyMatchedDirection_iff first second _ secondDirection).1
    (recoveredDirection_isMatched first second secondDirection)

/-- The causal matching relation therefore produces a genuine direction
equivalence between every pair of charts. -/
noncomputable def recoveredCSpecDirectionTransport
    (first second : WitnessState) : Equiv.Perm (Fin 3) where
  toFun := recoveredDirection first second
  invFun := recoveredDirection second first
  left_inv direction := by
    rw [recoveredDirection_eq_witness, recoveredDirection_eq_witness,
      witnessSheetTransport_reverse]
    exact (witnessSheetTransport first second).symm_apply_apply direction
  right_inv direction := by
    rw [recoveredDirection_eq_witness, recoveredDirection_eq_witness]
    calc
      witnessSheetTransport first second
          (witnessSheetTransport second first direction) =
          witnessSheetTransport first second
            ((witnessSheetTransport first second).symm direction) := by
              rw [witnessSheetTransport_reverse first second]
      _ = direction :=
        (witnessSheetTransport first second).apply_symm_apply direction

theorem recoveredCSpecDirectionTransport_eq_witness
    (first second : WitnessState) :
    recoveredCSpecDirectionTransport first second =
      witnessSheetTransport first second := by
  apply Equiv.ext
  intro direction
  exact recoveredDirection_eq_witness first second direction

theorem recoveredCSpecDirectionTransport_refl (chart : WitnessState) :
    recoveredCSpecDirectionTransport chart chart = Equiv.refl (Fin 3) := by
  rw [recoveredCSpecDirectionTransport_eq_witness,
    witnessSheetTransport_refl]

theorem recoveredCSpecDirectionTransport_reverse
    (first second : WitnessState) :
    recoveredCSpecDirectionTransport second first =
      (recoveredCSpecDirectionTransport first second).symm := by
  rw [recoveredCSpecDirectionTransport_eq_witness,
    recoveredCSpecDirectionTransport_eq_witness,
    witnessSheetTransport_reverse]

/-- **Intrinsic filled-overlap composition.** Whenever one genuine regular
CSpec point belongs to three charts, the continuation-recovered transports
obey the Cech cocycle law there.  For three distinct charts the antecedent is
impossible because their regular intersection is empty; this guard is exactly
what permits nontrivial holonomy on the two unfilled triangles. -/
theorem recoveredCSpecDirectionTransport_cocycle_on_commonPoint
    (first second third : WitnessState)
    (point : CSpec globalAtlasCausalAlgebra)
    (hFirst : point ∈ globalRegularCSpecChart first)
    (hSecond : point ∈ globalRegularCSpecChart second)
    (hThird : point ∈ globalRegularCSpecChart third) :
    (recoveredCSpecDirectionTransport second third).trans
        (recoveredCSpecDirectionTransport first second) =
      recoveredCSpecDirectionTransport first third := by
  by_cases hFirstSecond : first = second
  · subst second
    rw [recoveredCSpecDirectionTransport_refl]
    rfl
  by_cases hFirstThird : first = third
  · subst third
    rw [recoveredCSpecDirectionTransport_refl,
      recoveredCSpecDirectionTransport_reverse]
    exact Equiv.symm_trans_self _
  by_cases hSecondThird : second = third
  · subst third
    rw [recoveredCSpecDirectionTransport_refl]
    rfl
  have hEmpty := globalRegularCSpecChart_triple_intersection_empty
    first second third hFirstSecond hFirstThird hSecondThird
  have hPointIntersection : point ∈
      globalRegularCSpecChart first ∩
        globalRegularCSpecChart second ∩
          globalRegularCSpecChart third :=
    ⟨⟨hFirst, hSecond⟩, hThird⟩
  rw [hEmpty] at hPointIntersection
  simp at hPointIntersection

/-! ## Full S3 monodromy of the unfilled CSpec nerve -/

/-- Boundary transport recovered from the global causal scheme along one
three-chart nerve cycle. -/
noncomputable def recoveredTriangleHolonomy
    (vertex : Fin 3 → WitnessState) : Equiv.Perm (Fin 3) :=
  (((recoveredCSpecDirectionTransport (vertex 2) (vertex 0)).trans
    (recoveredCSpecDirectionTransport (vertex 1) (vertex 2))).trans
      (recoveredCSpecDirectionTransport (vertex 0) (vertex 1)))

theorem recovered_firstTriangle_holonomy :
    recoveredTriangleHolonomy firstWitnessTriangleVertex = swapZeroOne := by
  simp only [recoveredTriangleHolonomy,
    recoveredCSpecDirectionTransport_eq_witness]
  exact firstWitnessTriangle_holonomy

theorem recovered_secondTriangle_holonomy :
    recoveredTriangleHolonomy secondWitnessTriangleVertex = swapOneTwo := by
  simp only [recoveredTriangleHolonomy,
    recoveredCSpecDirectionTransport_eq_witness]
  exact secondWitnessTriangle_holonomy

/-- Six words in the two holonomies recovered from the global causal order. -/
noncomputable def recoveredGlobalCSpecHolonomyWord :
    Fin 6 → Equiv.Perm (Fin 3) :=
  let first := recoveredTriangleHolonomy firstWitnessTriangleVertex
  let second := recoveredTriangleHolonomy secondWitnessTriangleVertex
  ![
    Equiv.refl (Fin 3),
    first,
    second,
    second.trans first,
    first.trans second,
    first.trans (second.trans first)
  ]

theorem recoveredGlobalCSpecHolonomyWord_eq_fullS3Word (index : Fin 6) :
    recoveredGlobalCSpecHolonomyWord index = fullS3PermutationWord index := by
  fin_cases index <;>
    simp [recoveredGlobalCSpecHolonomyWord,
      recovered_firstTriangle_holonomy, recovered_secondTriangle_holonomy,
      fullS3PermutationWord]

/-- **Global finite CSpec realization theorem.** Every permutation of the
three intrinsic direction points is a word in the two unfilled loop
holonomies recovered from one global finite causal scheme. -/
theorem globalCSpecAtlas_hasFullS3Monodromy
    (relabeling : Equiv.Perm (Fin 3)) :
    ∃ index : Fin 6, recoveredGlobalCSpecHolonomyWord index = relabeling := by
  obtain ⟨index, hIndex⟩ := fullS3WitnessHolonomy_surjective relabeling
  refine ⟨index, ?_⟩
  rw [recoveredGlobalCSpecHolonomyWord_eq_fullS3Word,
    ← fullS3WitnessHolonomy_eq_word]
  exact hIndex

/-- Full S3 monodromy acts transitively on the three directions.  This is the
finite algebraic content behind connectedness of the associated three-sheet
cover; no topological connectedness claim is made without an upstream CSpec
topology. -/
theorem globalCSpecMonodromy_action_transitive
    (first second : Fin 3) :
    ∃ index : Fin 6,
      recoveredGlobalCSpecHolonomyWord index first = second := by
  obtain ⟨index, hIndex⟩ :=
    globalCSpecAtlas_hasFullS3Monodromy (Equiv.swap first second)
  refine ⟨index, ?_⟩
  rw [hIndex]
  simp

/-! ## The full monodromy obstructs a global sheet labeling -/

/-- Regard every ordered chart pair as an edge, with its direction transport
recovered from the global CSpec continuation relation. -/
noncomputable def globalCSpecDirectionEdgeLaw :
    DirectionEdgeLaw WitnessState (fun _ => Fin 3)
      (fun _ => WitnessState) where
  target := fun _ next => next
  transport := fun state next =>
    recoveredCSpecDirectionTransport next state

/-- The first unfilled loop, oriented to follow the edge-law convention. -/
noncomputable def globalCSpecNontrivialDirectionLoop :
    DirectionPath globalCSpecDirectionEdgeLaw 0 0 :=
  .cons 3 (.cons 1 (.cons 0 (.nil 0)))

theorem globalCSpecNontrivialDirectionLoop_transport :
    directionPathTransport globalCSpecNontrivialDirectionLoop =
      swapZeroOne := by
  apply Equiv.ext
  intro direction
  fin_cases direction <;>
    simp [globalCSpecNontrivialDirectionLoop, directionPathTransport,
      globalCSpecDirectionEdgeLaw,
      recoveredCSpecDirectionTransport_eq_witness,
      witnessSheetTransport, swapZeroOne]

/-- The continuation-derived full-S3 atlas cannot be globally assigned three
path-independent sheet labels. -/
theorem globalCSpecAtlas_has_no_globalDirectionLabeling :
    ¬ Nonempty (GlobalDirectionLabeling globalCSpecDirectionEdgeLaw) := by
  apply nontrivial_path_comparison_forbids_global_labeling
    (DirectionPath.nil 0) globalCSpecNontrivialDirectionLoop
  intro hEqual
  have hAtZero := DFunLike.congr_fun hEqual (0 : Fin 3)
  rw [globalCSpecNontrivialDirectionLoop_transport] at hAtZero
  norm_num [directionPathTransport, swapZeroOne] at hAtZero

/-! ## The associated rank-two connection has no parallel mode -/

/-- The uniform reversible connection whose sheet transport is recovered from
native CSpec continuation incidence. -/
noncomputable def globalCSpecRecoveredSheetConnection :
    ReversibleSheetConnection WitnessState where
  stationary := fun _ => 1
  transition := fun _ _ => 1 / 4
  sheetTransport := recoveredCSpecDirectionTransport
  stationary_pos := by intro; norm_num
  transition_nonneg := by intro; norm_num
  row_stochastic := by
    intro state
    fin_cases state <;> norm_num [Fin.sum_univ_succ]
  detailed_balance := by intro; norm_num
  transport_refl := recoveredCSpecDirectionTransport_refl
  transport_reverse := recoveredCSpecDirectionTransport_reverse

theorem globalCSpecRecovered_connectionLaplacian_eq_witness
    (field : WitnessState → SheetCarrier) (state : WitnessState) :
    connectionLaplacian globalCSpecRecoveredSheetConnection field state =
      connectionLaplacian fullS3WitnessConnection field state := by
  unfold connectionLaplacian twistedMarkov
  apply congrArg (fun transported => field state - transported)
  apply Finset.sum_congr rfl
  intro next _hNext
  rw [show globalCSpecRecoveredSheetConnection.transition state next =
      fullS3WitnessConnection.transition state next by rfl]
  rw [show globalCSpecRecoveredSheetConnection.sheetTransport state next =
      recoveredCSpecDirectionTransport state next by rfl]
  rw [recoveredCSpecDirectionTransport_eq_witness]
  rfl

/-- The rank-two trace-zero carrier associated to the intrinsic CSpec
transport has trivial connection-Laplacian kernel. -/
theorem globalCSpecRecoveredSheetConnection_kernel_trivial
    (field : WitnessState → SheetCarrier)
    (hKernel : ∀ state,
      connectionLaplacian globalCSpecRecoveredSheetConnection field state = 0) :
    field = 0 := by
  apply fullS3WitnessConnection_kernel_trivial field
  intro state
  rw [← globalCSpecRecovered_connectionLaplacian_eq_witness]
  exact hKernel state

/-- Equivalently, the intrinsic full-S3 carrier connection admits no nonzero
globally parallel carrier section. -/
theorem globalCSpecRecoveredSheetConnection_parallel_trivial
    (field : WitnessState → SheetCarrier)
    (hParallel : IsParallelSheetSection
      globalCSpecRecoveredSheetConnection field) :
    field = 0 := by
  apply globalCSpecRecoveredSheetConnection_kernel_trivial field
  exact (connectionLaplacian_eq_zero_iff_parallel
    globalCSpecRecoveredSheetConnection field).2 hParallel

/-- The complete finite certificate: one native causal scheme supplies
future-distinct regular CSpec points, an unfilled pairwise-overlap nerve, and
full S3 monodromy derived from causal overlap incidence. -/
theorem exists_global_finite_causal_CSpec_fullS3_atlas :
    Function.Injective globalRegularCSpecPoint ∧
      (∀ first second : WitnessState,
        (globalRegularCSpecChart first ∩
          globalRegularCSpecChart second).Nonempty) ∧
      (∀ first second third : WitnessState,
        first ≠ second → first ≠ third → second ≠ third →
          globalRegularCSpecChart first ∩
              globalRegularCSpecChart second ∩
                globalRegularCSpecChart third = ∅) ∧
      (∀ relabeling : Equiv.Perm (Fin 3),
        ∃ index : Fin 6,
          recoveredGlobalCSpecHolonomyWord index = relabeling) := by
  exact ⟨globalRegularCSpecPoint_injective,
    globalRegularCSpecChart_pair_intersection_nonempty,
    globalRegularCSpecChart_triple_intersection_empty,
    globalCSpecAtlas_hasFullS3Monodromy⟩

/-- **Intrinsic descent capstone.** Prime-future continuation incidence is
total on every overlap, composes on every genuine common regular point, has
surjective S3 monodromy, admits no global path-independent sheet labeling,
and leaves no nonzero parallel vector in the associated rank-two carrier. -/
theorem intrinsic_CSpec_descent_fullS3_package :
    (∀ first second : WitnessState, ∀ secondDirection : Fin 3,
      ∃! firstDirection,
        CSpecMatchedDirection first second firstDirection secondDirection) ∧
    (∀ first second third : WitnessState,
      ∀ point : CSpec globalAtlasCausalAlgebra,
        point ∈ globalRegularCSpecChart first →
        point ∈ globalRegularCSpecChart second →
        point ∈ globalRegularCSpecChart third →
          (recoveredCSpecDirectionTransport second third).trans
              (recoveredCSpecDirectionTransport first second) =
            recoveredCSpecDirectionTransport first third) ∧
    (∀ relabeling : Equiv.Perm (Fin 3),
      ∃ index : Fin 6,
        recoveredGlobalCSpecHolonomyWord index = relabeling) ∧
    ¬ Nonempty (GlobalDirectionLabeling globalCSpecDirectionEdgeLaw) ∧
    (∀ field : WitnessState → SheetCarrier,
      IsParallelSheetSection globalCSpecRecoveredSheetConnection field →
        field = 0) := by
  exact ⟨existsUnique_CSpecMatchedDirection,
    recoveredCSpecDirectionTransport_cocycle_on_commonPoint,
    globalCSpecAtlas_hasFullS3Monodromy,
    globalCSpecAtlas_has_no_globalDirectionLabeling,
    globalCSpecRecoveredSheetConnection_parallel_trivial⟩

#print axioms globalAtlasLE_trans
#print axioms globalAtlasEvent_card
#print axioms globalRegularCSpecPoint_injective
#print axioms globalRegularCSpecChart_pair_intersection_nonempty
#print axioms globalRegularCSpecChart_triple_intersection_empty
#print axioms globallyMatchedDirection_iff
#print axioms CSpecMatchedDirection_iff
#print axioms continuationWitness_independent
#print axioms existsUnique_CSpecMatchedDirection
#print axioms recoveredCSpecDirectionTransport_eq_witness
#print axioms recoveredCSpecDirectionTransport_cocycle_on_commonPoint
#print axioms globalCSpecAtlas_hasFullS3Monodromy
#print axioms globalCSpecMonodromy_action_transitive
#print axioms globalCSpecAtlas_has_no_globalDirectionLabeling
#print axioms globalCSpecRecoveredSheetConnection_parallel_trivial
#print axioms exists_global_finite_causal_CSpec_fullS3_atlas
#print axioms intrinsic_CSpec_descent_fullS3_package

end

end UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
