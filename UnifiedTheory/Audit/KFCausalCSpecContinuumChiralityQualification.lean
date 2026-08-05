/-
  Audit/KFCausalCSpecContinuumChiralityQualification.lean

  CONTINUUM QUALIFICATION OF THE PHYSICALLY REALIZED CSPEC CHIRAL SECTOR

  The physical global-atlas history now derives a finite determinant sign and
  a pure gamma-five weak vertex.  This file proves the strongest continuum
  statement supported by the present repository.

  * The finite vertex lifts pointwise to a nontrivial purely chiral weak-field
    operator on every nonempty base type.
  * Every order-faithful causal-to-continuum map intertwines order duality with
    target-order reversal, without metric reconstruction.
  * Four-dimensional time reversal has determinant -1, and an orientation-odd
    continuum integral makes the corresponding Term-III action change sign.

  It also proves the decisive boundary: orientation-oddness is not automatic
  for an arbitrary continuum functional.  Thus sequential growth has now
  supplied the physical finite CSpec sector, but a genuine Lorentzian Dirac
  limit still requires a continuum field/integration construction.  We do not
  disguise that missing construction as a theorem.

  Zero sorry. Zero custom axioms.
-/

import UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
import UnifiedTheory.LayerA.ArrowChiralityLock
import UnifiedTheory.LayerA.ContinuumChiralityFlip

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace UnifiedTheory.Audit.KFCausalCSpecContinuumChiralityQualification

noncomputable section

open UnifiedTheory.Audit.KFCausalSetSequentialGrowth
open UnifiedTheory.Audit.KFCausalCSpecGlobalAtlas
open UnifiedTheory.Audit.KFCausalCSpecDeterminantChirality
open UnifiedTheory.Audit.KFCausalDeterminantWeakCurrent
open UnifiedTheory.Audit.KFCausalCSpecPhysicalGrowthRealization
open UnifiedTheory.Audit.KFCausalSetWeakHandednessBridge
open UnifiedTheory.LayerA.ArrowChiralityLock
open UnifiedTheory.LayerA.ContinuumChiralityFlip

/-! ## 1. Pointwise weak fields over an arbitrary continuum base -/

/-- A continuum-indexed weak Dirac field.  No topology, smoothness, Lorentz
action, or Dirac equation is silently included in this abbreviation. -/
abbrev DiracWeakField (X : Type*) := X → DiracWeakSpinor

/-- Pointwise lift of a finite spinor vertex to fields. -/
def pointwiseWeakFieldVertex {X : Type*}
    (vertex : DiracWeakSpinor → DiracWeakSpinor)
    (field : DiracWeakField X) : DiracWeakField X :=
  fun point => vertex (field point)

def leftWeylFieldProjector {X : Type*}
    (field : DiracWeakField X) : DiracWeakField X :=
  fun point => leftWeylProjector (field point)

def rightWeylFieldProjector {X : Type*}
    (field : DiracWeakField X) : DiracWeakField X :=
  fun point => rightWeylProjector (field point)

/-- Exact pointwise specification of a nontrivial purely left-handed field
interaction. -/
def IsNontrivialPointwiseLeftHanded {X : Type*}
    (vertex : DiracWeakField X → DiracWeakField X) : Prop :=
  (∀ field, vertex (rightWeylFieldProjector field) = 0) ∧
  (∀ field, vertex (leftWeylFieldProjector field) = vertex field) ∧
  ∃ field, vertex field ≠ 0

def IsNontrivialPointwiseRightHanded {X : Type*}
    (vertex : DiracWeakField X → DiracWeakField X) : Prop :=
  (∀ field, vertex (leftWeylFieldProjector field) = 0) ∧
  (∀ field, vertex (rightWeylFieldProjector field) = vertex field) ∧
  ∃ field, vertex field ≠ 0

theorem pointwise_lift_preserves_nontrivial_left
    {X : Type*} [Nonempty X]
    (vertex : DiracWeakSpinor → DiracWeakSpinor)
    (hVertex : IsNontrivialPurelyLeftHanded vertex) :
    IsNontrivialPointwiseLeftHanded
      (pointwiseWeakFieldVertex (X := X) vertex) := by
  refine ⟨?_, ?_, ?_⟩
  · intro field
    funext point chirality spin isospin
    have hZero := hVertex.1 (field point)
    exact congrFun (congrFun (congrFun hZero chirality) spin) isospin
  · intro field
    funext point chirality spin isospin
    have hAbsorb := hVertex.2.1 (field point)
    exact congrFun (congrFun (congrFun hAbsorb chirality) spin) isospin
  · let field : DiracWeakField X := fun _ => leftLowerWeakState
    refine ⟨field, ?_⟩
    intro hZero
    let point : X := Classical.choice inferInstance
    have hAtPoint := congrFun hZero point
    exact hVertex.2.2 hAtPoint

theorem pointwise_lift_preserves_nontrivial_right
    {X : Type*} [Nonempty X]
    (vertex : DiracWeakSpinor → DiracWeakSpinor)
    (hVertex : IsNontrivialPurelyRightHanded vertex) :
    IsNontrivialPointwiseRightHanded
      (pointwiseWeakFieldVertex (X := X) vertex) := by
  refine ⟨?_, ?_, ?_⟩
  · intro field
    funext point chirality spin isospin
    have hZero := hVertex.1 (field point)
    exact congrFun (congrFun (congrFun hZero chirality) spin) isospin
  · intro field
    funext point chirality spin isospin
    have hAbsorb := hVertex.2.1 (field point)
    exact congrFun (congrFun (congrFun hAbsorb chirality) spin) isospin
  · let field : DiracWeakField X := fun _ => rightLowerWeakState
    refine ⟨field, ?_⟩
    intro hZero
    let point : X := Classical.choice inferInstance
    have hAtPoint := congrFun hZero point
    exact hVertex.2.2 hAtPoint

/-- The determinant-selected finite law therefore gives a nontrivial purely
chiral pointwise weak-field law on every nonempty base. -/
theorem cSpecDeterminant_derives_pointwise_chiral_weakField
    {X : Type*} [Nonempty X] (n : ℕ)
    (history : RankedGrowthPath CSpecAtlasBranch n) :
    (cSpecAtlasOrientation n history = 1 ∧
        IsNontrivialPointwiseLeftHanded
          (pointwiseWeakFieldVertex (X := X)
            (cSpecAtlasWeakVertex n history)))
      ∨ (cSpecAtlasOrientation n history = -1 ∧
        IsNontrivialPointwiseRightHanded
          (pointwiseWeakFieldVertex (X := X)
            (cSpecAtlasWeakVertex n history))) := by
  rcases cSpecDeterminant_derives_purelyChiral_weakVertex n history with
    hLeft | hRight
  · exact Or.inl ⟨hLeft.1,
      pointwise_lift_preserves_nontrivial_left _ hLeft.2⟩
  · exact Or.inr ⟨hRight.1,
      pointwise_lift_preserves_nontrivial_right _ hRight.2⟩

/-! ## 2. What order faithfulness and oriented integration actually imply -/

/-- Every order-faithful embedding carries reversal of the physically
realized atlas order to reversal of the target causal order. -/
theorem physicalAtlas_orderDual_intertwines
    {Q : Type*} [Preorder Q] (embedding : GlobalAtlasEvent ↪o Q)
    (event : GlobalAtlasEventᵒᵈ) :
    bridgeDual embedding event = embedding (OrderDual.ofDual event) := rfl

/-- The continuum sign-flip package in 3+1 dimensions.  Its only non-finite
input is the defining orientation-oddness of the continuum integral. -/
theorem fourDimensional_continuum_chirality_flip
    (integral : ZMod 2 → ℝ) (hOdd : OrientationOdd integral)
    (gamma : ℝ) (orientation : ZMod 2) :
    (timeReversal 3).det = -1 ∧
      gamma * integral (orientationFlip orientation) =
        -(gamma * integral orientation) ∧
      orientationFlip orientation ≠ orientation := by
  exact ⟨timeReversal_det 3,
    termIII_flips_under_time_reversal integral hOdd gamma orientation,
    by
      rw [orientationFlip]
      intro hFixed
      have hOne : (1 : ZMod 2) = 0 := by linear_combination hFixed
      exact one_ne_zero hOne⟩

/-! ## 3. The remaining continuum datum is provably not automatic -/

/-- A simple orientation-even functional. -/
def constantUnitIntegral : ZMod 2 → ℝ := fun _ => 1

/-- Orientation-oddness is not a theorem about arbitrary functionals. -/
theorem constantUnitIntegral_not_orientationOdd :
    ¬ OrientationOdd constantUnitIntegral := by
  intro hOdd
  have hAtZero := hOdd 0
  norm_num [constantUnitIntegral] at hAtZero

theorem orientationOdd_not_automatic :
    ¬ (∀ integral : ZMod 2 → ℝ, OrientationOdd integral) := by
  intro hAll
  exact constantUnitIntegral_not_orientationOdd
    (hAll constantUnitIntegral)

/-! ## 4. Qualified physical-to-continuum capstone -/

/-- **Qualified continuum theorem.**  A nonzero-amplitude physical growth
history realizes the full-S3 CSpec endpoint.  On every nonempty continuum
base its odd determinant loop lifts to a nontrivial pointwise right-handed
mirror field in the fixed convention.  Every order-faithful embedding carries
causal reversal to target reversal, and every orientation-odd continuum
integral flips the Term-III sign in 3+1 dimensions.

This theorem explicitly takes the order embedding and orientation-odd
integral as continuum inputs; `orientationOdd_not_automatic` proves that the
latter cannot be erased from the current theory. -/
theorem physicalCSpec_continuum_chirality_qualification
    {X Q : Type*} [Nonempty X] [Preorder Q]
    (embedding : GlobalAtlasEvent ↪o Q)
    (integral : ZMod 2 → ℝ) (hOdd : OrientationOdd integral)
    (gamma : ℝ) (orientation : ZMod 2) :
    IsPhysicalCausalGrowthPath 140
        (globalAtlasPhysicalGrowthPath 140 le_rfl)
      ∧ finiteRankedPathAmplitude uniformUnlabeledCausalSetGrowthLaw 140
          (globalAtlasPhysicalGrowthPath 140 le_rfl) ≠ 0
      ∧ IsNontrivialPointwiseRightHanded
          (pointwiseWeakFieldVertex (X := X)
            (cSpecAtlasWeakVertex 3 cSpecOddLoopHistory))
      ∧ (∀ event : GlobalAtlasEventᵒᵈ,
          bridgeDual embedding event =
            embedding (OrderDual.ofDual event))
      ∧ (timeReversal 3).det = -1
      ∧ gamma * integral (orientationFlip orientation) =
          -(gamma * integral orientation) := by
  refine ⟨globalAtlasPhysicalGrowthPath_isPhysical 140 le_rfl,
    globalAtlasPhysicalGrowthPath_uniformAmplitude_ne_zero 140 le_rfl,
    ?_, fun event => physicalAtlas_orderDual_intertwines embedding event,
    timeReversal_det 3,
    termIII_flips_under_time_reversal integral hOdd gamma orientation⟩
  exact pointwise_lift_preserves_nontrivial_right _
    cSpecOddLoop_derives_rightWeakMirror

#print axioms cSpecDeterminant_derives_pointwise_chiral_weakField
#print axioms fourDimensional_continuum_chirality_flip
#print axioms orientationOdd_not_automatic
#print axioms physicalCSpec_continuum_chirality_qualification

end

end UnifiedTheory.Audit.KFCausalCSpecContinuumChiralityQualification
