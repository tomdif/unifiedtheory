/-
  LayerB/FarField.lean — Net-charge far-field theorem

  The far-field gravitational response of any finite defect composite
  depends only on its total charge. Two systems with the same net
  charge are indistinguishable at large distance.

  This is the formal version of "gravity sees only total mass-energy."

  ALL PROVEN. No sorry. No axioms beyond Lean core.
-/
import UnifiedTheory.LayerB.MultiParticle

namespace UnifiedTheory.LayerB

open LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Far-field equivalence -/

/-- Two defects are **far-field equivalent** if they have the same charge.
    At large distance, only the charge (= net source strength) matters. -/
def FarFieldEquiv (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect) : Prop :=
  charge db d₁ = charge db d₂

/-- Far-field equivalence is an equivalence relation. -/
theorem farFieldEquiv_refl (db : ComposableDefectBlock V) (d : db.Defect) :
    FarFieldEquiv db d d := rfl

theorem farFieldEquiv_symm (db : ComposableDefectBlock V) (d₁ d₂ : db.Defect)
    (h : FarFieldEquiv db d₁ d₂) : FarFieldEquiv db d₂ d₁ := h.symm

theorem farFieldEquiv_trans (db : ComposableDefectBlock V) (d₁ d₂ d₃ : db.Defect)
    (h₁₂ : FarFieldEquiv db d₁ d₂) (h₂₃ : FarFieldEquiv db d₂ d₃) :
    FarFieldEquiv db d₁ d₃ := h₁₂.trans h₂₃

/-! ### Net-charge far-field theorem -/

/-- **Net-charge determines far field (composites).**
    Any two composites with the same net charge are far-field equivalent.
    This is the formal version of: gravity sees only total mass-energy. -/
theorem net_charge_determines_far_field (db : ComposableDefectBlock V)
    (base₁ base₂ : db.Defect) (rest₁ rest₂ : List db.Defect)
    (h_base : charge db base₁ = charge db base₂)
    (h_rest : totalCharge db rest₁ = totalCharge db rest₂) :
    FarFieldEquiv db (composeList db base₁ rest₁) (composeList db base₂ rest₂) := by
  simp only [FarFieldEquiv, charge_foldl, h_base, h_rest]

/-- **Internal rearrangement invariance.**
    The far-field response is unchanged by rearranging internal
    structure, as long as net charge is preserved.
    Two composites from the same ingredients in different order
    have the same far field. -/
theorem far_field_rearrangement (db : ComposableDefectBlock V)
    (d₁ d₂ : db.Defect) :
    FarFieldEquiv db (db.compose d₁ d₂) (db.compose d₂ d₁) := by
  simp only [FarFieldEquiv]
  exact charge_compose_comm db d₁ d₂

/-- **Neutral composites are far-field invisible.**
    Any composite with zero net charge has zero far-field response. -/
theorem neutral_far_field_invisible (db : ComposableDefectBlock V)
    (base : db.Defect) (rest : List db.Defect)
    (hbase : IsNeutral db base) (hrest : IsChargeBalanced db rest) :
    charge db (composeList db base rest) = 0 := by
  rw [charge_foldl, hbase, hrest, add_zero]

/-- **Single defect determines its own far field.**
    A lone defect's far-field response is exactly its charge. -/
theorem single_defect_far_field (db : ComposableDefectBlock V)
    (d : db.Defect) :
    charge db (composeList db d []) = charge db d := by
  simp [composeList, totalCharge, charge_foldl]

/-- **Far-field screening**: adding a neutral composite to any system
    does not change the far-field response. -/
theorem far_field_screening (db : ComposableDefectBlock V)
    (d : db.Defect) (screen : db.Defect) (h_neutral : IsNeutral db screen) :
    FarFieldEquiv db d (db.compose d screen) := by
  show charge db d = charge db (db.compose d screen)
  rw [charge_additive, h_neutral, add_zero]

/-- **Far-field screening by conjugate pair**: surrounding any defect
    with a conjugate pair does not alter its far field. -/
theorem far_field_conjugate_screen (db : ComposableDefectBlock V)
    (d screen : db.Defect) :
    FarFieldEquiv db d
      (db.compose (db.compose d screen) (db.conjugate screen)) := by
  show charge db d = charge db (db.compose (db.compose d screen) (db.conjugate screen))
  rw [charge_additive, charge_additive, charge_conjugate]
  ring

/-! ### Summary -/

/-- **Far-field theorem (complete).**
    The gravitational far field of any defect system is fully determined
    by its net charge. Neutral systems are invisible. Screening by
    conjugate pairs is exact. -/
theorem far_field_theorem (db : ComposableDefectBlock V) :
    -- (1) Net charge determines far field
    (∀ b₁ b₂ r₁ r₂, charge db b₁ = charge db b₂ →
      totalCharge db r₁ = totalCharge db r₂ →
      FarFieldEquiv db (composeList db b₁ r₁) (composeList db b₂ r₂))
    -- (2) Neutral systems invisible
    ∧ (∀ b r, IsNeutral db b → IsChargeBalanced db r →
        charge db (composeList db b r) = 0)
    -- (3) Conjugate screening exact
    ∧ (∀ d s, FarFieldEquiv db d
        (db.compose (db.compose d s) (db.conjugate s))) :=
  ⟨net_charge_determines_far_field db,
   neutral_far_field_invisible db,
   far_field_conjugate_screen db⟩

end UnifiedTheory.LayerB
