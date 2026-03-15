/-
  LayerB/DefectEquivalence.lean — Defect equivalence and classification

  Defines when two defects are physically equivalent: same source
  measure, same bias, same dressing class. Then classifies stable
  defects into three sectors: inert, source-carrying, and purely
  topological.

  This is the first defect classification layer.
-/
import UnifiedTheory.LayerB.DefectBridge

namespace UnifiedTheory.LayerB

open LayerA

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-! ### Defect invariants -/

/-- The observable invariants of a defect: source strength, bias,
    and dressing strength. Two defects with the same invariants
    are physically equivalent. -/
structure DefectInvariants where
  /-- Source strength (from K-part) -/
  sourceStrength : ℝ
  /-- Focusing bias (from null projection) -/
  focusingBias : ℝ
  /-- Dressing strength (from P-part) -/
  dressingStrength : ℝ

/-- Extract the observable invariants from a defect. -/
def extractInvariants (db : DefectBlock V) (d : db.Defect) : DefectInvariants where
  sourceStrength := db.sourceMeas.measure (db.toBF d).Kpart
  focusingBias := (db.toNull d).bias
  dressingStrength := db.sourceMeas.measure (db.toBF d).Ppart

/-- Two defects are **physically equivalent** if they have the
    same observable invariants. -/
def DefectEquiv (db : DefectBlock V) (d₁ d₂ : db.Defect) : Prop :=
  extractInvariants db d₁ = extractInvariants db d₂

/-- DefectEquiv is reflexive. -/
theorem defectEquiv_refl (db : DefectBlock V) (d : db.Defect) :
    DefectEquiv db d d :=
  rfl

/-- DefectEquiv is symmetric. -/
theorem defectEquiv_symm (db : DefectBlock V) (d₁ d₂ : db.Defect)
    (h : DefectEquiv db d₁ d₂) : DefectEquiv db d₂ d₁ :=
  h.symm

/-- DefectEquiv is transitive. -/
theorem defectEquiv_trans (db : DefectBlock V) (d₁ d₂ d₃ : db.Defect)
    (h₁₂ : DefectEquiv db d₁ d₂) (h₂₃ : DefectEquiv db d₂ d₃) :
    DefectEquiv db d₁ d₃ :=
  h₁₂.trans h₂₃

/-! ### Defect sectors -/

/-- A defect is **inert** if it carries zero source strength
    and zero focusing bias. It is pure dressing. -/
def IsInert (db : DefectBlock V) (d : db.Defect) : Prop :=
  db.sourceMeas.measure (db.toBF d).Kpart = 0
  ∧ (db.toNull d).bias = 0

/-- A defect is **source-carrying** if it has nonzero source strength. -/
def IsSourceCarrying (db : DefectBlock V) (d : db.Defect) : Prop :=
  db.sourceMeas.measure (db.toBF d).Kpart ≠ 0

/-- A defect is **purely topological** if its K-part vanishes in V
    (not just zero source measure, but actually zero K-component). -/
def IsPurelyTopological (db : DefectBlock V) (d : db.Defect) : Prop :=
  (db.toBF d).Kpart = 0

/-! ### Classification theorems -/

/-- **Stable inert defects have zero focusing bias.**
    An inert stable defect contributes nothing to either the
    gravitational source or the null focusing. -/
theorem inert_has_zero_bias (db : DefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (hi : IsInert db d) :
    biasMeasure (db.toNull d) db.biasScale = 0 := by
  rw [← defect_source_bridge db d hd]
  exact hi.1

/-- **Source-carrying defects have nonzero focusing bias**
    (assuming nonzero bias scale). The bridge theorem forces this:
    if the K-part sources gravity, it must also focus null rays. -/
theorem source_carrying_has_bias (db : DefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (hs : IsSourceCarrying db d)
    (_hscale : db.biasScale ≠ 0) :
    (db.toNull d).bias ≠ 0 := by
  intro hbias
  apply hs
  rw [defect_source_bridge db d hd]
  simp [biasMeasure, hbias]

/-- **Purely topological defects are inert** (assuming stable). -/
theorem purely_topological_is_inert (db : DefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (ht : IsPurelyTopological db d)
    (hscale : db.biasScale ≠ 0) :
    IsInert db d := by
  have hK : (db.toBF d).Kpart = 0 := ht
  constructor
  · rw [hK, map_zero]
  · have h := defect_source_bridge db d hd
    rw [hK, map_zero] at h
    simp only [biasMeasure] at h
    exact (mul_eq_zero.mp h.symm).resolve_left hscale

/-- **Stable defects dichotomize** (with nonzero bias scale):
    every stable defect is either inert or source-carrying. -/
theorem defect_dichotomy (db : DefectBlock V)
    (d : db.Defect) (hd : db.Stable d) (hscale : db.biasScale ≠ 0) :
    IsInert db d ∨ IsSourceCarrying db d := by
  by_cases h : db.sourceMeas.measure (db.toBF d).Kpart = 0
  · left
    exact ⟨h, by
      have hbridge := defect_source_bridge db d hd
      rw [h] at hbridge
      simp only [biasMeasure] at hbridge
      exact (mul_eq_zero.mp hbridge.symm).resolve_left hscale⟩
  · exact Or.inr h

end UnifiedTheory.LayerB
